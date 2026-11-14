#!/usr/bin/env python3
"""Actualiza data/resultados.json leyendo los extractos publicados en páginas web.

Consulta VARIAS fuentes a la vez (la web oficial de la Lotería de la Ciudad, La Nación, El Cronista y, como respaldo, NotiTimba) y, para cada sorteo, se queda con la
primera que lo trae completo y válido (20 premios, que coincidan con "A la cabeza").
Si otra fuente trae el mismo sorteo con números distintos, deja un aviso y no pisa lo ya guardado.

Uso normal (lo corre GitHub Actions cada pocos minutos):
    python scripts/actualizar.py

Opciones útiles:
    --siempre                         consulta todas las fuentes aunque no haya sorteos pendientes

Historial: se guardan 10 días (hoy y los 9 anteriores). Si en esos días falta algún sorteo ya jugado, el mismo comando
lo rellena desde la web oficial, que publica unas 4 semanas de sorteos. Por eso alcanza con correr una vez el flujo a mano.
    --archivo pagina.html --quiniela provincia
                                      lee un HTML guardado de La Nación y muestra qué entendió (no escribe nada)
    --archivo nota.html --quiniela entrerios --fuente cronista --turno vespertina --fecha 2026-11-14
                                      lo mismo con una nota de El Cronista
    --archivo sorteo.js --fuente oficial
                                      lo mismo con el archivo de un sorteo de la web oficial (muestra las 6 quinielas)
    --archivo respuesta.txt --fuente notitimba
                                      lo mismo con una respuesta guardada de notitimba.com/lots/cfms/aQsEq.php

Solo usa la librería estándar de Python.
"""
import argparse
import json
import re
import sys
import unicodedata
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import date, datetime, timedelta, timezone
from functools import partial
from html.parser import HTMLParser
from pathlib import Path
from threading import Lock

AR = timezone(timedelta(hours=-3))                      # Argentina no usa horario de verano
RAIZ = Path(__file__).resolve().parent.parent
SALIDA = RAIZ / "data" / "resultados.json"
DIAS_A_GUARDAR = 10                                     # días corridos: hoy y los 9 anteriores (los domingos no hay sorteos)
MINUTOS_DE_ESPERA = 120                                 # cuánto se sigue buscando un sorteo después de su hora

# Quinielas que maneja la app.
QUINIELAS = ("provincia", "ciudad", "santafe", "cordoba", "entrerios", "montevideo")

# Fuente 1: La Nación (una página por quiniela con los últimos sorteos). No tiene Entre Ríos.
BASE = "https://www.lanacion.com.ar/loterias/"
FUENTES = {
    "provincia": BASE + "quiniela-provincia/",
    "ciudad": BASE + "quiniela-nacional/",
    "santafe": BASE + "quiniela-santa-fe/",
    "cordoba": BASE + "quiniela-cordoba/",
    "montevideo": BASE + "quiniela-montevideo/",
}

# Fuente 2: El Cronista (una nota por sorteo; las notas se encuentran desde la página de temas).
CRONISTA = "https://www.cronista.com"
CRONISTA_TEMA = CRONISTA + "/tema/quiniela/"
CRONISTA_CLAVE = {                                      # cómo aparece cada quiniela en las direcciones de las notas
    "provincia": "provincia-y-ciudad", "ciudad": "provincia-y-ciudad", "santafe": "santa-fe",
    "cordoba": "cordoba", "entrerios": "entre-rios", "montevideo": "montevideo",
}

# Mismos horarios que en index.html.
HORARIOS = {
    "base": {"previa": "10:15", "primera": "12:00", "matutina": "15:00", "vespertina": "18:00", "nocturna": "21:00"},
    "montevideo": {"matutina": "15:00", "nocturna": "21:00"},
}
# Todas las quinielas se muestran con 4 cifras. Montevideo sortea 3 y toma la primera cifra del número de Ciudad (Nacional)
# que salió en la misma posición: las fuentes ya lo traen armado de 4, pero si alguna lo trae de 3 se completa (ajustar_montevideo).
CIFRAS = {"montevideo": (3, 4)}
TURNOS = ("previa", "primera", "matutina", "vespertina", "nocturna")


# ---------- HTML -> texto ----------
class _Texto(HTMLParser):
    BLOQUES = {"p", "div", "li", "ul", "ol", "br", "tr", "td", "th", "table", "section", "article", "header",
               "footer", "h1", "h2", "h3", "h4", "h5", "h6", "main", "aside", "nav", "figure", "figcaption",
               "blockquote", "pre", "dd", "dt", "dl"}
    IGNORAR = {"script", "style", "noscript", "template", "svg"}

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.partes, self._saltar = [], 0

    def handle_starttag(self, tag, attrs):
        if tag in self.IGNORAR:
            self._saltar += 1
        elif tag in self.BLOQUES:
            self.partes.append("\n")

    def handle_endtag(self, tag):
        if tag in self.IGNORAR:
            self._saltar = max(0, self._saltar - 1)
        elif tag in self.BLOQUES:
            self.partes.append("\n")

    def handle_data(self, dato):
        if not self._saltar:
            self.partes.append(dato)


def html_a_texto(html):
    p = _Texto()
    p.feed(html)
    lineas = [re.sub(r"[ \t ]+", " ", l).strip() for l in "".join(p.partes).split("\n")]
    return "\n".join(l for l in lineas if l)


# ---------- Lectura de sorteos ----------
ENCABEZADO = re.compile(
    r"^(Previa|Primera|Matutina|Vespertina|Nocturna)\s*[-–—]\s*[^\d\n]*?(\d{1,2})/(\d{1,2})/(\d{4})",
    re.I | re.M,
)
CABEZA = re.compile(r"A la Cabeza\s*:?\s*(\d{1,2})[ \t]*([^\n]*)", re.I)
LETRAS = re.compile(r"Letras\s*:?\s*([A-ZÑ])\s*[-–]?\s*([A-ZÑ])\s*[-–]?\s*([A-ZÑ])\s*[-–]?\s*([A-ZÑ])", re.I)


def _intentar(tokens, i, cifras):
    """Lee 20 premios seguidos desde tokens[i]. Cada premio puede venir como 'PPNNNN' o como 'PP' y 'NNNN'.
    Devuelve (numeros, indice_del_token_siguiente) o None."""
    nums, j, largo = [], i, None
    for pos in range(1, 21):
        if j >= len(tokens):
            return None
        t, p = tokens[j], f"{pos:02d}"
        if len(t) >= 5 and t[:2] == p:
            n, j = t[2:], j + 1
        elif t in (p, str(pos)) and j + 1 < len(tokens):
            n, j = tokens[j + 1], j + 2
        else:
            return None
        if len(n) not in cifras or (largo is not None and len(n) != largo):
            return None
        largo = len(n)
        nums.append(n)
    return nums, j


NO_VINCULANTE = re.compile(r"no\s+vinculantes?", re.I)
JURISDICCIONES = (
    ("entrerios", "Entre Ríos", r"entre\s*r[ií]os"),
    ("santafe", "Santa Fe", r"santa\s*fe"),
    ("cordoba", "Córdoba", r"c[óo]rdoba"),
    ("montevideo", "Montevideo", r"montevideo"),
    ("provincia", "Provincia", r"provincia|buenos\s+aires"),
    ("ciudad", "Ciudad", r"ciudad|nacional"),
)


def detectar_no_vinculante(ventana, quiniela):
    """Si el texto del sorteo dice 'no vinculante', devuelve (True, jurisdiccion_o_None).
    La jurisdicción solo se informa si, descartando la propia quiniela, aparece una sola cerca de la frase."""
    m = NO_VINCULANTE.search(ventana)
    if not m:
        return False, None
    cerca = ventana[max(0, m.start() - 140): m.end() + 140]
    otras = [nombre for qid, nombre, rx in JURISDICCIONES if qid != quiniela and re.search(rx, cerca, re.I)]
    return True, (otras[0] if len(otras) == 1 else None)


def leer_sorteos(html, quiniela):
    """Devuelve (sorteos, avisos). Un sorteo solo se acepta si trae 20 premios y coincide con 'A la Cabeza'."""
    texto = html_a_texto(html)
    cifras = CIFRAS.get(quiniela, (4,))
    avisos, sorteos, vistos = [], [], set()
    marcas = list(ENCABEZADO.finditer(texto))
    if not marcas:
        return [], ["No encontré ningún encabezado de turno (ej. 'Matutina - Sábado 14/11/2026'). ¿Cambió la página?"]
    for i, m in enumerate(marcas):
        turno = m.group(1).lower()
        fecha = f"{m.group(4)}-{int(m.group(3)):02d}-{int(m.group(2)):02d}"
        if turno not in TURNOS or (fecha, turno) in vistos:
            continue
        fin = marcas[i + 1].start() if i + 1 < len(marcas) else len(texto)
        bloque = texto[m.end():fin]
        cab = CABEZA.search(bloque)
        cabeza = cab.group(1).zfill(2) if cab else None
        nombre = re.split(r"Letras", cab.group(2), flags=re.I)[0].strip() if cab else None
        lt = LETRAS.search(bloque)
        letras = "".join(lt.groups()).upper() if lt else None
        resto = bloque[cab.end():] if cab else bloque
        marcas_num = list(re.finditer(r"\d+", resto))
        tokens = [t.group() for t in marcas_num]
        hallado = next((r for r in (_intentar(tokens, k, cifras) for k in range(len(tokens))) if r), None)
        nums = hallado[0] if hallado else None
        etiqueta = f"{quiniela} {turno} {fecha}"
        if not nums:
            avisos.append(f"{etiqueta}: no pude leer los 20 premios (puede que el sorteo todavía no esté publicado).")
            continue
        if cabeza and nums[0][-2:] != cabeza:
            avisos.append(f"{etiqueta}: 'A la Cabeza' dice {cabeza} pero el primer premio es {nums[0]}. Lo descarto.")
            continue
        vistos.add((fecha, turno))
        # Se mira solo el texto de este sorteo (del encabezado hasta un poco después del último premio),
        # para no confundirse con avisos generales del pie de la página.
        fin_premios = (cab.end() if cab else 0) + marcas_num[hallado[1] - 1].end()
        no_vinc, por = detectar_no_vinculante(texto[m.start(): m.end() + fin_premios + 160], quiniela)
        sorteo = {"fecha": fecha, "turno": turno, "numeros": nums, "nombre": nombre or None, "letras": letras}
        if no_vinc:
            sorteo["no_vinculante"], sorteo["sorteado_por"] = True, por
            avisos.append(f"NOTA {etiqueta}: sorteo NO VINCULANTE" + (f" (realizado por {por})" if por else "") + ".")
        sorteos.append(sorteo)
    return sorteos, avisos


# ---------- El Cronista ----------
MESES = {"enero": 1, "febrero": 2, "marzo": 3, "abril": 4, "mayo": 5, "junio": 6, "julio": 7, "agosto": 8,
         "septiembre": 9, "setiembre": 9, "octubre": 10, "noviembre": 11, "diciembre": 12}
DIAS_SEMANA = ("lunes", "martes", "miercoles", "jueves", "viernes", "sabado", "domingo")
ENLACE = re.compile(r"""href=["']((?:https://www\.cronista\.com)?/informacion-gral/[^"'#?\s]+)""", re.I)
FECHA_EN_ENLACE = re.compile(r"(lunes|martes|miercoles|jueves|viernes|sabado|domingo)-(\d{1,2})-de-([a-z]+)")
PAR = re.compile(r"(?<![\d.,])(\d{1,2})\s*[°º.]\s*(\d{3,4})(?!\d)")        # "1° 8161", "11. 4673"
CABEZA_CRONISTA = re.compile(r"a la cabeza[^0-9]{0,40}?(\d{3,4})(?:\s*[-–—]\s*([^\n|.:]{1,40}))?", re.I)
LETRAS_CRONISTA = re.compile(r"(?i:letras)[^\n:]{0,45}:?\s*([A-ZÑ])[\s,.\-–]*([A-ZÑ])[\s,.\-–]*([A-ZÑ])[\s,.\-–]*([A-ZÑ])(?![A-Za-zñÑ])")


def _sin_tildes(t):
    return "".join(c for c in unicodedata.normalize("NFD", t) if unicodedata.category(c) != "Mn")


def _fecha_del_enlace(dia_semana, dia, mes, ahora):
    """El enlace trae 'jueves-17-de-septiembre' sin año: se busca el año que cuadra con el día de la semana y esté cerca de hoy."""
    if mes not in MESES:
        return None
    for anio in (ahora.year, ahora.year - 1, ahora.year + 1):
        try:
            f = date(anio, MESES[mes], int(dia))
        except ValueError:
            continue
        if DIAS_SEMANA[f.weekday()] == dia_semana and abs((f - ahora.date()).days) <= 10:
            return f.isoformat()
    return None


def enlaces_cronista(html, quiniela, ahora):
    """Notas de la página de temas que son de esta quiniela y de hoy/ayer. Devuelve [(url, turno, fecha_iso)]."""
    clave = f"quiniela-de-{CRONISTA_CLAVE[quiniela]}-"
    validas = {ahora.date().isoformat(), (ahora.date() - timedelta(days=1)).isoformat()}
    vistos, res = set(), []
    for href in ENLACE.findall(html):
        url = href if href.startswith("http") else CRONISTA + href
        slug = _sin_tildes(url.rstrip("/").rsplit("/", 1)[-1].lower())
        if url in vistos or clave not in slug:
            continue
        vistos.add(url)
        turno = next((t for t in slug.split("-") if t in TURNOS), None)
        m = FECHA_EN_ENLACE.search(slug)
        fecha = _fecha_del_enlace(m.group(1), m.group(2), m.group(3), ahora) if m else None
        if turno and fecha in validas:
            res.append((url, turno, fecha))
    return res


def _bloques_de_20(texto, cifras):
    """Busca grupos de 20 pares 'N° número' que cubran exactamente las posiciones 1 a 20 (en una o dos columnas)."""
    pares = [(m.start(), int(m.group(1)), m.group(2)) for m in PAR.finditer(texto)]
    pares = [p for p in pares if 1 <= p[1] <= 20 and len(p[2]) in cifras]
    bloques, i = [], 0
    while i < len(pares):
        grupo = pares[i:i + 20]
        if len(grupo) == 20 and sorted(g[1] for g in grupo) == list(range(1, 21)) and len({len(g[2]) for g in grupo}) == 1:
            nums = [n for _, _, n in sorted(grupo, key=lambda g: g[1])]
            bloques.append((grupo[0][0], grupo[-1][0], nums))
            i += 20
        else:
            i += 1
    return bloques


def _etiqueta_de_bloque(texto_norm, inicio):
    """En la nota conjunta de Provincia y Ciudad, decide a cuál pertenece una tabla según el título más cercano que la antecede."""
    previo = texto_norm[max(0, inicio - 700):inicio]
    prov = max(previo.rfind("provincia"), previo.rfind("bonaerense"))
    ciu = max(previo.rfind("ciudad"), previo.rfind("nacional"))
    if prov == ciu:
        return None
    return "provincia" if prov > ciu else "ciudad"


def leer_articulo_cronista(html, quiniela, turno, fecha, cifras=None):
    """Lee una nota de El Cronista. Devuelve (sorteo_o_None, avisos)."""
    cifras = cifras or CIFRAS.get(quiniela, (4,))
    avisos, etiqueta = [], f"{quiniela} {turno} {fecha} (El Cronista)"
    titulo = re.search(r"<title[^>]*>(.*?)</title>", html, re.I | re.S)
    if titulo:
        en_titulo = {t for t in TURNOS if t in _sin_tildes(titulo.group(1).lower())}
        if en_titulo and turno not in en_titulo:
            return None, [f"{etiqueta}: la dirección dice {turno} pero el título dice {sorted(en_titulo)}. No lo uso."]
    texto = re.sub(r"[ \t ]+", " ", html_a_texto(html))
    norm = _sin_tildes(texto.lower())
    bloques = _bloques_de_20(texto, cifras)
    if not bloques:
        return None, [f"{etiqueta}: no encontré la tabla de 20 premios (puede que todavía no esté publicada)."]
    if CRONISTA_CLAVE[quiniela] == "provincia-y-ciudad":                   # nota conjunta: dos tablas
        propias = {}
        for ini, fin, nums in bloques:
            lado = _etiqueta_de_bloque(norm, ini)
            if lado is None:
                avisos.append(f"{etiqueta}: no pude saber a qué quiniela corresponde una de las tablas.")
                continue
            if lado in propias and propias[lado][2] != nums:
                return None, avisos + [f"{etiqueta}: hay dos tablas distintas para {lado}. No lo uso."]
            propias.setdefault(lado, (ini, fin, nums))
        if quiniela not in propias:
            return None, avisos + [f"{etiqueta}: la nota todavía no trae la tabla de {quiniela}."]
        ini, fin, nums = propias[quiniela]
        otro_ini = min([b[0] for b in propias.values() if b[0] > ini], default=None)
    else:
        distintas = {tuple(b[2]) for b in bloques}
        if len(distintas) > 1:
            return None, [f"{etiqueta}: hay más de una tabla distinta en la nota. No lo uso."]
        ini, fin, nums = bloques[0]
        otro_ini = None
    # "A la cabeza": la mención más cercana antes de la tabla.
    cabezas = [m for m in CABEZA_CRONISTA.finditer(texto, 0, ini)]
    nombre = None
    if cabezas:
        c = cabezas[-1]
        if c.group(1)[-2:] != nums[0][-2:]:
            return None, avisos + [f"{etiqueta}: 'A la cabeza' dice {c.group(1)} pero el primer premio es {nums[0]}. Lo descarto."]
        nombre = (c.group(2) or "").strip() or None
    letras = None
    if quiniela == "ciudad":
        lt = LETRAS_CRONISTA.search(texto, ini, otro_ini or min(len(texto), fin + 600)) or LETRAS_CRONISTA.search(texto, max(0, ini - 500), ini)
        letras = "".join(lt.groups()).upper() if lt else None
    sorteo = {"fecha": fecha, "turno": turno, "numeros": nums, "nombre": nombre, "letras": letras}
    contexto = texto[max(0, ini - 400):fin + 200]
    no_vinc, por = detectar_no_vinculante(contexto, quiniela)
    if no_vinc:
        sorteo["no_vinculante"], sorteo["sorteado_por"] = True, por
        avisos.append(f"NOTA {etiqueta}: sorteo NO VINCULANTE" + (f" (realizado por {por})" if por else "") + ".")
    return sorteo, avisos


def leer_cronista(quiniela, ahora, bajar, ya_tiene=lambda fecha, turno: False):
    """Busca en la página de temas las notas de hoy de esta quiniela y lee las que todavía no tenemos."""
    sorteos, avisos = [], []
    enlaces = enlaces_cronista(bajar(CRONISTA_TEMA), quiniela, ahora)
    for url, turno, fecha in enlaces[:6]:
        if ya_tiene(fecha, turno):
            continue
        try:
            nota = bajar(url)
        except Exception as e:
            avisos.append(f"{quiniela} {turno} {fecha} (El Cronista): no se pudo descargar la nota ({e})")
            continue
        sorteo, av = leer_articulo_cronista(nota, quiniela, turno, fecha)
        avisos += av
        if sorteo:
            sorteos.append(sorteo)
    return sorteos, avisos


# ---------- Web oficial de la Lotería de la Ciudad ----------
# Es la fuente de primera mano: por cada sorteo publica en un solo archivo los 20 premios de Ciudad, Provincia,
# Santa Fe, Córdoba, Entre Ríos y Montevideo (también Mendoza, que la app no usa).
OFICIAL = "https://quiniela.loteriadelaciudad.gob.ar"
OFICIAL_DATOS = OFICIAL + "/includes/resultados-data.php?sorteo={}"
OFICIAL_MODALIDADES = {"PREV": "previa", "PRIM": "primera", "MATU": "matutina", "VESP": "vespertina", "NOCT": "nocturna"}
# En la portada cada sorteo ya publicado figura así: <li data-value='53170'>14/11/2026 - 18:00 - Sorteo Nº 53170 - VESPERTINA</li>
OFICIAL_LISTA = re.compile(r"data-value='(\d+)'>\s*(\d{2})/(\d{2})/(\d{4})\s*-\s*\d{1,2}:\d{2}\s*-\s*Sorteo\s+N\S{0,2}\s*\d+\s*-\s*([A-ZÁÉÍÓÚ]+)\s*<")


def _jurisdiccion_a_quiniela(nombre):
    n = _sin_tildes(str(nombre)).lower()
    if "montevideo" in n:
        return "montevideo"
    if "ciudad" in n:
        return "ciudad"
    if "santa fe" in n:
        return "santafe"
    if "cordoba" in n:
        return "cordoba"
    if "entre rios" in n:
        return "entrerios"
    if "buenos aires" in n or re.search(r"\bbs\.? ?as\b", n):
        return "provincia"
    return None                                         # Mendoza y cualquier otra: la app no las usa


def _textos(x):
    if isinstance(x, str):
        yield x
    elif isinstance(x, dict):
        for v in x.values():
            yield from _textos(v)
    elif isinstance(x, list):
        for v in x:
            yield from _textos(v)


def leer_datos_oficiales(texto):
    """Interpreta el archivo de un sorteo ('window.RESULTADOS_DATA = [ {...} ];'). Devuelve el sorteo como dict,
    o None si el archivo está vacío (el sorteo todavía no se publicó)."""
    i = texto.find("[")
    if i < 0:
        raise ValueError("el archivo no trae datos")
    lista, _ = json.JSONDecoder().raw_decode(texto[i:])
    if not isinstance(lista, list):
        raise ValueError("el archivo tiene otro formato")
    return lista[0] if lista else None


def sorteo_oficial(datos, quiniela):
    """Saca de un sorteo oficial ya interpretado el de una quiniela. Devuelve (sorteo | None, avisos)."""
    num = datos.get("sorteo")
    m = re.fullmatch(r"(\d{2})/(\d{2})/(\d{4})", str(datos.get("fecha", "")).strip())
    turno = OFICIAL_MODALIDADES.get(str(datos.get("modalidad", "")).upper())
    if not m or not turno:
        return None, [f"{quiniela}: el sorteo oficial {num} trae una fecha o un turno que no entiendo ({datos.get('fecha')!r}, {datos.get('modalidad')!r})."]
    fecha = f"{m.group(3)}-{m.group(2)}-{m.group(1)}"
    etiqueta = f"{quiniela} {turno} {fecha}"
    jur = next((j for j in (datos.get("jurisdicciones") or {}).values()
                if isinstance(j, dict) and _jurisdiccion_a_quiniela(j.get("nombre", "")) == quiniela), None)
    if jur is None:
        # Montevideo solo figura los días que juega (no hay sorteo en los feriados de Uruguay): no es una falla.
        return None, ([] if quiniela == "montevideo" else [f"{etiqueta}: el sorteo oficial {num} no trae esta quiniela."])
    filas = jur.get("numeros") or []
    try:
        posiciones = [int(f["pos"]) for f in filas]
        numeros = [str(f["val"]).strip() for f in filas]
    except (KeyError, TypeError, ValueError):
        return None, [f"{etiqueta}: cambió el formato de los premios en la web oficial."]
    cifras = CIFRAS.get(quiniela, (4,))
    if posiciones != list(range(1, 21)) or not all(n.isdigit() and len(n) in cifras for n in numeros):
        return None, [f"{etiqueta}: los premios oficiales no son 20 números válidos. Lo descarto."]
    letras = None
    if quiniela == "ciudad":                            # las letras se sortean solo con la Ciudad
        lt = str(jur.get("letras") or "").strip().upper()
        letras = lt if re.fullmatch(r"[A-ZÑ]{4}", lt) else None
    sorteo = {"fecha": fecha, "turno": turno, "numeros": numeros, "nombre": None, "letras": letras}
    avisos = []
    # Todavía no se vio cómo marca la web oficial un sorteo no vinculante: si lo dijera con esas palabras, se anota.
    if any(NO_VINCULANTE.search(t) for t in _textos(jur)):
        sorteo["no_vinculante"], sorteo["sorteado_por"] = True, None
        avisos.append(f"NOTA {etiqueta}: sorteo NO VINCULANTE (según la web oficial).")
    return sorteo, avisos


def leer_oficial(quiniela, ahora, bajar, ya_tiene=lambda fecha, turno: False, dias_atras=1, tope=12):
    """Mira en la portada oficial los sorteos que ya salieron desde hace `dias_atras` días y baja el archivo de los que faltan
    (como mucho `tope`, los más nuevos primero). Normalmente alcanza con hoy y ayer; para rellenar el historial se mira más atrás."""
    portada = bajar(OFICIAL + "/")
    if not OFICIAL_LISTA.search(portada):
        return [], ["No encontré la lista de sorteos en la portada oficial. ¿Cambió la página?"]
    desde = (ahora.date() - timedelta(days=dias_atras)).isoformat()
    publicados = []
    for n, d, mes, a, mod in OFICIAL_LISTA.findall(portada):
        fecha, turno = f"{a}-{mes}-{d}", _sin_tildes(mod).lower()
        if turno not in TURNOS or fecha < desde:
            continue
        if turno not in turnos_del_dia(quiniela, date.fromisoformat(fecha).weekday()):
            continue                                    # esa quiniela no sortea ese turno ese día (Montevideo, sábados)
        if not ya_tiene(fecha, turno):
            publicados.append((int(n), fecha, turno))
    sorteos, avisos = [], []
    for n, fecha, turno in sorted(publicados, reverse=True)[:tope]:
        etiqueta = f"{quiniela} {turno} {fecha}"
        try:
            datos = leer_datos_oficiales(bajar(OFICIAL_DATOS.format(n)))
        except Exception as e:
            avisos.append(f"{etiqueta}: no pude leer el sorteo oficial {n} ({e}).")
            continue
        if datos is None:                               # figura en la lista pero todavía sin datos
            continue
        if str(datos.get("sorteo")) != str(n):
            avisos.append(f"{etiqueta}: pedí el sorteo oficial {n} y llegó el {datos.get('sorteo')}. Lo descarto.")
            continue
        s, av = sorteo_oficial(datos, quiniela)
        avisos += av
        if s and (s["fecha"], s["turno"]) != (fecha, turno):
            avisos.append(f"{etiqueta}: la lista oficial dice una cosa y el archivo {n} otra ({s['turno']} {s['fecha']}). Lo descarto.")
            continue
        if s:
            sorteos.append(s)
    return sorteos, avisos


# ---------- NotiTimba (solo respaldo) ----------
# Sitio privado con anuncios. Su página "en vivo" le pide los resultados a este archivo cada ~24 segundos.
# El formato no es público: se dedujo del script de la propia página y de una respuesta real (14/11/2026).
# Respuesta = campos separados por "|":  [0] "modo ç banderas ç aviso"  [1] HTML  [2] fecha AAAAMMDD  [3] segundos de refresco
#   [4] "banderas&n&turno" (D previa, P primera, M matutina, V vespertina, N nocturna)  [5] letras de la Ciudad
#   y después 25 bloques de 4 campos (uno por jurisdicción, en el orden de abajo): estado, cifras, 20 premios, vacío.
#   Cada premio ocupa 6 caracteres: "00" + 4 cifras. Estado 0 = sin sorteo. Modo "t" = resultado final.
NOTITIMBA = "https://www.notitimba.com/lots/cfms/aQsEq.php"
NOTITIMBA_LUGAR = {0: "provincia", 1: "ciudad", 3: "santafe", 4: "entrerios", 6: "cordoba"}
# Montevideo (lugar 2) queda afuera: no vi cómo manda sus premios (su ficha dice 3 cifras; la cuarta, la primera, sale de Ciudad).
NOTITIMBA_TURNOS = {"D": "previa", "P": "primera", "M": "matutina", "V": "vespertina", "N": "nocturna"}
NV_SOLICITO = re.compile(r"(?P<a>[^.;:]*?)\bsolicit\w*\s+a\s+(?P<b>[^.;:]*?)\s+(?:un\s+|el\s+)?sorteo\s+no\s+vinculante", re.I)
RESPALDO = {"NotiTimba"}                                # fuentes que solo valen si ninguna otra trajo ese sorteo


def _jurisdiccion_en_texto(texto):
    for qid, nombre, rx in JURISDICCIONES:
        if re.search(rx, texto, re.I):
            return qid, nombre
    return None, None


def interpretar_notitimba(texto, ahora, fresco=True):
    """Interpreta la respuesta de aQsEq.php. Devuelve ({quiniela: sorteo}, avisos).
    Con fresco=False no se controla la fecha ni la hora (para probar con respuestas guardadas)."""
    seg = texto.split("|")
    cab = seg[0].split("ç")                        # "ç"
    if cab[0] != "t":                                   # otro modo: sorteo en vivo (números provisorios) u otra cosa
        return {}, []
    if len(seg) < 6 + 4 * (max(NOTITIMBA_LUGAR) + 1):
        return {}, ["la respuesta es más corta de lo esperado. ¿Cambió el formato?"]
    m = re.fullmatch(r"(\d{4})(\d{2})(\d{2})", seg[2].strip())
    ctrl = seg[4].split("&")
    turno = NOTITIMBA_TURNOS.get(ctrl[2].strip()) if len(ctrl) >= 3 else None
    if not m or not turno or not ctrl[0].strip().isdigit():
        return {}, ["no entiendo la fecha o el turno de la respuesta. ¿Cambió el formato?"]
    if int(ctrl[0]) & 8:                                # la página muestra "sorteando": los números son provisorios
        return {}, []
    try:
        d = date(int(m.group(1)), int(m.group(2)), int(m.group(3)))
    except ValueError:
        return {}, ["la fecha de la respuesta no es válida."]
    fecha = d.isoformat()
    if fresco:
        if d < ahora.date() - timedelta(days=1) or d > ahora.date():
            return {}, []                               # resultado viejo: no sirve
        hh, mm = map(int, HORARIOS["base"][turno].split(":"))
        if datetime(d.year, d.month, d.day, hh, mm, tzinfo=AR) > ahora:
            return {}, [f"trae un sorteo {turno} del {fecha} que todavía no empezó. Lo descarto."]
    letras = seg[5].strip().upper()
    letras = letras if re.fullmatch(r"[A-ZÑ]{4}", letras) else None
    por_q, avisos = {}, []
    for lugar, q in NOTITIMBA_LUGAR.items():
        estado, cifras, premios = (seg[6 + 4 * lugar + k].strip() for k in range(3))
        if estado == "0" or not premios or set(premios) <= {"-"}:
            continue                                    # esa quiniela no tiene resultados en este turno
        etiqueta = f"{q} {turno} {fecha}"
        if cifras != "4" or not re.fullmatch(r"\d{120}", premios):
            avisos.append(f"{etiqueta}: NotiTimba manda los premios en un formato que no reconozco. Lo descarto.")
            continue
        trozos = [premios[i:i + 6] for i in range(0, 120, 6)]
        if any(t[:2] != "00" for t in trozos):
            avisos.append(f"{etiqueta}: NotiTimba manda los premios en un formato que no reconozco. Lo descarto.")
            continue
        por_q[q] = {"fecha": fecha, "turno": turno, "numeros": [t[2:] for t in trozos], "nombre": None,
                    "letras": letras if q == "ciudad" else None}
    # El aviso del encabezado solo vale si la página lo muestra (bit 128). Si no, es un mensaje viejo que quedó cargado.
    aviso = cab[2] if len(cab) > 2 else ""
    try:
        banderas = int(cab[1])
    except ValueError:
        banderas = 0
    if banderas & 128 and NO_VINCULANTE.search(aviso):
        s = NV_SOLICITO.search(aviso)
        afectada = _jurisdiccion_en_texto(s.group("a"))[0] if s else None
        por = _jurisdiccion_en_texto(s.group("b"))[1] if s else None
        if afectada in por_q and por:
            por_q[afectada]["no_vinculante"], por_q[afectada]["sorteado_por"] = True, por
            avisos.append(f"NOTA {afectada} {turno} {fecha}: sorteo NO VINCULANTE (realizado por {por}), según el aviso de NotiTimba.")
        else:
            avisos.append(f"NotiTimba publica un aviso de sorteo no vinculante que no pude aplicar a ninguna quiniela: «{aviso[:160]}». Revisalo a mano.")
    return por_q, avisos


def leer_notitimba(quiniela, ahora, bajar, ya_tiene=lambda fecha, turno: False):
    """NotiTimba trae un solo sorteo (el último) con todas las jurisdicciones: se baja una vez y cada quiniela toma el suyo."""
    if quiniela not in NOTITIMBA_LUGAR.values():
        return [], []
    por_q, avisos = interpretar_notitimba(bajar(NOTITIMBA), ahora)
    otras = tuple(q for q in QUINIELAS if q != quiniela)
    avisos = [a for a in avisos if not a.startswith(tuple(f"{o} " for o in otras) + tuple(f"NOTA {o} " for o in otras))]
    s = por_q.get(quiniela)
    if s and (not ya_tiene(s["fecha"], s["turno"]) or s.get("no_vinculante")):
        return [s], avisos
    return [], avisos


# ---------- Varias fuentes a la vez ----------
class Descargas:
    """Descarga cada dirección una sola vez por corrida, aunque la pidan dos lectores a la vez
    (la nota conjunta de Provincia y Ciudad sirve para las dos). Si falla, el error también se recuerda."""

    def __init__(self, bajar):
        self._bajar, self._resultados, self._candados, self._lock = bajar, {}, {}, Lock()

    def __call__(self, url):
        with self._lock:
            candado = self._candados.setdefault(url, Lock())
        with candado:                                   # el segundo que llega espera al primero
            if url not in self._resultados:
                try:
                    self._resultados[url] = (True, self._bajar(url))
                except Exception as e:
                    self._resultados[url] = (False, e)
        ok, valor = self._resultados[url]
        if not ok:
            raise valor
        return valor


def _leer_lanacion(quiniela, ahora, bajar, ya_tiene):
    if quiniela not in FUENTES:
        return [], []
    return leer_sorteos(bajar(FUENTES[quiniela]), quiniela)


# Para sumar otra fuente: escribí una función (quiniela, ahora, bajar, ya_tiene) -> (sorteos, avisos) y agregala acá.
LECTORES = (("Web oficial", leer_oficial), ("La Nación", _leer_lanacion), ("El Cronista", leer_cronista), ("NotiTimba", leer_notitimba))


def _anotar(elegidos, q, nombre, s, avisos, respaldo=False):
    """Suma un sorteo leído a los elegidos de una quiniela: el primero que llega se queda; los demás solo completan datos."""
    k = (s["fecha"], s["turno"])
    previo = elegidos.get(k)
    if previo is None:
        elegidos[k] = (nombre, s)
    elif previo[1]["numeros"] != s["numeros"]:
        motivo = f"{nombre} es solo respaldo." if respaldo else "que llegó primero."
        avisos.append(f"{q} {s['turno']} {s['fecha']}: {previo[0]} y {nombre} no coinciden. Me quedo con {previo[0]}, {motivo}")
    else:                                               # mismos números: se completa lo que le falte a la primera
        base = previo[1]
        for campo in ("letras", "nombre"):
            if not base.get(campo) and s.get(campo):
                base[campo] = s[campo]
        if s.get("no_vinculante") and not base.get("no_vinculante"):
            base["no_vinculante"], base["sorteado_por"] = True, s.get("sorteado_por")


def consultar(quinielas, ahora, bajar, ya_tiene, lectores=LECTORES):
    """Pregunta a todas las fuentes a la vez. Para cada sorteo vale la primera fuente que lo trae;
    las de RESPALDO (NotiTimba) solo cuentan si ninguna otra lo trajo, aunque sí completan datos que falten.
    Devuelve ({quiniela: [sorteos]}, avisos)."""
    bajar = Descargas(bajar)
    elegidos = {q: {} for q in quinielas}
    respaldos, avisos = [], []

    def avisar(texto):
        if texto not in avisos:                         # las cinco quinielas leen lo mismo: el aviso sale una sola vez
            avisos.append(texto)

    with ThreadPoolExecutor(max_workers=max(1, len(quinielas) * len(lectores))) as pool:
        futuros = {}
        for q in quinielas:
            for nombre, leer in lectores:
                futuros[pool.submit(leer, q, ahora, bajar, (lambda f, t, q=q: ya_tiene(q, f, t)))] = (q, nombre)
        for fut in as_completed(futuros):
            q, nombre = futuros[fut]
            try:
                sorteos, av = fut.result()
            except Exception as e:                      # una fuente caída no debe frenar a las demás
                avisar(f"{nombre} no respondió ({e})")
                continue
            for a in av:
                avisar(a if a.startswith(("NOTA ", q + " ")) else f"{nombre}: {a}")
            for s in sorteos:
                if nombre in RESPALDO:
                    respaldos.append((q, nombre, s))
                else:
                    _anotar(elegidos[q], q, nombre, s, avisos)
    for q, nombre, s in respaldos:                      # recién ahora, con todas las demás fuentes ya contadas
        _anotar(elegidos[q], q, nombre, s, avisos, respaldo=True)
    return {q: [s for _, s in elegidos[q].values()] for q in quinielas}, avisos


# ---------- Archivo de resultados ----------
def cargar_json():
    try:
        d = json.loads(SALIDA.read_text(encoding="utf-8"))
        if isinstance(d, dict) and isinstance(d.get("dias"), dict):
            return d
    except (OSError, ValueError):
        pass
    return {"version": 1, "demo": True, "actualizado": None, "dias": {}}


def unir(datos, quiniela, sorteos):
    """Mete los sorteos leídos en el JSON. Devuelve (hubo_cambios, avisos).
    Un sorteo ya guardado no se pisa: si llega con números distintos solo se avisa; si llega igual, se le completan datos que faltaban."""
    cambio, avisos = False, []
    for s in sorteos:
        nuevo = {"numeros": s["numeros"], "nombre": s["nombre"], "letras": s["letras"]}
        if s.get("no_vinculante"):
            nuevo["no_vinculante"], nuevo["sorteado_por"] = True, s.get("sorteado_por")
        dia = datos["dias"].setdefault(s["fecha"], {}).setdefault(quiniela, {})
        actual = dia.get(s["turno"])
        if not actual or not actual.get("numeros"):
            dia[s["turno"]] = nuevo
            cambio = True
        elif actual["numeros"] != nuevo["numeros"]:
            avisos.append(f"{quiniela} {s['turno']} {s['fecha']}: ya estaba cargado con otros números y no lo piso. Si el guardado está mal, borralo de resultados.json.")
        else:
            for campo in ("letras", "nombre"):
                if not actual.get(campo) and nuevo.get(campo):
                    actual[campo] = nuevo[campo]
                    cambio = True
            if nuevo.get("no_vinculante") and not actual.get("no_vinculante"):
                actual["no_vinculante"], actual["sorteado_por"] = True, nuevo.get("sorteado_por")
                cambio = True
    return cambio, avisos


def guardar(datos, ahora):
    datos["version"], datos["demo"] = 1, False
    datos["actualizado"] = ahora.isoformat(timespec="seconds")
    limite = (ahora.date() - timedelta(days=DIAS_A_GUARDAR - 1)).isoformat()
    for f in [f for f in datos["dias"] if f < limite]:  # lo más viejo que el historial se descarta
        del datos["dias"][f]
    SALIDA.parent.mkdir(parents=True, exist_ok=True)
    SALIDA.write_text(json.dumps(datos, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")


def turnos_del_dia(quiniela, dia_semana):
    """{turno: "HH:MM"} que se sortean ese día de la semana (0 = lunes ... 6 = domingo)."""
    if dia_semana == 6:                                 # domingo: no hay sorteos
        return {}
    horarios = HORARIOS.get(quiniela, HORARIOS["base"])
    if quiniela == "montevideo" and dia_semana == 5:    # los sábados Montevideo sortea solo la nocturna
        return {t: h for t, h in horarios.items() if t == "nocturna"}
    return dict(horarios)


def pendientes(datos, ahora):
    """Quinielas con algún sorteo de hoy que ya debería estar y todavía no está cargado."""
    hoy, minutos = ahora.strftime("%Y-%m-%d"), ahora.hour * 60 + ahora.minute
    faltan = set()
    for q in QUINIELAS:
        for turno, hhmm in turnos_del_dia(q, ahora.weekday()).items():
            h, m = map(int, hhmm.split(":"))
            t = h * 60 + m
            if t <= minutos <= t + MINUTOS_DE_ESPERA and not datos["dias"].get(hoy, {}).get(q, {}).get(turno):
                faltan.add(q)
    return faltan


def faltantes(datos, ahora):
    """Quinielas a las que les falta algún sorteo ya jugado en los días anteriores del historial (hoy lo cubre `pendientes`).
    Un feriado sin sorteos también figura acá, pero no cuesta casi nada: la web oficial no lo lista y no se baja nada."""
    faltan = set()
    for i in range(1, DIAS_A_GUARDAR):
        dia = ahora.date() - timedelta(days=i)
        for q in QUINIELAS:
            for turno in turnos_del_dia(q, dia.weekday()):
                if not datos["dias"].get(dia.isoformat(), {}).get(q, {}).get(turno):
                    faltan.add(q)
    return faltan


def ajustar_montevideo(sorteos, ciudad):
    """Montevideo = número uruguayo de 3 cifras + la primera cifra del número de Ciudad en la misma posición.
    Si un sorteo llega de 3 cifras se completa con Ciudad (si todavía no está, se espera). Si llega de 4, se controla que la
    primera cifra coincida con la de Ciudad (en los sorteos reales coincide siempre) y, si no, se avisa pero se guarda.
    `ciudad` es {(fecha, turno): [20 números]}. Devuelve (sorteos, avisos)."""
    salida, avisos = [], []
    for s in sorteos:
        etiqueta = f"montevideo {s['turno']} {s['fecha']}"
        base = ciudad.get((s["fecha"], s["turno"]))
        if len(s["numeros"][0]) == 3:
            if not base:
                avisos.append(f"{etiqueta}: llegó de 3 cifras y todavía no tengo el sorteo de Ciudad para completarlo. Espero a la próxima vuelta.")
                continue
            s = {**s, "numeros": [b[0] + n for b, n in zip(base, s["numeros"])]}
        elif base and any(b[0] != n[0] for b, n in zip(base, s["numeros"])):
            avisos.append(f"{etiqueta}: la primera cifra no coincide con la de Ciudad en alguna posición, y en los sorteos reales siempre coincide. Revisalo.")
        salida.append(s)
    return salida, avisos


def descargar(url):
    headers = {
        "User-Agent": "alacabeza-actualizador/1.0 (proyecto personal; una consulta cada 5 minutos como máximo)",
        "Accept-Language": "es-AR,es;q=0.9",
        "Cache-Control": "no-cache",
    }
    if url.startswith(OFICIAL):
        headers["Referer"] = OFICIAL + "/"
    elif url.startswith(NOTITIMBA):
        headers["Referer"] = "https://www.notitimba.com/lots/"
    req = urllib.request.Request(url, headers=headers)
    with urllib.request.urlopen(req, timeout=15) as r:
        return r.read().decode(r.headers.get_content_charset() or "utf-8", errors="replace")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--siempre", action="store_true", help="consultar todas las fuentes")
    ap.add_argument("--archivo", help="HTML guardado para probar el lector")
    ap.add_argument("--quiniela", default="provincia", help="quiniela a la que corresponde --archivo")
    ap.add_argument("--fuente", choices=("oficial", "lanacion", "cronista", "notitimba"), default="lanacion", help="de qué sitio es --archivo")
    ap.add_argument("--turno", help="solo para --fuente cronista: turno de la nota")
    ap.add_argument("--fecha", help="solo para --fuente cronista: fecha de la nota (AAAA-MM-DD)")
    a = ap.parse_args()

    if a.archivo:
        html = Path(a.archivo).read_text(encoding="utf-8", errors="replace")
        if a.fuente == "notitimba":                     # respuesta guardada de aQsEq.php (no se controla fecha ni hora)
            por_q, avisos = interpretar_notitimba(html, datetime.now(AR), fresco=False)
            for q, s in por_q.items():
                print(f"{q:<10} {s['fecha']} {s['turno']:<10} cabeza={s['numeros'][0][-2:]} letras={s['letras']}{' NO VINCULANTE' if s.get('no_vinculante') else ''} -> {' '.join(s['numeros'])}")
            for v in avisos:
                print("AVISO:", v)
            print(f"{len(por_q)} quiniela(s) leída(s).")
            return 0 if por_q else 1
        if a.fuente == "oficial":                       # el archivo trae todas las quinielas de un sorteo
            datos = leer_datos_oficiales(html)
            if datos is None:
                print("El archivo está vacío: ese sorteo todavía no se publicó.")
                return 1
            total = 0
            for q in QUINIELAS:
                s, av = sorteo_oficial(datos, q)
                if s:
                    total += 1
                    print(f"{q:<10} {s['fecha']} {s['turno']:<10} cabeza={s['numeros'][0][-2:]} letras={s['letras']} -> {' '.join(s['numeros'])}")
                for v in av:
                    print("AVISO:", v)
            print(f"{total} quiniela(s) leída(s).")
            return 0 if total else 1
        if a.fuente == "cronista":
            if a.turno not in TURNOS or not a.fecha:
                print("Con --fuente cronista hay que indicar --turno y --fecha.")
                return 2
            sorteo, avisos = leer_articulo_cronista(html, a.quiniela, a.turno, a.fecha)
            sorteos = [sorteo] if sorteo else []
        else:
            sorteos, avisos = leer_sorteos(html, a.quiniela)
        for s in sorteos:
            print(f"{s['fecha']} {s['turno']:<10} cabeza={s['numeros'][0][-2:]} letras={s['letras']} -> {' '.join(s['numeros'])}")
        for v in avisos:
            print("AVISO:", v)
        print(f"{len(sorteos)} sorteo(s) leído(s).")
        return 0 if sorteos else 1

    ahora = datetime.now(AR)
    datos = cargar_json()
    urgentes = set(QUINIELAS) if a.siempre else pendientes(datos, ahora)
    huecos = faltantes(datos, ahora)
    objetivo = urgentes | huecos
    if not objetivo:
        print("Nada pendiente en este momento.")
        return 0
    lectores = LECTORES if urgentes else ()
    if huecos:                                          # relleno del historial: la web oficial, mirando todo el período
        lectores += (("Web oficial", partial(leer_oficial, dias_atras=DIAS_A_GUARDAR - 1, tope=80)),)

    def ya_tiene(q, fecha, turno):
        return bool(datos["dias"].get(fecha, {}).get(q, {}).get(turno))

    leidos, avisos = consultar(sorted(objetivo), ahora, descargar, ya_tiene, lectores)
    if leidos.get("montevideo"):
        ciudad = {(f, tu): v["numeros"] for f, qs in datos["dias"].items() for tu, v in qs.get("ciudad", {}).items() if v.get("numeros")}
        ciudad.update({(s["fecha"], s["turno"]): s["numeros"] for s in leidos.get("ciudad", [])})
        leidos["montevideo"], av = ajustar_montevideo(leidos["montevideo"], ciudad)
        avisos += av
    hubo_cambio = False
    for q in sorted(leidos):
        cambio, av = unir(datos, q, leidos[q])
        avisos += av
        if cambio:
            hubo_cambio = True
            print(f"{q}: datos nuevos ({len(leidos[q])} sorteo(s) leído(s)).")
    for v in avisos:
        print(f"::notice::{v}" if v.startswith("NOTA ") else f"::warning::{v}")
    if hubo_cambio:
        guardar(datos, ahora)
        print("Archivo actualizado.")
    else:
        print("Sin cambios.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
