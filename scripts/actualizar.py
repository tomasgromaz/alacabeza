#!/usr/bin/env python3
"""Actualiza data/resultados.json leyendo los extractos publicados en una página web.

Uso normal (lo corre GitHub Actions cada pocos minutos):
    python scripts/actualizar.py

Opciones útiles:
    --siempre                         consulta todas las fuentes aunque no haya sorteos pendientes
    --archivo pagina.html --quiniela provincia
                                      lee un HTML guardado y muestra qué entendió (no escribe nada)

Solo usa la librería estándar de Python.
"""
import argparse
import json
import re
import sys
import urllib.request
from datetime import datetime, timedelta, timezone
from html.parser import HTMLParser
from pathlib import Path

AR = timezone(timedelta(hours=-3))                      # Argentina no usa horario de verano
RAIZ = Path(__file__).resolve().parent.parent
SALIDA = RAIZ / "data" / "resultados.json"
DIAS_A_GUARDAR = 8
MINUTOS_DE_ESPERA = 120                                 # cuánto se sigue buscando un sorteo después de su hora

# De dónde se lee cada quiniela. Para cambiar de fuente, editá solo esta tabla.
# Entre Ríos no tiene fuente cargada todavía: la app la muestra como "sin datos".
BASE = "https://www.lanacion.com.ar/loterias/"
FUENTES = {
    "provincia": BASE + "quiniela-provincia/",
    "ciudad": BASE + "quiniela-nacional/",
    "santafe": BASE + "quiniela-santa-fe/",
    "cordoba": BASE + "quiniela-cordoba/",
    "montevideo": BASE + "quiniela-montevideo/",
    # "entrerios": "https://...",
}

# Mismos horarios que en index.html.
HORARIOS = {
    "base": {"previa": "10:15", "primera": "12:00", "matutina": "15:00", "vespertina": "18:00", "nocturna": "21:00"},
    "montevideo": {"matutina": "15:00", "nocturna": "21:00"},
}
CIFRAS = {"montevideo": (3, 4)}                         # el resto tiene 4 cifras
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
    """Lee 20 premios seguidos desde tokens[i]. Cada premio puede venir como 'PPNNNN' o como 'PP' y 'NNNN'."""
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
    return nums


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
        tokens = re.findall(r"\d+", resto)
        nums = next((r for r in (_intentar(tokens, k, cifras) for k in range(len(tokens))) if r), None)
        etiqueta = f"{quiniela} {turno} {fecha}"
        if not nums:
            avisos.append(f"{etiqueta}: no pude leer los 20 premios (puede que el sorteo todavía no esté publicado).")
            continue
        if cabeza and nums[0][-2:] != cabeza:
            avisos.append(f"{etiqueta}: 'A la Cabeza' dice {cabeza} pero el primer premio es {nums[0]}. Lo descarto.")
            continue
        vistos.add((fecha, turno))
        sorteos.append({"fecha": fecha, "turno": turno, "numeros": nums, "nombre": nombre or None, "letras": letras})
    return sorteos, avisos


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
    """Mete los sorteos leídos en el JSON. Devuelve True si algo cambió."""
    cambio = False
    for s in sorteos:
        nuevo = {"numeros": s["numeros"], "nombre": s["nombre"], "letras": s["letras"]}
        dia = datos["dias"].setdefault(s["fecha"], {}).setdefault(quiniela, {})
        if dia.get(s["turno"]) != nuevo:
            dia[s["turno"]] = nuevo
            cambio = True
    return cambio


def guardar(datos, ahora):
    datos["version"], datos["demo"] = 1, False
    datos["actualizado"] = ahora.isoformat(timespec="seconds")
    for f in sorted(datos["dias"], reverse=True)[DIAS_A_GUARDAR:]:
        del datos["dias"][f]
    SALIDA.parent.mkdir(parents=True, exist_ok=True)
    SALIDA.write_text(json.dumps(datos, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")


def pendientes(datos, ahora):
    """Quinielas con algún sorteo de hoy que ya debería estar y todavía no está cargado."""
    if ahora.weekday() == 6:                            # domingo
        return set()
    hoy, minutos = ahora.strftime("%Y-%m-%d"), ahora.hour * 60 + ahora.minute
    faltan = set()
    for q in FUENTES:
        horarios = HORARIOS.get(q, HORARIOS["base"])
        for turno, hhmm in horarios.items():
            if q == "montevideo" and ahora.weekday() == 5 and turno != "nocturna":
                continue
            h, m = map(int, hhmm.split(":"))
            t = h * 60 + m
            if t <= minutos <= t + MINUTOS_DE_ESPERA and not datos["dias"].get(hoy, {}).get(q, {}).get(turno):
                faltan.add(q)
    return faltan


def descargar(url):
    req = urllib.request.Request(url, headers={
        "User-Agent": "alacabeza-actualizador/1.0 (proyecto personal; una consulta cada 5 minutos como máximo)",
        "Accept-Language": "es-AR,es;q=0.9",
    })
    with urllib.request.urlopen(req, timeout=25) as r:
        return r.read().decode(r.headers.get_content_charset() or "utf-8", errors="replace")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--siempre", action="store_true", help="consultar todas las fuentes")
    ap.add_argument("--archivo", help="HTML guardado para probar el lector")
    ap.add_argument("--quiniela", default="provincia", help="quiniela a la que corresponde --archivo")
    a = ap.parse_args()

    if a.archivo:
        html = Path(a.archivo).read_text(encoding="utf-8", errors="replace")
        sorteos, avisos = leer_sorteos(html, a.quiniela)
        for s in sorteos:
            print(f"{s['fecha']} {s['turno']:<10} cabeza={s['numeros'][0][-2:]} letras={s['letras']} -> {' '.join(s['numeros'])}")
        for v in avisos:
            print("AVISO:", v)
        print(f"{len(sorteos)} sorteo(s) leído(s).")
        return 0 if sorteos else 1

    ahora = datetime.now(AR)
    datos = cargar_json()
    objetivo = set(FUENTES) if a.siempre else pendientes(datos, ahora) & set(FUENTES)
    if not objetivo:
        print("Nada pendiente en este momento.")
        return 0
    hubo_cambio = False
    for q in sorted(objetivo):
        try:
            sorteos, avisos = leer_sorteos(descargar(FUENTES[q]), q)
        except Exception as e:                          # una fuente caída no debe frenar a las demás
            print(f"::warning::{q}: no se pudo descargar ({e})")
            continue
        for v in avisos:
            print(f"::warning::{v}")
        if unir(datos, q, sorteos):
            hubo_cambio = True
            print(f"{q}: datos nuevos ({len(sorteos)} sorteo(s) leído(s)).")
    if hubo_cambio:
        guardar(datos, ahora)
        print("Archivo actualizado.")
    else:
        print("Sin cambios.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
