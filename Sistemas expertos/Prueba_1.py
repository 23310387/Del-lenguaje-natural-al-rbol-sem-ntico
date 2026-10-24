#!/usr/bin/env python3
"""Motor de inferencia con árboles semánticos (lógica proposicional).

Recibe reglas y hechos en español (uno por línea), extrae los átomos, los
traduce a fórmulas, construye el árbol semántico y reporta las condiciones
en las que todas las reglas son verdaderas.

Uso:
    python motor_inferencia.py              # escribes las reglas (línea vacía = analizar)
    python motor_inferencia.py reglas.txt   # lee las reglas de un archivo
    python motor_inferencia.py --ejemplo    # ejemplo del video
"""
import re
import sys
import unicodedata

LETRAS = "pqrstuvwxyzabcdefghijklmno"
EJEMPLO = [
    "Si es de día, entonces voy a trabajar",
    "Si llueve, entonces no voy a trabajar",
    "Es de día",
]
MAX_NODOS = 500
SIMBOLO = {"and": "∧", "or": "∨", "imp": "→", "iff": "↔"}


# ---------------------------------------------------------------- átomos
class Atomos:
    """Tabla de átomos: la misma frase escrita igual es el mismo átomo."""

    def __init__(self):
        self.tabla = {}  # clave normalizada -> (letra, texto)

    @staticmethod
    def clave(texto):
        s = unicodedata.normalize("NFD", texto)
        s = "".join(c for c in s if unicodedata.category(c) != "Mn")
        s = re.sub(r"[.,;:¿?¡!]", "", s)
        return re.sub(r"\s+", " ", s).strip()

    def obtener(self, texto):
        k = self.clave(texto)
        if not k:
            raise ValueError("Hay una parte vacía en la regla.")
        if k not in self.tabla:
            n = len(self.tabla)
            letra = LETRAS[n] if n < len(LETRAS) else "p%d" % (n - len(LETRAS) + 1)
            self.tabla[k] = (letra, limpiar(texto))
        return ("atom", k)


def limpiar(s):
    return re.sub(r"[.;!]+$", "", s.strip()).strip()


# ---------------------------------------------------------------- análisis
# Fórmulas: ("atom", k) | ("not", f) | (op, a, b) con op en and/or/imp/iff
def p_no(s, at):
    s = s.strip()
    m = re.match(r"^no\s+es\s+cierto\s+que\s+(.+)$", s) or re.match(r"^no\s+(.+)$", s)
    return ("not", p_no(m.group(1), at)) if m else at.obtener(s)


def plegar(partes, op, f):
    formulas = [f(p) for p in partes]
    r = formulas[0]
    for x in formulas[1:]:
        r = (op, r, x)
    return r


def p_y(s, at):
    return plegar(re.split(r"\s+y\s+", s), "and", lambda p: p_no(p, at))


def p_o(s, at):
    return plegar(re.split(r"\s+o\s+", s), "or", lambda p: p_y(p, at))


def analizar_regla(s, at):
    s = limpiar(s.lower())
    m = re.match(r"^(.+?),?\s+s[ií]\s+y\s+s[oó]lo\s+s[ií],?\s+(.+)$", s)
    if m:
        return ("iff", analizar_regla(m.group(1), at), analizar_regla(m.group(2), at))
    m = re.match(r"^s[ií]\s+(.+?),?\s+entonces,?\s+(.+)$", s) or re.match(
        r"^s[ií]\s+(.+?),\s+(.+)$", s
    )
    if m:
        return ("imp", analizar_regla(m.group(1), at), analizar_regla(m.group(2), at))
    return p_o(s, at)


def texto(f, at, envolver=False):
    """Fórmula como texto, con paréntesis cuando hacen falta."""
    if f[0] == "atom":
        return at.tabla[f[1]][0]
    if f[0] == "not":
        return "¬" + texto(f[1], at, True)
    s = "%s %s %s" % (texto(f[1], at, True), SIMBOLO[f[0]], texto(f[2], at, True))
    return "(" + s + ")" if envolver else s


# ---------------------------------------------------------------- árbol
def es_literal(f):
    return f[0] == "atom" or (f[0] == "not" and f[1][0] == "atom")


def neg(f):
    return ("not", f)


def expandir(f):
    """Devuelve ('a', [fórmulas]) si no bifurca o ('b', [[ramaA], [ramaB]])."""
    t = f[0]
    if t == "and":
        return "a", [f[1], f[2]]
    if t == "or":
        return "b", [[f[1]], [f[2]]]
    if t == "imp":
        return "b", [[neg(f[1])], [f[2]]]
    if t == "iff":
        return "b", [[f[1], f[2]], [neg(f[1]), neg(f[2])]]
    g = f[1]  # negaciones
    if g[0] == "not":
        return "a", [g[1]]
    if g[0] == "or":
        return "a", [neg(g[1]), neg(g[2])]
    if g[0] == "imp":
        return "a", [g[1], neg(g[2])]
    if g[0] == "and":
        return "b", [[neg(g[1])], [neg(g[2])]]
    return "b", [[g[1], neg(g[2])], [neg(g[1]), g[2]]]  # ¬↔


class Nodo:
    def __init__(self, f, etiqueta=""):
        self.f, self.etiqueta = f, etiqueta
        self.hijos = []
        self.aplicada = False
        self.cerrada = False


class Arbol:
    def __init__(self):
        self.nodos = 0
        self.cerradas = 0
        self.modelos = []  # (positivos, negativos) de cada rama abierta

    def nuevo(self, f, etiqueta=""):
        self.nodos += 1
        if self.nodos > MAX_NODOS:
            raise ValueError("El árbol es demasiado grande para mostrarlo.")
        return Nodo(f, etiqueta)

    def construir(self, hoja, camino, hechas):
        while True:
            pos = {n.f[1] for n in camino if n.f[0] == "atom"}
            ng = {n.f[1][1] for n in camino if n.f[0] == "not" and n.f[1][0] == "atom"}
            if pos & ng:  # átomo y su negación: rama cerrada
                hoja.cerrada = True
                self.cerradas += 1
                return
            elegido, exp = None, None
            for n in camino:  # primero las reglas de una sola rama
                if n in hechas or es_literal(n.f):
                    continue
                x = expandir(n.f)
                if x[0] == "a":
                    elegido, exp = n, x
                    break
                if elegido is None:
                    elegido, exp = n, x
            if elegido is None:  # solo letras: rama abierta
                self.modelos.append((pos, ng))
                return
            hechas.add(elegido)
            elegido.aplicada = True
            if exp[0] == "a":
                for g in exp[1]:
                    nn = self.nuevo(g)
                    hoja.hijos.append(nn)
                    hoja = nn
                    camino = camino + [nn]
            else:
                for rama in exp[1]:
                    primero = ultimo = None
                    c2, h2 = list(camino), set(hechas)
                    for g in rama:
                        nn = self.nuevo(g)
                        if primero is None:
                            primero = nn
                            hoja.hijos.append(nn)
                        else:
                            ultimo.hijos.append(nn)
                        ultimo = nn
                        c2.append(nn)
                    self.construir(ultimo, c2, h2)
                return


def mostrar(n, at, ind="", rama=""):
    et = n.etiqueta + ": " if n.etiqueta else ""
    print(rama + et + texto(n.f, at) + (" ✓" if n.aplicada else ""))
    if not n.hijos:
        print(ind + ("✕ rama cerrada" if n.cerrada else "● rama abierta"))
    elif len(n.hijos) == 1:
        mostrar(n.hijos[0], at, ind, ind)
    else:
        for i, k in enumerate(n.hijos):
            ultimo = i == len(n.hijos) - 1
            mostrar(k, at, ind + ("    " if ultimo else "│   "), ind + ("└── " if ultimo else "├── "))


# ---------------------------------------------------------------- programa
def resolver(lineas):
    at = Atomos()
    reglas, errores = [], []
    for i, s in enumerate(lineas, 1):
        try:
            reglas.append(("R%d" % (len(reglas) + 1), s, analizar_regla(s, at)))
        except ValueError as e:
            errores.append("Línea %d: %s" % (i, e))
    for e in errores:
        print("ERROR - " + e)
    if not reglas:
        print("Escribe al menos una regla o un hecho.")
        return

    print("\n=== TABLA DE ÁTOMOS ===")
    for letra, txt in at.tabla.values():
        print("  %-3s %s" % (letra, txt))

    print("\n=== REGLAS Y FÓRMULAS ===")
    for etq, src, f in reglas:
        print("  %s: %-45s %s" % (etq, src, texto(f, at)))

    arbol = Arbol()
    nodos = [arbol.nuevo(f, etq) for etq, _, f in reglas]
    for a, b in zip(nodos, nodos[1:]):
        a.hijos.append(b)
    try:
        arbol.construir(nodos[-1], list(nodos), set())
    except ValueError as e:
        print("\nERROR - " + str(e))
        return

    print("\n=== ÁRBOL SEMÁNTICO ===")
    print("(✓ fórmula aplicada, ✕ rama cerrada, ● rama abierta)\n")
    mostrar(nodos[0], at)

    print("\n=== RESULTADO ===")
    if not arbol.modelos:
        print("La base de conocimiento es INCONSISTENTE: todas las ramas se cierran,")
        print("ninguna asignación hace verdaderas todas las reglas.")
        return
    print("La base es CONSISTENTE: %d rama(s) abierta(s) y %d cerrada(s)."
          % (len(arbol.modelos), arbol.cerradas))
    for i, (pos, ng) in enumerate(arbol.modelos, 1):
        asig, frases = [], []
        for k, (letra, txt) in at.tabla.items():
            if k in pos:
                asig.append("%s = V" % letra)
                frases.append(txt)
            elif k in ng:
                asig.append("%s = F" % letra)
                frases.append("no " + txt)
            else:
                asig.append("%s = libre" % letra)
        print("\nRama abierta %d: %s" % (i, ", ".join(asig)))
        print("Todas las reglas se cumplen cuando: " + "; ".join(frases) + ".")


def main():
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except (AttributeError, OSError):
        pass
    args = sys.argv[1:]
    if args and args[0] == "--ejemplo":
        lineas = EJEMPLO
    elif args:
        with open(args[0], encoding="utf-8") as fh:
            lineas = [x.strip() for x in fh if x.strip()]
    else:
        print("Escribe una regla o hecho por línea. Línea vacía para analizar:")
        lineas = []
        while True:
            try:
                x = input("> ").strip()
            except EOFError:
                break
            if not x:
                break
            lineas.append(x)
    for s in lineas:
        print("  " + s) if args else None
    resolver(lineas)


if __name__ == "__main__":
    main()
    