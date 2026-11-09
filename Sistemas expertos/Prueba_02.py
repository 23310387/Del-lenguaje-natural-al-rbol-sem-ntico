#prueba 2 con interfaz gráfica
"""Motor de inferencia con árboles semánticos (lógica proposicional).

Recibe reglas y hechos en español (uno por línea), extrae los átomos, los
traduce a fórmulas, construye el árbol semántico y reporta las condiciones
en las que todas las reglas son verdaderas.

"""
import re
import sys
import unicodedata
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from tkinter import font as tkfont

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


def mostrar(n, at, out, ind="", rama=""):
    """Agrega el árbol a `out` como lista de (línea, etiqueta de color)."""
    et = n.etiqueta + ": " if n.etiqueta else ""
    out.append((rama + et + texto(n.f, at) + (" ✓" if n.aplicada else ""), "nodo"))
    if not n.hijos:
        if n.cerrada:
            out.append((ind + "✕ rama cerrada", "cerrada"))
        else:
            out.append((ind + "● rama abierta", "abierta"))
    elif len(n.hijos) == 1:
        mostrar(n.hijos[0], at, out, ind, ind)
    else:
        for i, k in enumerate(n.hijos):
            ultimo = i == len(n.hijos) - 1
            mostrar(k, at, out, ind + ("    " if ultimo else "│   "),
                    ind + ("└── " if ultimo else "├── "))


# ---------------------------------------------------------------- motor
def resolver(lineas):
    """Analiza las líneas y devuelve un diccionario con todo lo que se muestra."""
    r = {"errores": [], "atomos": [], "reglas": [], "arbol": [], "resultado": []}
    at = Atomos()
    reglas = []
    for i, s in enumerate(lineas, 1):
        try:
            reglas.append(("R%d" % (len(reglas) + 1), s, analizar_regla(s, at)))
        except ValueError as e:
            r["errores"].append("Línea %d: %s" % (i, e))
    if not reglas:
        r["errores"].append("Escribe al menos una regla o un hecho.")
        return r

    r["atomos"] = list(at.tabla.values())
    r["reglas"] = [(etq, src, texto(f, at)) for etq, src, f in reglas]

    arbol = Arbol()
    try:
        nodos = [arbol.nuevo(f, etq) for etq, _, f in reglas]
        for a, b in zip(nodos, nodos[1:]):
            a.hijos.append(b)
        arbol.construir(nodos[-1], list(nodos), set())
    except ValueError as e:
        r["errores"].append(str(e))
        return r

    mostrar(nodos[0], at, r["arbol"])

    res = r["resultado"]
    if not arbol.modelos:
        res.append(("La base de conocimiento es INCONSISTENTE: todas las ramas se cierran,", "mal"))
        res.append(("ninguna asignación hace verdaderas todas las reglas.", "mal"))
        return r
    res.append(("La base es CONSISTENTE: %d rama(s) abierta(s) y %d cerrada(s)."
                % (len(arbol.modelos), arbol.cerradas), "ok"))
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
        res.append(("", "normal"))
        res.append(("Rama abierta %d: %s" % (i, ", ".join(asig)), "negrita"))
        res.append(("Todas las reglas se cumplen cuando: " + "; ".join(frases) + ".", "normal"))
    return r


# ---------------------------------------------------------------- interfaz
class App(tk.Tk):
    def __init__(self, lineas_iniciales=None):
        super().__init__()
        self.title("Motor de inferencia · Árboles semánticos")
        self.geometry("900x700")
        self.minsize(640, 520)
        mono = tkfont.nametofont("TkFixedFont").copy()
        mono.configure(size=11)
        self.mono = mono
        self.negrita = tkfont.nametofont("TkDefaultFont").copy()
        self.negrita.configure(weight="bold")

        # --- entrada
        cab = ttk.Frame(self, padding=(12, 10, 12, 4))
        cab.pack(fill="x")
        ttk.Label(cab, text="Reglas y hechos (uno por línea)", font=self.negrita).pack(anchor="w")
        ttk.Label(
            cab, foreground="#666",
            text="Conectores: si … entonces …, … si y sólo si …, y, o, no, no es cierto que",
        ).pack(anchor="w")

        marco = ttk.Frame(self, padding=(12, 0))
        marco.pack(fill="x")
        self.entrada = tk.Text(marco, height=7, wrap="word", font=self.mono, undo=True)
        sb = ttk.Scrollbar(marco, command=self.entrada.yview)
        self.entrada.configure(yscrollcommand=sb.set)
        self.entrada.pack(side="left", fill="x", expand=True)
        sb.pack(side="right", fill="y")

        botones = ttk.Frame(self, padding=(12, 8))
        botones.pack(fill="x")
        ttk.Button(botones, text="Analizar", command=self.analizar).pack(side="left")
        ttk.Button(botones, text="Cargar ejemplo", command=self.cargar_ejemplo).pack(side="left", padx=6)
        ttk.Button(botones, text="Abrir archivo…", command=self.abrir_archivo).pack(side="left")
        ttk.Button(botones, text="Limpiar", command=self.limpiar_todo).pack(side="left", padx=6)
        self.estado = ttk.Label(botones, foreground="#666")
        self.estado.pack(side="right")

        # --- resultados en pestañas
        self.pestanas = ttk.Notebook(self)
        self.pestanas.pack(fill="both", expand=True, padx=12, pady=(0, 12))

        t1 = ttk.Frame(self.pestanas, padding=8)
        self.pestanas.add(t1, text="Átomos y fórmulas")
        ttk.Label(t1, text="Tabla de átomos", font=self.negrita).pack(anchor="w")
        self.tabla_atomos = self._tabla(t1, ("letra", "enunciado"), ("Letra", "Enunciado"), (70, 600), 6)
        ttk.Label(t1, text="Reglas y fórmulas", font=self.negrita).pack(anchor="w", pady=(10, 0))
        self.tabla_reglas = self._tabla(
            t1, ("regla", "texto", "formula"), ("Regla", "Texto", "Fórmula"), (60, 420, 220), 8)

        t2 = ttk.Frame(self.pestanas, padding=8)
        self.pestanas.add(t2, text="Árbol semántico")
        ttk.Label(t2, foreground="#666",
                  text="✓ fórmula aplicada   ✕ rama cerrada   ● rama abierta").pack(anchor="w")
        self.txt_arbol = self._texto(t2, wrap="none")

        t3 = ttk.Frame(self.pestanas, padding=8)
        self.pestanas.add(t3, text="Resultado")
        self.txt_res = self._texto(t3, wrap="word")

        for w in (self.txt_arbol, self.txt_res):
            w.tag_configure("nodo", foreground="#1b1f24")
            w.tag_configure("cerrada", foreground="#b3261e")
            w.tag_configure("abierta", foreground="#1a7f4b")
            w.tag_configure("ok", foreground="#1a7f4b", font=self.negrita)
            w.tag_configure("mal", foreground="#b3261e", font=self.negrita)
            w.tag_configure("error", foreground="#b3261e")
            w.tag_configure("negrita", font=self.negrita)
            w.tag_configure("normal")

        self.bind("<Control-Return>", lambda e: self.analizar())
        if lineas_iniciales:
            self.entrada.insert("1.0", "\n".join(lineas_iniciales))
            self.analizar()

    # --- helpers de widgets
    def _tabla(self, padre, cols, titulos, anchos, filas):
        marco = ttk.Frame(padre)
        marco.pack(fill="x")
        t = ttk.Treeview(marco, columns=cols, show="headings", height=filas)
        for c, ti, a in zip(cols, titulos, anchos):
            t.heading(c, text=ti, anchor="w")
            t.column(c, width=a, anchor="w", stretch=(c == cols[-1] or c == cols[1]))
        sb = ttk.Scrollbar(marco, command=t.yview)
        t.configure(yscrollcommand=sb.set)
        t.pack(side="left", fill="x", expand=True)
        sb.pack(side="right", fill="y")
        return t

    def _texto(self, padre, wrap):
        marco = ttk.Frame(padre)
        marco.pack(fill="both", expand=True, pady=(4, 0))
        t = tk.Text(marco, wrap=wrap, font=self.mono, state="disabled")
        sy = ttk.Scrollbar(marco, command=t.yview)
        t.configure(yscrollcommand=sy.set)
        sy.pack(side="right", fill="y")
        if wrap == "none":
            sx = ttk.Scrollbar(padre, orient="horizontal", command=t.xview)
            t.configure(xscrollcommand=sx.set)
            sx.pack(side="bottom", fill="x")
        t.pack(side="left", fill="both", expand=True)
        return t

    @staticmethod
    def _llenar_texto(w, items):
        w.configure(state="normal")
        w.delete("1.0", "end")
        for linea, etiqueta in items:
            w.insert("end", linea + "\n", etiqueta)
        w.configure(state="disabled")

    # --- acciones
    def analizar(self):
        lineas = [x.strip() for x in self.entrada.get("1.0", "end").splitlines() if x.strip()]
        r = resolver(lineas)

        self.tabla_atomos.delete(*self.tabla_atomos.get_children())
        for letra, txt in r["atomos"]:
            self.tabla_atomos.insert("", "end", values=(letra, txt))
        self.tabla_reglas.delete(*self.tabla_reglas.get_children())
        for fila in r["reglas"]:
            self.tabla_reglas.insert("", "end", values=fila)

        self._llenar_texto(self.txt_arbol, r["arbol"])
        salida = [("ERROR - " + e, "error") for e in r["errores"]]
        if salida and r["resultado"]:
            salida.append(("", "normal"))
        self._llenar_texto(self.txt_res, salida + r["resultado"])

        if r["errores"] and not r["resultado"]:
            self.estado.configure(text="Hay errores, revisa la pestaña Resultado")
            self.pestanas.select(2)
        else:
            self.estado.configure(text="%d regla(s), %d átomo(s)" % (len(r["reglas"]), len(r["atomos"])))
            self.pestanas.select(1)

    def cargar_ejemplo(self):
        self.entrada.delete("1.0", "end")
        self.entrada.insert("1.0", "\n".join(EJEMPLO))
        self.analizar()

    def abrir_archivo(self):
        ruta = filedialog.askopenfilename(
            title="Abrir reglas", filetypes=[("Texto", "*.txt"), ("Todos", "*.*")])
        if not ruta:
            return
        try:
            with open(ruta, encoding="utf-8") as fh:
                contenido = fh.read()
        except (OSError, UnicodeDecodeError) as e:
            messagebox.showerror("No se pudo abrir el archivo", str(e))
            return
        self.entrada.delete("1.0", "end")
        self.entrada.insert("1.0", contenido.strip())
        self.analizar()

    def limpiar_todo(self):
        self.entrada.delete("1.0", "end")
        self.tabla_atomos.delete(*self.tabla_atomos.get_children())
        self.tabla_reglas.delete(*self.tabla_reglas.get_children())
        self._llenar_texto(self.txt_arbol, [])
        self._llenar_texto(self.txt_res, [])
        self.estado.configure(text="")
        self.entrada.focus_set()


def main():
    args = sys.argv[1:]
    lineas = None
    if args and args[0] == "--ejemplo":
        lineas = EJEMPLO
    elif args:
        with open(args[0], encoding="utf-8") as fh:
            lineas = [x.strip() for x in fh if x.strip()]
    App(lineas).mainloop()


if __name__ == "__main__":
    main()