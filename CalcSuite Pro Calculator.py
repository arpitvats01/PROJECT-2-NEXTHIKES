import ast
import calendar
import datetime as dt
import json
import math
import operator
import queue
import re
import statistics
import threading
import urllib.request
import tkinter as tk
from tkinter import ttk, messagebox

# --------------------------------------------------------------------------- #
#  Theme
# --------------------------------------------------------------------------- #
C = dict(
    bg="#EEF2F7", panel="#FFFFFF", border="#D5DDE8",
    header="#14213D", header_fg="#FFFFFF", header_sub="#A9B7D0",
    display_bg="#0F1B33", display_fg="#FFFFFF", sub_fg="#8FA2C0",
    num="#FFFFFF", num_h="#E6EDF7",
    op="#DCE4F0", op_h="#C9D6E8",
    fn="#EAF0F8", fn_h="#D8E3F2",
    mem="#F4F7FB", mem_h="#E3EAF4",
    eq="#2563EB", eq_h="#1D4ED8",
    clr="#FDE8E8", clr_h="#F9CFCF", clr_fg="#B91C1C",
    text="#1E293B", muted="#64748B", accent="#2563EB",
    good="#059669", warn="#D97706", bad="#DC2626", info="#2563EB",
)
FONT = ("Segoe UI", 10)
FONT_B = ("Segoe UI", 10, "bold")


# --------------------------------------------------------------------------- #
#  Safe expression evaluator (no eval(), only whitelisted operations)
# --------------------------------------------------------------------------- #
_BIN = {
    ast.Add: operator.add, ast.Sub: operator.sub, ast.Mult: operator.mul,
    ast.Div: operator.truediv, ast.Pow: operator.pow, ast.Mod: operator.mod,
    ast.FloorDiv: operator.floordiv,
}
_UN = {ast.UAdd: operator.pos, ast.USub: operator.neg}


def safe_eval(expr, env):
    tree = ast.parse(expr, mode="eval")

    def ev(n):
        if isinstance(n, ast.Expression):
            return ev(n.body)
        if isinstance(n, ast.Constant) and isinstance(n.value, (int, float)) \
                and not isinstance(n.value, bool):
            return n.value
        if isinstance(n, ast.Name):
            if n.id in env:
                return env[n.id]
            raise ValueError(f"Unknown name '{n.id}'")
        if isinstance(n, ast.BinOp) and type(n.op) in _BIN:
            left, right = ev(n.left), ev(n.right)
            if isinstance(n.op, ast.Pow) and isinstance(left, int) \
                    and isinstance(right, int) and abs(right) > 10000:
                raise ValueError("Exponent too large")
            return _BIN[type(n.op)](left, right)
        if isinstance(n, ast.UnaryOp) and type(n.op) in _UN:
            return _UN[type(n.op)](ev(n.operand))
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name):
            fn = env.get(n.func.id)
            if not callable(fn):
                raise ValueError(f"Unknown function '{n.func.id}'")
            return fn(*[ev(a) for a in n.args])
        if isinstance(n, (ast.List, ast.Tuple)):
            return [ev(e) for e in n.elts]
        raise ValueError("Unsupported expression")

    return ev(tree)


def preprocess(expr):
    """Make user-friendly input valid: 2pi -> 2*pi, ^ -> **, symbols, (a)(b) ..."""
    s = (expr.strip()
         .replace("×", "*").replace("÷", "/").replace("−", "-")
         .replace("^", "**").replace("π", "pi").replace("√", "sqrt")
         .replace("²", "**2").replace("³", "**3"))
    s = re.sub(r"(?<![A-Za-z_\d.])(\d+(?:\.\d+)?)\s*([A-Za-z_(])", r"\1*\2", s)
    s = re.sub(r"\)\s*(?=[\dA-Za-z_(])", ")*", s)
    return s


def _flat(args):
    out = []
    for a in args:
        if isinstance(a, (list, tuple)):
            out.extend(_flat(a))
        else:
            out.append(a)
    return out


def _fact(n):
    if n < 0:
        raise ValueError("Factorial of a negative number")
    if n > 2000:
        raise ValueError("Number too large for factorial")
    if isinstance(n, float) and not n.is_integer():
        return math.gamma(n + 1)
    return math.factorial(int(n))


def _clean(v):
    return 0.0 if abs(v) < 1e-12 else v


def calc_env(deg, ans):
    to_r = math.radians if deg else (lambda v: v)
    from_r = math.degrees if deg else (lambda v: v)
    return {
        "pi": math.pi, "e": math.e, "ans": ans,
        "sin": lambda v: _clean(math.sin(to_r(v))),
        "cos": lambda v: _clean(math.cos(to_r(v))),
        "tan": lambda v: _clean(math.tan(to_r(v))),
        "asin": lambda v: from_r(math.asin(v)),
        "acos": lambda v: from_r(math.acos(v)),
        "atan": lambda v: from_r(math.atan(v)),
        "sinh": math.sinh, "cosh": math.cosh, "tanh": math.tanh,
        "sqrt": math.sqrt, "cbrt": lambda v: math.copysign(abs(v) ** (1 / 3), v),
        "ln": math.log, "log": math.log10, "log2": math.log2, "exp": math.exp,
        "abs": abs, "fact": _fact, "pow": pow, "round": round,
        "floor": math.floor, "ceil": math.ceil,
        # multi-argument / list functions
        "sum": lambda *a: sum(_flat(a)),
        "mean": lambda *a: statistics.fmean(_flat(a)),
        "median": lambda *a: statistics.median(_flat(a)),
        "stdev": lambda *a: statistics.stdev(_flat(a)),
        "max": lambda *a: max(_flat(a)),
        "min": lambda *a: min(_flat(a)),
        "gcd": lambda *a: math.gcd(*[int(v) for v in _flat(a)]),
        "lcm": lambda *a: math.lcm(*[int(v) for v in _flat(a)]),
    }


def fmt(v):
    """Pretty-print a result."""
    if isinstance(v, (list, tuple)):
        return "[" + ", ".join(fmt(i) for i in v) + "]"
    if isinstance(v, int):
        return str(v)
    if math.isnan(v):
        return "NaN"
    if math.isinf(v):
        return "∞" if v > 0 else "-∞"
    if v == int(v) and abs(v) < 1e15:
        return str(int(v))
    return f"{v:.12g}"


# --------------------------------------------------------------------------- #
#  Small UI helpers
# --------------------------------------------------------------------------- #
class FlatButton(tk.Label):
    """Cross-platform flat button (tk.Button ignores colours on macOS)."""

    def __init__(self, master, text, command, bg, hover, fg=None,
                 font=("Segoe UI", 13), **kw):
        super().__init__(master, text=text, bg=bg, fg=fg or C["text"], font=font,
                         cursor="hand2", **kw)
        self._bg, self._hover, self._cmd = bg, hover, command
        self.bind("<Enter>", lambda e: self.config(bg=self._hover))
        self.bind("<Leave>", lambda e: self.config(bg=self._bg))
        self.bind("<ButtonRelease-1>", self._release)

    def _release(self, e):
        if 0 <= e.x <= self.winfo_width() and 0 <= e.y <= self.winfo_height():
            self._cmd()


def make_card(parent):
    return tk.Frame(parent, bg=C["panel"], highlightbackground=C["border"], highlightthickness=1)


def labeled_entry(parent, text, var, row, width=16, on_enter=None, col=0):
    ttk.Label(parent, text=text).grid(row=row, column=col, sticky="w", padx=(0, 12), pady=6)
    e = ttk.Entry(parent, textvariable=var, width=width)
    e.grid(row=row, column=col + 1, sticky="w", pady=6)
    if on_enter:
        e.bind("<Return>", lambda _e: on_enter())
    return e


def set_text(widget, content):
    widget.config(state="normal")
    widget.delete("1.0", "end")
    widget.insert("1.0", content)
    widget.config(state="disabled")


# --------------------------------------------------------------------------- #
#  Tab 1: Calculator
# --------------------------------------------------------------------------- #
class CalculatorTab(tk.Frame):
    # (label, kind, text, colspan, rowspan)  - last two are optional
    SCI = [
        [("DEG", "mode", None), ("sin", "fn", "sin("), ("cos", "fn", "cos("), ("tan", "fn", "tan(")],
        [("RAD", "mode", None), ("sin⁻¹", "fn", "asin("), ("cos⁻¹", "fn", "acos("), ("tan⁻¹", "fn", "atan(")],
        [("π", "fn", "pi"), ("ln", "fn", "ln("), ("log", "fn", "log("), ("e", "fn", "e")],
        [("x²", "sfn", "**2"), ("xʸ", "sfn", "**"), ("√x", "fn", "sqrt("), ("n!", "fn", "fact(")],
        [("(", "fn", "("), (")", "sfn", ")"), ("|x|", "fn", "abs("), ("1/x", "fn", "1/(")],
        [("mod", "sfn", "%"), ("mean", "fn", "mean("), ("median", "fn", "median("), ("max", "fn", "max(")],
        [(",", "sfn", ",", 4)],
    ]
    BASIC = [
        [("MC", "mem", None), ("MR", "mem", None), ("M+", "mem", None), ("M−", "mem", None)],
        [("C", "clr", None), ("⌫", "clr", None), ("±", "op", None), ("÷", "op", "/")],
        [("7", "num", "7"), ("8", "num", "8"), ("9", "num", "9"), ("×", "op", "*")],
        [("4", "num", "4"), ("5", "num", "5"), ("6", "num", "6"), ("−", "op", "-")],
        [("1", "num", "1"), ("2", "num", "2"), ("3", "num", "3"), ("+", "op", "+")],
        [("0", "num", "0", 2), (".", "num", "."), ("=", "eq", None, 1, 2)]

    ]
    STYLE = {
        "num": (C["num"], C["num_h"], C["text"]),
        "op": (C["op"], C["op_h"], C["text"]),
        "fn": (C["fn"], C["fn_h"], C["text"]),
        "sfn": (C["fn"], C["fn_h"], C["text"]),   # same look as "fn", but keeps the current result when pressed
        "mode": (C["fn"], C["fn_h"], C["text"]),
        "mem": (C["mem"], C["mem_h"], C["muted"]),
        "clr": (C["clr"], C["clr_h"], C["clr_fg"]),
        "eq": (C["eq"], C["eq_h"], "#FFFFFF"),
    }

    def __init__(self, master):
        super().__init__(master, bg=C["bg"])
        self.deg, self.ans, self.memory, self.fresh = True, 0, 0.0, False
        self.hist = []
        self.mode_btns = {}

        self.columnconfigure(0, weight=1)
        self.columnconfigure(1, weight=0)
        self.rowconfigure(0, weight=1)

        left = tk.Frame(self, bg=C["bg"])
        left.grid(row=0, column=0, sticky="nsew", padx=(16, 8), pady=16)
        left.columnconfigure(0, weight=1)

        # --- display
        disp = tk.Frame(left, bg=C["display_bg"])
        disp.grid(row=0, column=0, sticky="ew", pady=(0, 10))
        top = tk.Frame(disp, bg=C["display_bg"])
        top.pack(fill="x", padx=14, pady=(8, 0))
        self.mode_lbl = tk.Label(top, text="DEG", bg=C["display_bg"], fg=C["sub_fg"], font=("Segoe UI", 9, "bold"))
        self.mode_lbl.pack(side="left")
        self.mem_lbl = tk.Label(top, text="", bg=C["display_bg"], fg="#60A5FA", font=("Segoe UI", 9, "bold"))
        self.mem_lbl.pack(side="left", padx=10)
        self.sub = tk.Label(disp, text=" ", bg=C["display_bg"], fg=C["sub_fg"], font=("Segoe UI", 11), anchor="e")
        self.sub.pack(fill="x", padx=14)
        self.entry = tk.Entry(disp, font=("Segoe UI", 28), bg=C["display_bg"], fg=C["display_fg"],
                              insertbackground="#FFFFFF", relief="flat", justify="right", bd=0,
                              highlightthickness=0)
        self.entry.pack(fill="x", padx=14, pady=(0, 12))
        self.entry.bind("<Return>", lambda e: self.evaluate())
        self.entry.bind("<KP_Enter>", lambda e: self.evaluate())
        self.entry.bind("<Escape>", lambda e: self.clear())
        self.entry.bind("<Key>", lambda e: setattr(self, "fresh", False))
        self.entry.focus_set()

        # --- keypads
        pads = tk.Frame(left, bg=C["bg"])
        pads.grid(row=1, column=0, sticky="nsew")
        left.rowconfigure(1, weight=1)
        pads.columnconfigure(0, weight=1, uniform="pad")
        pads.columnconfigure(1, weight=1, uniform="pad")
        pads.rowconfigure(0, weight=1)
        sci = tk.Frame(pads, bg=C["bg"])
        sci.grid(row=0, column=0, sticky="nsew", padx=(0, 6))
        basic = tk.Frame(pads, bg=C["bg"])
        basic.grid(row=0, column=1, sticky="nsew", padx=(6, 0))
        self._build_pad(sci, self.SCI)
        self._build_pad(basic, self.BASIC)
        self._set_mode(True)

        # --- history
        hist_card = make_card(self)
        hist_card.grid(row=0, column=1, sticky="ns", padx=(8, 16), pady=16)
        tk.Label(hist_card, text="History", bg=C["panel"], fg=C["text"], font=("Segoe UI", 12, "bold")
                 ).pack(anchor="w", padx=14, pady=(12, 4))
        self.listbox = tk.Listbox(hist_card, width=30, bd=0, highlightthickness=0, relief="flat",
                                  font=("Consolas", 10), bg=C["panel"], fg=C["text"],
                                  selectbackground=C["accent"], selectforeground="#FFFFFF",
                                  activestyle="none")
        self.listbox.pack(fill="both", expand=True, padx=10, pady=4)
        self.listbox.bind("<Double-Button-1>", self._recall)
        tk.Label(hist_card, text="Double-click an entry to reuse it", bg=C["panel"], fg=C["muted"],
                 font=("Segoe UI", 8)).pack(padx=10)
        FlatButton(hist_card, "Clear history", self._clear_history, C["mem"], C["mem_h"], fg=C["muted"],
                   font=("Segoe UI", 10), pady=6).pack(fill="x", padx=10, pady=10)

    def _build_pad(self, frame, rows):
        for c in range(4):
            frame.columnconfigure(c, weight=1, uniform="btn")
        occupied = set()
        for r, row in enumerate(rows):
            frame.rowconfigure(r, weight=1, uniform="row")
            col = 0
            for spec in row:
                label, kind, text = spec[:3]
                cspan = spec[3] if len(spec) > 3 else 1
                rspan = spec[4] if len(spec) > 4 else 1
                while (r, col) in occupied:
                    col += 1
                bg, hv, fg = self.STYLE[kind]
                small = kind in ("fn", "sfn", "mode", "mem")
                btn = FlatButton(frame, label, lambda l=label, k=kind, t=text: self._click(l, k, t),
                                 bg, hv, fg, font=("Segoe UI", 12 if small else 14), pady=9)
                btn.grid(row=r, column=col, columnspan=cspan, rowspan=rspan,
                         sticky="nsew", padx=3, pady=3)
                for dr in range(rspan):
                    for dc in range(cspan):
                        occupied.add((r + dr, col + dc))
                if kind == "mode":
                    self.mode_btns[label] = btn
                col += cspan

    def _set_mode(self, deg):
        """Highlight the active angle mode (DEG or RAD)."""
        self.deg = deg
        name = "DEG" if deg else "RAD"
        self.mode_lbl.config(text=name)
        for n, b in self.mode_btns.items():
            on = n == name
            b._bg = C["accent"] if on else C["fn"]
            b._hover = C["eq_h"] if on else C["fn_h"]
            b.config(bg=b._bg, fg="#FFFFFF" if on else C["text"])

    # ---- actions
    def _click(self, label, kind, text):
        if kind == "mem":
            self._memory(label)
        elif label == "C":
            self.clear()
        elif label == "⌫":
            self.backspace()
        elif label == "±":
            self.negate()
        elif kind == "mode":
            self._set_mode(label == "DEG")
        elif kind == "eq":
            self.evaluate()
        else:
            self.press(text, kind)
        self.entry.focus_set()

    def press(self, text, kind):
        if self.fresh:
            if kind in ("num", "fn"):
                self.entry.delete(0, tk.END)
            self.fresh = False
        self.entry.insert(tk.END, text)
        self.entry.icursor(tk.END)

    def clear(self):
        self.entry.delete(0, tk.END)
        self.sub.config(text=" ", fg=C["sub_fg"])
        self.fresh = False

    def backspace(self):
        if self.fresh:
            self.clear()
        else:
            t = self.entry.get()
            self.entry.delete(0, tk.END)
            self.entry.insert(0, t[:-1])

    def negate(self):
        t = self.entry.get().strip()
        if not t:
            return
        t = t[2:-1] if (t.startswith("-(") and t.endswith(")")) else f"-({t})"
        self.entry.delete(0, tk.END)
        self.entry.insert(0, t)

    def _error(self, msg):
        self.sub.config(text=msg, fg="#F87171")

    def _compute(self, raw):
        expr = raw + ")" * max(0, raw.count("(") - raw.count(")"))
        return safe_eval(preprocess(expr), calc_env(self.deg, self.ans))

    def evaluate(self):
        raw = self.entry.get().strip()
        if not raw:
            return
        try:
            res = self._compute(raw)
            text = fmt(res)
        except ZeroDivisionError:
            return self._error("Cannot divide by zero")
        except SyntaxError:
            return self._error("Invalid expression")
        except OverflowError:
            return self._error("Result too large")
        except Exception as ex:  # noqa: BLE001
            return self._error(f"Error: {ex}")
        self.sub.config(text=f"{raw} =", fg=C["sub_fg"])
        self.entry.delete(0, tk.END)
        self.entry.insert(0, text)
        if isinstance(res, (int, float)):
            self.ans = res
        self.hist.insert(0, raw)
        self.listbox.insert(0, f"{raw}  =  {text}")
        self.fresh = True

    def _peek(self):
        raw = self.entry.get().strip()
        if not raw:
            return None
        try:
            v = self._compute(raw)
            return float(v) if isinstance(v, (int, float)) else None
        except Exception:  # noqa: BLE001
            self._error("Enter a valid number first")
            return None

    def _memory(self, op):
        if op == "MC":
            self.memory = 0.0
        elif op == "MR":
            self.press(fmt(self.memory), "num")
        else:
            v = self._peek()
            if v is None:
                return
            self.memory += v if op == "M+" else -v
        self.mem_lbl.config(text="M" if self.memory else "")

    def _recall(self, _e):
        sel = self.listbox.curselection()
        if sel:
            self.entry.delete(0, tk.END)
            self.entry.insert(0, self.hist[sel[0]])
            self.fresh = False

    def _clear_history(self):
        self.hist.clear()
        self.listbox.delete(0, tk.END)


# --------------------------------------------------------------------------- #
#  Tab 2: BMI
# --------------------------------------------------------------------------- #
class BMITab(tk.Frame):
    def __init__(self, master):
        super().__init__(master, bg=C["bg"])
        self.unit = tk.StringVar(value="metric")
        self.kg, self.cm = tk.StringVar(), tk.StringVar()
        self.lb, self.ft, self.inch = tk.StringVar(), tk.StringVar(), tk.StringVar(value="0")

        card = make_card(self)
        card.pack(pady=24, ipadx=36, ipady=16)
        tk.Label(card, text="Body Mass Index", bg=C["panel"], fg=C["text"], font=("Segoe UI", 16, "bold")
                 ).pack(anchor="w", padx=28, pady=(20, 2))
        tk.Label(card, text="Enter your measurements to see where you fall on the BMI scale.",
                 bg=C["panel"], fg=C["muted"], font=("Segoe UI", 10)).pack(anchor="w", padx=28, pady=(0, 12))

        units = tk.Frame(card, bg=C["panel"])
        units.pack(anchor="w", padx=28)
        ttk.Radiobutton(units, text="Metric (kg, cm)", variable=self.unit, value="metric",
                        command=self._switch).pack(side="left", padx=(0, 16))
        ttk.Radiobutton(units, text="Imperial (lb, ft/in)", variable=self.unit, value="imperial",
                        command=self._switch).pack(side="left")

        form = tk.Frame(card, bg=C["panel"])
        form.pack(anchor="w", padx=28, pady=10)
        self.metric = tk.Frame(form, bg=C["panel"])
        labeled_entry(self.metric, "Weight (kg)", self.kg, 0, on_enter=self.calculate)
        labeled_entry(self.metric, "Height (cm)", self.cm, 1, on_enter=self.calculate)
        self.imperial = tk.Frame(form, bg=C["panel"])
        labeled_entry(self.imperial, "Weight (lb)", self.lb, 0, on_enter=self.calculate)
        ttk.Label(self.imperial, text="Height").grid(row=1, column=0, sticky="w", pady=6)
        hf = tk.Frame(self.imperial, bg=C["panel"])
        hf.grid(row=1, column=1, sticky="w")
        ttk.Entry(hf, textvariable=self.ft, width=5).pack(side="left")
        ttk.Label(hf, text=" ft  ").pack(side="left")
        ttk.Entry(hf, textvariable=self.inch, width=5).pack(side="left")
        ttk.Label(hf, text=" in").pack(side="left")
        self.metric.pack()

        FlatButton(card, "Calculate BMI", self.calculate, C["eq"], C["eq_h"], "#FFFFFF",
                   font=("Segoe UI", 12, "bold"), pady=8).pack(fill="x", padx=28, pady=(4, 14))

        self.value = tk.Label(card, text="--", bg=C["panel"], fg=C["text"], font=("Segoe UI", 40, "bold"))
        self.value.pack()
        self.category = tk.Label(card, text="", bg=C["panel"], fg=C["muted"], font=("Segoe UI", 14, "bold"))
        self.category.pack()
        self.scale = tk.Canvas(card, width=440, height=64, bg=C["panel"], highlightthickness=0)
        self.scale.pack(pady=(10, 0))
        self.range_lbl = tk.Label(card, text="", bg=C["panel"], fg=C["muted"], font=("Segoe UI", 10))
        self.range_lbl.pack(pady=(4, 0))
        self._draw_scale(None)

    def _switch(self):
        self.metric.pack_forget()
        self.imperial.pack_forget()
        (self.metric if self.unit.get() == "metric" else self.imperial).pack()

    def _draw_scale(self, bmi):
        c, w = self.scale, 440
        c.delete("all")
        segs = [(10, 18.5, "#60A5FA"), (18.5, 25, "#34D399"), (25, 30, "#FBBF24"), (30, 40, "#F87171")]
        px = lambda v: (min(max(v, 10), 40) - 10) / 30 * (w - 20) + 10  # noqa: E731
        for a, b, col in segs:
            c.create_rectangle(px(a), 26, px(b), 40, fill=col, outline="")
        for v in (18.5, 25, 30):
            c.create_text(px(v), 52, text=str(v), fill=C["muted"], font=("Segoe UI", 8))
        if bmi is not None:
            x = px(bmi)
            c.create_polygon(x - 7, 8, x + 7, 8, x, 22, fill=C["header"], outline="")

    def calculate(self):
        try:
            if self.unit.get() == "metric":
                w, h = float(self.kg.get()), float(self.cm.get()) / 100
            else:
                w = float(self.lb.get()) * 0.45359237
                h = (float(self.ft.get() or 0) * 12 + float(self.inch.get() or 0)) * 0.0254
        except ValueError:
            return messagebox.showerror("Invalid input", "Please enter numbers only.")
        if w <= 0 or h <= 0:
            return messagebox.showerror("Invalid input", "Weight and height must be greater than zero.")
        bmi = w / (h * h)
        if bmi < 18.5:
            cat, col = "Underweight", C["info"]
        elif bmi < 25:
            cat, col = "Normal weight", C["good"]
        elif bmi < 30:
            cat, col = "Overweight", C["warn"]
        else:
            cat, col = "Obese", C["bad"]
        lo, hi = 18.5 * h * h, 24.9 * h * h
        if self.unit.get() == "imperial":
            lo, hi, u = lo / 0.45359237, hi / 0.45359237, "lb"
        else:
            u = "kg"
        self.value.config(text=f"{bmi:.1f}", fg=col)
        self.category.config(text=cat, fg=col)
        self.range_lbl.config(text=f"Healthy weight for your height: {lo:.1f} – {hi:.1f} {u}")
        self._draw_scale(bmi)


# --------------------------------------------------------------------------- #
#  Tab 3: Currency converter
# --------------------------------------------------------------------------- #
class CurrencyTab(tk.Frame):
    API = "https://open.er-api.com/v6/latest/USD"
    # Approximate offline fallback rates (per 1 USD). Use "Update live rates" for current values.
    RATES = {"USD": 1.0, "EUR": 0.92, "GBP": 0.78, "INR": 84.0, "JPY": 150.0, "AUD": 1.52,
             "CAD": 1.38, "CHF": 0.88, "CNY": 7.2, "AED": 3.6725, "SGD": 1.34, "HKD": 7.8,
             "NZD": 1.65, "SAR": 3.75, "ZAR": 18.0, "KRW": 1350.0, "BRL": 5.5, "MXN": 18.5}
    NAMES = {"USD": "US Dollar", "EUR": "Euro", "GBP": "British Pound", "INR": "Indian Rupee",
             "JPY": "Japanese Yen", "AUD": "Australian Dollar", "CAD": "Canadian Dollar",
             "CHF": "Swiss Franc", "CNY": "Chinese Yuan", "AED": "UAE Dirham", "SGD": "Singapore Dollar",
             "HKD": "Hong Kong Dollar", "NZD": "New Zealand Dollar", "SAR": "Saudi Riyal",
             "ZAR": "South African Rand", "KRW": "South Korean Won", "BRL": "Brazilian Real",
             "MXN": "Mexican Peso"}

    def __init__(self, master):
        super().__init__(master, bg=C["bg"])
        self.rates = dict(self.RATES)
        self.amount = tk.StringVar(value="100")
        self.src, self.dst = tk.StringVar(), tk.StringVar()
        self.q = queue.Queue()

        card = make_card(self)
        card.pack(pady=24, ipadx=36, ipady=16)
        tk.Label(card, text="Currency Converter", bg=C["panel"], fg=C["text"], font=("Segoe UI", 16, "bold")
                 ).pack(anchor="w", padx=28, pady=(20, 2))
        tk.Label(card, text="Tip: enter several amounts separated by commas, e.g.  10, 50, 250",
                 bg=C["panel"], fg=C["muted"], font=("Segoe UI", 10)).pack(anchor="w", padx=28, pady=(0, 12))

        form = tk.Frame(card, bg=C["panel"])
        form.pack(anchor="w", padx=28)
        labeled_entry(form, "Amount(s)", self.amount, 0, width=34, on_enter=self.convert)
        ttk.Label(form, text="From").grid(row=1, column=0, sticky="w", pady=6)
        self.cb_src = ttk.Combobox(form, textvariable=self.src, state="readonly", width=32)
        self.cb_src.grid(row=1, column=1, sticky="w", pady=6)
        ttk.Label(form, text="To").grid(row=2, column=0, sticky="w", pady=6)
        self.cb_dst = ttk.Combobox(form, textvariable=self.dst, state="readonly", width=32)
        self.cb_dst.grid(row=2, column=1, sticky="w", pady=6)
        self._refresh_lists("USD", "INR")
        for cb in (self.cb_src, self.cb_dst):
            cb.bind("<<ComboboxSelected>>", lambda e: self.convert())

        btns = tk.Frame(card, bg=C["panel"])
        btns.pack(fill="x", padx=28, pady=(8, 10))
        FlatButton(btns, "Convert", self.convert, C["eq"], C["eq_h"], "#FFFFFF", font=("Segoe UI", 11, "bold"),
                   padx=22, pady=7).pack(side="left")
        FlatButton(btns, "⇄  Swap", self.swap, C["op"], C["op_h"], C["text"], font=("Segoe UI", 11),
                   padx=16, pady=7).pack(side="left", padx=8)
        FlatButton(btns, "Update live rates", self.fetch_live, C["mem"], C["mem_h"], C["accent"],
                   font=("Segoe UI", 11), padx=16, pady=7).pack(side="left")

        self.out = tk.Text(card, width=52, height=8, bd=0, highlightthickness=1,
                           highlightbackground=C["border"], font=("Consolas", 12), bg="#F8FAFC",
                           fg=C["text"], padx=12, pady=10, state="disabled")
        self.out.pack(padx=28, pady=(4, 6))
        self.rate_lbl = tk.Label(card, text="", bg=C["panel"], fg=C["text"], font=("Segoe UI", 10, "bold"))
        self.rate_lbl.pack(anchor="w", padx=28)
        self.status = tk.Label(card, text="Using offline approximate rates (click “Update live rates” for current ones).",
                               bg=C["panel"], fg=C["muted"], font=("Segoe UI", 9))
        self.status.pack(anchor="w", padx=28, pady=(2, 0))
        self.convert()

    # ---- helpers
    def _label(self, code):
        return f"{code}  –  {self.NAMES.get(code, code)}"

    def _refresh_lists(self, src=None, dst=None):
        values = [self._label(c) for c in sorted(self.rates)]
        self.cb_src["values"] = values
        self.cb_dst["values"] = values
        if src:
            self.src.set(self._label(src))
        if dst:
            self.dst.set(self._label(dst))

    @staticmethod
    def _code(value):
        return value.split()[0]

    def swap(self):
        a, b = self.src.get(), self.dst.get()
        self.src.set(b)
        self.dst.set(a)
        self.convert()

    def convert(self):
        try:
            amounts = [float(t) for t in re.split(r"[;,\s]+", self.amount.get().strip()) if t]
            if not amounts:
                raise ValueError
        except ValueError:
            return messagebox.showerror("Invalid amount", "Enter one or more numbers, e.g.  100  or  10, 50, 250")
        a, b = self._code(self.src.get()), self._code(self.dst.get())
        rate = self.rates[b] / self.rates[a]
        lines = [f"{amt:>14,.2f} {a}  =  {amt * rate:>16,.2f} {b}" for amt in amounts]
        if len(amounts) > 1:
            lines.append("-" * 46)
            lines.append(f"{sum(amounts):>14,.2f} {a}  =  {sum(amounts) * rate:>16,.2f} {b}   (total)")
        set_text(self.out, "\n".join(lines))
        self.rate_lbl.config(text=f"1 {a} = {rate:,.4f} {b}")

    # ---- live rates (network call runs in a background thread)
    def fetch_live(self):
        self.status.config(text="Fetching live rates…", fg=C["muted"])

        def work():
            try:
                with urllib.request.urlopen(self.API, timeout=8) as r:
                    data = json.load(r)
                if data.get("result") != "success":
                    raise RuntimeError("Rate service returned an error")
                self.q.put(("ok", data))
            except Exception as ex:  # noqa: BLE001
                self.q.put(("err", str(ex)))

        threading.Thread(target=work, daemon=True).start()
        self.after(200, self._poll)

    def _poll(self):
        try:
            kind, payload = self.q.get_nowait()
        except queue.Empty:
            return self.after(200, self._poll)
        if kind == "ok":
            keep = (self._code(self.src.get()), self._code(self.dst.get()))
            self.rates = {k: float(v) for k, v in payload["rates"].items() if v}
            self._refresh_lists(*[k if k in self.rates else "USD" for k in keep])
            stamp = payload.get("time_last_update_utc", "")[:16]
            self.status.config(text=f"Live rates loaded ({stamp} UTC).", fg=C["good"])
            self.convert()
        else:
            self.status.config(text="Couldn't fetch live rates (offline?). Using stored approximate rates.",
                               fg=C["bad"])


# --------------------------------------------------------------------------- #
#  Tab 4: Unit converter
# --------------------------------------------------------------------------- #
class UnitTab(tk.Frame):
    # Each category maps unit -> size expressed in the category's base unit.
    UNITS = {
        "Length": {  # base: meter
            "Kilometer (km)": 1000.0, "Meter (m)": 1.0, "Centimeter (cm)": 0.01,
            "Millimeter (mm)": 0.001, "Mile (mi)": 1609.344, "Yard (yd)": 0.9144,
            "Foot (ft)": 0.3048, "Inch (in)": 0.0254, "Nautical mile (nmi)": 1852.0,
        },
        "Mass": {  # base: kilogram
            "Tonne (t)": 1000.0, "Kilogram (kg)": 1.0, "Gram (g)": 0.001, "Milligram (mg)": 1e-6,
            "Pound (lb)": 0.45359237, "Ounce (oz)": 0.028349523125, "Stone (st)": 6.35029318,
        },
        "Area": {  # base: square meter
            "Square km (km²)": 1e6, "Hectare (ha)": 1e4, "Square meter (m²)": 1.0,
            "Square cm (cm²)": 1e-4, "Square mile (mi²)": 2589988.110336, "Acre (ac)": 4046.8564224,
            "Square yard (yd²)": 0.83612736, "Square foot (ft²)": 0.09290304,
            "Square inch (in²)": 0.00064516,
        },
        "Volume": {  # base: liter
            "Cubic meter (m³)": 1000.0, "Liter (L)": 1.0, "Milliliter (mL)": 0.001,
            "US gallon (gal)": 3.785411784, "US quart (qt)": 0.946352946, "US pint (pt)": 0.473176473,
            "US cup": 0.2365882365, "US fluid ounce (fl oz)": 0.0295735295625,
            "Tablespoon (US)": 0.01478676478125, "Teaspoon (US)": 0.00492892159375,
            "Imperial gallon": 4.54609,
        },
        "Speed": {  # base: meter / second
            "Meter/second (m/s)": 1.0, "Kilometer/hour (km/h)": 1 / 3.6, "Mile/hour (mph)": 0.44704,
            "Knot (kn)": 1852 / 3600, "Foot/second (ft/s)": 0.3048,
        },
        "Time": {  # base: second
            "Year (365.25 d)": 31557600.0, "Week": 604800.0, "Day": 86400.0, "Hour": 3600.0,
            "Minute": 60.0, "Second": 1.0, "Millisecond": 0.001,
        },
        "Data": {  # base: byte
            "Bit": 0.125, "Byte (B)": 1.0, "Kilobyte (KB)": 1e3, "Megabyte (MB)": 1e6,
            "Gigabyte (GB)": 1e9, "Terabyte (TB)": 1e12, "Kibibyte (KiB)": 1024.0,
            "Mebibyte (MiB)": 1024.0 ** 2, "Gibibyte (GiB)": 1024.0 ** 3, "Tebibyte (TiB)": 1024.0 ** 4,
        },
        "Energy": {  # base: joule
            "Joule (J)": 1.0, "Kilojoule (kJ)": 1000.0, "Calorie (cal)": 4.184,
            "Kilocalorie (kcal)": 4184.0, "Watt-hour (Wh)": 3600.0, "Kilowatt-hour (kWh)": 3.6e6,
            "BTU": 1055.05585262,
        },
        "Pressure": {  # base: pascal
            "Pascal (Pa)": 1.0, "Kilopascal (kPa)": 1000.0, "Bar": 1e5, "Atmosphere (atm)": 101325.0,
            "PSI": 6894.757293168, "mmHg": 133.322387415,
        },
    }
    # Temperature is not a pure scale factor, so it goes through Celsius.
    TEMPS = {
        "Celsius (°C)": (lambda c: c, lambda c: c),
        "Fahrenheit (°F)": (lambda f: (f - 32) * 5 / 9, lambda c: c * 9 / 5 + 32),
        "Kelvin (K)": (lambda k: k - 273.15, lambda c: c + 273.15),
    }

    @staticmethod
    def _num(v):
        if v == 0:
            return "0"
        if abs(v) >= 1e12 or abs(v) < 1e-5:
            return f"{v:.6e}"
        return format(v, ",.10g")

    def __init__(self, master):
        super().__init__(master, bg=C["bg"])
        self.cat = tk.StringVar(value="Length")
        self.val = tk.StringVar(value="1")
        self.src, self.dst = tk.StringVar(), tk.StringVar()

        card = make_card(self)
        card.pack(pady=24, ipadx=36, ipady=16)
        tk.Label(card, text="Unit Converter", bg=C["panel"], fg=C["text"], font=("Segoe UI", 16, "bold")
                 ).pack(anchor="w", padx=28, pady=(20, 2))
        tk.Label(card, text="Pick a category, enter a value and choose the units.",
                 bg=C["panel"], fg=C["muted"], font=("Segoe UI", 10)).pack(anchor="w", padx=28, pady=(0, 12))

        form = tk.Frame(card, bg=C["panel"])
        form.pack(anchor="w", padx=28)
        ttk.Label(form, text="Category").grid(row=0, column=0, sticky="w", padx=(0, 12), pady=6)
        cb_cat = ttk.Combobox(form, textvariable=self.cat, state="readonly", width=32,
                              values=list(self.UNITS) + ["Temperature"])
        cb_cat.grid(row=0, column=1, sticky="w", pady=6)
        cb_cat.bind("<<ComboboxSelected>>", lambda e: self._category_changed())
        labeled_entry(form, "Value", self.val, 1, width=34, on_enter=self.convert)
        ttk.Label(form, text="From").grid(row=2, column=0, sticky="w", pady=6)
        self.cb_src = ttk.Combobox(form, textvariable=self.src, state="readonly", width=32)
        self.cb_src.grid(row=2, column=1, sticky="w", pady=6)
        ttk.Label(form, text="To").grid(row=3, column=0, sticky="w", pady=6)
        self.cb_dst = ttk.Combobox(form, textvariable=self.dst, state="readonly", width=32)
        self.cb_dst.grid(row=3, column=1, sticky="w", pady=6)
        for cb in (self.cb_src, self.cb_dst):
            cb.bind("<<ComboboxSelected>>", lambda e: self.convert())

        btns = tk.Frame(card, bg=C["panel"])
        btns.pack(fill="x", padx=28, pady=(8, 10))
        FlatButton(btns, "Convert", self.convert, C["eq"], C["eq_h"], "#FFFFFF", font=("Segoe UI", 11, "bold"),
                   padx=22, pady=7).pack(side="left")
        FlatButton(btns, "⇄  Swap", self.swap, C["op"], C["op_h"], C["text"], font=("Segoe UI", 11),
                   padx=16, pady=7).pack(side="left", padx=8)

        self.result = tk.Label(card, text="--", bg=C["panel"], fg=C["accent"], font=("Segoe UI", 20, "bold"))
        self.result.pack(anchor="w", padx=28, pady=(4, 2))
        tk.Label(card, text="Same value in every unit of this category:", bg=C["panel"], fg=C["muted"],
                 font=("Segoe UI", 9)).pack(anchor="w", padx=28)
        self.out = tk.Text(card, width=52, height=10, bd=0, highlightthickness=1,
                           highlightbackground=C["border"], font=("Consolas", 11), bg="#F8FAFC",
                           fg=C["text"], padx=12, pady=10, state="disabled")
        self.out.pack(padx=28, pady=(4, 6))
        self._category_changed()

    def _units(self):
        c = self.cat.get()
        return list(self.TEMPS) if c == "Temperature" else list(self.UNITS[c])

    def _category_changed(self):
        units = self._units()
        self.cb_src["values"] = units
        self.cb_dst["values"] = units
        self.src.set(units[0])
        self.dst.set(units[1] if len(units) > 1 else units[0])
        self.convert()

    def swap(self):
        a, b = self.src.get(), self.dst.get()
        self.src.set(b)
        self.dst.set(a)
        self.convert()

    def _to_all(self, x, a):
        """Return {unit: value} converting x from unit a to every unit in the category."""
        c = self.cat.get()
        if c == "Temperature":
            celsius = self.TEMPS[a][0](x)
            return {u: self.TEMPS[u][1](celsius) for u in self.TEMPS}
        base = x * self.UNITS[c][a]
        return {u: base / f for u, f in self.UNITS[c].items()}

    def convert(self):
        try:
            x = float(self.val.get().strip().replace(",", ""))
        except ValueError:
            return messagebox.showerror("Invalid value", "Please enter a number.")
        a, b = self.src.get(), self.dst.get()
        if self.cat.get() == "Temperature" and a == "Kelvin (K)" and x < 0:
            return messagebox.showerror("Invalid value", "Kelvin cannot be negative.")
        allv = self._to_all(x, a)
        self.result.config(text=f"{self._num(x)} {a.split('(')[-1].rstrip(')') if '(' in a else a}  =  "
                                f"{self._num(allv[b])} {b.split('(')[-1].rstrip(')') if '(' in b else b}")
        width = max(len(u) for u in allv)
        set_text(self.out, "\n".join(f"{u:<{width}}  {self._num(v):>20}" for u, v in allv.items()))


# --------------------------------------------------------------------------- #
#  Tab 5: Age calculator
# --------------------------------------------------------------------------- #
def add_months(d, n):
    """Add n months to date d, clamping the day (e.g. 31 Jan + 1 month -> 28/29 Feb)."""
    y, m = divmod(d.month - 1 + n, 12)
    year, month = d.year + y, m + 1
    return dt.date(year, month, min(d.day, calendar.monthrange(year, month)[1]))


def age_between(dob, ref):
    """Return (years, months, days) elapsed from dob to ref (ref >= dob)."""
    months = (ref.year - dob.year) * 12 + ref.month - dob.month
    if add_months(dob, months) > ref:
        months -= 1
    days = (ref - add_months(dob, months)).days
    years, months = divmod(months, 12)
    return years, months, days


class AgeTab(tk.Frame):
    def __init__(self, master):
        super().__init__(master, bg=C["bg"])
        today = dt.date.today()
        self.b_d, self.b_m, self.b_y = tk.StringVar(), tk.StringVar(), tk.StringVar()
        self.a_d, self.a_m, self.a_y = (tk.StringVar(value=str(today.day)),
                                        tk.StringVar(value=str(today.month)),
                                        tk.StringVar(value=str(today.year)))

        card = make_card(self)
        card.pack(pady=24, ipadx=36, ipady=16)
        tk.Label(card, text="Age Calculator", bg=C["panel"], fg=C["text"], font=("Segoe UI", 16, "bold")
                 ).pack(anchor="w", padx=28, pady=(20, 2))
        tk.Label(card, text="Find an exact age, or the time between any two dates.",
                 bg=C["panel"], fg=C["muted"], font=("Segoe UI", 10)).pack(anchor="w", padx=28, pady=(0, 12))

        form = tk.Frame(card, bg=C["panel"])
        form.pack(anchor="w", padx=28)
        for c, h in enumerate(("Day", "Month", "Year"), start=1):
            ttk.Label(form, text=h, foreground=C["muted"]).grid(row=0, column=c, sticky="w", padx=(0, 6))
        self._date_row(form, 1, "Date of birth", self.b_d, self.b_m, self.b_y)
        self._date_row(form, 2, "Age at date", self.a_d, self.a_m, self.a_y)

        btns = tk.Frame(card, bg=C["panel"])
        btns.pack(fill="x", padx=28, pady=(10, 10))
        FlatButton(btns, "Calculate age", self.calculate, C["eq"], C["eq_h"], "#FFFFFF",
                   font=("Segoe UI", 11, "bold"), padx=22, pady=7).pack(side="left")
        FlatButton(btns, "Use today", self.use_today, C["op"], C["op_h"], C["text"],
                   font=("Segoe UI", 11), padx=16, pady=7).pack(side="left", padx=8)

        self.big = tk.Label(card, text="--", bg=C["panel"], fg=C["accent"], font=("Segoe UI", 22, "bold"))
        self.big.pack(anchor="w", padx=28, pady=(4, 6))
        self.out = tk.Text(card, width=52, height=11, bd=0, highlightthickness=1,
                           highlightbackground=C["border"], font=("Consolas", 11), bg="#F8FAFC",
                           fg=C["text"], padx=12, pady=10, state="disabled")
        self.out.pack(padx=28, pady=(0, 6))
        self.msg = tk.Label(card, text="", bg=C["panel"], fg=C["good"], font=("Segoe UI", 10, "bold"))
        self.msg.pack(anchor="w", padx=28)

    def _date_row(self, parent, row, text, d, m, y):
        ttk.Label(parent, text=text).grid(row=row, column=0, sticky="w", padx=(0, 12), pady=6)
        for col, (var, w) in enumerate(((d, 5), (m, 5), (y, 8)), start=1):
            e = ttk.Entry(parent, textvariable=var, width=w)
            e.grid(row=row, column=col, sticky="w", padx=(0, 6), pady=6)
            e.bind("<Return>", lambda _e: self.calculate())

    def use_today(self):
        t = dt.date.today()
        self.a_d.set(str(t.day))
        self.a_m.set(str(t.month))
        self.a_y.set(str(t.year))
        if self.b_y.get().strip():
            self.calculate()

    @staticmethod
    def _parse(d, m, y, what):
        try:
            return dt.date(int(y.get()), int(m.get()), int(d.get()))
        except ValueError:
            raise ValueError(f"Please enter a valid {what} (day, month and year as numbers).") from None

    def calculate(self):
        try:
            dob = self._parse(self.b_d, self.b_m, self.b_y, "date of birth")
            ref = self._parse(self.a_d, self.a_m, self.a_y, "'age at' date")
            if dob > ref:
                raise ValueError("Date of birth must not be after the 'age at' date.")
            yrs, mos, days = age_between(dob, ref)
            nxt = add_months(dob, 12 * (yrs + 1))
        except (ValueError, OverflowError) as ex:
            return messagebox.showerror("Invalid date", str(ex))

        def plural(n, word):
            return f"{n} {word}{'' if n == 1 else 's'}"

        total_days = (ref - dob).days
        total_months = yrs * 12 + mos
        n_yrs, n_mos, n_days = age_between(ref, nxt)
        next_in = ", ".join(plural(n, w) for n, w in ((n_mos, "month"), (n_days, "day")) if n) or "0 days"
        self.big.config(text=f"{plural(yrs, 'year')}, {plural(mos, 'month')}, {plural(days, 'day')}")
        lines = [
            f"Born on          {dob:%A, %d %B %Y}",
            f"Age at           {ref:%A, %d %B %Y}",
            "",
            f"Total months     {total_months:,}  (+ {plural(days, 'day')})",
            f"Total weeks      {total_days // 7:,}  (+ {plural(total_days % 7, 'day')})",
            f"Total days       {total_days:,}",
            f"Total hours      {total_days * 24:,}",
            f"Total minutes    {total_days * 1440:,}",
            "",
            f"Next birthday    {nxt:%A, %d %B %Y}",
            f"                 in {next_in} ({(nxt - ref).days:,} days)",
        ]
        set_text(self.out, "\n".join(lines))
        is_birthday = yrs > 0 and mos == 0 and days == 0
        self.msg.config(text="Happy birthday!" if is_birthday else "")


# --------------------------------------------------------------------------- #
#  Application
# --------------------------------------------------------------------------- #
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Advanced Calculator")
        self.geometry("1040x780")
        self.minsize(960, 720)
        self.configure(bg=C["bg"])
        self._style()

        head = tk.Frame(self, bg=C["header"])
        head.pack(fill="x")
        tk.Label(head, text="CalcSuite Pro Calculator", bg=C["header"], fg=C["header_fg"],
                 font=("Segoe UI", 16, "bold")).pack(side="left", padx=20, pady=12)

        nb = ttk.Notebook(self)
        nb.pack(fill="both", expand=True, padx=12, pady=12)
        nb.add(CalculatorTab(nb), text="Calculator")
        nb.add(BMITab(nb), text="BMI")
        nb.add(CurrencyTab(nb), text="Currency")
        nb.add(UnitTab(nb), text="Units")
        nb.add(AgeTab(nb), text="Age")

    def _style(self):
        st = ttk.Style(self)
        st.theme_use("clam")
        st.configure("TNotebook", background=C["bg"], borderwidth=0)
        st.configure("TNotebook.Tab", padding=(22, 10), font=FONT_B, background="#DCE3EE",
                     foreground=C["muted"], borderwidth=0)
        st.map("TNotebook.Tab", background=[("selected", C["panel"])], foreground=[("selected", C["accent"])])
        st.configure("TLabel", background=C["panel"], foreground=C["text"], font=FONT)
        st.configure("TEntry", fieldbackground="#F8FAFC", padding=6, font=FONT)
        st.configure("TCombobox", fieldbackground="#F8FAFC", padding=5, font=FONT)
        for w in ("TRadiobutton", "TCheckbutton"):
            st.configure(w, background=C["panel"], foreground=C["text"], font=FONT)
            st.map(w, background=[("active", C["panel"])])


if __name__ == "__main__":
    App().mainloop()