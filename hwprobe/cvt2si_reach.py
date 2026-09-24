#!/usr/bin/env python3
"""hwprobe/cvt2si_reach.py — B6a's REACH TABLE: which of D287's cvt*2si rows no vector reaches (D290).

B0's rule (D267 §2) pins a row iff x86isa disagrees with it OR no vector of the same form reaches its class over the
88 differential pre-states. x86isa agrees with every cvt*2si row (D287 §4), so only the reach half selects here.

⚖️ THE CLASS IS THE ROUNDING PATH, as B3 classed `cvtsd2ss` (D273) and not by value equality, which no random state
meets at 5/2 or 7/2. A row's class is
    (the path, the sign, and the RC where the path is inexact)
with the path one of
    nan · inf · zero · exact · toward (inexact, rounded toward zero) · away (inexact, rounded away from zero)
    · tie (exactly half-way, whichever way it went) · range (a NaN-free value whose ROUNDED result is out of range)
so a row is REACHED iff some vector of the same form (same format, same destination width) presents a source of
the same path, sign and, where it matters, RC. ⚠️ `tie` is its own path because the tie-breaking rule is what it
asks; `away` at nearest is the half of D289 §2's gap that is not a tie.

    python3 hwprobe/cvt2si_reach.py              the table and the totals
    python3 hwprobe/cvt2si_reach.py --pinned     just the pinned names
    python3 hwprobe/cvt2si_reach.py --selftest   the known answers (below)

INPUT, DECLARED: run/prestates.json (the 88 pre-states, D283 §1). The vectors are read from `Tests/Vectors.lean`'s
CONSTRUCTORS (`vcvt2si`/`vcvt2sim`), never their asm text.
⚠️ NOT MEASURED: whether the differential compares a reached case soundly (reach is not coverage).
"""
import json
import os
import re
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import mk_rows as M                                    # noqa: E402
import portable as P                                   # noqa: E402

PRESTATES = os.path.join(ROOT, "run", "prestates.json")
VECTORS = os.path.join(ROOT, "Tests", "Vectors.lean")
VEC_RE = re.compile(r"\.vcvt2si(m?) (true|false) (true|false) \.\w+ "
                    r"(?:\.x(\d+)|\{ base := some \.rbx(?:, disp := (-?(?:0x)?[0-9a-f]+))? \})")


def form(dbl, wide):
    return "p_cvt%s2si%s" % ("sd" if dbl else "ss", "q" if wide else "")


def vectors(text):
    out = []
    for mem, dbl, wide, reg, disp in VEC_RE.findall(text):
        src = ("m", int(disp, 0) if disp else 0) if mem else ("x", int(reg))
        out.append((form(dbl == "true", wide == "true"), src))
    return out


def klass(fmt, width, rc, a):
    w = 1 + fmt[0] + fmt[1]
    x = a & ((1 << w) - 1)
    k = M.kind(fmt, x)
    neg = bool(x >> (w - 1))
    if k in ("qnan", "snan"):
        return ("nan", None, None)
    if k == "inf":
        return ("inf", neg, None)
    if k == "zero":
        return ("zero", neg, None)
    v = M.R.value(fmt, x)
    r, f = M.cvt2si(fmt, width, rc, x)
    if f & M.IE:
        return ("range", neg, rc)
    lo = v.numerator // v.denominator
    if lo == v:
        return ("exact", neg, None)
    if v - lo == Fraction(1, 2):
        return ("tie", neg, rc)
    t = int(v)                                          # toward zero
    got = r - (1 << width) if r >> (width - 1) else r
    return ("toward" if got == t else "away", neg, rc)


def fmt_width(fn):
    return (M.F64 if "sd" in fn else M.F32), (64 if fn.endswith("q") else 32)


def state_source(s, src):
    if src[0] == "x":
        return s["xmm"][str(src[1])] & ((1 << 64) - 1)
    base = s["gpr"]["3"] + src[1]
    return sum(s["mem"].get(str(base + j), 0) << (8 * j) for j in range(8))


def reached(states, vecs):
    got = {}
    for fn, src in vecs:
        fmt, width = fmt_width(fn)
        acc = got.setdefault(fn, set())
        for s in states:
            acc.add(klass(fmt, width, (s["mxcsr"] >> 13) & 3, state_source(s, src)))
    return got


def table(states, vecs):
    M.ROWS.clear()
    M.build()
    got = reached(states, vecs)
    out = []
    for name, fn, mx, a, b, want, mask, fl in M.ROWS:
        if fn not in ("p_cvtss2si", "p_cvtss2siq", "p_cvtsd2si", "p_cvtsd2siq"):
            continue
        fmt, width = fmt_width(fn)
        c = klass(fmt, width, (mx >> 13) & 3, a)
        out.append((name, c, c in got.get(fn, set())))
    return out


def load():
    return json.load(open(PRESTATES, encoding="utf-8")), vectors(open(VECTORS, encoding="utf-8").read())


def selftest():
    states, vecs = load()
    t = {n: (c, r) for n, c, r in table(states, vecs)}
    arms = [
        ("12 vectors read from the constructors", len(vecs) == 12),
        ("264 rows classed", len(t) == 264),
        # KNOWN ANSWERS, from D289 §2, which this file did not produce: no binary64 source rounds away at nearest,
        # so every cvtsd2si*_frac/nearest-class row that rounds away is unreached; and the memory source is
        # RC-sensitive in all 88 states, so SOME inexact row at round-up is reached.
        ("cvtsd2si_half/nearest (a tie) is unreached", not t["cvtsd2si_half/nearest"][1]),
        ("cvtsd2si_tie/nearest is unreached", not t["cvtsd2si_tie/nearest"][1]),
        ("some cvtsd2si row at round-up is reached",
         any(r for n, (c, r) in t.items() if n.startswith("cvtsd2si_") and n.endswith("/up"))),
        ("a NaN row is reached (NaN sources exist)", t["cvtsd2si_qnan"][1]),
    ]
    # MUTANT: class by VALUE and RC (B4's rule) must pin a strict superset, or the path class is not what carries.
    seen = set()
    for fn, src in vecs:
        for s in states:
            seen.add((fn, (s["mxcsr"] >> 13) & 3, state_source(s, src) & ((1 << (64 if "sd" in fn else 32)) - 1)))
    M.ROWS.clear()
    M.build()
    lit = {n for n, fn, mx, a, b, w, m, f in M.ROWS if fn in ("p_cvtss2si", "p_cvtss2siq", "p_cvtsd2si", "p_cvtsd2siq")
           and (fn, (mx >> 13) & 3, a) not in seen}
    ours = {n for n, (c, r) in t.items() if not r}
    arms.append(("control: value-and-RC equality pins %d, a strict superset of %d" % (len(lit), len(ours)),
                 ours < lit))
    ok = True
    for name, good in arms:
        print(("  ✔ " if good else "  ✖ ") + name)
        ok = ok and good
    print("✅ cvt2si_reach selftest" if ok else "⛔ cvt2si_reach selftest FAILED")
    return 0 if ok else 1


def main(argv):
    P.strict_flags(__file__, argv)
    if "--selftest" in argv:
        return selftest()
    rows = table(*load())
    if "--pinned" in argv:
        print("\n".join(n for n, c, r in rows if not r))
        return 0
    for n, c, r in rows:
        print("%-28s %-8s %-5s %-4s %s" % (n, c[0], c[1], c[2], "CARRIED" if r else "no vector reaches"))
    pinned = sum(1 for _, _, r in rows if not r)
    print("TOTAL %d / PINNED %d / CARRIED %d" % (len(rows), pinned, len(rows) - pinned))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
