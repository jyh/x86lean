#!/usr/bin/env python3
"""hwprobe/sqrt_reach.py — B6b's REACH TABLE: which of D287's sqrt rows no vector reaches (D293).

B0's rule (D267 §2): a row is pinned iff x86isa disagrees with it OR no vector of the same form reaches its class over
the 88 differential pre-states. x86isa differs on the 6 negative-source rows (D287 §4), which are pinned regardless.
⚖️ THE CLASS IS THE PATH, as for cvt*2si (D290): (path, denormal source?, RC where the root is inexact), with the path
    nan (quiet or signalling, separately) · zero · inf · negative · exact · inexact
so a row is REACHED iff some vector of the same format presents a source of that class. A preset flag is a part too:
a row that presets a flag the root does not raise needs a state that does the same.

    python3 hwprobe/sqrt_reach.py              the table and the totals
    python3 hwprobe/sqrt_reach.py --pinned     just the pinned names
    python3 hwprobe/sqrt_reach.py --selftest   the known answers (below)

INPUTS, DECLARED: run/prestates.json (D283 §1) and run/hwprobe_score3.txt (x86isa's reading after D287). The vectors
are read from `Tests/Vectors.lean`'s CONSTRUCTORS (`vsqrt`/`vsqrtm`), never their asm text.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import mk_rows as M                                    # noqa: E402
import portable as P                                   # noqa: E402

PRESTATES = os.path.join(ROOT, "run", "prestates.json")
X86ISA = os.path.join(ROOT, "run", "hwprobe_score3.txt")
VECTORS = os.path.join(ROOT, "Tests", "Vectors.lean")
VEC_RE = re.compile(r"\.vsqrt(m?) \.(q|d) \.x\d+ (?:\.x(\d+)|\{ base := some \.rbx(?:, disp := (-?(?:0x)?[0-9a-f]+))? \})")


def vectors(text):
    return [("p_sqrtsd" if sz == "q" else "p_sqrtss", ("m", int(d, 0) if d else 0) if mem else ("x", int(r)))
            for mem, sz, r, d in VEC_RE.findall(text)]


def klass(fmt, rc, mx, a):
    w = 1 + fmt[0] + fmt[1]
    x = a & ((1 << w) - 1)
    k = M.kind(fmt, x)
    v, f = M.fsqrt(fmt, rc, x)
    if k in ("qnan", "snan"):
        path = k
    elif k == "zero":
        path = "zero"
    elif x >> (w - 1):
        path = "negative"
    elif k == "inf":
        path = "inf"
    else:
        path = "inexact" if f & M.PE else "exact"
    pre = bool((mx & 0x3F) & ~f)
    return (path, k == "den", rc if path == "inexact" else None, pre)


def fmt_of(fn):
    return M.F64 if fn == "p_sqrtsd" else M.F32


def state_source(s, src):
    if src[0] == "x":
        return s["xmm"][str(src[1])] & ((1 << 64) - 1)
    base = s["gpr"]["3"] + src[1]
    return sum(s["mem"].get(str(base + j), 0) << (8 * j) for j in range(8))


def table(states, vecs, diffs):
    got = {}
    for fn, src in vecs:
        for s in states:
            got.setdefault(fn, set()).add(klass(fmt_of(fn), (s["mxcsr"] >> 13) & 3, s["mxcsr"], state_source(s, src)))
    M.ROWS.clear()
    M.build()
    out = []
    for name, fn, mx, a, b, want, mask, fl in M.ROWS:
        if fn not in ("p_sqrtsd", "p_sqrtss"):
            continue
        c = klass(fmt_of(fn), (mx >> 13) & 3, mx, a)
        why = "x86isa differs" if name in diffs else ("" if c in got.get(fn, set()) else "no vector reaches")
        out.append((name, c, why))
    return out


def load():
    diffs = {m.group(1) for m in re.finditer(r"^DIFF (\S+)", open(X86ISA, encoding="utf-8").read(), re.M)}
    return json.load(open(PRESTATES, encoding="utf-8")), vectors(open(VECTORS, encoding="utf-8").read()), diffs


def selftest():
    states, vecs, diffs = load()
    t = {n: (c, w) for n, c, w in table(states, vecs, diffs)}
    arms = [
        ("6 vectors read from the constructors", len(vecs) == 6),
        ("90 rows classed", len(t) == 90),
        ("the 6 negative-source rows are x86isa's, and only they",
         {n for n, (c, w) in t.items() if w == "x86isa differs"} ==
         {"sqrt%s_%s" % (f, k) for f in ("sd", "ss") for k in ("neginf", "negone", "negden")}),
        # KNOWN ANSWERS from D292 §1-2, which this file did not produce: the memory vector reaches an inexact root at
        # every RC (rcSens 88), and no vector presents +inf.
        ("sqrtsd_two/up (an inexact root at up) is reached", not t["sqrtsd_two/up"][1]),
        ("sqrtsd_inf is unreached", t["sqrtsd_inf"][1] == "no vector reaches"),
    ]
    # MUTANT: class by VALUE and RC must pin a strict superset, or the path class is not what carries.
    seen = {(fn, (s["mxcsr"] >> 13) & 3, state_source(s, src) & ((1 << (64 if fn == "p_sqrtsd" else 32)) - 1))
            for fn, src in vecs for s in states}
    M.ROWS.clear()
    M.build()
    lit = {n for n, fn, mx, a, b, w, m, f in M.ROWS if fn in ("p_sqrtsd", "p_sqrtss")
           and (n in diffs or (fn, (mx >> 13) & 3, a) not in seen)}
    ours = {n for n, (c, w) in t.items() if w}
    arms.append(("control: value-and-RC equality pins %d, a strict superset of %d" % (len(lit), len(ours)), ours < lit))
    ok = True
    for name, good in arms:
        print(("  ✔ " if good else "  ✖ ") + name)
        ok = ok and good
    print("✅ sqrt_reach selftest" if ok else "⛔ sqrt_reach selftest FAILED")
    return 0 if ok else 1


def main(argv):
    P.strict_flags(__file__, argv)
    if "--selftest" in argv:
        return selftest()
    rows = table(*load())
    if "--pinned" in argv:
        print("\n".join(n for n, c, w in rows if w))
        return 0
    for n, c, w in rows:
        print("%-28s %-9s den=%-5s rc=%-4s pre=%-5s %s" % (n, c[0], c[1], c[2], c[3], w or "CARRIED"))
    p = sum(1 for _, _, w in rows if w)
    print("TOTAL %d / PINNED %d (x86isa %d) / CARRIED %d"
          % (len(rows), p, sum(1 for _, _, w in rows if w == "x86isa differs"), len(rows) - p))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
