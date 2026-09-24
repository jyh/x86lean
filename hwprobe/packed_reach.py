#!/usr/bin/env python3
"""hwprobe/packed_reach.py — B5's REACH TABLE: which of D281's and D284's packed rows no vector reaches (D285).

B0's rule (D267 §2) pins a row iff x86isa disagrees with it OR no vector of the same form reaches its class over the
88 differential pre-states. For the scalar forms a row is reached when some vector's source EQUALS the row's at that
RC (`reach_table.py`). ⛔ THAT DEFINITION DOES NOT TRANSFER TO 128 BITS: two or four lanes of chosen constants are
equalled by no random state, so the rule read literally pins every packed row, including the ones the lane arms
(D283 §2) show the differential already kills.

⚖️ THE PACKED CLASS (D285 §1). A packed row is REACHED iff every one of its parts is reached by some (vector, state)
of the SAME mnemonic at the SAME RC:
  LANE      for every lane: (the flags that lane raises alone, and the RC where the lane ROUNDS). A lane that
            raises nothing is a part too. The lane's POSITION is not a part: where a lane's result and flags land is
            what D283 §2's arms measure the differential already kills (lane 0's flags alone: 377; lane 0 computed and
            the lanes above kept: 1,412). `--positional` adds the position back; it pins 59 where this pins 40 (D285).
  DE-X      if the row raises DE in one lane while another lane holds a NaN or a zero divisor (the condition that
            suppresses DE within a lane): some state with that cross-lane shape. Its CONTROL rows (a NaN or a zero
            divisor beside a denormal in the SAME lane, and no DE anywhere) are classed by LANE alone.
  PRESET    if the row presets a flag it does not raise: some state that presets a flag its lanes do not raise.
The per-lane VALUE (sign, tie, path) is deliberately not a part: it is the scalar rule's class, and the scalar rule
is the same function (`varithCall`, D282) pinned and carried by B1 and B2. ⚠️ That is an argument about shared code,
and it is stated as one; the lane arms are what measure the packed half.

    python3 hwprobe/packed_reach.py                 the table: one line per packed row, and the totals
    python3 hwprobe/packed_reach.py --pinned        just the pinned names, one per line
    python3 hwprobe/packed_reach.py --positional    the same, with a lane's position a part of its class
    python3 hwprobe/packed_reach.py --selftest      the known-answer controls (below)

INPUTS, both DECLARED (neither is re-run here):
  run/prestates.json      the 88 pre-states, read out of run/cases.lsp (D283 §1)
  run/hwprobe_score2.txt  rows_on_x86isa.py's reading after D284: a `DIFF <row>` line per x86isa disagreement
The vectors are read from `Tests/Vectors.lean`'s CONSTRUCTORS (`vparith`/`vparithm`), never their asm text.

⚠️ WHAT THIS DOES NOT MEASURE: whether the differential's comparison of a reached part is sound (reach is not
coverage); any row x86isa has not been asked since its saved reading; the memory form's alignment rule (no row asks it).
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
X86ISA = os.path.join(ROOT, "run", "hwprobe_score4.txt")   # after D294: B5 + B7
VECTORS = os.path.join(ROOT, "Tests", "Vectors.lean")
FLAGBITS = "IDZOUP"
POSITIONAL = False

VEC_RE = re.compile(r"\.vparith(m?) \.(mul|add|sub|div) (true|false) \.x0 "
                    r"(?:\.x(\d+)|\{ base := some \.rbx(?:, disp := (-?(?:0x)?[0-9a-f]+))? \})")
# B7 (D296): CVTPD2PS, whose lanes are the binary64 source's two, each narrowed by CVTSD2SS's own rule.
CVT_RE = re.compile(r"\.vcvtpd2ps(m?) \.x\d+ (?:\.x(\d+)|\{ base := some \.rbx(?:, disp := (-?(?:0x)?[0-9a-f]+))? \})")
# The packed forms this table classes. SQRTPS has hardware rows and no roster row (D295 §2), so it is not classed.
CLASSED = {"p_mulps", "p_mulpd", "p_addps", "p_addpd", "p_subps", "p_subpd", "p_divps", "p_divpd", "p_cvtpd2ps"}


def fl(f):
    return "".join(c for i, c in enumerate(FLAGBITS) if f >> i & 1) or "-"


def vectors(text):
    out = []
    for mem, op, pd, reg, disp in VEC_RE.findall(text):
        src = ("m", int(disp, 0) if disp else 0) if mem else ("x", int(reg))
        out.append((op, M.F64 if pd == "true" else M.F32, src))
    for mem, reg, disp in CVT_RE.findall(text):
        out.append(("cvt", M.F64, ("m", int(disp, 0) if disp else 0) if mem else ("x", int(reg))))
    return out


def lanes(op, fmt, rc, A, B):
    """Per lane: (flags alone, suppress condition present, raises DE)."""
    w = 1 + fmt[0] + fmt[1]
    m = (1 << w) - 1
    res = []
    for i in range(128 // w):
        a, b = (A >> (w * i)) & m, (B >> (w * i)) & m
        if op == "cvt":
            _, g = M.cvtsd2ss(rc, b)
            res.append((g, M.kind(fmt, b) in ("qnan", "snan")))
            continue
        _, g = M.mul(fmt, M.MODES[rc], a, b) if op == "mul" else M.arith(op, fmt, rc, a, b)
        ka, kb = M.kind(fmt, a), M.kind(fmt, b)
        sup = "qnan" in (ka, kb) or "snan" in (ka, kb) or (op == "div" and kb == "zero")
        res.append((g, sup))
    return res


def parts(op, fmt, mx, A, B):
    rc, pre = (mx >> 13) & 3, mx & 0x3F
    ls = lanes(op, fmt, rc, A, B)
    # RC is part of a lane's class only where the lane ROUNDS (raises PE): an exact, NaN, invalid or zero-divide
    # result is the same at every mode, so asking for it at each RC would pin a row for a dimension it cannot show.
    ps = {("lane", rc if g & M.PE else None, k if POSITIONAL else None, g) for k, (g, _) in enumerate(ls)}
    if any(g & M.DE for g, _ in ls) and any(s for _, s in ls):
        dl = {k for k, (g, _) in enumerate(ls) if g & M.DE}
        sl = {k for k, (_, s) in enumerate(ls) if s}
        if sl - dl or dl - sl:                         # the DE and the suppress condition in DIFFERENT lanes
            ps.add(("de-x", None))
    new = 0
    for g, _ in ls:
        new |= g
    if pre & ~new:
        ps.add(("preset", None))
    return ps


def mnemonic(op, fmt):
    return op + ("pd" if fmt == M.F64 else "ps")


def state_source(s, src):
    if src[0] == "x":
        return s["xmm"][str(src[1])]
    base = s["gpr"]["3"] + src[1]
    return sum(s["mem"].get(str(base + j), 0) << (8 * j) for j in range(16))


def reached(states, vecs):
    """{mnemonic: set of parts} over every (vector, state)."""
    got = {}
    for op, fmt, src in vecs:
        acc = got.setdefault(mnemonic(op, fmt), set())
        for s in states:
            acc |= parts(op, fmt, s["mxcsr"], s["xmm"]["0"], state_source(s, src))
    return got


def x86isa_diffs(path):
    return {m.group(1) for m in re.finditer(r"^DIFF (\S+)", open(path, encoding="utf-8").read(), re.M)}


def table(states, vecs, diffs):
    M.PROWS.clear()
    M.build_packed()
    got = reached(states, vecs)
    rows = []
    for name, fn, mx, A, B, want, f in M.PROWS:
        if fn not in CLASSED:
            continue
        op, suf = (("cvt", "pd") if fn == "p_cvtpd2ps" else (fn[2:5], fn[5:]))
        fmt = M.F64 if suf == "pd" else M.F32
        miss = sorted(parts(op, fmt, mx, A, B) - got.get(op + suf, set()), key=repr)
        why = "x86isa differs" if name in diffs else ("no vector reaches" if miss else "")
        rows.append((name, why, miss))
    return rows


def literal_pins(states, vecs, diffs):
    seen = set()
    for op, fmt, src in vecs:
        for s in states:
            seen.add((mnemonic(op, fmt), (s["mxcsr"] >> 13) & 3, s["xmm"]["0"], state_source(s, src)))
    key = lambda fn: "cvtpd" if fn == "p_cvtpd2ps" else fn[2:]
    return {name for name, fn, mx, A, B, want, f in M.PROWS
            if fn in CLASSED and (name in diffs or (key(fn), (mx >> 13) & 3, A, B) not in seen)}


def show_part(p):
    at = "" if p[1] is None else "@rc%d" % p[1]
    if p[0] == "lane":
        return "%s=%s%s" % ("lane" if p[2] is None else "lane%d" % p[2], fl(p[3]), at)
    return p[0] + at


def load():
    return (json.load(open(PRESTATES, encoding="utf-8")), vectors(open(VECTORS, encoding="utf-8").read()),
            x86isa_diffs(X86ISA))


def selftest():
    states, vecs, diffs = load()
    rows = {n: (w, m) for n, w, m in table(states, vecs, diffs)}
    divps = [v for v in vecs if mnemonic(v[0], v[1]) == "divps"]
    arms = [
        # KNOWN ANSWERS, from D283 §1's census, which this file did not produce: divps's only vector (m-16) reaches
        # no IE, so every loud@k row of divps is unreached; mulps's x7 reaches IE, so the mulps loud@k rows are not.
        ("22 vectors read from the constructors (19 of B5, 3 of B7)", len(vecs) == 22),
        ("divps has exactly one vector, m-16", divps == [("div", M.F32, ("m", -16))]),
        ("every divps loud@k is unreached", all(rows["divps_loud@%d" % k][1] for k in range(4))),
        ("every mulps loud@k is carried", all(not rows["mulps_loud@%d" % k][1] for k in range(4))),
        ("x86isa's rows are the 8 indefinites and cvtpd2ps_sticky1fbf (D294), and only they",
         {n for n, (w, _) in rows.items() if w == "x86isa differs"} ==
         {n for n in rows if "_indef@" in n} | {"cvtpd2ps_sticky1fbf"}),
    ]
    # MUTANT: the scalar rule transferred literally (some state's two sources EQUAL the row's at its RC) must pin
    # every row this rule carries, or the lane class is not what is doing the carrying.
    lit = literal_pins(states, vecs, diffs)
    ours = {n for n, (w, _) in rows.items() if w}
    arms.append(("control: the literal equality rule pins %d, a strict superset of this rule's %d"
                 % (len(lit), len(ours)), ours < lit))
    # MUTANT 2: with position a part, the rule must pin a STRICT SUPERSET, or the position dimension is dead code.
    global POSITIONAL
    POSITIONAL = True
    posp = {n for n, w, _ in table(states, vecs, diffs) if w}
    POSITIONAL = False
    arms.append(("control: the positional rule pins %d, a strict superset of %d" % (len(posp), len(ours)),
                 ours < posp))
    ok = True
    for name, good in arms:
        print(("  ✔ " if good else "  ✖ ") + name)
        ok = ok and good
    print("✅ packed_reach selftest" if ok else "⛔ packed_reach selftest FAILED")
    return 0 if ok else 1


def main(argv):
    P.strict_flags(__file__, argv)
    if "--selftest" in argv:
        return selftest()
    global POSITIONAL
    POSITIONAL = "--positional" in argv
    rows = table(*load())
    if "--pinned" in argv:
        print("\n".join(n for n, w, _ in rows if w))
        return 0
    for n, w, miss in rows:
        print("%-24s %-18s %s" % (n, w or "CARRIED", " ".join(show_part(p) for p in miss)))
    pinned = sum(1 for _, w, _ in rows if w)
    print("TOTAL %d / PINNED %d (x86isa %d) / CARRIED %d"
          % (len(rows), pinned, sum(1 for _, w, _ in rows if w == "x86isa differs"), len(rows) - pinned))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
