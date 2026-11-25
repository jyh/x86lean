#!/usr/bin/env python3
"""hwprobe/mk_mmxsil_rows.py — D407: the MMX forms x86isa cannot execute (PMAXSW, PSADBW, PAVGB, PSHUFW at %mm), with
expectations DERIVED HERE from the SDM, one 64-bit rule per mnemonic.

The referee is the processor (`mmxsil_probe.c` on the CI runners). x86isa's inst-listing names no handler for these NP forms,
so it cannot be asked, and the model is not asked either: every expected value below comes from a rule stated in this file
(SDM Vol. 2B, each instruction's Operation section, at the 64-bit MMX operand size), never from x86lean. Lane i of a 64-bit
value is bits (i+1)w-1 : iw. DEST is %mm0, SRC is %mm1 or the m64 at [RBX].

  PMAXSW   word i (4 words) := DEST.w[i] if DEST.w[i] > SRC.w[i] (SIGNED) else SRC.w[i].
  PSADBW   DEST[15:0] := sum over i = 0..7 of |DEST.b[i] - SRC.b[i]| (unsigned bytes); DEST[63:16] := 0.
  PAVGB    byte i (8 bytes) := (DEST.b[i] + SRC.b[i] + 1) >> 1, both unsigned, the sum taken in 9 bits.
  PSHUFW   word i := SRC.w[(imm8 >> 2i) & 3] for i = 0..3; DEST's old value is not read.

THE ROW POPULATION, per mnemonic (the same pairs at both shapes, register `rr` and memory `rm`): 8 EDGE rows (lane i of
DEST and SRC from an edge set, SRC rotated by the row number), 4 UNIFORM rows at the extremes, and 6 RANDOM rows from
`random.Random(407000 + k)`. PSHUFW takes its SRC from the same population and one imm8 per row: the four identity-free
patterns 0x1B (reverse), 0x00 (broadcast word 0), 0xFF (broadcast word 3), 0xE4 (identity), then random bytes.
CONTROL: PADDW at %mm, a differential form (D404 d1) whose rule here must agree with the processor, or the probe refuses.

Usage: mk_mmxsil_rows.py [--plant | --summary | --reach]   writes C rows on stdout.
  --plant    flips bit 63 of ONE expectation: exactly that row must disagree (the probe exits 1)
  --summary  prints the per-form row counts, not C
  --reach    prints, per mnemonic, how many rows each named WRONG rule disagrees on (0 would be a vacuous row set)
"""
import random
import sys

M64 = (1 << 64) - 1
MNEMONICS = ["pmaxsw", "psadbw", "pavgb", "pshufw"]
WIDTH = {"pmaxsw": 16, "psadbw": 8, "pavgb": 8, "pshufw": 16, "paddw": 16}
EDGES = {
    16: [0x0000, 0x0001, 0xFFFF, 0x7FFF, 0x8000, 0x8001, 0x4000, 0x00FF],
    8: [0x00, 0x01, 0xFF, 0x7F, 0x80, 0x81, 0x40, 0xFE],
}
UNIFORM = {
    16: [(0x8000, 0x8000), (0x7FFF, 0x7FFF), (0x8000, 0x7FFF), (0xFFFF, 0x0001)],
    8: [(0xFF, 0x7F), (0xFF, 0x80), (0x00, 0xFF), (0x7F, 0xFF)],
}
SHUF_FIXED = [0x1B, 0x00, 0xFF, 0xE4]


def lanes(v, w):
    return [(v >> (i * w)) & ((1 << w) - 1) for i in range(64 // w)]


def join(ls, w):
    r = 0
    for i, x in enumerate(ls):
        r |= (x & ((1 << w) - 1)) << (i * w)
    return r


def sx(x, w):
    return x - (1 << w) if x >> (w - 1) & 1 else x


def rule(mn, a, b, imm=0):
    """The SDM rule at 64 bits: DEST a, SRC b (64-bit ints), imm8 for pshufw -> the new DEST."""
    if mn == "pmaxsw":
        return join([p if sx(p, 16) > sx(q, 16) else q for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    if mn == "psadbw":
        return sum(abs(p - q) for p, q in zip(lanes(a, 8), lanes(b, 8)))
    if mn == "pavgb":
        return join([(p + q + 1) >> 1 for p, q in zip(lanes(a, 8), lanes(b, 8))], 8)
    if mn == "pshufw":
        s = lanes(b, 16)
        return join([s[(imm >> (2 * i)) & 3] for i in range(4)], 16)
    if mn == "paddw":
        return join([p + q for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    raise KeyError(mn)


# The WRONG rules D407 §3 prediction 2 names; --reach shows each disagrees on at least one row of its mnemonic.
WRONG = {
    "pmaxsw": ("UNSIGNED maximum", lambda a, b, i: join([max(p, q) for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)),
    "pavgb": ("rounding DOWN", lambda a, b, i: join([(p + q) >> 1 for p, q in zip(lanes(a, 8), lanes(b, 8))], 8)),
    "psadbw": ("bits 63:16 kept from DEST", lambda a, b, i: (a & ~0xFFFF & M64) | rule("psadbw", a, b)),
    "pshufw": ("field order reversed", lambda a, b, i: join([lanes(b, 16)[(i >> (2 * (3 - j))) & 3] for j in range(4)], 16)),
}
WRONG_PSHUFW_DWORD = ("pshufd's dword lanes, low 64 kept",
                      lambda a, b, i: join([lanes(b, 32)[(i >> (2 * j)) & 3] if ((i >> (2 * j)) & 3) < 2 else 0
                                            for j in range(2)], 32))


def pairs(mn, k):
    w = WIDTH[mn]
    out = []
    e = EDGES[w]
    n = 64 // w
    for r in range(8):
        a = join([e[(i) % 8] for i in range(n)], w)
        b = join([e[(i + r) % 8] for i in range(n)], w)
        out.append(("edge%d" % r, a, b))
    for j, (x, y) in enumerate(UNIFORM[w]):
        out.append(("uni%d" % j, join([x] * n, w), join([y] * n, w)))
    rnd = random.Random(407000 + k)
    for j in range(6):
        out.append(("rnd%d" % j, rnd.getrandbits(64), rnd.getrandbits(64)))
    return out


def rows():
    """(form, mnemonic, shape, dest, src, imm, expected) for every row, the control's last."""
    out = []
    for k, mn in enumerate(MNEMONICS + ["paddw"]):
        rnd_imm = random.Random(407900 + k)
        for idx, (tag, a, b) in enumerate(pairs(mn, k)):
            imm = (SHUF_FIXED[idx] if idx < len(SHUF_FIXED) else rnd_imm.getrandbits(8)) if mn == "pshufw" else 0
            for shape in ("rr", "rm"):
                out.append((mn + "_" + shape + "_" + tag, mn, shape, a, b, imm, rule(mn, a, b, imm)))
    return out


def main(argv):
    rs = rows()
    if "--summary" in argv:
        from collections import Counter
        c = Counter((r[1], r[2]) for r in rs)
        for (mn, sh), n in sorted(c.items()):
            print(f"{mn:8s} {sh}  {n}")
        print(f"total {len(rs)} rows ({sum(1 for r in rs if r[1] != 'paddw')} probed + "
              f"{sum(1 for r in rs if r[1] == 'paddw')} control)")
        return 0
    if "--reach" in argv:
        bad = 0
        checks = [(mn, WRONG[mn]) for mn in MNEMONICS] + [("pshufw", WRONG_PSHUFW_DWORD)]
        for mn, (name, f) in checks:
            hit = sum(1 for r in rs if r[1] == mn and f(r[3], r[4], r[5]) & M64 != r[6])
            tot = sum(1 for r in rs if r[1] == mn)
            print(f"  {'✔' if hit else '⛔'} {mn:7s} {name:36s} disagrees on {hit} of {tot} rows")
            bad += hit == 0
        print("reach: " + ("PASS" if not bad else f"FAIL ({bad} vacuous)"))
        return 1 if bad else 0
    plant = "--plant" in argv
    print("/* GENERATED by hwprobe/mk_mmxsil_rows.py%s. Do not edit by hand. */" % (" --plant" if plant else ""))
    print("typedef struct { const char *form; int op; int mem; unsigned long long dest, src; int imm; "
          "unsigned long long want; } row_t;")
    print("enum { OP_PMAXSW, OP_PSADBW, OP_PAVGB, OP_PSHUFW, OP_PADDW };")
    print("static const row_t ROWS[] = {")
    planted = False
    for form, mn, shape, a, b, imm, want in rs:
        if plant and not planted and mn == "pavgb":
            want ^= 1 << 63
            planted = True
        print(f'  {{"{form}", OP_{mn.upper()}, {1 if shape == "rm" else 0}, 0x{a:016x}ULL, 0x{b:016x}ULL, '
              f'0x{imm:02x}, 0x{want:016x}ULL}},')
    print("};")
    print("#define N_ROWS (sizeof ROWS / sizeof ROWS[0])")
    # pshufw's imm8 is an assembly-time immediate, so the selectors the rows use are dispatched by a generated switch.
    imms = sorted({r[5] for r in rs if r[1] == "pshufw"})
    print("static int run_pshufw(int mem, unsigned long long src, int imm, unsigned long long *out) {")
    print("  unsigned long long r = 0;")
    print("  switch (imm) {")
    for i in imms:
        print(f'  case 0x{i:02x}: if (mem) __asm__ volatile("pshufw $0x{i:02x}, %1, %%mm0\\n\\tmovq %%mm0, %0\\n\\temms" '
              f': "=m"(r) : "m"(src) : "mm0"); else __asm__ volatile("movq %1, %%mm1\\n\\tpshufw $0x{i:02x}, %%mm1, %%mm0\\n\\t'
              f'movq %%mm0, %0\\n\\temms" : "=m"(r) : "m"(src) : "mm0", "mm1"); break;')
    print("  default: return 0;")
    print("  }")
    print("  *out = r; return 1;")
    print("}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
