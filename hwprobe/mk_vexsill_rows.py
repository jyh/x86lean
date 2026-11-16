#!/usr/bin/env python3
"""hwprobe/mk_vexsill_rows.py — D393 (wave F): the VEX twins of the five legacy unpacks the model's VEX path does not
take, the rows the x86-64 referee runs, with expectations DERIVED HERE. D384's `mk_vexsilk_rows.py` with its kind list,
its 128-bit function, its seeding and its wrong rules changed; the frame, the plants and the output format are that
file's, so the same probe (`vexsile_probe.c`) runs it.

The forms (x86isa refuses all ten register encodings, D393 P1), each at VEX.128 and VEX.256, register and memory source:
  vpunpckldq vpunpcklqdq vpunpckhbw vpunpckhdq vpunpckhqdq
Frame (D361's): YMM1 = SRC1 (VEX.vvvv), YMM2 = SRC2 (ModRM.rm) or RBX = &mem[off] (the memory source), YMM3 = DEST;
MXCSR, RAX, the six arithmetic flags and the 64-byte buffer loaded from the row and read back.

THE 128-BIT FUNCTION IS NOT RESTATED HERE. It is `mk_vexsil_rows.r_unpck(a, b, w, high)` — D345's statement of SDM
Vol. 2B PUNPCKLBW/PUNPCKLWD/PUNPCKLDQ/PUNPCKLQDQ and PUNPCKH*, the rule its three VEX unpacks hold on silicon — imported,
so one rule has one home:
  PUNPCKL<w>   DEST element 2i := SRC1 element i, 2i+1 := SRC2 element i, i < 64/w   (the LOW 64 bits of each source)
  PUNPCKH<w>   the same from the HIGH 64 bits of each source
  VEX.128      DEST[127:0] := F(SRC1[127:0], SRC2[127:0]);  DEST[255:128] := 0
  VEX.256      DEST[127:0] := F(SRC1[127:0], SRC2[127:0]);  DEST[255:128] := F(SRC1[255:128], SRC2[255:128])  (per lane)
  MEMORY       SRC2 := the 16 (VEX.128) or 32 (VEX.256) bytes at mem[off], NO alignment check (VEX Exception Type 4)
  NO-OTHERS    flags, MXCSR, RAX, YMM1, YMM2 and the buffer unchanged.
THE SECOND DERIVATION (`textbook`) re-derives the whole result from BYTE LISTS — every element moved as its bytes, the
lanes cut as 16-byte lists, the upper half written as 16 zero bytes — and never calls `r_unpck`; every row must agree
with the rule or the build refuses.

THE BYTES are derived from the SDM's VEX rule, not copied from an assembler: each is 66 0F xx, so the two-byte VEX C5,
then R̄ vvvv̄ L pp = F1 (L = 0) or F5 (L = 1) with vvvv = 1 (YMM1), then the legacy opcode byte, then ModRM DA (reg 3,
rm 2) or 1B (reg 3, [RBX]). The selftest compares them with clang's; `vexsile_probe.c` refuses a run whose assembled
bytes differ from the declared ones.

THE SEEDING (prediction 1). Every source is a PERMUTATION of byte values, so every element of every width, in every
lane, of both sources, is distinct: a row tells the low half from the high, SRC1 from SRC2, and one lane from the other.
Register forms: 8 rows at each length. Memory forms: 6 sources, each at offset 0 and at an odd offset. YMM3, YMM2 (at a
memory form) and the buffer outside the operand are random and nonzero; at VEX.128 YMM1's and YMM3's upper halves are
nonzero, so the zeroing is read.

Usage: mk_vexsill_rows.py [--plant | --plant-op | --plant-hi | --summary | --reach | --asm | --selftest]
  --plant      flips bit 128 (the HIGH lane) of one VEX.256 row's expectation: exactly that row must disagree (exit 1)
  --plant-op   declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --plant-hi   one VEX.128 row's expectation keeps YMM3's upper half: exactly that row must disagree
  --summary    per-function row counts, not C
  --reach      per named wrong rule, how many rows it disagrees on (every count must be non-zero)
  --asm        prints `vexsill_ops.S` (the committed file must equal it; the selftest checks)
  --selftest   the bytes against clang's, every row's two derivations, the seeding, the wrong rules' reach, the plants,
               and the committed .S
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "scripts"))
sys.path.insert(0, HERE)
import portable as P  # noqa: E402
import mk_vexsil_rows as V  # noqa: E402  (D345's r_unpck: the 128-bit unpack rule)

ARITH = 0x8d5
M64 = (1 << 64) - 1
M128 = (1 << 128) - 1
M256 = (1 << 256) - 1
MX = 0x1f80

# (VEX mnemonic, element width, high half?, the 66 0F opcode byte) — the five D393 twins (SDM Vol. 2B PUNPCKHBW..).
KINDS = [("vpunpckldq", 32, False, "62"), ("vpunpcklqdq", 64, False, "6c"), ("vpunpckhbw", 8, True, "68"),
         ("vpunpckhdq", 32, True, "6a"), ("vpunpckhqdq", 64, True, "6d")]
KIND = {v: (w, h, op) for v, w, h, op in KINDS}
UNALIGNED = [1, 3, 5, 7, 9, 13]
N_REG = 8
N_MEM = 6
PLANT_ROW = "vpunpckhdq256_r_p0"    # --plant: bit 128 of its expectation
PLANT_HI = "vpunpckldq128_r_p0"     # --plant-hi: its expectation keeps YMM3's upper half


def enc(v, L, shape):
    """The SDM's VEX.128/256.66.0F encoding of the legacy opcode, with this probe's registers."""
    return "c5" + ("f1" if L == 128 else "f5") + KIND[v][2] + ("da" if shape == "r" else "1b")


OPS = []   # (function, vex mnemonic, L, shape, declared bytes)
for _v, *_ in KINDS:
    for _L in (128, 256):
        for _s in ("r", "m"):
            OPS.append(("x_%s%d_%s" % (_v, _L, _s), _v, _L, _s, enc(_v, _L, _s)))


def F(v, a, b, w=None, high=None):
    kw, kh, _ = KIND[v]
    return V.r_unpck(a & M128, b & M128, kw if w is None else w, kh if high is None else high) & M128


def src2(L, shape, y2, mem, off):
    return y2 & (M128 if L == 128 else M256) if shape == "r" else (mem >> (8 * off)) & (M128 if L == 128 else M256)


def rule(v, L, shape, y1, y2, y3, mem, off):
    """YMM3 after the instruction."""
    b = src2(L, shape, y2, mem, off)
    lo = F(v, y1, b)
    return lo if L == 128 else lo | (F(v, y1 >> 128, b >> 128) << 128)


def le(x, n):
    return [(x >> (8 * i)) & 0xff for i in range(n)]


def un(bs):
    return sum(x << (8 * i) for i, x in enumerate(bs))


def textbook(v, L, shape, y1, y2, y3, mem, off):
    """The same from byte lists, without `r_unpck`: each lane's 16 bytes, its low or high 8, cut into w/8-byte elements,
    interleaved SRC1, SRC2, SRC1, SRC2 …; the upper half written as 16 zero bytes at VEX.128."""
    w, high, _ = KIND[v]
    k = w // 8
    a = le(y1, 32)
    b = le(y2, 32) if shape == "r" else le(mem, 64)[off:off + 32]

    def lane(al, bl):
        half = slice(8, 16) if high else slice(0, 8)
        ah, bh = al[half], bl[half]
        out = []
        for i in range(0, 8, k):
            out += ah[i:i + k] + bh[i:i + k]
        return out
    out = lane(a[:16], b[:16])
    out += lane(a[16:32], b[16:32]) if L == 256 else [0] * 16
    return un(out)


# --reach: the wrong rules D393's prediction 2 names. Each must disagree with the rule on at least one row.
def w_other_half(v, L, shape, y1, y2, y3, mem, off):                 # (a) an `l` form reads the high halves, `h` the low
    b = src2(L, shape, y2, mem, off)
    hi = not KIND[v][1]
    lo = F(v, y1, b, high=hi)
    return lo if L == 128 else lo | (F(v, y1 >> 128, b >> 128, high=hi) << 128)


def w_swapped(v, L, shape, y1, y2, y3, mem, off):                    # (b) SRC1 and SRC2 swapped
    b = src2(L, shape, y2, mem, off)
    lo = F(v, b, y1)
    return lo if L == 128 else lo | (F(v, b >> 128, y1 >> 128) << 128)


def w_cross_lane(v, L, shape, y1, y2, y3, mem, off):                 # (c) VEX.256 unpacks ACROSS the 256 bits
    if L == 128:
        return rule(v, L, shape, y1, y2, y3, mem, off)
    w, high, _ = KIND[v]
    b = src2(L, shape, y2, mem, off)
    n = 128 // w                                                     # elements in the chosen 128-bit HALF of 256
    base = n if high else 0
    out = 0
    for i in range(n):
        ea = (y1 >> (w * (base + i))) & ((1 << w) - 1)
        eb = (b >> (w * (base + i))) & ((1 << w) - 1)
        out |= ea << (w * 2 * i) | eb << (w * (2 * i + 1))
    return out


WIDER = {"vpunpckldq": 16, "vpunpcklqdq": 32, "vpunpckhbw": 16, "vpunpckhdq": 16, "vpunpckhqdq": 32}


def w_width(v, L, shape, y1, y2, y3, mem, off):                      # (d) the wrong element width
    b = src2(L, shape, y2, mem, off)
    w = WIDER[v]
    lo = F(v, y1, b, w=w)
    return lo if L == 128 else lo | (F(v, y1 >> 128, b >> 128, w=w) << 128)


def w_keep_upper(v, L, shape, y1, y2, y3, mem, off):                 # (e) VEX.128 keeps YMM3[255:128]
    r = rule(v, L, shape, y1, y2, y3, mem, off)
    return r | (y3 >> 128 << 128) if L == 128 else r


def w_aligned_read(v, L, shape, y1, y2, y3, mem, off):               # (f) the memory operand read from mem[off & ~15]
    return rule(v, L, shape, y1, y2, y3, mem, off & ~15)


WRONG = [("(a) l/h: the other half of each lane", w_other_half), ("(b) SRC1 and SRC2 swapped", w_swapped),
         ("(c) VEX.256 unpacks across lanes", w_cross_lane), ("(d) the wrong element width", w_width),
         ("(e) VEX.128 keeps YMM3[255:128]", w_keep_upper), ("(f) the operand read from the aligned address", w_aligned_read)]

ROWS = []   # (name, fn, v, L, shape, y1, y2, y3, f, rax, mem, off, w3)


def place(mem, off, value, n):
    mask = ((1 << (8 * n)) - 1) << (8 * off)
    return (mem & ~mask & ((1 << 512) - 1)) | ((value & ((1 << (8 * n)) - 1)) << (8 * off))


def perm_pair(rng):
    """SRC1 and SRC2 as one shuffled run of 64 distinct byte values: every byte of both 32-byte sources is distinct,
    so every element of every width is too."""
    bs = list(range(256))
    rng.shuffle(bs)
    return un(bs[:32]), un(bs[32:64])


def build():
    ROWS.clear()
    for k, (fn, v, L, shape, _bs) in enumerate(OPS):
        rng = random.Random(393100 + k)
        if shape == "r":
            cases = [("p%d" % i, 0) for i in range(N_REG)]
        else:
            cases = [("s%d_%s" % (j, x), 0 if x == "a" else UNALIGNED[j]) for j in range(N_MEM) for x in "au"]
        for i, (nm, off) in enumerate(cases):
            a, b = perm_pair(rng)
            y3 = rng.getrandbits(256) | (1 << 128) | 1
            rax = rng.getrandbits(64) | (1 << 63)
            y1 = (a & M128) | ((rng.getrandbits(128) | 1) << 128) if L == 128 else a & M256
            if shape == "r":
                y2 = (b & M128) | ((rng.getrandbits(128) | 1) << 128) if L == 128 else b & M256
                mem = rng.getrandbits(512)
            else:
                y2 = rng.getrandbits(256) | 1 | (1 << 128)
                mem = place(rng.getrandbits(512), off, b, L // 8)
            f = ARITH if i % 2 else 0
            name = "%s_%s" % (fn[2:], nm)
            got = rule(v, L, shape, y1, y2, y3, mem, off)
            tb = textbook(v, L, shape, y1, y2, y3, mem, off)
            if got != tb:
                raise SystemExit("mk_vexsill_rows: ⛔ row %s: the rule gives %064x, the textbook %064x" % (name, got, tb))
            ROWS.append((name, fn, v, L, shape, y1, y2, y3, f, rax, mem, off, got))


def disagreements(rl):
    return [r[0] for r in ROWS if rl(r[2], r[3], r[4], r[5], r[6], r[7], r[10], r[11]) != r[12]]


def q(x, n):
    return ", ".join("0x%016xULL" % ((x >> (64 * i)) & M64) for i in range(n))


ASM_HEAD = r"""/* hwprobe/vexsill_ops.S — D393: the VEX twins of wave F's five unpacks (vpunpckldq vpunpcklqdq vpunpckhbw vpunpckhdq
   vpunpckhqdq), one function per form and length, in D361's frame (`vexsile_ops.S`), so `vexsile_probe.c` runs them
   against `vexsill_rows.h`: YMM1 = SRC1 (VEX.vvvv), YMM2 = SRC2 (a register form), RBX = &mem[off] (a memory form),
   YMM3 = DEST. GENERATED by `mk_vexsill_rows.py --asm`; its selftest refuses a committed copy that differs. */

#ifdef __APPLE__
#define SYM(x) _##x
#else
#define SYM(x) x
#endif

        .text
"""


def asm():
    src = open(os.path.join(HERE, "vexsilk_ops.S"), encoding="utf-8").read()
    a, z = src.index("#define PRE"), src.index("#define AT(name)")
    frame = src[a:src.index("\n", z) + 1]
    out = [ASM_HEAD, "\n", frame]
    for fn, v, L, shape, bs in OPS:
        r = "%xmm" if L == 128 else "%ymm"
        srcop = r + "2" if shape == "r" else "(%rbx)"
        out.append("\nFN(%s)\n        PRE\nAT(%s_at)\n        %s %s, %s1, %s3     /* %s */\n        POST\n" % (
            fn, fn, v, srcop, r, r, " ".join(bs[i:i + 2] for i in range(0, len(bs), 2))))
    return "".join(out)


def selftest():
    ok = True

    def say(c, what):
        nonlocal ok
        print(("  ✔ " if c else "  ✖ ") + what)
        ok = ok and c
    clang = {   # clang's bytes for the register forms (objdump of P1's encodings, 2026-11-07) and the memory forms
        ("vpunpckldq", 128, "r"): "c5f162da", ("vpunpcklqdq", 128, "r"): "c5f16cda", ("vpunpckhbw", 128, "r"): "c5f168da",
        ("vpunpckhdq", 128, "r"): "c5f16ada", ("vpunpckhqdq", 128, "r"): "c5f16dda",
        ("vpunpckldq", 256, "r"): "c5f562da", ("vpunpcklqdq", 256, "r"): "c5f56cda", ("vpunpckhbw", 256, "r"): "c5f568da",
        ("vpunpckhdq", 256, "r"): "c5f56ada", ("vpunpckhqdq", 256, "r"): "c5f56dda",
        ("vpunpckldq", 128, "m"): "c5f1621b", ("vpunpckhqdq", 256, "m"): "c5f56d1b"}
    for (v, L, s), want in clang.items():
        say(enc(v, L, s) == want, "%s %d %s: the SDM derivation gives clang's %s" % (v, L, s, want))
    build()
    say(len(ROWS) == len(KINDS) * 2 * (N_REG + 2 * N_MEM), "%d rows = 5 × 2 × (8 + 12)" % len(ROWS))
    say(all(r[11] == 0 or r[11] % 2 for r in ROWS) and any(r[11] for r in ROWS),
        "every memory row is at offset 0 or an odd offset, and some are odd")

    def distinct(r):
        a = le(r[5], 32 if r[3] == 256 else 16)
        b = le(src2(r[3], r[4], r[6], r[10], r[11]), 32 if r[3] == 256 else 16)
        return len(set(a + b)) == len(a + b)
    say(all(distinct(r) for r in ROWS), "every row's SRC1 and SRC2 bytes are all distinct (the seeding, prediction 1)")
    for label, rl in WRONG:
        n = len(disagreements(rl))
        say(n > 0, "%s disagrees on %d rows" % (label, n))
    say(any(r[0] == PLANT_ROW and r[3] == 256 for r in ROWS), "--plant's row %s exists and is VEX.256" % PLANT_ROW)
    say(any(r[0] == PLANT_HI and r[3] == 128 for r in ROWS), "--plant-hi's row %s exists and is VEX.128" % PLANT_HI)
    say(F("vpunpckldq", 0x33333333_22222222_11111111_00000000, 0xbbbbbbbb_aaaaaaaa_99999999_88888888)
        == 0x99999999_11111111_88888888_00000000
        and F("vpunpckhqdq", 0x1111_0000 << 64 | 0x2222, 0x3333_0000 << 64 | 0x4444) == (0x3333_0000 << 64 | 0x1111_0000),
        "F is the SDM's: PUNPCKLDQ interleaves the low dwords A0 B0 A1 B1, PUNPCKHQDQ takes A1, B1")
    try:
        committed = open(os.path.join(HERE, "vexsill_ops.S"), encoding="utf-8").read()
    except OSError:
        committed = None
    say(committed == asm(), "the committed vexsill_ops.S equals `--asm`")
    print("✅ mk_vexsill_rows selftest" if ok else "⛔ mk_vexsill_rows selftest FAILED")
    return 0 if ok else 1


def main():
    P.strict_flags(__file__)
    if "--selftest" in sys.argv:
        return selftest()
    if "--asm" in sys.argv:
        sys.stdout.write(asm())
        return 0
    build()
    if "--summary" in sys.argv:
        for fn, *_ in OPS:
            print("%-28s %3d" % (fn, sum(1 for r in ROWS if r[1] == fn)))
        print("rows %d functions %d" % (len(ROWS), len(OPS)))
        return 0
    if "--reach" in sys.argv:
        bad = 0
        for label, rl in WRONG:
            n = len(disagreements(rl))
            print("%-48s disagrees on %4d of %d rows" % (label, n, len(ROWS)))
            bad += n == 0
        return 1 if bad else 0
    plant, plant_hi = "--plant" in sys.argv, "--plant-hi" in sys.argv
    print("/* GENERATED by hwprobe/mk_vexsill_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    for fn, *_ in OPS:
        print("void %s(struct xio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const struct xrow XROWS[] = {")
    for name, fn, _v, L, _s, y1, y2, y3, f, rax, mem, off, w3 in ROWS:
        if plant and name == PLANT_ROW:
            w3 ^= 1 << 128
        if plant_hi and name == PLANT_HI:
            w3 |= y3 >> 128 << 128
        print('  {"%s", %s, {%s}, {%s}, {%s}, 0x%03x, 0x%04x, 0x%016xULL, {%s}, %d, {%s}, 0x%016xULL, 0x%04x},' % (
            name, fn, q(y1, 4), q(y2, 4), q(y3, 4), f, MX, rax, q(mem, 8), off, q(w3, 4), rax, MX))
    print("};")
    print("static const struct xop XOPS[] = {")
    for i, (fn, _v, _L, _s, bs) in enumerate(OPS):
        bb = bytearray.fromhex(bs)
        if "--plant-op" in sys.argv and i == 0:
            bb[-1] ^= 0x01
        print('  {"%s", %s_at, %d, {%s}},' % (fn, fn, len(bb), ", ".join("0x%02x" % x for x in bb)))
    print("};")
    return 0


if __name__ == "__main__":
    sys.exit(main())
