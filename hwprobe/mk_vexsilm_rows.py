#!/usr/bin/env python3
"""hwprobe/mk_vexsilm_rows.py — D394 (wave G): the VEX twins of the legacy SCALAR floating-point forms, the rows the
x86-64 referee runs, with expectations DERIVED HERE. D393's `mk_vexsill_rows.py` with its kinds, its function, its seeding
and its wrong rules changed; the frame (`vexsilk_ops.S`'s PRE/POST) is that file's. The probe is `vexsilm_probe.c`, which
is `vexsile_probe.c` plus ONE field, the buffer's expected bytes, because the two store forms write memory and every
earlier VEX-silicon probe checks the buffer UNCHANGED.

The forms (x86isa refuses every VEX scalar-FP shape, D394 P1 2026-11-08 and reading 0), all VEX.128 (LIG; L = 0 assembled):
  vaddss vaddsd vsubss vsubsd vmulss vmulsd vdivss vdivsd   register and m32/m64 source
  vmovss vmovsd                                              register-register, load, store
Frame (D361's): YMM1 = SRC1 (VEX.vvvv), YMM2 = SRC2 (ModRM.rm) or RBX = &mem[off] (the memory source), YMM3 = DEST (and the
store's SOURCE); MXCSR, RAX, the six arithmetic flags and the 64-byte buffer loaded from the row and read back.

THE SCALAR ARITHMETIC IS NOT RESTATED HERE. It is `mk_rows.mul` / `mk_rows.arith` — B1/B2's independent reference (IEEE 754
by exact Fractions, D265–D271), the rule the legacy `mulss`…`divsd` rows hold on silicon — and the operand pairs and MXCSR
values are those rows' own (`mk_rows.build()`), so one rule and one set of hard cases have one home. What THIS file states is
the VEX rule around it (SDM Vol. 2B ADDSD … DIVSS, MOVSS/MOVSD, the VEX.128 encodings):
  ARITH (rr, rm)  DEST[w-1:0] := OP(SRC1[w-1:0], SRC2[w-1:0]) under MXCSR.RC;  DEST[127:w] := SRC1[127:w];  DEST[255:128] := 0
                  MXCSR := MXCSR | the flags OP raises (all exceptions masked in every row)
  MOVS rr         DEST[w-1:0] := SRC2[w-1:0];  DEST[127:w] := SRC1[127:w];  DEST[255:128] := 0
  MOVS load       DEST[w-1:0] := mem[off];      DEST[255:w] := 0
  MOVS store      mem[off .. off + w/8) := YMM3[w-1:0]; no register written
  MEMORY          no alignment check (a scalar operand states none);  NO-OTHERS: flags, RAX, YMM1, YMM2 unchanged.
THE SECOND DERIVATION (`textbook`) re-derives every expectation from BYTE LISTS — the low w/8 bytes, then SRC1's bytes
w/8 … 15 (or zeros), then sixteen zero bytes — and takes from `mk_rows` only the low lane's value; every row must agree
with the rule or the build refuses.

THE BYTES are derived from the SDM's VEX rule, not copied from an assembler: two-byte VEX C5, then R̄ vvvv̄ L pp, with
vvvv = 1 (YMM1) for the three-operand forms and 1111 (none) for the load and store, pp = F3 (ss) or F2 (sd): F2 · F3 · FA ·
FB; then the legacy opcode (58 add · 59 mul · 5C sub · 5E div · 10 movs · 11 the store); then ModRM DA (reg 3, rm 2) or 1B
(reg 3, [RBX]). The selftest compares them with clang's; `vexsilm_probe.c` refuses a run whose assembled bytes differ.

THE SEEDING (prediction 2). Every row's YMM1, YMM2 and YMM3 carry distinct random bytes above the operand, with YMM1's and
YMM3's upper halves nonzero, so a row tells SRC1's upper bits from DEST's (the legacy rule), and the zeroing is read.

Usage: mk_vexsilm_rows.py [--plant | --plant-op | --plant-hi | --summary | --reach | --asm | --selftest]
  --plant      flips bit 64 (SRC1's merged bits) of one vaddsd row's expectation: exactly that row must disagree (exit 1)
  --plant-op   declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --plant-hi   one row's expectation keeps YMM3's upper half: exactly that row must disagree
  --summary    per-function row counts, not C
  --reach      per named wrong rule, how many rows it disagrees on (every count must be non-zero)
  --asm        prints `vexsilm_ops.S` (the committed file must equal it; the selftest checks)
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
import mk_rows as R  # noqa: E402  (B1/B2's scalar reference and its rows)

ARITH = 0x8d5
M64 = (1 << 64) - 1
M128 = (1 << 128) - 1
M256 = (1 << 256) - 1
M512 = (1 << 512) - 1
MX = 0x1f80
OPC = {"add": "58", "mul": "59", "sub": "5c", "div": "5e"}
UNALIGNED = [1, 3, 5, 7, 9, 13]
N_MOV = 8
PLANT_ROW = "vaddsd_r_exact/nearest"   # --plant: bit 64 of its expectation (SRC1's merged quadword)
PLANT_HI = "vmulss_r_exact/nearest"    # --plant-hi: its expectation keeps YMM3's upper half


def pp(w, vvvv):
    """The second VEX byte: R̄ = 1, vvvv̄, L = 0, pp (F3 = 10 for ss, F2 = 11 for sd)."""
    return "%02x" % (0x80 | ((~vvvv & 0xf) << 3) | (0b10 if w == 32 else 0b11))


def enc(kind, w, shape):
    if kind == "movs":
        if shape == "r":
            return "c5" + pp(w, 1) + "10da"
        return "c5" + pp(w, 0) + ("10" if shape == "l" else "11") + "1b"
    return "c5" + pp(w, 1) + OPC[kind] + ("da" if shape == "r" else "1b")


def mnem(kind, w):
    return "v%ss" % ("mov" if kind == "movs" else kind) + ("s" if w == 32 else "d")


OPS = []   # (function, kind, w, shape, declared bytes)
for _k in ("add", "sub", "mul", "div"):
    for _w in (32, 64):
        for _s in ("r", "m"):
            OPS.append(("x_%s_%s" % (mnem(_k, _w), _s), _k, _w, _s, enc(_k, _w, _s)))
for _w in (32, 64):
    for _s in ("r", "l", "s"):
        OPS.append(("x_%s_%s" % (mnem("movs", _w), _s), "movs", _w, _s, enc("movs", _w, _s)))


def fmt(w):
    return R.F32 if w == 32 else R.F64


def low(kind, w, rc, a, b):
    """(value, flags) of the scalar operation on the low lanes: mk_rows's rule, never restated."""
    mode = R.MODES[rc]
    if kind == "mul":
        return R.mul(fmt(w), mode, a, b)
    return R.arith(kind, fmt(w), rc, a, b)


def src2(shape, w, y2, mem, off):
    return y2 & ((1 << w) - 1) if shape == "r" else (mem >> (8 * off)) & ((1 << w) - 1)


def rule(kind, w, shape, rc, y1, y2, y3, mem, off):
    """(YMM3 after, MXCSR flags raised, the buffer after)."""
    mw = (1 << w) - 1
    if kind == "movs":
        if shape == "s":
            k = w // 8
            m = (mem & ~(((1 << (8 * k)) - 1) << (8 * off)) & M512) | ((y3 & mw) << (8 * off))
            return y3, 0, m
        b = src2("r" if shape == "r" else "m", w, y2, mem, off)
        upper = (y1 & M128 & ~mw) if shape == "r" else 0
        return b | upper, 0, mem
    v, f = low(kind, w, rc, y1 & mw, src2(shape, w, y2, mem, off))
    return (v & mw) | (y1 & M128 & ~mw), f, mem


def le(x, n):
    return [(x >> (8 * i)) & 0xff for i in range(n)]


def un(bs):
    return sum(x << (8 * i) for i, x in enumerate(bs))


def textbook(kind, w, shape, rc, y1, y2, y3, mem, off):
    """The same from byte lists: the low k bytes, then SRC1's bytes k … 15 or zeros, then 16 zero bytes; a store's k
    bytes written into the buffer's byte list at off. Only the low lane's VALUE comes from `mk_rows`."""
    k = w // 8
    a, b, c, m = le(y1, 32), le(y2, 32), le(y3, 32), le(mem, 64)
    if kind == "movs" and shape == "s":
        return un(c), 0, un(m[:off] + c[:k] + m[off + k:])
    if kind == "movs":
        lo = b[:k] if shape == "r" else m[off:off + k]
        hi = a[k:16] if shape == "r" else [0] * (16 - k)
        return un(lo + hi + [0] * 16), 0, mem
    b2 = b[:k] if shape == "r" else m[off:off + k]
    v, f = low(kind, w, rc, un(a[:k]), un(b2))
    return un(le(v, k) + a[k:16] + [0] * 16), f, mem


# --reach: the wrong rules D394's prediction 2 names. Each must disagree with the rule on at least one row.
def w_merge_dest(kind, w, shape, rc, y1, y2, y3, mem, off):          # (a) [127:w] from DEST (the legacy rule)
    d, f, m = rule(kind, w, shape, rc, y1, y2, y3, mem, off)
    if kind == "movs" and shape != "r":
        return d, f, m
    mw = (1 << w) - 1
    return (d & mw) | (y3 & M128 & ~mw), f, m


def w_keep_upper(kind, w, shape, rc, y1, y2, y3, mem, off):          # (b) YMM3[255:128] kept
    d, f, m = rule(kind, w, shape, rc, y1, y2, y3, mem, off)
    return (d | (y3 >> 128 << 128)) if not (kind == "movs" and shape == "s") else d, f, m


def w_swapped(kind, w, shape, rc, y1, y2, y3, mem, off):             # (c) SRC1 and SRC2 swapped in the operation
    if kind == "movs":
        return rule(kind, w, shape, rc, y1, y2, y3, mem, off)
    mw = (1 << w) - 1
    v, f = low(kind, w, rc, src2(shape, w, y2, mem, off), y1 & mw)
    return (v & mw) | (y1 & M128 & ~mw), f, mem


def w_round_nearest(kind, w, shape, rc, y1, y2, y3, mem, off):       # (d) MXCSR.RC ignored (always nearest)
    return rule(kind, w, shape, 0, y1, y2, y3, mem, off)


def w_no_flags(kind, w, shape, rc, y1, y2, y3, mem, off):            # (e) MXCSR's flags left unwritten
    d, _f, m = rule(kind, w, shape, rc, y1, y2, y3, mem, off)
    return d, 0, m


def w_movs_flip(kind, w, shape, rc, y1, y2, y3, mem, off):           # (f) the load merges, the register form zeroes
    d, f, m = rule(kind, w, shape, rc, y1, y2, y3, mem, off)
    if kind != "movs" or shape == "s":
        return d, f, m
    mw = (1 << w) - 1
    if shape == "r":
        return d & mw, f, m
    return (d & mw) | (y1 & M128 & ~mw), f, m


def w_aligned_read(kind, w, shape, rc, y1, y2, y3, mem, off):        # (g) the memory operand at mem[off & ~15]
    return rule(kind, w, shape, rc, y1, y2, y3, mem, off & ~15)


WRONG = [("(a) [127:w] from DEST, not SRC1 (the legacy rule)", w_merge_dest), ("(b) YMM3[255:128] kept", w_keep_upper),
         ("(c) SRC1 and SRC2 swapped (sub, div, NaN order)", w_swapped), ("(d) MXCSR.RC ignored", w_round_nearest),
         ("(e) MXCSR flags left unwritten", w_no_flags), ("(f) movs: the load merges, rr zeroes", w_movs_flip),
         ("(g) the operand read from the aligned address", w_aligned_read)]

ROWS = []   # (name, fn, kind, w, shape, rc, mx, y1, y2, y3, f, rax, mem, off, w3, wflags, wmem)


def place(mem, off, value, n):
    mask = ((1 << (8 * n)) - 1) << (8 * off)
    return (mem & ~mask & M512) | ((value & ((1 << (8 * n)) - 1)) << (8 * off))


def legacy_cases():
    """{(kind, w): [(case name, mxcsr, a, b)]} — the legacy B1/B2 rows' own operands and MXCSR, in their order."""
    R.ROWS.clear()
    R.build()
    out = {}
    for name, fn, mx, a, b, _want, _mask, _flags in R.ROWS:
        op = fn[2:]
        for kind in ("add", "sub", "mul", "div"):
            for w, suf in ((32, "ss"), (64, "sd")):
                if op == kind + suf:
                    out.setdefault((kind, w), []).append((name.split("_", 1)[1], mx, a, b))
    return out


def build():
    ROWS.clear()
    cases = legacy_cases()
    for k, (fn, kind, w, shape, _bs) in enumerate(OPS):
        rng = random.Random(394100 + k)
        mw = (1 << w) - 1
        if kind == "movs":
            todo = [("p%d" % i, MX, None, None, 0) for i in range(N_MOV)] if shape == "r" else \
                   [("s%d_%s" % (j, x), MX, None, None, 0 if x == "a" else UNALIGNED[j]) for j in range(N_MOV // 2)
                    for x in "au"]
        elif shape == "r":
            todo = [(c, mx, a, b, 0) for c, mx, a, b in cases[(kind, w)]]
        else:   # the memory form: the round-to-nearest cases, alternating offset 0 and an odd offset
            near = [(c, mx, a, b) for c, mx, a, b in cases[(kind, w)] if (mx >> 13) & 3 == 0]
            todo = [(c, mx, a, b, 0 if i % 2 == 0 else UNALIGNED[(i // 2) % len(UNALIGNED)])
                    for i, (c, mx, a, b) in enumerate(near)]
        for i, (nm, mx, a, b, off) in enumerate(todo):
            if a is None:
                a, b = rng.getrandbits(w), rng.getrandbits(w)
            y1 = ((rng.getrandbits(256) | (1 << 128) | (1 << w)) & ~mw) | (a & mw)
            y3 = (rng.getrandbits(256) | (1 << 128) | 1 | (1 << w))
            rax = rng.getrandbits(64) | (1 << 63)
            if shape == "r":
                y2 = ((rng.getrandbits(256) | (1 << 128)) & ~mw) | (b & mw)
                mem = rng.getrandbits(512)
            else:
                y2 = rng.getrandbits(256) | 1 | (1 << 128)
                mem = place(rng.getrandbits(512), off, b, w // 8)
            rc = (mx >> 13) & 3
            f = ARITH if i % 2 else 0
            name = "%s_%s_%s" % (fn[2:].rsplit("_", 1)[0], shape, nm)
            got = rule(kind, w, shape, rc, y1, y2, y3, mem, off)
            tb = textbook(kind, w, shape, rc, y1, y2, y3, mem, off)
            if got != tb:
                raise SystemExit("mk_vexsilm_rows: ⛔ row %s: the rule gives %r, the textbook %r" % (name, got, tb))
            ROWS.append((name, fn, kind, w, shape, rc, mx, y1, y2, y3, f, rax, mem, off, got[0], got[1], got[2]))


def disagreements(rl):
    return [r[0] for r in ROWS if rl(r[2], r[3], r[4], r[5], r[7], r[8], r[9], r[12], r[13]) != (r[14], r[15], r[16])]


def q(x, n):
    return ", ".join("0x%016xULL" % ((x >> (64 * i)) & M64) for i in range(n))


ASM_HEAD = r"""/* hwprobe/vexsilm_ops.S — D394: the VEX twins of the legacy scalar floating-point forms (vaddss/sd vsubss/sd vmulss/sd
   vdivss/sd at a register and a memory source; vmovss/sd register-register, load and store), one function per form, in
   D361's frame (`vexsilk_ops.S`), so `vexsilm_probe.c` runs them against `vexsilm_rows.h`: YMM1 = SRC1 (VEX.vvvv), YMM2 =
   SRC2 (a register form), RBX = &mem[off] (a memory form), YMM3 = DEST (the store's source). GENERATED by
   `mk_vexsilm_rows.py --asm`; its selftest refuses a committed copy that differs. */

#ifdef __APPLE__
#define SYM(x) _##x
#else
#define SYM(x) x
#endif

        .text
"""


def operands(kind, shape):
    if kind == "movs":
        return {"r": "%xmm2, %xmm1, %xmm3", "l": "(%rbx), %xmm3", "s": "%xmm3, (%rbx)"}[shape]
    return ("%xmm2" if shape == "r" else "(%rbx)") + ", %xmm1, %xmm3"


def asm():
    src = open(os.path.join(HERE, "vexsilk_ops.S"), encoding="utf-8").read()
    a, z = src.index("#define PRE"), src.index("#define AT(name)")
    frame = src[a:src.index("\n", z) + 1]
    out = [ASM_HEAD, "\n", frame]
    for fn, kind, w, shape, bs in OPS:
        out.append("\nFN(%s)\n        PRE\nAT(%s_at)\n        %s %s     /* %s */\n        POST\n" % (
            fn, fn, mnem(kind, w), operands(kind, shape), " ".join(bs[i:i + 2] for i in range(0, len(bs), 2))))
    return "".join(out)


def selftest():
    ok = True

    def say(c, what):
        nonlocal ok
        print(("  ✔ " if c else "  ✖ ") + what)
        ok = ok and c
    clang = {   # objdump of clang's encodings for this probe's registers (2026-11-09)
        ("add", 32, "r"): "c5f258da", ("add", 64, "r"): "c5f358da", ("sub", 64, "m"): "c5f35c1b",
        ("div", 32, "m"): "c5f25e1b", ("movs", 32, "r"): "c5f210da", ("movs", 64, "r"): "c5f310da",
        ("movs", 32, "l"): "c5fa101b", ("movs", 64, "l"): "c5fb101b", ("movs", 32, "s"): "c5fa111b",
        ("movs", 64, "s"): "c5fb111b"}
    for (kd, w, s), want in clang.items():
        say(enc(kd, w, s) == want, "%s %d %s: the SDM derivation gives clang's %s" % (kd, w, s, want))
    build()
    fns = {r[1] for r in ROWS}
    say(fns == {o[0] for o in OPS} and len(OPS) == 22, "all 22 functions have rows (%d rows)" % len(ROWS))
    say(all(r[13] == 0 or r[13] % 2 for r in ROWS) and any(r[13] for r in ROWS),
        "every memory row is at offset 0 or an odd offset, and some are odd")
    say(all((r[7] >> 128) and (r[9] >> 128) and ((r[7] ^ r[9]) & M128 >> r[3] << r[3]) for r in ROWS),
        "every row's YMM1 and YMM3 upper halves are nonzero and their bits [127:w] differ (the seeding)")
    say(all(r[16] == r[12] for r in ROWS if not (r[2] == "movs" and r[4] == "s"))
        and all(r[16] != r[12] for r in ROWS if r[2] == "movs" and r[4] == "s"),
        "only the store rows change the buffer, and every store row does")
    for label, rl in WRONG:
        n = len(disagreements(rl))
        say(n > 0, "%s disagrees on %d rows" % (label, n))
    say(any(r[0] == PLANT_ROW for r in ROWS), "--plant's row %s exists" % PLANT_ROW)
    say(any(r[0] == PLANT_HI for r in ROWS), "--plant-hi's row %s exists" % PLANT_HI)
    try:
        committed = open(os.path.join(HERE, "vexsilm_ops.S"), encoding="utf-8").read()
    except OSError:
        committed = None
    say(committed == asm(), "the committed vexsilm_ops.S equals `--asm`")
    print("✅ mk_vexsilm_rows selftest" if ok else "⛔ mk_vexsilm_rows selftest FAILED")
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
            print("%-22s %3d" % (fn, sum(1 for r in ROWS if r[1] == fn)))
        print("rows %d functions %d" % (len(ROWS), len(OPS)))
        return 0
    if "--reach" in sys.argv:
        bad = 0
        for label, rl in WRONG:
            n = len(disagreements(rl))
            print("%-52s disagrees on %4d of %d rows" % (label, n, len(ROWS)))
            bad += n == 0
        return 1 if bad else 0
    plant, plant_hi = "--plant" in sys.argv, "--plant-hi" in sys.argv
    print("/* GENERATED by hwprobe/mk_vexsilm_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    for fn, *_ in OPS:
        print("void %s(struct xio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const struct xrow XROWS[] = {")
    for name, fn, _k, _w, _s, _rc, mx, y1, y2, y3, f, rax, mem, off, w3, wf, wmem in ROWS:
        if plant and name == PLANT_ROW:
            w3 ^= 1 << 64
        if plant_hi and name == PLANT_HI:
            w3 |= y3 >> 128 << 128
        print('  {"%s", %s, {%s}, {%s}, {%s}, 0x%03x, 0x%04x, 0x%016xULL, {%s}, %d, {%s}, 0x%016xULL, 0x%04x, {%s}},' % (
            name, fn, q(y1, 4), q(y2, 4), q(y3, 4), f, mx, rax, q(mem, 8), off, q(w3, 4), rax, mx | wf, q(wmem, 8)))
    print("};")
    print("static const struct xop XOPS[] = {")
    for i, (fn, _k, _w, _s, bs) in enumerate(OPS):
        bb = bytearray.fromhex(bs)
        if "--plant-op" in sys.argv and i == 0:
            bb[-1] ^= 0x01
        print('  {"%s", %s_at, %d, {%s}},' % (fn, fn, len(bb), ", ".join("0x%02x" % x for x in bb)))
    print("};")
    return 0


if __name__ == "__main__":
    sys.exit(main())
