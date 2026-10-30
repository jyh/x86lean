#!/usr/bin/env python3
"""hwprobe/mk_vexsilg_rows.py — D374: the VEX twins of eleven modelled packed-integer kinds (D335's and D373's), the rows
the x86-64 referee runs, with expectations DERIVED HERE.

The forms (x86isa refuses all of them, D374 P1), each at VEX.128 and VEX.256, with a register and a memory source:
  vpaddsw vpmaxsw vpminsw vpsubusb vpsadbw vpmullw vpavgb vpsubusw vpmulhw vpmulhuw vpmuludq
The probe is D361's (`vexsile_probe.c`, compiled against `vexsilg_rows.h`) and `vexsilg_ops.S` uses its frame: YMM1 =
SRC1 (VEX.vvvv), YMM2 = SRC2 (ModRM.rm) or RBX = &mem[off] (the memory source), YMM3 = DEST; MXCSR, RAX, the six
arithmetic flags and the 64-byte buffer loaded from the row and read back.

THE 128-BIT FUNCTION IS NOT RESTATED HERE. It is `mk_simda_rows.rule(legacy, a, b)` — D335's and D373's SDM rules, the
ones their silicon rows already hold — imported, with SRC1 in the place the legacy form gives its destination. D348's
generator restated D335's rules in a second file; one home for a rule cannot drift from itself.
  VEX.128      DEST[127:0] := F(SRC1[127:0], SRC2[127:0]);  DEST[255:128] := 0
  VEX.256      DEST[127:0] := F(SRC1[127:0], SRC2[127:0]);  DEST[255:128] := F(SRC1[255:128], SRC2[255:128])
  MEMORY       SRC2 := the 16 (VEX.128) or 32 (VEX.256) bytes at mem[off], NO alignment check (VEX Exception Type 4)
  NO-OTHERS    flags, MXCSR, RAX, YMM1, YMM2 and the buffer unchanged.
THE SECOND DERIVATION (`textbook`) re-derives the VEX wrapping from byte lists — the lane split, the zeroing and the
memory slice — calling F only on 16-byte values; every row must agree with the rule or the build refuses.

THE BYTES are derived from the SDM's VEX rule, not copied from an assembler: C5, then R̄ vvvv̄ L pp with vvvv = 1
(YMM1), R = 0, pp = 01 (66) — F1 at L = 0 and F5 at L = 1 — then the legacy opcode byte (`mk_simda_rows`' table), then
ModRM DA (reg 3, rm 2) or 1B (reg 3, [RBX]). `vexsile_probe.c` refuses the run unless the assembled bytes match.

THE ROWS. The register forms carry the arithmetic: VEX.128 takes the legacy form's 18 operand pairs (`operands`), and
VEX.256 nine rows whose two lanes are two different pairs, so the 18 pairs each reach a lane. The memory forms carry the
operand read: six pairs, each at offset 0 and at an odd offset. YMM3, YMM2 (at a memory form) and the buffer outside the
operand are random and nonzero; at VEX.128 YMM1's and YMM3's upper halves are nonzero, so the zeroing is read.

Usage: mk_vexsilg_rows.py [--plant | --plant-op | --plant-hi | --summary | --reach | --selftest]
  --plant      flips bit 128 (the HIGH lane) of one VEX.256 row's expectation: exactly that row must disagree (exit 1)
  --plant-op   declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --plant-hi   one VEX.128 row's expectation keeps YMM3's upper half: exactly that row must disagree
  --summary    per-function row counts, not C
  --reach      per named wrong rule, how many rows it disagrees on (every count must be non-zero)
  --selftest   the bytes against the SDM rule's derivation, every row's two derivations, the wrong rules' reach, the plants
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "scripts"))
sys.path.insert(0, HERE)
import portable as P  # noqa: E402
import mk_simda_rows as M  # noqa: E402  (the 128-bit rules of D335 and D373)

ARITH = 0x8d5
M64 = (1 << 64) - 1
M128 = (1 << 128) - 1
M256 = (1 << 256) - 1
MX = 0x1f80

# (VEX mnemonic, the legacy mnemonic whose 128-bit rule it applies) — the eleven D374 twins.
KINDS = [("vpaddsw", "paddsw"), ("vpmaxsw", "pmaxsw"), ("vpminsw", "pminsw"), ("vpsubusb", "psubusb"),
         ("vpsadbw", "psadbw"), ("vpmullw", "pmullw"), ("vpavgb", "pavgb"), ("vpsubusw", "psubusw"),
         ("vpmulhw", "pmulhw"), ("vpmulhuw", "pmulhuw"), ("vpmuludq", "pmuludq")]
LEGACY = {mn: (w, op) for mn, w, op in M.MNEMONICS_A + M.MNEMONICS_B}
UNALIGNED = [1, 3, 5, 7, 9, 13]
N_MEM = 6
PLANT_ROW = "vpaddsw256_r_p0"       # --plant: bit 128 of its expectation
PLANT_HI = "vpaddsw128_r_edge0"     # --plant-hi: its expectation keeps YMM3's upper half


def enc(legacy, L, shape):
    """The SDM's VEX.128/256.66.0F encoding of the legacy opcode, with this probe's registers."""
    op = LEGACY[legacy][1]
    if not (op.startswith("660f") and len(op) == 6):
        raise SystemExit("mk_vexsilg_rows: %s is not a 66 0F xx opcode (%s)" % (legacy, op))
    return "c5" + ("f1" if L == 128 else "f5") + op[4:] + ("da" if shape == "r" else "1b")


OPS = []   # (function, vex mnemonic, legacy, L, shape, declared bytes)
for _v, _l in KINDS:
    for _L in (128, 256):
        for _s in ("r", "m"):
            OPS.append(("x_%s%d_%s" % (_v, _L, _s), _v, _l, _L, _s, enc(_l, _L, _s)))


def F(legacy, a, b):
    return M.rule(legacy, a & M128, b & M128) & M128


def src2(L, shape, y2, mem, off):
    return y2 & (M128 if L == 128 else M256) if shape == "r" else (mem >> (8 * off)) & (M128 if L == 128 else M256)


def rule(legacy, L, shape, y1, y2, y3, mem, off):
    """YMM3 after the instruction."""
    b = src2(L, shape, y2, mem, off)
    lo = F(legacy, y1, b)
    return lo if L == 128 else lo | (F(legacy, y1 >> 128, b >> 128) << 128)


def le(v, n):
    return [(v >> (8 * i)) & 0xff for i in range(n)]


def un(bs):
    return sum(x << (8 * i) for i, x in enumerate(bs))


def textbook(legacy, L, shape, y1, y2, y3, mem, off):
    """The same, from byte lists: the operand sliced from the buffer's bytes, the lanes cut as 16-byte lists, the upper
    half written as 16 zero bytes. F is called on 16-byte values only."""
    a = le(y1, 32)
    b = le(y2, 32) if shape == "r" else le(mem, 64)[off:off + 32]
    out = le(F(legacy, un(a[:16]), un(b[:16])), 16)
    out += le(F(legacy, un(a[16:32]), un(b[16:32])), 16) if L == 256 else [0] * 16
    return un(out)


# --reach: the wrong rules D374 names. Each must disagree with the rule on at least one row.
def w_keep_upper(legacy, L, shape, y1, y2, y3, mem, off):            # (a) the legacy rule: YMM3[255:128] kept
    r = rule(legacy, L, shape, y1, y2, y3, mem, off)
    return r | (y3 >> 128 << 128) if L == 128 else r


def w_low_lane_only(legacy, L, shape, y1, y2, y3, mem, off):         # (b) VEX.256 applies F to the low lane only
    r = rule(legacy, L, shape, y1, y2, y3, mem, off)
    return r & M128 if L == 256 else r


def w_swapped(legacy, L, shape, y1, y2, y3, mem, off):               # (c) SRC2 in the destination's place
    b = src2(L, shape, y2, mem, off)
    lo = F(legacy, b, y1)
    return lo if L == 128 else lo | (F(legacy, b >> 128, y1 >> 128) << 128)


def w_aligned_read(legacy, L, shape, y1, y2, y3, mem, off):          # (d) the memory operand read from mem[off & ~15]
    return rule(legacy, L, shape, y1, y2, y3, mem, off & ~15)


WRONG = [("(a) VEX.128 keeps YMM3[255:128]", w_keep_upper), ("(b) VEX.256 low lane only", w_low_lane_only),
         ("(c) the operands swapped", w_swapped), ("(d) the operand read from the aligned address", w_aligned_read)]

ROWS = []   # (name, fn, legacy, L, shape, y1, y2, y3, f, rax, mem, off, w3)


def place(mem, off, value, n):
    mask = ((1 << (8 * n)) - 1) << (8 * off)
    return (mem & ~mask & ((1 << 512) - 1)) | ((value & ((1 << (8 * n)) - 1)) << (8 * off))


def build():
    ROWS.clear()
    for k, (fn, _v, legacy, L, shape, _bs) in enumerate(OPS):
        w = LEGACY[legacy][0]
        pairs = M.operands(k, legacy, w)                         # 18 (name, a, b) pairs at the legacy form's lanes
        rng = random.Random(374000 + k)
        if shape == "r" and L == 128:
            cases = [(nm, a, b, 0) for nm, a, b in pairs]
        elif shape == "r":
            cases = [("p%d" % i, pairs[i][1] | pairs[i + 9][1] << 128, pairs[i][2] | pairs[i + 9][2] << 128, 0)
                     for i in range(9)]
        else:
            n = L // 8
            sel = pairs[:N_MEM] if L == 128 else [(pairs[i][0], pairs[i][1] | pairs[i + 9][1] << 128,
                                                   pairs[i][2] | pairs[i + 9][2] << 128) for i in range(N_MEM)]
            cases = [(nm + "_" + v, a, b, 0 if v == "a" else UNALIGNED[j]) for j, (nm, a, b) in enumerate(sel)
                     for v in "au"]
        for i, (nm, a, b, off) in enumerate(cases):
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
            got = rule(legacy, L, shape, y1, y2, y3, mem, off)
            tb = textbook(legacy, L, shape, y1, y2, y3, mem, off)
            if got != tb:
                raise SystemExit("mk_vexsilg_rows: ⛔ row %s: the rule gives %064x, the textbook %064x" % (name, got, tb))
            ROWS.append((name, fn, legacy, L, shape, y1, y2, y3, f, rax, mem, off, got))


def disagreements(rl):
    return [r[0] for r in ROWS if rl(r[2], r[3], r[4], r[5], r[6], r[7], r[10], r[11]) != r[12]]


def q(v, n):
    return ", ".join("0x%016xULL" % ((v >> (64 * i)) & M64) for i in range(n))


def selftest():
    ok = True

    def say(c, what):
        nonlocal ok
        print(("  ✔ " if c else "  ✖ ") + what)
        ok = ok and c
    clang = {   # clang's bytes for one form per row of the derivation (D374, read with objdump when this was written)
        ("vpaddsw", 128, "r"): "c5f1edda", ("vpaddsw", 256, "m"): "c5f5ed1b", ("vpmuludq", 256, "r"): "c5f5f4da",
        ("vpavgb", 128, "m"): "c5f1e01b", ("vpsadbw", 256, "r"): "c5f5f6da", ("vpminsw", 128, "r"): "c5f1eada"}
    for (v, L, s), want in clang.items():
        say(enc(dict(KINDS)[v], L, s) == want, "%s %d %s: the SDM derivation gives clang's %s" % (v, L, s, want))
    build()
    say(len(ROWS) == len(KINDS) * (18 + 9 + 2 * N_MEM * 2), "%d rows = 11 × (18 + 9 + 12 + 12)" % len(ROWS))
    say(all(r[11] == 0 or r[11] % 2 for r in ROWS) and any(r[11] for r in ROWS),
        "every memory row is at offset 0 or an odd offset, and some are odd")
    for label, rl in WRONG:
        n = len(disagreements(rl))
        say(n > 0, "%s disagrees on %d rows" % (label, n))
    say(any(r[0] == PLANT_ROW and r[3] == 256 for r in ROWS), "--plant's row %s exists and is VEX.256" % PLANT_ROW)
    say(any(r[0] == PLANT_HI and r[3] == 128 for r in ROWS), "--plant-hi's row %s exists and is VEX.128" % PLANT_HI)
    say(F("paddsw", 0x7fff, 0x0001) == 0x7fff and F("pavgb", 0xff, 0xff) == 0xff,
        "F is D335/D373's rule: PADDSW saturates 7FFFH + 1, PAVGB FFH + FFH is FFH")
    print("✅ mk_vexsilg_rows selftest" if ok else "⛔ mk_vexsilg_rows selftest FAILED")
    return 0 if ok else 1


def main():
    P.strict_flags(__file__)
    if "--selftest" in sys.argv:
        return selftest()
    build()
    if "--summary" in sys.argv:
        for fn, *_ in OPS:
            print("%-24s %3d" % (fn, sum(1 for r in ROWS if r[1] == fn)))
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
    print("/* GENERATED by hwprobe/mk_vexsilg_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    for fn, *_ in OPS:
        print("void %s(struct xio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const struct xrow XROWS[] = {")
    for name, fn, _l, L, _s, y1, y2, y3, f, rax, mem, off, w3 in ROWS:
        if plant and name == PLANT_ROW:
            w3 ^= 1 << 128
        if plant_hi and name == PLANT_HI:
            w3 |= y3 >> 128 << 128
        print('  {"%s", %s, {%s}, {%s}, {%s}, 0x%03x, 0x%04x, 0x%016xULL, {%s}, %d, {%s}, 0x%016xULL, 0x%04x},' % (
            name, fn, q(y1, 4), q(y2, 4), q(y3, 4), f, MX, rax, q(mem, 8), off, q(w3, 4), rax, MX))
    print("};")
    print("static const struct xop XOPS[] = {")
    for i, (fn, _v, _l, _L, _s, bs) in enumerate(OPS):
        bb = bytearray.fromhex(bs)
        if "--plant-op" in sys.argv and i == 0:
            bb[-1] ^= 0x01
        print('  {"%s", %s_at, %d, {%s}},' % (fn, fn, len(bb), ", ".join("0x%02x" % x for x in bb)))
    print("};")
    return 0


if __name__ == "__main__":
    sys.exit(main())
