#!/usr/bin/env python3
"""hwprobe/mk_simda_rows.py — D335 (V1a): the SSE-legacy PACKED-INTEGER ARITHMETIC rows the x86-64 referee runs, with
expectations DERIVED HERE.

A fourth path, beside the SSE soft-float one (`mk_rows.py`, `probe.c`), the integer one (`mk_int_rows.py`) and the
bit-string one (`mk_bitstr_rows.py`), sharing nothing with any of them: `simda_ops.S` (one function per form: both
128-bit operands in, the destination XMM, the source XMM and RFLAGS out), `simda_probe.c`, and this file.

Every expected value comes from a stated rule in this file (SDM Vol. 2B, each instruction's Operation section), never
from ACL2 x86isa — which refuses all eleven mnemonics at every pre-state (`scripts/oracle_availability.py`) — and never
from x86lean. Lane i of a 128-bit value is bits (i+1)w-1 : iw. DEST is %xmm0 (the AT&T second operand), SRC is %xmm1
or the 16-byte-aligned m128 at [RBX].

  PMADDWD    dword j := DEST.w[2j]*SRC.w[2j] + DEST.w[2j+1]*SRC.w[2j+1], every word SIGNED, the sum taken mod 2^32 — the
             one overflowing case (all four words 0x8000) wraps to 0x80000000; there is no saturation.
  PMADDUBSW  word j := SaturateToSignedWord(DEST.b[2j+1]*SRC.b[2j+1] + DEST.b[2j]*SRC.b[2j]), DEST's bytes UNSIGNED and
             SRC's bytes SIGNED — the asymmetry is the instruction.
  PMULLW     word i := the low 16 bits of DEST.w[i]*SRC.w[i] (sign-independent).
  PMULHRSW   word i := TEMP[16:1], TEMP := ((DEST.w[i]*SRC.w[i]) >> 14) + 1, the product SIGNED 32-bit: round to
             nearest by the +1, and 0x8000*0x8000 gives 0x8000 (the one result that overflows the signed word).
  PMULUDQ    qword k := DEST.d[2k] * SRC.d[2k], both UNSIGNED 32-bit, the full 64-bit product; dwords 1 and 3 are not read.
  PADDSW     word i := SaturateToSignedWord(DEST.w[i] + SRC.w[i]).
  PSUBUSW    word i := SaturateToUnsignedWord(DEST.w[i] - SRC.w[i]), both unsigned: 0 when SRC > DEST.
  PSUBUSB    the same at bytes.
  PMAXSW     word i := DEST.w[i] if DEST.w[i] > SRC.w[i] (SIGNED) else SRC.w[i].
  PSADBW     DEST[15:0] := sum over i = 0..7 of |DEST.b[i] - SRC.b[i]| (unsigned bytes); DEST[63:16] := 0; and the same
             for bytes 8..15 into DEST[79:64], with DEST[127:80] := 0.
  PACKSSDW   DEST.w[i] := SaturateToSignedWord(DEST.d[i]) for i = 0..3, and DEST.w[4+i] := SaturateToSignedWord(SRC.d[i]):
             the destination's four dwords become the LOW four words.
  NO-FLAGS   "Flags Affected: None" for all eleven: the six arithmetic flags leave the instruction as they entered.
  SRC-KEPT   the source register, and the memory source, are not written.

THE ROW POPULATION, per mnemonic (the same operand pairs at both shapes, `xx` and `xm`):
  EDGE    8 rows at the mnemonic's lane width (16 for word lanes, 8 for byte lanes, 32 for PMULUDQ and PACKSSDW): lane i
          of DEST and of SRC are drawn from an 8-value edge set so every (DEST, SRC) edge pair occurs (word and byte
          lanes: SRC is DEST's edge sequence rotated by the row number; dword lanes: 32 of the 64 pairs).
  UNIFORM 4 rows with every lane equal, at the extremes a lane rule saturates or overflows on.
  RANDOM  6 rows, every bit from `random.Random(335000 + k)` (k the mnemonic's index in MNEMONICS), never re-seeded.
Flags in: all six clear on even-numbered rows of a form, all six set on odd-numbered ones.

SET B (D373, `--set-b`): PMINSW PMULHW PMULHUW PAVGB, the same row construction and the same probe, its own `.S`
(`simdb_ops.S`), its own rows header and its own random seeds (373000 + k):
  PMINSW     word i := DEST.w[i] if DEST.w[i] < SRC.w[i] (SIGNED) else SRC.w[i].
  PMULHW     word i := bits 31:16 of the SIGNED 32-bit product DEST.w[i]*SRC.w[i].
  PMULHUW    the same with both words UNSIGNED.
  PAVGB      byte i := (DEST.b[i] + SRC.b[i] + 1) >> 1, both unsigned, the sum taken in 9 bits.

Usage: mk_simda_rows.py [--set-b] [--plant | --plant-op | --summary | --reach]   writes C rows on stdout.
  --plant     flips bit 64 (the HIGH quadword) of ONE expectation: exactly that row must disagree (exit 1)
  --plant-op  declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --summary   prints the per-form row counts, not C
  --reach     prints, per mnemonic, how many of its rows a named WRONG rule disagrees on (0 would be a vacuous row set)
"""
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "scripts"))
import portable as P  # noqa: E402

ARITH = 0x8d5
M128 = (1 << 128) - 1

# (mnemonic, its lane class for the edge rows, the two declared encodings) — the bytes read back by the probe at the
# function's `_at` label; a mismatch refuses the run. ModRM c1 = %xmm1,%xmm0; 03 = (%rbx),%xmm0.
MNEMONICS = [
    ("pmaddwd", 16, "660ff5"),
    ("pmaddubsw", 8, "660f3804"),
    ("pmullw", 16, "660fd5"),
    ("pmulhrsw", 16, "660f380b"),
    ("pmuludq", 32, "660ff4"),
    ("paddsw", 16, "660fed"),
    ("psubusw", 16, "660fd9"),
    ("psubusb", 8, "660fd8"),
    ("pmaxsw", 16, "660fee"),
    ("psadbw", 8, "660ff6"),
    ("packssdw", 32, "660f6b"),
]
SSSE3 = {"pmaddubsw", "pmulhrsw"}
# D373: set B, all SSE2 (SDM Vol. 2B). Its own list, so set A's random rows (seeded by index) do not move.
MNEMONICS_B = [
    ("pminsw", 16, "660fea"),
    ("pmulhw", 16, "660fe5"),
    ("pmulhuw", 16, "660fe4"),
    ("pavgb", 8, "660fe0"),
]
# D384: set C, wave E (SDM Vol. 2B). PSUBSW and PAVGW are SSE2; PMULDQ is SSE4.1, which the probe does not test by
# CPUID (it tests SSE2 and SSSE3): on a processor without it the form raises #UD, a crash and never a reading.
MNEMONICS_C = [
    ("psubsw", 16, "660fe9"),
    ("pavgw", 16, "660fe3"),
    ("pmuldq", 32, "660f3828"),
]
SEED = {"a": 335000, "b": 373000, "c": 384000}
SET = "a"

OPS = []   # (form, function, declared bytes hex, mnemonic, shape)


def select(name):
    """Make set `name` ("a": D335's eleven, "b": D373's four) the module's MNEMONICS and OPS."""
    global MNEMONICS, SET
    SET = name
    MNEMONICS = {"a": MNEMONICS_A, "b": MNEMONICS_B, "c": MNEMONICS_C}[name]
    OPS.clear()
    for _mn, _w, _op in MNEMONICS:
        OPS.append((_mn + "_xx", "v_" + _mn + "_xx", _op + "c1", _mn, "xx"))
        OPS.append((_mn + "_xm", "v_" + _mn + "_xm", _op + "03", _mn, "xm"))


MNEMONICS_A = MNEMONICS
select("a")

EDGES = {
    16: [0x0000, 0x0001, 0xFFFF, 0x7FFF, 0x8000, 0x8001, 0x4000, 0x00FF],
    8: [0x00, 0x01, 0xFF, 0x7F, 0x80, 0x81, 0x40, 0xFE],
    32: [0x00000000, 0x00000001, 0xFFFFFFFF, 0x7FFFFFFF, 0x80000000, 0x00008000, 0xFFFF8000, 0xFFFF7FFF],
}
UNIFORM = {
    16: [("min_min", 0x8000, 0x8000), ("max_max", 0x7FFF, 0x7FFF), ("min_max", 0x8000, 0x7FFF),
         ("m1_one", 0xFFFF, 0x0001)],
    8: [("ff_7f", 0xFF, 0x7F), ("ff_80", 0xFF, 0x80), ("00_ff", 0x00, 0xFF), ("7f_ff", 0x7F, 0xFF)],
    32: [("min_max", 0x80000000, 0x7FFFFFFF), ("ones_ones", 0xFFFFFFFF, 0xFFFFFFFF),
         ("max_min", 0x7FFFFFFF, 0x80000000), ("p8000_m8001", 0x00008000, 0xFFFF7FFF)],
}
N_RANDOM = 6


def lanes(v, w):
    return [(v >> (i * w)) & ((1 << w) - 1) for i in range(128 // w)]


def join(ls, w):
    r = 0
    for i, x in enumerate(ls):
        r |= (x & ((1 << w) - 1)) << (i * w)
    return r


def sx(x, w):
    return x - (1 << w) if x >> (w - 1) & 1 else x


def ssat16(v):
    return max(-32768, min(32767, v)) & 0xFFFF


def rule(mn, a, b):
    """The SDM rule for one mnemonic: DEST a, SRC b (128-bit ints) -> the new DEST."""
    if mn == "pmaddwd":
        x, y = lanes(a, 16), lanes(b, 16)
        return join([sx(x[2 * j], 16) * sx(y[2 * j], 16) + sx(x[2 * j + 1], 16) * sx(y[2 * j + 1], 16)
                     for j in range(4)], 32)
    if mn == "pmaddubsw":
        x, y = lanes(a, 8), lanes(b, 8)
        return join([ssat16(x[2 * j + 1] * sx(y[2 * j + 1], 8) + x[2 * j] * sx(y[2 * j], 8)) for j in range(8)], 16)
    if mn == "pmullw":
        return join([sx(p, 16) * sx(q, 16) for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    if mn == "pmulhrsw":
        return join([(((sx(p, 16) * sx(q, 16)) >> 14) + 1) >> 1 for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    if mn == "pmuludq":
        x, y = lanes(a, 32), lanes(b, 32)
        return join([x[0] * y[0], x[2] * y[2]], 64)
    if mn == "paddsw":
        return join([ssat16(sx(p, 16) + sx(q, 16)) for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    if mn == "psubusw":
        return join([max(0, p - q) for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    if mn == "psubusb":
        return join([max(0, p - q) for p, q in zip(lanes(a, 8), lanes(b, 8))], 8)
    if mn == "pmaxsw":
        return join([p if sx(p, 16) > sx(q, 16) else q for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    if mn == "psadbw":
        x, y = lanes(a, 8), lanes(b, 8)
        return join([sum(abs(x[i] - y[i]) for i in range(8)), sum(abs(x[i] - y[i]) for i in range(8, 16))], 64)
    if mn == "packssdw":
        return join([ssat16(sx(d, 32)) for d in lanes(a, 32)] + [ssat16(sx(d, 32)) for d in lanes(b, 32)], 16)
    if mn == "pminsw":
        return join([p if sx(p, 16) < sx(q, 16) else q for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    if mn == "pmulhw":
        return join([(sx(p, 16) * sx(q, 16)) >> 16 for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    if mn == "pmulhuw":
        return join([(p * q) >> 16 for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    if mn == "pavgb":
        return join([(p + q + 1) >> 1 for p, q in zip(lanes(a, 8), lanes(b, 8))], 8)
    if mn == "psubsw":
        return join([ssat16(sx(p, 16) - sx(q, 16)) for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    if mn == "pavgw":
        return join([(p + q + 1) >> 1 for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    if mn == "pmuldq":
        x, y = lanes(a, 32), lanes(b, 32)
        return join([sx(x[0], 32) * sx(y[0], 32), sx(x[2], 32) * sx(y[2], 32)], 64)
    raise SystemExit("mk_simda_rows: no rule for %s" % mn)


# --reach: one named WRONG rule per mnemonic — the mistake a reader most plausibly makes. A row set on which it agrees
# with the rule everywhere could not tell the two apart, so the count must be non-zero.
def wrong(mn, a, b):
    if mn == "pmaddwd":        # saturating the dword sum instead of wrapping
        x, y = lanes(a, 16), lanes(b, 16)
        return join([max(-2**31, min(2**31 - 1, sx(x[2 * j], 16) * sx(y[2 * j], 16)
                                     + sx(x[2 * j + 1], 16) * sx(y[2 * j + 1], 16))) for j in range(4)], 32)
    if mn == "pmaddubsw":      # the signedness swapped: DEST signed, SRC unsigned
        return rule(mn, b, a)
    if mn == "pmullw":         # the HIGH half (PMULHW) instead of the low
        return join([(sx(p, 16) * sx(q, 16)) >> 16 for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    if mn == "pmulhrsw":       # no rounding: (product >> 15)
        return join([(sx(p, 16) * sx(q, 16)) >> 15 for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    if mn == "pmuludq":        # the odd dwords instead of the even
        x, y = lanes(a, 32), lanes(b, 32)
        return join([x[1] * y[1], x[3] * y[3]], 64)
    if mn == "paddsw":         # wrapping (PADDW)
        return join([p + q for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    if mn == "psubusw":        # wrapping (PSUBW)
        return join([p - q for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    if mn == "psubusb":        # signed saturation (PSUBSB)
        return join([max(-128, min(127, sx(p, 8) - sx(q, 8))) for p, q in zip(lanes(a, 8), lanes(b, 8))], 8)
    if mn == "pmaxsw":         # unsigned comparison (PMAXUW)
        return join([max(p, q) for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    if mn == "psadbw":         # the two sums swapped between the quadwords
        x, y = lanes(a, 8), lanes(b, 8)
        return join([sum(abs(x[i] - y[i]) for i in range(8, 16)), sum(abs(x[i] - y[i]) for i in range(8))], 64)
    if mn == "packssdw":       # the source's dwords low and the destination's high
        return rule(mn, b, a)
    if mn == "pminsw":         # unsigned comparison (PMINUW)
        return join([min(p, q) for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    if mn == "pmulhw":         # unsigned words (PMULHUW)
        return rule("pmulhuw", a, b)
    if mn == "pmulhuw":        # signed words (PMULHW)
        return rule("pmulhw", a, b)
    if mn == "pavgb":          # truncating: no +1
        return join([(p + q) >> 1 for p, q in zip(lanes(a, 8), lanes(b, 8))], 8)
    if mn == "psubsw":         # (a) wrapping (PSUBW)
        return join([p - q for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    if mn == "pavgw":          # (b) truncating: no +1
        return join([(p + q) >> 1 for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)
    if mn == "pmuldq":         # (d) zero-extending: PMULUDQ's rule
        return rule("pmuludq", a, b)
    raise SystemExit("mk_simda_rows: no wrong rule for %s" % mn)


# D384: set C's SECOND named wrong rules, (c) and (e) of its predictions; each must also disagree somewhere.
WRONG_C2 = {
    "pavgw": ("(c) the carry lost: a 16-bit sum",
              lambda a, b: join([(((p + q) & 0xFFFF) + 1) >> 1 for p, q in zip(lanes(a, 16), lanes(b, 16))], 16)),
    "pmuldq": ("(e) the ODD dwords",
               lambda a, b: join([sx(lanes(a, 32)[1], 32) * sx(lanes(b, 32)[1], 32),
                                  sx(lanes(a, 32)[3], 32) * sx(lanes(b, 32)[3], 32)], 64)),
}


def operands(k, mn, w):
    """(name, DEST, SRC) for one mnemonic's EDGE, UNIFORM and RANDOM rows."""
    e, n = EDGES[w], 128 // w
    out = []
    for r in range(8):
        if w == 32:
            av = [e[(i + 4 * (r % 2)) % 8] for i in range(n)]
            bv = [e[(i + 4 * (r % 2) + r // 2) % 8] for i in range(n)]
        else:
            av = [e[i % 8] for i in range(n)]
            bv = [e[(i + r) % 8] for i in range(n)]
        out.append(("edge%d" % r, join(av, w), join(bv, w)))
    for nm, x, y in UNIFORM[w]:
        out.append((nm, join([x] * n, w), join([y] * n, w)))
    rng = random.Random(SEED[SET] + k)
    for r in range(N_RANDOM):
        out.append(("rand%d" % r, rng.getrandbits(128), rng.getrandbits(128)))
    return out


ROWS = []   # (name, fn, mnemonic, a, b, f, want)


def build():
    ROWS.clear()
    for k, (mn, w, _op) in enumerate(MNEMONICS):
        ops = operands(k, mn, w)
        for _form, fn, _bs, omn, _shape in OPS:
            if omn != mn:
                continue
            for i, (nm, a, b) in enumerate(ops):
                f = ARITH if i % 2 else 0
                ROWS.append(("%s_%s" % (fn[2:], nm), fn, mn, a, b, f, rule(mn, a, b) & M128))


def q2(v):
    return "0x%016xULL, 0x%016xULL" % (v & ((1 << 64) - 1), v >> 64)


def main():
    P.strict_flags(__file__)
    if "--set-b" in sys.argv:
        select("b")
    if "--set-c" in sys.argv:
        select("c")
    build()
    if "--summary" in sys.argv:
        for _form, fn, _bs, _mn, _sh in OPS:
            print("%-22s %d" % (fn, sum(1 for r in ROWS if r[1] == fn)))
        print("rows %d forms %d" % (len(ROWS), len(OPS)))
        return
    if "--reach" in sys.argv:
        bad = 0
        for mn, _w, _op in MNEMONICS:
            rs = [r for r in ROWS if r[2] == mn]
            n = sum(1 for r in rs if wrong(mn, r[3], r[4]) & M128 != r[6])
            print("%-10s wrong rule disagrees on %3d of %3d rows" % (mn, n, len(rs)))
            bad += n == 0
            if SET == "c" and mn in WRONG_C2:
                label, w2 = WRONG_C2[mn]
                n2 = sum(1 for r in rs if w2(r[3], r[4]) & M128 != r[6])
                print("%-10s %s disagrees on %3d of %3d rows" % (mn, label, n2, len(rs)))
                bad += n2 == 0
        return 1 if bad else 0
    plant = "--plant" in sys.argv
    print("/* GENERATED by hwprobe/mk_simda_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    for _form, fn, _b, _mn, _sh in OPS:
        print("void %s(struct sio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const struct srow SROWS[] = {")
    for i, (name, fn, _mn, a, b, f, want) in enumerate(ROWS):
        if plant and i == 0:
            want ^= 1 << 64        # the control: one expectation made wrong on purpose, in the HIGH quadword
        print('  {"%s", %s, {%s}, {%s}, 0x%03x, {%s}},' % (name, fn, q2(a), q2(b), f, q2(want)))
    print("};")
    print("static const struct sop SOPS[] = {")
    for i, (_form, fn, bs, mn, _sh) in enumerate(OPS):
        bb = bytearray.fromhex(bs)
        if "--plant-op" in sys.argv and i == 0:
            bb[-1] ^= 0x01         # the control: the declared instruction is not the one in simda_ops.S
        print('  {"%s", %s_at, %d, %d, {%s}},' % (fn, fn, len(bb), 1 if mn in SSSE3 else 0,
                                                ", ".join("0x%02x" % x for x in bb)))
    print("};")


if __name__ == "__main__":
    sys.exit(main())
