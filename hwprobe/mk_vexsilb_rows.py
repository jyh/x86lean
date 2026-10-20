#!/usr/bin/env python3
"""hwprobe/mk_vexsilb_rows.py — D348 (V8b): the VEX.128 and VEX.256 twins of four D335 (V1a) main-table forms, the rows
the x86-64 referee runs, with expectations DERIVED HERE.

The forms (register forms only; ACL2 x86isa refuses all 8 encodings, D348 P1):
  vpmaddwd · vpmulhrsw · vpmaddubsw · vpackssdw          each at VEX.128 (xmm) and at VEX.256 (ymm)
A ninth path, beside the SSE soft-float, integer, bit-string, shuffle, packed-integer, SHA-NI, AES/VEX and VEX-silicon
(D345) ones, sharing nothing with them: `vexsilb_ops.S` (one function per form and length), `vexsilb_probe.c`, and this
file.

Every expected value comes from a stated rule in this file (SDM Vol. 2B PMADDWD, PMULHRSW, PMADDUBSW, PACKSSDW/PACKSSWB,
each at its "VEX.128 encoded version" and "VEX.256 encoded version"), never from ACL2 x86isa and never from x86lean.
Element i of a vector is bits w(i+1)-1 : wi.

THE RULES (`rule` below). A, B are SRC1 (VEX.vvvv) and SRC2 (ModRM.rm); the 128-bit function F is the legacy one, with A
in the place the legacy form gives its DESTINATION.
  VEX.128      DEST[127:0] := F(A[127:0], B[127:0]);  DEST[255:128] := 0          (the VEX.128 zeroing)
  VEX.256      DEST[127:0] := F(A[127:0], B[127:0]);  DEST[255:128] := F(A[255:128], B[255:128])   (per lane)
  PMADDWD      dword i := A.w[2i]·B.w[2i] + A.w[2i+1]·B.w[2i+1], words SIGNED, the sum taken mod 2^32 — NO saturation:
               the one overflowing case (all four words 8000H) reads 80000000H
  PMULHRSW     word i := bits 16:1 of ((A.w[i]·B.w[i]) >> 14) + 1, words SIGNED: the 32-bit product shifted right 14,
               plus one, shifted right one more; 8000H·8000H reads 8000H
  PMADDUBSW    word i := SaturateToSignedWord(A.b[2i]·B.b[2i] + A.b[2i+1]·B.b[2i+1]), A's bytes UNSIGNED and B's SIGNED
  PACKSSDW     per lane: words 3:0 := A's four dwords, words 7:4 := B's four, each signed dword saturated to a signed word
               — at VEX.256 the low lane packs the two LOW lanes and the high lane the two HIGH lanes; it is not a 256-bit
               pack of A then B
  NO-OTHERS    "Flags Affected: None"; MXCSR unchanged; SRC1, SRC2 unchanged; RAX unchanged.

AMBIGUITIES, resolved by the SDM's pseudo-code reading (each is a rule above, and each is what a row reads):
  (1) PMADDUBSW's VEX operand order: the pseudo-code multiplies SRC1's bytes as unsigned and SRC2's as signed
      ("DEST[15-0] := SaturateToSignedWord(SRC2[15-8]*SRC1[15-8]+SRC2[7-0]*SRC1[7-0])" with SRC1 the unsigned operand),
      so VEX.vvvv supplies the UNSIGNED bytes — the role the legacy form's destination plays.
  (2) PMULHRSW's rounding: the pseudo-code is `temp := ((SRC1 * SRC2) >> 14) + 1; DEST := temp[16:1]`, an arithmetic
      shift of the signed 32-bit product.
  (3) PACKSSDW at VEX.256: the pseudo-code's high-lane words are SRC1[159:128..255:224] then SRC2[159:128..255:224].

THE PROBE'S REGISTERS (`vexsilb_ops.S`): YMM1 = SRC1 (VEX.vvvv), YMM2 = SRC2 (ModRM.rm), YMM3 = DEST, MXCSR and RAX loaded
from the row. All three YMM registers are loaded WHOLE (every upper half seeded random and non-zero at VEX.128; at VEX.256
the sources' upper halves are the high lane's data) and read back whole; MXCSR and RAX are read back after the instruction.

⭐ THE TEXTBOOKS, AND WHY EVERY ROW HAS ONE. A misread lane rule is a consistent mistake: a rule written with it and rows
derived from it agree. So every row is computed TWICE — by `rule` (128-bit integer bit operations, per lane, through
`lane128`) and by `textbook` (the SDM's flat element-by-element pseudo-code over byte strings, `int.from_bytes(signed=…)`,
with PACKSSDW's lanes written out as the pseudo-code writes them) — and `build` REFUSES any row where they differ.

THE ROW POPULATION (flags in: all six clear on even rows, all six set on odd ones; MXCSR.RC rotates by row):
  vpmaddwd     edge (all 8000H — the wrap), the squares of 7FFFH, mixed signs, zero, a lane marker, 4 random
  vpmulhrsw    edge (8000H·8000H, 7FFFH², the rounding boundaries ±1·4000H, -1·-1), zero, a lane marker, 4 random
  vpmaddubsw   edge (FFH·7FH pairs — the positive saturation, FFH·80H — the negative), the operand asymmetry, a lane
               marker, 4 random
  vpackssdw    the saturation edges (7FFFH, 8000H, FFFF8000H, FFFF7FFFH, 80000000H, 7FFFFFFFH, 0, -1), a lane marker,
               4 random
Random words from `random.Random(348000 + k)` (k the encoding's index), never re-seeded.

Usage: mk_vexsilb_rows.py [--plant | --plant-op | --plant-hi | --summary | --reach | --refuse-wrong | --selftest]
  --plant         flips bit 128 (the HIGH lane) of one VEX.256 row's expectation: exactly that row must disagree (exit 1)
  --plant-op      declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --plant-hi      one VEX.128 row's expectation keeps the destination's upper half instead of zeroing it: exactly that
                  row must disagree — the zeroing is compared, not assumed
  --summary       per-form row counts, not C
  --reach         per wrong rule, how many rows it disagrees on (0 would be a vacuous row set)
  --refuse-wrong  builds the rows under each wrong rule D348 names and shows `build` REFUSE it on its named row
  --selftest      hand-derived lanes against both references, every row's two derivations, the refusals, plants
"""
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "scripts"))
import portable as P  # noqa: E402

ARITH = 0x8d5
M16 = (1 << 16) - 1
M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
M128 = (1 << 128) - 1
M256 = (1 << 256) - 1

# Declared bytes: clang's assembly (`clang -target x86_64-unknown-linux-gnu -c`, read with `objdump -d`) of the
# `vexsilb_ops.S` line; the probe refuses to run if they differ from the bytes at the function's `_at` label.
# ModRM da = reg xmm3, rm xmm2; VEX.vvvv = xmm1.
ENC = {
    ("vpmaddwd", 128): "c5f1f5da", ("vpmaddwd", 256): "c5f5f5da",
    ("vpmulhrsw", 128): "c4e2710bda", ("vpmulhrsw", 256): "c4e2750bda",
    ("vpmaddubsw", 128): "c4e27104da", ("vpmaddubsw", 256): "c4e27504da",
    ("vpackssdw", 128): "c5f16bda", ("vpackssdw", 256): "c5f56bda",
}
FORMS = ["vpmaddwd", "vpmulhrsw", "vpmaddubsw", "vpackssdw"]

OPS = []   # (fn, form, L, declared bytes hex, imm — always None here, kept for the anchors generator's shape)
for _form in FORMS:
    for _L in (128, 256):
        OPS.append(("x_%s%d" % (_form, _L), _form, _L, ENC[(_form, _L)], None))

PLANT_ROW = "vpackssdw256_lane"     # --plant: bit 128 of its expectation
PLANT_HI = "vpmaddwd128_edge0"      # --plant-hi: its expectation keeps YMM3's upper half


# ── THE RULE: 128-bit integer bit operations, per lane ───────────────────────────────────────────────────────────────

def el(v, w, i):
    return (v >> (w * i)) & ((1 << w) - 1)


def sx(x, w):
    return x - (1 << w) if x >> (w - 1) else x


def of_els(xs, w):
    r = 0
    for i, x in enumerate(xs):
        r |= (x & ((1 << w) - 1)) << (w * i)
    return r


def sat(x, w):
    lo, hi = -(1 << (w - 1)), (1 << (w - 1)) - 1
    return max(lo, min(hi, x))


def r_maddwd(a, b):
    return of_els([sx(el(a, 16, 2 * i), 16) * sx(el(b, 16, 2 * i), 16)
                   + sx(el(a, 16, 2 * i + 1), 16) * sx(el(b, 16, 2 * i + 1), 16) for i in range(4)], 32)


def r_mulhrsw(a, b):
    return of_els([(((sx(el(a, 16, i), 16) * sx(el(b, 16, i), 16)) >> 14) + 1) >> 1 for i in range(8)], 16)


def r_maddubsw(a, b):
    return of_els([sat(el(a, 8, 2 * i) * sx(el(b, 8, 2 * i), 8) + el(a, 8, 2 * i + 1) * sx(el(b, 8, 2 * i + 1), 8), 16)
                   for i in range(8)], 16)


def r_packssdw(a, b):
    return of_els([sat(sx(el(a, 32, i), 32), 16) for i in range(4)] + [sat(sx(el(b, 32, i), 32), 16) for i in range(4)],
                  16)


LANE = {"vpmaddwd": r_maddwd, "vpmulhrsw": r_mulhrsw, "vpmaddubsw": r_maddubsw, "vpackssdw": r_packssdw}


def lane128(form, a, b):
    """The legacy 128-bit function, A in the destination's place."""
    if form not in LANE:
        raise SystemExit("mk_vexsilb_rows: no 128-bit rule for %s" % form)
    return LANE[form](a, b)


def rule(form, L, y1, y2, y3, mx, rax):
    """The SDM rule over the whole machine state the probe reads -> (YMM3, RAX, MXCSR)."""
    lo = lane128(form, y1 & M128, y2 & M128)
    if L == 128:
        return lo, rax, mx                              # VEX.128: DEST[255:128] := 0
    hi = lane128(form, y1 >> 128, y2 >> 128)
    return lo | (hi << 128), rax, mx


# ── THE WRONG RULES D348 NAMES, each a whole substitute for `rule`; `--refuse-wrong` shows `build` refuse each ────

def w_ubsw_swapped(form, L, y1, y2, y3, mx, rax):
    """(a) vpmaddubsw with the signedness of its two sources swapped: SRC1's bytes signed, SRC2's unsigned."""
    if form == "vpmaddubsw":
        def f(a, b):
            return r_maddubsw(b, a)
        lo = f(y1 & M128, y2 & M128)
        return (lo if L == 128 else lo | (f(y1 >> 128, y2 >> 128) << 128)), rax, mx
    return rule(form, L, y1, y2, y3, mx, rax)


def w_pack_across(form, L, y1, y2, y3, mx, rax):
    """(b) vpackssdw at VEX.256 packed across lanes: SRC1's eight dwords into the low lane, SRC2's into the high."""
    if form == "vpackssdw" and L == 256:
        def half(v):
            return of_els([sat(sx(el(v, 32, i), 32), 16) for i in range(8)], 16)
        return half(y1) | (half(y2) << 128), rax, mx
    return rule(form, L, y1, y2, y3, mx, rax)


def w_mulhrsw_trunc(form, L, y1, y2, y3, mx, rax):
    """(c) vpmulhrsw without its rounding increment: (A·B) >> 15 in place of ((A·B) >> 14 + 1) >> 1."""
    if form == "vpmulhrsw":
        def f(a, b):
            return of_els([(sx(el(a, 16, i), 16) * sx(el(b, 16, i), 16)) >> 15 for i in range(8)], 16)
        lo = f(y1 & M128, y2 & M128)
        return (lo if L == 128 else lo | (f(y1 >> 128, y2 >> 128) << 128)), rax, mx
    return rule(form, L, y1, y2, y3, mx, rax)


def w_maddwd_sat(form, L, y1, y2, y3, mx, rax):
    """(d) vpmaddwd saturating where it wraps: the all-8000H pair reads 7FFFFFFFH instead of 80000000H."""
    if form == "vpmaddwd":
        def f(a, b):
            return of_els([sat(sx(el(a, 16, 2 * i), 16) * sx(el(b, 16, 2 * i), 16)
                               + sx(el(a, 16, 2 * i + 1), 16) * sx(el(b, 16, 2 * i + 1), 16), 32) for i in range(4)], 32)
        lo = f(y1 & M128, y2 & M128)
        return (lo if L == 128 else lo | (f(y1 >> 128, y2 >> 128) << 128)), rax, mx
    return rule(form, L, y1, y2, y3, mx, rax)


WRONG = [   # (letter, label, rule, the row `build` must name on refusing it) — the rows are FILLED IN by the first
    # --refuse-wrong run and then fixed here, so a later change to the case order that moves a refusal is a red
    ("a", "vpmaddubsw with the signedness of its two sources swapped", w_ubsw_swapped, "vpmaddubsw128_edge0"),
    ("b", "vpackssdw at VEX.256 packed across lanes", w_pack_across, "vpackssdw256_edge0"),
    ("c", "vpmulhrsw without its rounding increment", w_mulhrsw_trunc, "vpmulhrsw128_edge0"),
    ("d", "vpmaddwd saturating where it wraps", w_maddwd_sat, "vpmaddwd128_edge0"),
]


def m_keep_upper(form, L, y1, y2, y3, mx, rax):
    """(reach only) D348's VEX.128 red-backwards mutant: the destination's upper half preserved."""
    d, r, m = rule(form, L, y1, y2, y3, mx, rax)
    if L == 128:
        d |= y3 >> 128 << 128
    return d, r, m


def m_copy_low(form, L, y1, y2, y3, mx, rax):
    """(reach only) D348's VEX.256 red-backwards mutant: the low lane's result copied into the high lane."""
    d, r, m = rule(form, L, y1, y2, y3, mx, rax)
    if L == 256:
        d = (d & M128) | ((d & M128) << 128)
    return d, r, m


MUTANTS = [("VEX.128 upper half preserved (D348 red-backwards)", m_keep_upper),
           ("VEX.256 low lane copied into the high lane (D348 red-backwards)", m_copy_low)]


# ── THE TEXTBOOK: the SDM's flat pseudo-code over byte strings ──────────────────────────────────────────────────────

def tb_bytes(v, n=32):
    return list((v & ((1 << (8 * n)) - 1)).to_bytes(n, "little"))


def tb_int(bs):
    return int.from_bytes(bytes(bs), "little")


def tb_chunks(v, size, n=32):
    bs = tb_bytes(v, n)
    return [bs[i:i + size] for i in range(0, n, size)]


def tb_s(chunk):
    return int.from_bytes(bytes(chunk), "little", signed=True)


def tb_u(chunk):
    return int.from_bytes(bytes(chunk), "little", signed=False)


def tb_out(x, size):
    return list((x % (1 << (8 * size))).to_bytes(size, "little"))


def tb_satw(x):
    return 32767 if x > 32767 else (-32768 if x < -32768 else x)


def textbook(form, L, y1, y2, y3, mx, rax):
    """The SDM's pseudo-code read flat over the 32 bytes of each register -> (YMM3, RAX, MXCSR)."""
    nb = L // 8                              # the bytes the form writes
    out = []
    if form == "vpmaddwd":                   # DEST[31:0] := SRC1[15:0]*SRC2[15:0] + SRC1[31:16]*SRC2[31:16], ...
        A, B = tb_chunks(y1, 2), tb_chunks(y2, 2)
        for j in range(nb // 4):
            out.append(tb_out(tb_s(A[2 * j]) * tb_s(B[2 * j]) + tb_s(A[2 * j + 1]) * tb_s(B[2 * j + 1]), 4))
    elif form == "vpmulhrsw":                # temp := ((SRC1 * SRC2) >> 14) + 1; DEST := temp[16:1]
        A, B = tb_chunks(y1, 2), tb_chunks(y2, 2)
        for j in range(nb // 2):
            temp = (tb_s(A[j]) * tb_s(B[j])) // (1 << 14) + 1
            out.append(tb_out((temp % (1 << 32)) >> 1, 2))
    elif form == "vpmaddubsw":               # SaturateToSignedWord(SRC2[15:8]*SRC1[15:8] + SRC2[7:0]*SRC1[7:0])
        A, B = tb_chunks(y1, 1), tb_chunks(y2, 1)
        for j in range(nb // 2):
            out.append(tb_out(tb_satw(tb_s(B[2 * j + 1]) * tb_u(A[2 * j + 1]) + tb_s(B[2 * j]) * tb_u(A[2 * j])), 2))
    elif form == "vpackssdw":                # per 128-bit lane: SRC1's four dwords, then SRC2's
        A, B = tb_chunks(y1, 4), tb_chunks(y2, 4)
        for lane in range(L // 128):
            for src in (A, B):
                for x in src[4 * lane:4 * lane + 4]:
                    out.append(tb_out(tb_satw(tb_s(x)), 2))
    else:
        raise SystemExit("mk_vexsilb_rows: no textbook for %s" % form)
    flat = []
    for c in out:
        flat += c
    dest = tb_int(flat)
    if L == 128:
        dest = tb_int(tb_bytes(dest, 16) + [0] * 16)        # VEX.128: bytes 31:16 := 0
    return dest, rax, mx


# ── the rows ────────────────────────────────────────────────────────────────────────────────────────────────────────

def lane_marker(seed):
    """Two sources whose LOW and HIGH lanes are unrelated and both non-degenerate, so a rule that mixes lanes or copies
    one into the other disagrees."""
    r = random.Random(seed)
    return r.getrandbits(256) | (1 << 255) | (1 << 127), r.getrandbits(256) | (1 << 200) | (1 << 72)


def cases_for(form, L, rng):
    """(name, y1 data, y2 data) — the data over 256 bits; the caller seeds what L does not read."""
    out = []
    if form == "vpmaddwd":
        out.append(("edge0", of_els([0x8000] * 16, 16), of_els([0x8000] * 16, 16)))         # the wrap, every dword
        out.append(("edge1", of_els([0x7fff] * 16, 16), of_els([0x7fff] * 16, 16)))
        out.append(("edge2", of_els([0x8000, 0x7fff, 0xffff, 0x0001] * 4, 16),
                    of_els([0x7fff, 0x8000, 0xffff, 0x8000] * 4, 16)))
        out.append(("zero", 0, of_els([0x8000] * 16, 16)))
    elif form == "vpmulhrsw":
        out.append(("edge0", of_els([0x8000, 0x7fff, 0x0001, 0xffff, 0x4000, 0xc000, 0x0001, 0x2000] * 2, 16),
                    of_els([0x8000, 0x7fff, 0x4000, 0xffff, 0x4000, 0x4000, 0xc000, 0x0003] * 2, 16)))
        out.append(("edge1", of_els([0x0001] * 16, 16), of_els([0x2000, 0x1fff, 0x6000, 0xe000] * 4, 16)))
        out.append(("zero", 0, of_els([0x8000] * 16, 16)))
    elif form == "vpmaddubsw":
        out.append(("edge0", of_els([0xff] * 32, 8), of_els([0x7f] * 32, 8)))                 # +saturation
        out.append(("edge1", of_els([0xff] * 32, 8), of_els([0x80] * 32, 8)))                 # -saturation
        out.append(("edge2", of_els([0x80, 0x01] * 16, 8), of_els([0x01, 0x80] * 16, 8)))     # the asymmetry
        out.append(("edge3", of_els([0x7f] * 32, 8), of_els([0xff] * 32, 8)))
    elif form == "vpackssdw":
        sats = [0x00007fff, 0x00008000, 0xffff8000, 0xffff7fff, 0x80000000, 0x7fffffff, 0x00000000, 0xffffffff]
        out.append(("edge0", of_els(sats, 32), of_els(sats[::-1], 32)))
        out.append(("edge1", of_els([0x00010000, 0xfffeffff, 0x00000001, 0x00007ffe] * 2, 32),
                    of_els([0x12345678, 0xedcba988, 0x00004000, 0xffffc000] * 2, 32)))
    else:
        raise SystemExit("mk_vexsilb_rows: no cases for %s" % form)
    out.append(("lane",) + lane_marker(348900 + FORMS.index(form)))
    for i in range(4):
        out.append(("rand%d" % i, rng.getrandbits(256), rng.getrandbits(256)))
    return out


ROWS = []   # (name, fn, form, L, y1, y2, y3, imm, f, mx, rax, w3, wrax, wmx)


class Refused(SystemExit):
    def __init__(self, row, msg):
        super().__init__(msg)
        self.row = row


def ymm(lo, hi):
    return (lo & M128) | ((hi & M128) << 128)


def build(rl=None):
    """Build every row. `rl` substitutes the rule; a row where the rule and the textbook differ REFUSES the build."""
    rl = rl or rule
    ROWS.clear()
    for k, (fn, form, L, _bs, imm) in enumerate(OPS):
        rng = random.Random(348000 + k)
        for i, (nm, a, b) in enumerate(cases_for(form, L, rng)):
            hi1, hi2 = rng.getrandbits(128) | 1, rng.getrandbits(128) | 1
            y3 = rng.getrandbits(256) | (1 << 128) | 1
            rax = rng.getrandbits(64) | (1 << 63)
            if L == 128:
                y1, y2 = ymm(a, hi1), ymm(b, hi2)
            else:
                y1, y2 = a & M256, b & M256
            mx = 0x1f80 | ((i % 4) << 13)
            f = ARITH if i % 2 else 0
            name = "%s_%s" % (fn[2:], nm)
            got = rl(form, L, y1, y2, y3, mx, rax)
            want = textbook(form, L, y1, y2, y3, mx, rax)
            if got != want:
                raise Refused(name, "mk_vexsilb_rows: ⛔ row %s: the RULE gives ymm3 %064x, the TEXTBOOK ymm3 %064x — "
                              "the rule's reading of the SDM is wrong, or the textbook is" % (name, got[0], want[0]))
            ROWS.append((name, fn, form, L, y1, y2, y3, imm, f, mx, rax, got[0], got[1], got[2]))


def q4(v):
    return ", ".join("0x%016xULL" % ((v >> (64 * i)) & M64) for i in range(4))


def wrong_reach(rl):
    """{form+L: (disagreeing rows, rows)} for a substitute rule, over the built rows."""
    out = {}
    for name, _fn, form, L, y1, y2, y3, _imm, _f, mx, rax, w3, wrax, wmx in ROWS:
        key = form + str(L)
        n, t = out.get(key, (0, 0))
        out[key] = (n + (rl(form, L, y1, y2, y3, mx, rax) != (w3, wrax, wmx)), t + 1)
    return out


def refusals(quiet=False):
    """Build under each wrong rule; each must be REFUSED on its named row. Returns the number that were NOT."""
    missed = 0
    for letter, label, rl, row in WRONG:
        try:
            build(rl)
        except Refused as e:
            if e.row == row:
                if not quiet:
                    print("  ✔ (%s) refused on %s — %s:\n      %s" % (letter, e.row, label, str(e)))
                continue
            if not quiet:
                print("  ✖ (%s) refused on %s, NOT on its named row %s — %s" % (letter, e.row, row, label))
            missed += 1
            continue
        missed += 1
        if not quiet:
            print("  ✖ (%s) NOT refused — %s" % (letter, label))
    build()
    return missed


def selftest():
    bad = 0

    def say(ok, msg):
        nonlocal bad
        print(("  ✔ " if ok else "  ✖ ") + msg)
        bad += not ok

    # hand-derived lanes, stated from the SDM's definitions and not by either reference: (form, A, B, DEST), 128 bits
    hand = [
        ("vpmaddwd", of_els([0x8000] * 8, 16), of_els([0x8000] * 8, 16), of_els([0x80000000] * 4, 32)),
        ("vpmaddwd", of_els([0x7fff] * 8, 16), of_els([0x7fff] * 8, 16), of_els([0x7ffe0002] * 4, 32)),
        ("vpmaddwd", of_els([0xffff, 0x0002] * 4, 16), of_els([0x0003, 0xffff] * 4, 16), of_els([0xfffffffb] * 4, 32)),
        ("vpmulhrsw", of_els([0x8000] * 8, 16), of_els([0x8000] * 8, 16), of_els([0x8000] * 8, 16)),
        ("vpmulhrsw", of_els([0x4000] * 8, 16), of_els([0x4000] * 8, 16), of_els([0x2000] * 8, 16)),
        ("vpmulhrsw", of_els([0x0001] * 8, 16), of_els([0x4000] * 8, 16), of_els([0x0001] * 8, 16)),
        ("vpmulhrsw", of_els([0x0001] * 8, 16), of_els([0x3fff] * 8, 16), of_els([0x0000] * 8, 16)),
        ("vpmulhrsw", of_els([0xffff] * 8, 16), of_els([0x4000] * 8, 16), of_els([0x0000] * 8, 16)),
        ("vpmaddubsw", of_els([0xff] * 16, 8), of_els([0x7f] * 16, 8), of_els([0x7fff] * 8, 16)),
        ("vpmaddubsw", of_els([0xff] * 16, 8), of_els([0x80] * 16, 8), of_els([0x8000] * 8, 16)),
        ("vpmaddubsw", of_els([0x80, 0x01] * 8, 8), of_els([0x01, 0x80] * 8, 8), of_els([0x0000] * 8, 16)),
        ("vpmaddubsw", of_els([0x02, 0x00] * 8, 8), of_els([0xff, 0x00] * 8, 8), of_els([0xfffe] * 8, 16)),
        ("vpackssdw", of_els([0x00007fff, 0x00008000, 0xffff8000, 0xffff7fff], 32),
         of_els([0x80000000, 0x7fffffff, 0, 0xffffffff], 32),
         of_els([0x7fff, 0x7fff, 0x8000, 0x8000, 0x8000, 0x7fff, 0x0000, 0xffff], 16)),
    ]
    hb = 0
    for form, a, b, d in hand:
        r = rule(form, 128, a, b, 0, 0x1f80, 0)[0]
        t = textbook(form, 128, a, b, 0, 0x1f80, 0)[0]
        if not (r == t == d):
            hb += 1
            print("      ✖ %s %032x %032x: rule %032x textbook %032x want %032x" % (form, a, b, r, t, d))
    say(hb == 0, "%d hand-derived 128-bit cases (the PMADDWD wrap, PMULHRSW's rounding and its 8000H·8000H, "
        "PMADDUBSW's two saturations and its operand asymmetry, PACKSSDW's edges): both references agree with each"
        % len(hand))
    # the two references against each other over a sweep of random 256-bit operands at both lengths
    rng = random.Random(348999)
    nsweep, ndiff = 0, 0
    for i in range(4000):
        form = FORMS[i % 4]
        L = 128 if i % 8 < 4 else 256
        a, b = rng.getrandbits(256), rng.getrandbits(256)
        nsweep += 1
        if rule(form, L, a, b, 0, 0x1f80, 0) != textbook(form, L, a, b, 0, 0x1f80, 0):
            ndiff += 1
    say(ndiff == 0, "the per-lane rule and the flat textbook agree on %d swept random operand pairs" % nsweep)
    build()
    say(len(ROWS) > 0, "%d rows built, every one equal under the rule and the textbook" % len(ROWS))
    say(refusals(quiet=True) == 0, "each of the %d wrong rules (a)-(d) is REFUSED on its named row" % len(WRONG))
    # each red-backwards mutant reds EXACTLY the rows it reaches, derived from the rows rather than declared:
    # keep-upper reaches every VEX.128 row (YMM3's upper half is seeded non-zero on all of them); copy-low reaches
    # exactly the VEX.256 rows whose two expected lanes differ (an all-8000H row has equal lanes and is unreachable)
    reaches = {m_keep_upper: {r[0] for r in ROWS if r[3] == 128},
               m_copy_low: {r[0] for r in ROWS if r[3] == 256 and (r[11] >> 128) != (r[11] & M128)}}
    for label, rl in MUTANTS:
        hit = {r[0] for r in ROWS if rl(r[2], r[3], r[4], r[5], r[6], r[9], r[10]) != (r[11], r[12], r[13])}
        say(hit == reaches[rl] and len(hit) > 0, "the mutant '%s' disagrees on exactly the %d rows it reaches, and on "
            "no other" % (label, len(hit)))
    pk = [r for r in ROWS if r[0] == PLANT_ROW]
    say(len(pk) == 1 and pk[0][3] == 256, "--plant's row %s exists once and is a VEX.256 row" % PLANT_ROW)
    ph = [r for r in ROWS if r[0] == PLANT_HI]
    say(len(ph) == 1 and ph[0][3] == 128 and (ph[0][6] >> 128) != 0 and ph[0][11] >> 128 == 0,
        "--plant-hi's row %s exists once, is VEX.128, its YMM3 upper half seeded non-zero and expected zero" % PLANT_HI)
    say(all((r[6] >> 128) != 0 for r in ROWS), "every row seeds YMM3's upper half non-zero")
    say(all((r[4] >> 128) != 0 and (r[5] >> 128) != 0 for r in ROWS if r[3] == 128),
        "every VEX.128 row seeds YMM1's and YMM2's upper halves non-zero")
    say(all(r[11] >> 128 == 0 for r in ROWS if r[3] == 128), "every VEX.128 row expects YMM3[255:128] = 0")
    say(all((r[11] >> 128) != (r[11] & M128) for r in ROWS if r[3] == 256 and r[0].endswith("_lane")),
        "every VEX.256 lane-marker row expects different results in its two lanes")
    say({(r[2], r[3]) for r in ROWS} == set(ENC), "the rows cover exactly the 4 mnemonics and the %d encodings, each "
        "at both lengths" % len(ENC))
    say(all(r[12] == r[10] and r[13] == r[9] for r in ROWS), "every row expects RAX and MXCSR unchanged")
    print("✅ mk_vexsilb_rows selftest" if not bad else "⛔ mk_vexsilb_rows selftest FAILED")
    return 1 if bad else 0


def main():
    P.strict_flags(__file__)
    if "--selftest" in sys.argv:
        return selftest()
    if "--refuse-wrong" in sys.argv:
        m = refusals()
        print("wrong rules refused %d of %d" % (len(WRONG) - m, len(WRONG)))
        return 1 if m else 0
    build()
    if "--summary" in sys.argv:
        for form in FORMS:
            for L in (128, 256):
                print("%-12s VEX.%d %4d" % (form, L, sum(1 for r in ROWS if r[2] == form and r[3] == L)))
        print("rows %d functions %d encodings %d" % (len(ROWS), len(OPS), len(ENC)))
        return 0
    if "--reach" in sys.argv:
        bad = 0
        for label, rl in [(w[1], w[2]) for w in WRONG] + MUTANTS:
            print(label)
            reach = wrong_reach(rl)
            for key, (n, t) in sorted(reach.items()):
                if n:
                    print("  %-16s disagrees on %3d of %3d rows" % (key, n, t))
            bad += sum(n for n, _t in reach.values()) == 0
        return 1 if bad else 0
    plant, plant_hi = "--plant" in sys.argv, "--plant-hi" in sys.argv
    print("/* GENERATED by hwprobe/mk_vexsilb_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    for fn, _f, _L, _b, _i in OPS:
        print("void %s(struct xio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const struct xrow XROWS[] = {")
    for name, fn, form, L, y1, y2, y3, _imm, f, mx, rax, w3, wrax, wmx in ROWS:
        if plant and name == PLANT_ROW:
            w3 ^= 1 << 128         # the control: one expectation made wrong on purpose, in the HIGH lane
        if plant_hi and name == PLANT_HI:
            w3 |= y3 >> 128 << 128  # the control: the VEX.128 destination's upper half NOT zeroed
        print('  {"%s", %s, {%s}, {%s}, {%s}, 0x%03x, 0x%04x, 0x%016xULL, {%s}, 0x%016xULL, 0x%04x},' % (
            name, fn, q4(y1), q4(y2), q4(y3), f, mx, rax, q4(w3), wrax, wmx))
    print("};")
    print("static const struct xop XOPS[] = {")
    for i, (fn, _f, _L, bs, _imm) in enumerate(OPS):
        bb = bytearray.fromhex(bs)
        if "--plant-op" in sys.argv and i == 0:
            bb[-1] ^= 0x01         # the control: the declared instruction is not the one in vexsilb_ops.S
        print('  {"%s", %s_at, %d, {%s}},' % (fn, fn, len(bb), ", ".join("0x%02x" % x for x in bb)))
    print("};")
    return 0


if __name__ == "__main__":
    sys.exit(main())
