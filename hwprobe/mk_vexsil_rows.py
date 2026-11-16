#!/usr/bin/env python3
"""hwprobe/mk_vexsil_rows.py — D345 (V7): the VEX.128 and VEX.256 twins of eleven main-table forms, the rows the x86-64
referee runs, with expectations DERIVED HERE.

The forms (register forms only; ACL2 x86isa refuses all 26 encodings, D345 P1):
  vshufps imm · vpsrad xmm · vpsrad imm · vpsraw xmm · vpsraw imm · vaddps · vsubps · vmulps · vpunpcklwd ·
  vpunpckhwd · vpunpcklbw · vpackuswb · vpmovmskb           each at VEX.128 (xmm) and at VEX.256 (ymm)
An eighth path, beside the SSE soft-float, integer, bit-string, shuffle, packed-integer, SHA-NI and AES/VEX ones,
sharing nothing with them: `vexsil_ops.S` (one function per form, length and imm8), `vexsil_probe.c`, and this file.

Every expected value comes from a stated rule in this file (SDM Vol. 2B SHUFPS, PSRAW/PSRAD, ADDPS, SUBPS, MULPS,
PUNPCKLBW/PUNPCKLWD, PUNPCKHWD, PACKUSWB, PMOVMSKB; Vol. 1 §4.8, §4.9 and §11.5 for the floating-point results and
exceptions), never from ACL2 x86isa and never from x86lean. Element i of a vector is bits w(i+1)-1 : wi.

THE RULES (`rule` below). A, B are SRC1 (VEX.vvvv) and SRC2 (ModRM.rm); the 128-bit function F is the legacy one.
  VEX.128      DEST[127:0] := F(A[127:0], B[127:0]);  DEST[255:128] := 0          (the VEX.128 zeroing)
  VEX.256      DEST[127:0] := F(A[127:0], B[127:0]);  DEST[255:128] := F(A[255:128], B[255:128])   (per lane)
  SHUFPS       per lane: D0 := A[imm[1:0]], D1 := A[imm[3:2]], D2 := B[imm[5:4]], D3 := B[imm[7:6]] (dwords) — at
               VEX.256 the SAME imm8 selects WITHIN each 128-bit lane (the high lane's selectors index the high lane)
  PSRAD/PSRAW  each dword (word) of A arithmetically shifted right by COUNT; COUNT > 31 (> 15) fills each element with
               its sign bit. xmm-count form: COUNT := B[63:0], UNSIGNED, the ONE count for every element of EVERY lane
               at both lengths (the count register is an xmm even at VEX.256; B[127:64] and B[255:128] are not read).
               imm8 form: COUNT := imm8 (VEX.vvvv is the destination; ModRM.rm the source).
  ADDPS/SUBPS/MULPS   per dword lane, IEEE 754 binary32 A op B rounded by MXCSR.RC (00 nearest-even, 01 down,
               10 up, 11 zero), FTZ = DAZ = 0, every exception MASKED (0x1F80): MXCSR's six sticky flags are the OR
               over ALL lanes (four at VEX.128, EIGHT at VEX.256) of each lane's flags:
    NAN        a NaN operand: the result is SRC1's NaN if SRC1 is a NaN, else SRC2's, quieted (bit 22 set);
               IE iff either operand is an SNaN; NO DE (a NaN operand withholds the denormal flag in its lane)
    INVALID    inf - inf (after SUBPS's sign flip) and 0 × inf: the QNaN indefinite 0xFFC00000 and IE alone
    DE         an operand that is a denormal (exponent 0, fraction ≠ 0), also beside an infinity or a zero
    ZERO-SUM   an exact zero sum is +0, or -0 under RC = down; x + y with both zeros of the SAME sign keeps that sign
    OE         a rounded result ≥ 2^128: OE|PE, and ∞ (nearest; up for +; down for -) or ±MAX (zero; the other)
    UE         TINY-AFTER: the exact result rounded to 24 bits with an UNBOUNDED exponent is below 2^-126; masked, UE
               is raised only when the result is ALSO inexact (an exact tiny result raises nothing); the delivered
               result is the subnormal (or zero) rounded at the subnormal precision
    PE         the delivered result differs from the exact one
               (add/sub never raise UE: a tiny sum of two binary32 values is exact)
  PUNPCKLBW/LWD per lane: DEST element 2i := A element i, 2i+1 := B element i, for i < half the lane's elements
  PUNPCKHWD    the same from the HIGH half of each lane's words
  PACKUSWB     per lane: bytes 7:0 := A's eight words, bytes 15:8 := B's, each signed word saturated to 0..255
  PMOVMSKB     the GPR destination: bit i := bit 7 of A's byte i, i < 16 (VEX.128) or < 32 (VEX.256) — bits 15:0 from
               the low lane, 31:16 from the high lane — and every other bit of the 64-bit register ZERO. No vector
               register is written.
  NO-OTHERS    "Flags Affected: None"; MXCSR unchanged by the integer forms; SRC1, SRC2 unchanged; RAX unchanged
               except by vpmovmskb, and the destination YMM3 unchanged by vpmovmskb.

AMBIGUITIES, resolved by the SDM's pseudo-code reading (each is a rule above, and each is what a row reads):
  (1) PSRAD/PSRAW xmm count at VEX.256: the pseudo-code takes COUNT from SRC2[63:0] once, and applies it to both
      lanes ("VPSRAD (VEX.256 version) … ARITHMETIC_RIGHT_SHIFT_DWORDS_256b(SRC1, SRC2)" with COUNT := SRC2[63:0]).
  (2) the count is UNSIGNED 64-bit: a count with bit 63 set saturates (the pseudo-code's "IF (COUNT > 31)").
  (3) the FP rules NAN, DE-beside-inf/zero, ZERO-SUM and TINY-AFTER are the readings mk_rows.py's B5 rows (the legacy
      packed twins) were refereed on; they are restated, not imported, and this file's rows ask them of every lane.
  (4) VPMOVMSKB with a 32-bit GPR operand (clang's `%eax`) writes the whole 64-bit register, upper 32 bits zero.

THE PROBE'S REGISTERS (`vexsil_ops.S`): YMM1 = SRC1 (VEX.vvvv; the shifted source of an imm8 shift; the mask source),
YMM2 = SRC2 (ModRM.rm; the count register), YMM3 = DEST, RAX = vpmovmskb's DEST, MXCSR loaded from the row. All three YMM
registers are loaded WHOLE (every upper half seeded random and non-zero at VEX.128; at VEX.256 the sources' upper halves
are the high lane's data) and read back whole; MXCSR and RAX are read back after the instruction.

⭐ THE TEXTBOOKS, AND WHY EVERY ROW HAS ONE. A misread lane rule is a consistent mistake: a rule written with it and rows
derived from it agree. So every row is computed TWICE — by `rule` (128-bit integer bit operations; floating point by
EXACT RATIONALS, fractions.Fraction, floored onto the result's ulp grid) and by `textbook` (the SDM's flat
element-by-element pseudo-code over byte strings, `int.from_bytes(signed=True)` and floor division for the shifts, and
floating point by INTEGER significands with explicit round and sticky bits) — and `build` REFUSES any row where they
differ. `--selftest` also holds both FP references to the host's IEEE binary32 (`struct.pack('<f')`) on products and
exactly-representable sums under round-to-nearest, a third source.

THE ROW POPULATION (flags in: all six clear on even rows, all six set on odd ones; MXCSR.RC rotates by row):
  vshufps      imm8 ∈ {00 1b 4e b1 e4 93 39 ff 72 d8} × 2 (marker dwords, random)
  vpsra[dw] x  the counts {0 1 5 w-1 w w+1 31 32 33 63 64 255 256 2^32 2^32+1 2^63 2^64-1} × 2 data (edge, random);
               B[127:64] and B[255:128] always random non-zero (never read)
  vpsra[dw] i  imm8 ∈ {0 1 7 15 16 17 31 32 255} × 2
  vaddps/vsubps/vmulps  the special-lane cases (NaN, SNaN, ∞, invalid, signed zeros, denormals, overflow, underflow,
               tininess-after, ties, inexact) packed into lanes under EACH rounding mode; at VEX.256 one row per flag
               raised in the HIGH lane alone (and one in the low lane alone); at VEX.128 one per flag in lane 3 alone;
               random rows (raw words and near-exponent normals) under every mode
  vpunpck*, vpackuswb   marker bytes, saturation edges, 4 random
  vpmovmskb    all-zero, all-sign, alternating, one sign bit in each lane, 6 random
Random words from `random.Random(345000 + k)` (k the encoding's index), never re-seeded.

Usage: mk_vexsil_rows.py [--plant | --plant-op | --plant-hi | --summary | --reach | --refuse-wrong | --selftest]
  --plant         flips bit 128 (the HIGH lane) of one VEX.256 row's expectation: exactly that row must disagree (exit 1)
  --plant-op      declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --plant-hi      one VEX.128 row's expectation keeps the destination's upper half instead of zeroing it: exactly that
                  row must disagree — the zeroing is compared, not assumed
  --summary       per-form row counts, not C
  --reach         per wrong rule, how many rows it disagrees on (0 would be a vacuous row set)
  --refuse-wrong  builds the rows under each wrong rule D345 names and shows `build` REFUSE it on its named row
  --selftest      the FP references against each other and the host, every row's two derivations, the refusals, plants
"""
import os
import random
import struct
import sys
from fractions import Fraction

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "scripts"))
import portable as P  # noqa: E402

ARITH = 0x8d5
M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
M128 = (1 << 128) - 1
M256 = (1 << 256) - 1
IE, DE, ZE, OE, UE, PE = 1, 2, 4, 8, 16, 32
FLAGNAMES = (("IE", IE), ("DE", DE), ("ZE", ZE), ("OE", OE), ("UE", UE), ("PE", PE))
MODES = ("nearest", "down", "up", "zero")       # MXCSR.RC 00 01 10 11

# Declared bytes: clang's assembly (`clang -target x86_64-unknown-linux-gnu -c`, read with `objdump -d`) of the
# `vexsil_ops.S` line; the probe refuses to run if they differ from the bytes at the function's `_at` label. An imm8
# form appends its imm8. ModRM da = reg xmm3, rm xmm2; e1 = /4, rm xmm1; c1 = reg eax, rm xmm1.
ENC = {
    ("vshufps", 128): "c5f0c6da", ("vshufps", 256): "c5f4c6da",
    ("vpsrad_x", 128): "c5f1e2da", ("vpsrad_x", 256): "c5f5e2da",
    ("vpsrad_i", 128): "c5e172e1", ("vpsrad_i", 256): "c5e572e1",
    ("vpsraw_x", 128): "c5f1e1da", ("vpsraw_x", 256): "c5f5e1da",
    ("vpsraw_i", 128): "c5e171e1", ("vpsraw_i", 256): "c5e571e1",
    ("vaddps", 128): "c5f058da", ("vaddps", 256): "c5f458da",
    ("vsubps", 128): "c5f05cda", ("vsubps", 256): "c5f45cda",
    ("vmulps", 128): "c5f059da", ("vmulps", 256): "c5f459da",
    ("vpunpcklwd", 128): "c5f161da", ("vpunpcklwd", 256): "c5f561da",
    ("vpunpckhwd", 128): "c5f169da", ("vpunpckhwd", 256): "c5f569da",
    ("vpunpcklbw", 128): "c5f160da", ("vpunpcklbw", 256): "c5f560da",
    ("vpackuswb", 128): "c5f167da", ("vpackuswb", 256): "c5f567da",
    ("vpmovmskb", 128): "c5f9d7c1", ("vpmovmskb", 256): "c5fdd7c1",
}
SHUF_IMMS = [0x00, 0x1b, 0x4e, 0xb1, 0xe4, 0x93, 0x39, 0xff, 0x72, 0xd8]
SHIFT_IMMS = [0, 1, 7, 15, 16, 17, 31, 32, 255]
FORMS = ["vshufps", "vpsrad_x", "vpsrad_i", "vpsraw_x", "vpsraw_i", "vaddps", "vsubps", "vmulps", "vpunpcklwd",
         "vpunpckhwd", "vpunpcklbw", "vpackuswb", "vpmovmskb"]
MNEMONICS = ["vshufps", "vpsrad", "vpsraw", "vaddps", "vsubps", "vmulps", "vpunpcklwd", "vpunpckhwd", "vpunpcklbw",
             "vpackuswb", "vpmovmskb"]
FP = ("vaddps", "vsubps", "vmulps")


def mnemonic(form):
    return form.split("_")[0]


OPS = []   # (fn, form, L, declared bytes hex, imm or None)
for _form in FORMS:
    for _L in (128, 256):
        if _form == "vshufps":
            for _i in SHUF_IMMS:
                OPS.append(("x_vshufps%d_%02x" % (_L, _i), _form, _L, ENC[(_form, _L)] + "%02x" % _i, _i))
        elif _form.endswith("_i"):
            for _i in SHIFT_IMMS:
                OPS.append(("x_%s%d_i%d" % (mnemonic(_form), _L, _i), _form, _L, ENC[(_form, _L)] + "%02x" % _i, _i))
        elif _form.endswith("_x"):
            OPS.append(("x_%s%d_x" % (mnemonic(_form), _L), _form, _L, ENC[(_form, _L)], None))
        else:
            OPS.append(("x_%s%d" % (_form, _L), _form, _L, ENC[(_form, _L)], None))

PLANT_ROW = "vshufps256_1b_p0"       # --plant: bit 128 of its expectation
PLANT_HI = "vpackuswb128_edge0"      # --plant-hi: its expectation keeps YMM3's upper half


# ── THE RULE: 128-bit integer bit operations; floating point by exact rationals ────────────────────────────────────

def el(v, w, i):
    return (v >> (w * i)) & ((1 << w) - 1)


def of_els(xs, w):
    r = 0
    for i, x in enumerate(xs):
        r |= (x & ((1 << w) - 1)) << (w * i)
    return r


def r_shufps(a, b, imm):
    return of_els([el(a, 32, imm & 3), el(a, 32, (imm >> 2) & 3), el(b, 32, (imm >> 4) & 3),
                   el(b, 32, (imm >> 6) & 3)], 32)


def r_psra(a, count, w):
    c = min(count, w - 1)
    out = []
    for i in range(128 // w):
        x = el(a, w, i)
        top = x >> (w - 1)
        out.append(((x >> c) | ((((1 << c) - 1) << (w - c)) if top else 0)) & ((1 << w) - 1))
    return of_els(out, w)


def r_unpck(a, b, w, high):
    n = 64 // w
    base = n if high else 0
    out = []
    for i in range(n):
        out += [el(a, w, base + i), el(b, w, base + i)]
    return of_els(out, w)


def r_packuswb(a, b):
    def sat(x):
        return 0 if x & 0x8000 else (0xff if x > 0xff else x)
    return of_els([sat(el(a, 16, i)) for i in range(8)] + [sat(el(b, 16, i)) for i in range(8)], 8)


def r_pmovmskb(a):
    return sum(((el(a, 8, i) >> 7) & 1) << i for i in range(16))


# binary32 by exact rationals
QNAN_BIT, INF32, SIGN32, INDEF = 0x00400000, 0x7f800000, 0x80000000, 0xffc00000
MAX32 = 0x7f7fffff


def f_kind(x):
    e, m = (x >> 23) & 0xff, x & 0x7fffff
    if e == 0xff:
        return "inf" if m == 0 else ("qnan" if m & QNAN_BIT else "snan")
    if e == 0:
        return "zero" if m == 0 else "den"
    return "norm"


def f_val(x):
    e, m = (x >> 23) & 0xff, x & 0x7fffff
    v = Fraction(m, 1 << 149) if e == 0 else Fraction((1 << 23) | m) * Fraction(2) ** (e - 150)
    return -v if x & SIGN32 else v


def flog2(v):
    k = v.numerator.bit_length() - v.denominator.bit_length()
    if Fraction(2) ** k > v:
        k -= 1
    return k


def f_onto(rc, neg, mag, q):
    """mag rounded onto the grid 2^q at mode rc (the sign `neg` decides directed modes). Returns (value, inexact)."""
    unit = Fraction(2) ** q
    n = mag / unit
    fl = n.numerator // n.denominator
    frac = n - fl
    if frac == 0:
        up = False
    elif rc == "nearest":
        up = frac > Fraction(1, 2) or (frac == Fraction(1, 2) and fl % 2 == 1)
    elif rc == "zero":
        up = False
    elif rc == "down":
        up = neg
    else:
        up = not neg
    return (fl + (1 if up else 0)) * unit, frac != 0


def f_round(rc, v):
    """A non-zero exact v as binary32: (bits, inexact, overflow, tiny-after)."""
    neg = v < 0
    mag = -v if neg else v
    k = flog2(mag)
    r, inexact = f_onto(rc, neg, mag, max(k - 23, -149))
    ru, _ = f_onto(rc, neg, mag, k - 23)
    tiny = ru < Fraction(2) ** -126
    sgn = SIGN32 if neg else 0
    if r >= Fraction(2) ** 128:
        away = rc == "nearest" or (rc == "up" and not neg) or (rc == "down" and neg)
        return sgn | (INF32 if away else MAX32), True, True, False
    if r == 0:
        return sgn, inexact, False, tiny
    k2 = flog2(r)
    if k2 < -126:
        q = r * Fraction(2) ** 149
        return sgn | int(q), inexact, False, tiny
    q = r / Fraction(2) ** (k2 - 23)
    return sgn | ((k2 + 127) << 23) | (int(q) - (1 << 23)), inexact, False, tiny


def r_fp_lane(op, rc, a, b):
    ka, kb = f_kind(a), f_kind(b)
    if ka in ("qnan", "snan") or kb in ("qnan", "snan"):
        res = (a if ka in ("qnan", "snan") else b) | QNAN_BIT
        return res, IE if "snan" in (ka, kb) else 0
    den = DE if "den" in (ka, kb) else 0
    sa, sb = a & SIGN32, b & SIGN32
    if op == "mul":
        sg = sa ^ sb
        if {ka, kb} == {"inf", "zero"}:
            return INDEF, IE
        if "inf" in (ka, kb):
            return sg | INF32, den
        if "zero" in (ka, kb):
            return sg, den
        v = f_val(a) * f_val(b)
    else:
        if op == "sub":
            sb ^= SIGN32
        if ka == "inf" and kb == "inf":
            return (sa | INF32, 0) if sa == sb else (INDEF, IE)
        if ka == "inf":
            return sa | INF32, den
        if kb == "inf":
            return sb | INF32, den
        v = f_val(a) + (f_val(b) if op == "add" else -f_val(b))
        if v == 0:
            if ka == "zero" and kb == "zero" and sa == sb:
                return sa, den
            return (SIGN32 if rc == "down" else 0), den
    bits, inexact, ovf, tiny = f_round(rc, v)
    if ovf:
        return bits, den | OE | PE
    if inexact:
        return bits, den | PE | (UE if tiny else 0)
    return bits, den


def r_fp128(op, rc, a, b):
    r, f = 0, 0
    for i in range(4):
        v, g = r_fp_lane(op, rc, el(a, 32, i), el(b, 32, i))
        r |= v << (32 * i)
        f |= g
    return r, f


def rc_of(mx):
    return MODES[(mx >> 13) & 3]


def lane128(form, a, b, imm, rc):
    """The legacy 128-bit function: (DEST[127:0], MXCSR flags)."""
    mn = mnemonic(form)
    if mn == "vshufps":
        return r_shufps(a, b, imm), 0
    if form in ("vpsrad_i", "vpsraw_i"):
        return r_psra(a, imm, 32 if mn == "vpsrad" else 16), 0
    if form in ("vaddps", "vsubps", "vmulps"):
        return r_fp128(form[1:4], rc, a, b)
    if mn == "vpunpcklwd":
        return r_unpck(a, b, 16, False), 0
    if mn == "vpunpckhwd":
        return r_unpck(a, b, 16, True), 0
    if mn == "vpunpcklbw":
        return r_unpck(a, b, 8, False), 0
    if mn == "vpackuswb":
        return r_packuswb(a, b), 0
    raise SystemExit("mk_vexsil_rows: no 128-bit rule for %s" % form)


def rule(form, L, y1, y2, y3, imm, mx, rax):
    """The SDM rule over the whole machine state the probe reads -> (YMM3, RAX, MXCSR's six sticky flags)."""
    rc = rc_of(mx)
    if form == "vpmovmskb":
        m = r_pmovmskb(y1 & M128)
        if L == 256:
            m |= r_pmovmskb(y1 >> 128) << 16
        return y3, m, 0
    if form in ("vpsrad_x", "vpsraw_x"):
        w = 32 if form == "vpsrad_x" else 16
        count = y2 & M64
        lo = r_psra(y1 & M128, count, w)
        hi = r_psra(y1 >> 128, count, w) if L == 256 else 0
        return lo | (hi << 128), rax, 0
    lo, f = lane128(form, y1 & M128, y2 & M128, imm, rc)
    if L == 128:
        return lo, rax, f                               # VEX.128: DEST[255:128] := 0
    hi, g = lane128(form, y1 >> 128, y2 >> 128, imm, rc)
    return lo | (hi << 128), rax, f | g


# ── THE WRONG RULES D345 NAMES, each a whole substitute for `rule`; `--refuse-wrong` shows `build` refuse each ────

def w_count_per_lane(form, L, y1, y2, y3, imm, mx, rax):
    """(a) the shift count taken per lane: each lane's count from the count register's own lane (bits 191:128 for the
    high lane) instead of B[63:0] for every lane."""
    if form in ("vpsrad_x", "vpsraw_x") and L == 256:
        w = 32 if form == "vpsrad_x" else 16
        return r_psra(y1 & M128, y2 & M64, w) | (r_psra(y1 >> 128, (y2 >> 128) & M64, w) << 128), rax, 0
    return rule(form, L, y1, y2, y3, imm, mx, rax)


def w_drop_hi_flags(form, L, y1, y2, y3, imm, mx, rax):
    """(b) the FP sticky flags of the high lane dropped at VEX.256."""
    d, r, f = rule(form, L, y1, y2, y3, imm, mx, rax)
    if form in FP and L == 256:
        f = lane128(form, y1 & M128, y2 & M128, imm, rc_of(mx))[1]
    return d, r, f


def w_mask_swapped(form, L, y1, y2, y3, imm, mx, rax):
    """(c) vpmovmskb's lanes swapped: the high lane's 16 bits in 15:0 and the low lane's in 31:16."""
    d, r, f = rule(form, L, y1, y2, y3, imm, mx, rax)
    if form == "vpmovmskb" and L == 256:
        r = (r >> 16) | ((r & 0xffff) << 16)
    return d, r, f


def w_shuf_across(form, L, y1, y2, y3, imm, mx, rax):
    """(d) vshufps's selectors applied ACROSS lanes: both destination lanes select from the LOW lane of the sources
    (the 2-bit selectors read as indices into the whole register's first four dwords)."""
    d, r, f = rule(form, L, y1, y2, y3, imm, mx, rax)
    if form == "vshufps" and L == 256:
        lo = r_shufps(y1 & M128, y2 & M128, imm)
        d = lo | (lo << 128)
    return d, r, f


WRONG = [   # (letter, label, rule, the row `build` must name on refusing it)
    ("a", "the shift count taken per lane, not from the count register's low 64 bits", w_count_per_lane,
     "vpsrad256_x_c0_edge"),
    ("b", "the FP sticky flags of the high lane dropped at VEX.256", w_drop_hi_flags, "vaddps256_hionly_IE"),
    ("c", "vpmovmskb's lanes swapped", w_mask_swapped, "vpmovmskb256_lo1"),
    ("d", "vshufps's immediate applied across lanes rather than within each", w_shuf_across, "vshufps256_00_p0"),
]


def m_keep_upper(form, L, y1, y2, y3, imm, mx, rax):
    """(reach only) D345's VEX.128 red-backwards mutant: the destination's upper half preserved."""
    d, r, f = rule(form, L, y1, y2, y3, imm, mx, rax)
    if L == 128 and form != "vpmovmskb":
        d |= y3 >> 128 << 128
    return d, r, f


def m_copy_low(form, L, y1, y2, y3, imm, mx, rax):
    """(reach only) D345's VEX.256 red-backwards mutant: the low lane's result copied into the high lane."""
    d, r, f = rule(form, L, y1, y2, y3, imm, mx, rax)
    if L == 256 and form != "vpmovmskb":
        d = (d & M128) | ((d & M128) << 128)
    return d, r, f


MUTANTS = [("VEX.128 upper half preserved (D345 red-backwards)", m_keep_upper),
           ("VEX.256 low lane copied into the high lane (D345 red-backwards)", m_copy_low)]


# ── THE TEXTBOOK: the SDM's flat pseudo-code over byte strings; FP by integer significands ─────────────────────────

def tb_bytes(v, n=32):
    return list((v & ((1 << (8 * n)) - 1)).to_bytes(n, "little"))


def tb_int(bs):
    return int.from_bytes(bytes(bs), "little")


def tb_chunks(v, size, n=32):
    bs = tb_bytes(v, n)
    return [bs[i:i + size] for i in range(0, n, size)]


def tb_join(chunks):
    out = []
    for c in chunks:
        out += c
    return tb_int(out)


def tb_signed(chunk):
    return int.from_bytes(bytes(chunk), "little", signed=True)


def tb_unsigned_bytes(x, size):
    return list((x % (1 << (8 * size))).to_bytes(size, "little"))


# binary32 by integer significands
def tb_unpack(x):
    s, e, m = x >> 31, (x >> 23) & 0xff, x & 0x7fffff
    if e == 255:
        return ("snan" if m and not (m >> 22) & 1 else "qnan" if m else "inf"), s, 0, 0
    if e == 0:
        return ("zero" if m == 0 else "sub"), s, m, -149
    return "fin", s, m + 0x800000, e - 150


def tb_shift_round(M, E, q, s, mode):
    """M·2^E onto the grid 2^q by integer shift with a round bit and a sticky remainder: (S, inexact)."""
    drop = q - E
    if drop <= 0:
        return M << (-drop), False
    S = M >> drop
    rem = M - (S << drop)
    half = 1 << (drop - 1)
    if rem == 0:
        inc = 0
    elif mode == 0:                                 # nearest-even
        inc = 1 if rem > half or (rem == half and S & 1) else 0
    elif mode == 1:                                 # down
        inc = s
    elif mode == 2:                                 # up
        inc = 1 - s
    else:
        inc = 0
    return S + inc, rem != 0


def tb_round(s, M, E, mode):
    """(bits, flags) for (-1)^s · M · 2^E, M > 0, all exceptions masked."""
    lead = M.bit_length() - 1 + E
    q_unbounded = lead - 23
    q = q_unbounded if q_unbounded > -149 else -149
    S, inexact = tb_shift_round(M, E, q, s, mode)
    if S == 1 << 24:
        S, q = S >> 1, q + 1
    if S and q + S.bit_length() - 1 >= 128:
        to_inf = mode == 0 or (mode == 2 and s == 0) or (mode == 1 and s == 1)
        return (s << 31) | (0x7f800000 if to_inf else 0x7f7fffff), OE | PE
    Su, _ = tb_shift_round(M, E, q_unbounded, s, mode)
    tiny = (q_unbounded + Su.bit_length() - 1) < -126
    if S == 0:
        bits = s << 31
    elif S < 1 << 23:
        bits = (s << 31) | S
    else:
        bits = (s << 31) | ((q + 150) << 23) | (S - (1 << 23))
    flags = (PE | (UE if tiny else 0)) if inexact else 0
    return bits, flags


def tb_fp(op, mode, a, b):
    """One lane, the SDM §4.9.2 precedence in order: SNaN invalid; QNaN operand; other invalid; denormal; result."""
    ka, sa, ma, ea = tb_unpack(a)
    kb, sb, mb, eb = tb_unpack(b)
    if op == "sub":
        sb ^= 1
    nans = [x for x, k in ((a, ka), (b, kb)) if k in ("snan", "qnan")]
    if nans:
        return nans[0] | 0x00400000, (IE if "snan" in (ka, kb) else 0)
    if op == "mul" and (("inf" in (ka, kb)) and ("zero" in (ka, kb))):
        return 0xffc00000, IE
    if op != "mul" and ka == kb == "inf" and sa != sb:
        return 0xffc00000, IE
    flags = DE if "sub" in (ka, kb) else 0
    if op == "mul":
        s = sa ^ sb
        if "inf" in (ka, kb):
            return (s << 31) | 0x7f800000, flags
        if "zero" in (ka, kb):
            return s << 31, flags
        bits, g = tb_round(s, ma * mb, ea + eb, mode)
        return bits, flags | g
    if ka == "inf":
        return (sa << 31) | 0x7f800000, flags
    if kb == "inf":
        return (sb << 31) | 0x7f800000, flags
    E = min(ea, eb)
    T = (-1) ** sa * (ma << (ea - E)) + (-1) ** sb * (mb << (eb - E))
    if T == 0:
        if ka == kb == "zero" and sa == sb:
            return sa << 31, flags
        return (0x80000000 if mode == 1 else 0), flags
    bits, g = tb_round(1 if T < 0 else 0, abs(T), E, mode)
    return bits, flags | g


def textbook(form, L, y1, y2, y3, imm, mx, rax):
    """The SDM's pseudo-code read flat over the 32 bytes of each register -> (YMM3, RAX, flags)."""
    mode = (mx >> 13) & 3
    nb = L // 8                              # the bytes the form writes
    mn = mnemonic(form)
    if mn == "vpmovmskb":
        src = tb_bytes(y1)
        mask = 0
        for i in range(nb):                  # bit i := SRC[8i+7]
            if src[i] >= 0x80:
                mask += 1 << i
        return y3, mask, 0                   # the 64-bit GPR: every bit above the mask is 0
    flags = 0
    if mn == "vshufps":
        A, B = tb_chunks(y1, 4), tb_chunks(y2, 4)
        out = []
        for j in range(nb // 4):
            lane, pos = j // 4, j % 4
            src = A if pos < 2 else B
            sel = (imm >> (2 * pos)) & 3
            out.append(src[4 * lane + sel])
    elif mn in ("vpsrad", "vpsraw"):
        size = 4 if mn == "vpsrad" else 2
        count = imm if form.endswith("_i") else tb_int(tb_bytes(y2)[0:8])
        if count > 8 * size - 1:
            count = 8 * size - 1
        out = [tb_unsigned_bytes(tb_signed(c) // (2 ** count), size) for c in tb_chunks(y1, size)[:nb // size]]
    elif form in FP:
        A, B = tb_chunks(y1, 4), tb_chunks(y2, 4)
        out = []
        for j in range(nb // 4):
            v, g = tb_fp(form[1:4], mode, tb_int(A[j]), tb_int(B[j]))
            out.append(tb_unsigned_bytes(v, 4))
            flags |= g
    elif mn in ("vpunpcklwd", "vpunpckhwd", "vpunpcklbw"):
        size = 1 if mn == "vpunpcklbw" else 2
        A, B = tb_chunks(y1, size), tb_chunks(y2, size)
        per = 16 // size                     # elements per 128-bit lane
        out = []
        for lane in range(L // 128):
            first = lane * per + (per // 2 if mn == "vpunpckhwd" else 0)
            for i in range(per // 2):
                out += [A[first + i], B[first + i]]
    elif mn == "vpackuswb":
        A, B = tb_chunks(y1, 2), tb_chunks(y2, 2)
        out = []
        for lane in range(L // 128):
            for src in (A, B):
                for x in src[8 * lane:8 * lane + 8]:
                    out.append([max(0, min(255, tb_signed(x)))])
    else:
        raise SystemExit("mk_vexsil_rows: no textbook for %s" % form)
    dest = tb_join(out)
    if L == 128:
        dest = tb_int(tb_bytes(dest, 16) + [0] * 16)        # VEX.128: bytes 31:16 := 0
    return dest, rax, flags


# ── the rows ────────────────────────────────────────────────────────────────────────────────────────────────────────

S1, S2, SH, S3 = 0x3f800000, 0x40000000, 0x3f000000, 0x40400000
QN, QN2, SN, SN2 = 0x7fc00000, 0xffc12345, 0x7f800001, 0xffa00000
INF, NINF, NZ, MINN, DEN, MIND = 0x7f800000, 0xff800000, 0x80000000, 0x00800000, 0x007fffff, 0x00000001

# per-lane (a, b) cases, every one a named SDM situation; the rows pack them into lanes in order
FP_CASES = {
    "add": [(S1, S1), (S1, 0x33800000), (S1, 0x33c00000), (MAX32, MAX32), (MAX32, 0x73000000), (INF, NINF),
            (QN, SN), (SN, S1), (S1, QN2), (DEN, DEN), (DEN, S1), (MIND, MIND | SIGN32), (NZ, NZ), (0, NZ),
            (INF, DEN), (QN, DEN), (S1, S1 | SIGN32), (0x3f800001, 0xb3800000), (MAX32 | SIGN32, 0xf3000000),
            (0x00800001, 0x80800000), (0x4b800000, 0x3f800001), (INF, INF), (NINF, S1), (0, DEN | SIGN32)],
    "sub": [(S1, S1), (S1, 0xb3800000), (MAX32, MAX32 | SIGN32), (INF, INF), (NINF, NINF), (INF, NINF),
            (SN2, QN), (QN2, S1), (S1, SN), (DEN, DEN), (DEN, 0x00000002), (NZ, 0), (0, 0), (NZ, NZ),
            (S1, DEN), (DEN, QN), (S3, 0x3f800001), (0x00800000, 0x007fffff), (0x4b800000, 0xbf800001),
            (MAX32 | SIGN32, 0x73000000), (0x3f800001, 0x33800000), (0, DEN), (INF, S2), (S2, INF)],
    "mul": [(S1, S1), (MAX32, S2), (MAX32 | SIGN32, S2), (MINN, SH), (MINN, 0x3f7fffff), (0x3f000001, 0x00fffffe),
            (DEN, S2), (MIND, SH), (MIND, MIND), (INF, 0), (NZ, NINF), (SN, QN), (QN2, SN), (S1, QN),
            (INF, DEN), (0, DEN), (QN, DEN), (NZ, S3), (0x3f800001, 0x3f800001), (0x3f800001, 0x3fffffff),
            (0x5f800000, 0x5f800000), (0x1f800000, 0x1f800000), (0x00c00000, 0x3f400000), (S3, 0x3eaaaaab)],
}
# a pair raising exactly the named flag(s) (under every mode), with the benign pair for the other lanes
FLAG_PAIR = {
    "add": {"IE": (INF, NINF), "DE": (DEN, 0), "OE": (MAX32, MAX32), "PE": (S1, 0x33c00000)},
    "sub": {"IE": (INF, INF), "DE": (DEN, 0), "OE": (MAX32, MAX32 | SIGN32), "PE": (S1, 0x33c00000)},
    "mul": {"IE": (INF, 0), "DE": (DEN, S1), "OE": (MAX32, S2), "UE": (MIND, SH), "PE": (S3, 0x3eaaaaab)},
}
BENIGN = {"add": (S1, S1), "sub": (S2, S1), "mul": (S1, S2)}


def ymm(lo, hi):
    return (lo & M128) | ((hi & M128) << 128)


def lanes_to_int(pairs):
    return of_els([p[0] for p in pairs], 32), of_els([p[1] for p in pairs], 32)


def cases_for(form, L, imm, rng):
    """(name, y1 data, y2 data, rc or None) — the data over L bits; the caller seeds what L does not read."""
    n = L // 32
    out = []
    mn = mnemonic(form)
    if mn == "vshufps":
        out.append(("p0", of_els([0x11110000 + i for i in range(8)], 32), of_els([0xbbbb0000 + i for i in range(8)], 32),
                    None))
        out.append(("p1", rng.getrandbits(256), rng.getrandbits(256), None))
    elif form in ("vpsrad_x", "vpsraw_x"):
        w = 32 if mn == "vpsrad" else 16
        edge = of_els([0x80000000, 0x7fffffff, 0xffffffff, 0x00000001, 0xc0000000, 0x40000000, 0x80000001,
                       0x0000ffff] if w == 32 else
                      [0x8000, 0x7fff, 0xffff, 0x0001, 0xc000, 0x4000, 0x8001, 0x00ff] * 2, w)
        counts = [0, 1, 5, w - 1, w, w + 1, 31, 32, 33, 63, 64, 255, 256, 1 << 32, (1 << 32) + 1, 1 << 63, M64]
        seen = []
        for c in counts:
            if c in seen:
                continue
            seen.append(c)
            k = len(seen) - 1
            junk = rng.getrandbits(192) | 1 | (1 << 64)          # B[255:64]: never read, never zero
            out.append(("c%d_edge" % k, edge, c | (junk << 64), None))
            out.append(("c%d_rand" % k, rng.getrandbits(256), c | ((rng.getrandbits(192) | 1 | (1 << 64)) << 64),
                        None))
    elif form in ("vpsrad_i", "vpsraw_i"):
        out.append(("p0", of_els([0x80000000, 0x7fffffff, 0xffffffff, 0x00000001, 0xc0000000, 0x40000000,
                                  0x80000001, 0x0000ffff], 32), 0, None))
        out.append(("p1", rng.getrandbits(256), 0, None))
    elif form in FP:
        op = form[1:4]
        cs = FP_CASES[op]
        if L == 256:
            for fl in FLAG_PAIR[op]:
                pairs = [BENIGN[op]] * 8
                pairs[4 + (len(out) % 4)] = FLAG_PAIR[op][fl]       # one HIGH-lane element, the rest benign
                a, b = lanes_to_int(pairs)
                out.append(("hionly_%s" % fl, a, b, len(out) % 4))
            for fl in FLAG_PAIR[op]:
                pairs = [BENIGN[op]] * 8
                pairs[len(out) % 4] = FLAG_PAIR[op][fl]
                a, b = lanes_to_int(pairs)
                out.append(("loonly_%s" % fl, a, b, len(out) % 4))
        else:
            for fl in FLAG_PAIR[op]:
                pairs = [BENIGN[op]] * 3 + [FLAG_PAIR[op][fl]]
                a, b = lanes_to_int(pairs)
                out.append(("lane3_%s" % fl, a, b, len(out) % 4))
        for g in range(0, len(cs), n):
            grp = cs[g:g + n]
            grp = grp + [BENIGN[op]] * (n - len(grp))
            a, b = lanes_to_int(grp)
            for rc in range(4):
                out.append(("case%d_%s" % (g // n, MODES[rc]), a, b, rc))
        for i in range(8):
            if i % 2 == 0:
                a, b = rng.getrandbits(256), rng.getrandbits(256)
            else:
                def near():
                    return (rng.getrandbits(1) << 31) | (rng.randrange(100, 155) << 23) | rng.getrandbits(23)
                a, b = of_els([near() for _ in range(8)], 32), of_els([near() for _ in range(8)], 32)
            out.append(("rand%d_%s" % (i, MODES[i % 4]), a, b, i % 4))
    elif mn in ("vpunpcklwd", "vpunpckhwd", "vpunpcklbw", "vpackuswb"):
        out.append(("edge0", of_els(range(0x00, 0x20), 8), of_els(range(0x80, 0xa0), 8), None))
        sat = [0x0000, 0x00ff, 0x0100, 0x7fff, 0x8000, 0xffff, 0x0080, 0x007f, 0x00fe, 0xff00, 0x0001, 0x01ff,
               0x8001, 0x7f00, 0x00c3, 0x0200]
        out.append(("edge1", of_els(sat, 16), of_els(sat[::-1], 16), None))
        for i in range(4):
            out.append(("rand%d" % i, rng.getrandbits(256), rng.getrandbits(256), None))
    elif mn == "vpmovmskb":
        out += [("zero", 0, 0, None), ("ones", M256, 0, None), ("alt", of_els([0x80, 0x7f] * 16, 8), 0, None),
                ("lo1", 1 << 7, 0, None), ("hi1", 1 << (128 + 8 * 15 + 7), 0, None),
                ("lohi", of_els([0x80] * 16 + [0x00] * 16, 8), 0, None)]
        for i in range(6):
            out.append(("rand%d" % i, rng.getrandbits(256), 0, None))
    else:
        raise SystemExit("mk_vexsil_rows: no cases for %s" % form)
    return out


ROWS = []   # (name, fn, form, L, y1, y2, y3, imm, f, mx, rax, w3, wrax, wflags)


class Refused(SystemExit):
    def __init__(self, row, msg):
        super().__init__(msg)
        self.row = row


def build(rl=None):
    """Build every row. `rl` substitutes the rule; a row where the rule and the textbook differ REFUSES the build."""
    rl = rl or rule
    ROWS.clear()
    for k, (fn, form, L, _bs, imm) in enumerate(OPS):
        rng = random.Random(345000 + k)
        for i, (nm, a, b, rc) in enumerate(cases_for(form, L, imm, rng)):
            hi1, hi2 = rng.getrandbits(128) | 1, rng.getrandbits(128) | 1
            y3 = rng.getrandbits(256) | (1 << 128) | 1
            rax = rng.getrandbits(64) | (1 << 63)
            if L == 128:
                y1 = ymm(a, hi1)
                y2 = ymm(b, hi2) if form not in ("vpsrad_x", "vpsraw_x") else b
            else:
                y1, y2 = a & M256, b & M256
                if form in ("vpsrad_i", "vpsraw_i", "vpmovmskb"):
                    y2 = rng.getrandbits(256) | 1 | (1 << 128)     # an unread register, seeded anyway
            if rc is None:
                rc = i % 4
            mx = 0x1f80 | (rc << 13)
            f = ARITH if i % 2 else 0
            name = "%s_%s" % (fn[2:], nm)
            got = rl(form, L, y1, y2, y3, imm, mx, rax)
            want = textbook(form, L, y1, y2, y3, imm, mx, rax)
            if got != want:
                raise Refused(name, "mk_vexsil_rows: ⛔ row %s: the RULE gives ymm3 %064x rax %016x flags %02x, the "
                              "TEXTBOOK ymm3 %064x rax %016x flags %02x — the rule's reading of the SDM is wrong, "
                              "or the textbook is" % (name, got[0], got[1], got[2], want[0], want[1], want[2]))
            ROWS.append((name, fn, form, L, y1, y2, y3, imm, f, mx, rax, got[0], got[1], got[2]))


def q4(v):
    return ", ".join("0x%016xULL" % ((v >> (64 * i)) & M64) for i in range(4))


def wrong_reach(rl):
    """{mnemonic: (disagreeing rows, rows)} for a substitute rule, over the built rows."""
    out = {}
    for name, _fn, form, L, y1, y2, y3, imm, _f, mx, rax, w3, wrax, wfl in ROWS:
        key = mnemonic(form) + ("_x" if form.endswith("_x") else "_i" if form.endswith("_i") else "") + str(L)
        n, t = out.get(key, (0, 0))
        out[key] = (n + (rl(form, L, y1, y2, y3, imm, mx, rax) != (w3, wrax, wfl)), t + 1)
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


def host_f32(op, a, b):
    """The host's IEEE binary32 at round-to-nearest-even, or None where it cannot speak exactly: a product of two
    binary32 values is exact in binary64, a sum is exact when the exponents are within 29; struct.pack('<f') then
    rounds once (and raises OverflowError past the range)."""
    fa, fb = struct.unpack("<f", struct.pack("<I", a))[0], struct.unpack("<f", struct.pack("<I", b))[0]
    if f_kind(a) not in ("norm", "den") or f_kind(b) not in ("norm", "den"):
        return None
    if op == "mul":
        v = fa * fb
    else:
        ea, eb = (a >> 23) & 0xff, (b >> 23) & 0xff
        if abs(ea - eb) > 20:
            return None
        v = fa + fb if op == "add" else fa - fb
        if v == 0:
            return None
    try:
        return struct.unpack("<I", struct.pack("<f", v))[0]
    except OverflowError:
        return None


def selftest():
    bad = 0

    def say(ok, msg):
        nonlocal bad
        print(("  ✔ " if ok else "  ✖ ") + msg)
        bad += not ok

    # hand-derivable lanes, stated by IEEE 754 and not by either reference
    hand = [("add", 0, S1, S1, S2, 0), ("add", 0, S1, 0x33800000, S1, PE), ("add", 2, S1, 0x33800000, 0x3f800001, PE),
            ("add", 0, MAX32, MAX32, INF, OE | PE), ("add", 3, MAX32, MAX32, MAX32, OE | PE),
            ("add", 0, INF, NINF, INDEF, IE), ("add", 1, S1, S1 | SIGN32, NZ, 0), ("add", 0, S1, S1 | SIGN32, 0, 0),
            ("add", 0, QN, SN, QN, IE), ("add", 0, SN, S1, 0x7fc00001, IE), ("add", 0, QN, DEN, QN, 0),
            ("mul", 0, MIND, SH, 0, UE | PE | DE), ("mul", 2, MIND, SH, MIND, UE | PE | DE),
            ("mul", 0, MINN, SH, 0x00400000, 0), ("mul", 0, 0x3f000001, 0x00fffffe, MINN, PE),
            ("mul", 3, 0x3f000001, 0x00fffffe, 0x007fffff, UE | PE), ("mul", 0, INF, 0, INDEF, IE),
            ("sub", 0, S1, S1, 0, 0), ("sub", 1, S1, S1, NZ, 0), ("sub", 0, INF, INF, INDEF, IE)]
    hb = 0
    for op, rc, a, b, v, fl in hand:
        r = r_fp_lane(op, MODES[rc], a, b)
        t = tb_fp(op, rc, a, b)
        if not (r == t == (v, fl)):
            hb += 1
            print("      ✖ %s %s %08x %08x: rule %08x/%02x textbook %08x/%02x want %08x/%02x" % (
                op, MODES[rc], a, b, r[0], r[1], t[0], t[1], v, fl))
    say(hb == 0, "%d hand-derived binary32 lanes (ties, overflow per mode, TINY-AFTER, signed zeros, NaN order, "
        "invalid): both references agree with each" % len(hand))
    # the two FP references against each other over a sweep, and against the host at round-to-nearest
    rng = random.Random(345999)
    nsweep, ndiff, nhost, hdiff = 0, 0, 0, 0
    for i in range(6000):
        op = ("add", "sub", "mul")[i % 3]
        if i % 2:
            a, b = rng.getrandbits(32), rng.getrandbits(32)
        else:
            e = rng.randrange(0, 255)
            a = (rng.getrandbits(1) << 31) | (e << 23) | rng.getrandbits(23)
            e2 = max(0, min(254, e + rng.randrange(-30, 31) if op != "mul" else 254 - e + rng.randrange(-140, 20)))
            b = (rng.getrandbits(1) << 31) | (e2 << 23) | rng.getrandbits(23)
        for rc in range(4):
            nsweep += 1
            r, t = r_fp_lane(op, MODES[rc], a, b), tb_fp(op, rc, a, b)
            if r != t:
                ndiff += 1
                if ndiff <= 5:
                    print("      ✖ %s %s %08x %08x: rule %08x/%02x textbook %08x/%02x" % (op, MODES[rc], a, b, r[0],
                                                                                         r[1], t[0], t[1]))
        h = host_f32(op, a, b)
        if h is not None:
            nhost += 1
            if h != r_fp_lane(op, "nearest", a, b)[0]:
                hdiff += 1
    say(ndiff == 0, "the exact-rational rule and the integer-significand textbook agree on %d swept lanes "
        "(add/sub/mul × 4 modes, value AND flags)" % nsweep)
    say(hdiff == 0 and nhost > 2000, "the rule agrees with the host's IEEE binary32 (round-to-nearest) on %d lanes "
        "where the host speaks exactly" % nhost)
    build()
    say(len(ROWS) > 0, "%d rows built, every one equal under the rule and the textbook" % len(ROWS))
    say(refusals(quiet=True) == 0, "each of the %d wrong rules (a)-(d) is REFUSED on its named row" % len(WRONG))
    for label, rl in MUTANTS:
        say(sum(n for n, _t in wrong_reach(rl).values()) > 0, "the mutant '%s' disagrees on some row" % label)
    pk = [r for r in ROWS if r[0] == PLANT_ROW]
    say(len(pk) == 1 and pk[0][3] == 256 and pk[0][2] != "vpmovmskb", "--plant's row %s exists once and is a VEX.256 "
        "vector row" % PLANT_ROW)
    ph = [r for r in ROWS if r[0] == PLANT_HI]
    say(len(ph) == 1 and ph[0][3] == 128 and (ph[0][6] >> 128) != 0 and ph[0][11] >> 128 == 0,
        "--plant-hi's row %s exists once, is VEX.128, its YMM3 upper half seeded non-zero and expected zero" % PLANT_HI)
    say(all((r[6] >> 128) != 0 for r in ROWS), "every row seeds YMM3's upper half non-zero")
    say(all((r[4] >> 128) != 0 and (r[5] >> 128) != 0 for r in ROWS if r[3] == 128),
        "every VEX.128 row seeds YMM1's and YMM2's upper halves non-zero")
    say(all(r[11] >> 128 == 0 for r in ROWS if r[3] == 128 and r[2] != "vpmovmskb"),
        "every VEX.128 vector row expects YMM3[255:128] = 0")
    say(all(((r[5] >> 64) & M64) != 0 for r in ROWS if r[2] in ("vpsrad_x", "vpsraw_x")),
        "every xmm-count row carries junk in the count register's bits 127:64")
    say(all(r[12] >> 32 == 0 and (r[10] >> 32) != 0 for r in ROWS if r[2] == "vpmovmskb"),
        "every vpmovmskb row expects RAX[63:32] = 0 from a RAX seeded non-zero there")
    say({mnemonic(r[2]) for r in ROWS} == set(MNEMONICS) and {(r[2], r[3]) for r in ROWS} == set(ENC),
        "the rows cover exactly the 11 mnemonics and the %d encodings, each at both lengths" % len(ENC))
    for form in FP:
        for L in (128, 256):
            rs = [r for r in ROWS if r[2] == form and r[3] == L]
            seen = 0
            for r in rs:
                seen |= r[13]
            need = IE | DE | OE | PE | (UE if form == "vmulps" else 0)
            say(seen & need == need and not seen & ZE and {(r[9] >> 13) & 3 for r in rs} == {0, 1, 2, 3},
                "%s VEX.%d: the rows raise %s, never ZE, under all four modes" % (
                    form, L, "|".join(n for n, b in FLAGNAMES if seen & b)))
    print("✅ mk_vexsil_rows selftest" if not bad else "⛔ mk_vexsil_rows selftest FAILED")
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
    print("/* GENERATED by hwprobe/mk_vexsil_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    for fn, _f, _L, _b, _i in OPS:
        print("void %s(struct xio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const struct xrow XROWS[] = {")
    for name, fn, form, L, y1, y2, y3, _imm, f, mx, rax, w3, wrax, wfl in ROWS:
        if plant and name == PLANT_ROW:
            w3 ^= 1 << 128         # the control: one expectation made wrong on purpose, in the HIGH lane
        if plant_hi and name == PLANT_HI:
            w3 |= y3 >> 128 << 128  # the control: the VEX.128 destination's upper half NOT zeroed
        print('  {"%s", %s, %d, {%s}, {%s}, {%s}, 0x%03x, 0x%04x, 0x%016xULL, {%s}, 0x%016xULL, 0x%04x},' % (
            name, fn, 1 if form == "vpmovmskb" else 0, q4(y1), q4(y2), q4(y3), f, mx, rax, q4(w3), wrax, mx | wfl))
    print("};")
    print("static const struct xop XOPS[] = {")
    for i, (fn, _f, _L, bs, _imm) in enumerate(OPS):
        bb = bytearray.fromhex(bs)
        if "--plant-op" in sys.argv and i == 0:
            bb[-1] ^= 0x01         # the control: the declared instruction is not the one in vexsil_ops.S
        print('  {"%s", %s_at, %d, {%s}},' % (fn, fn, len(bb), ", ".join("0x%02x" % x for x in bb)))
    print("};")
    return 0


if __name__ == "__main__":
    sys.exit(main())
