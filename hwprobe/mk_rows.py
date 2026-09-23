#!/usr/bin/env python3
"""hwprobe/mk_rows.py — the rows the x86-64 referee runs, with expectations DERIVED HERE.

Every expected value and flag comes from a stated rule in this file (the SDM's exception lists and NaN
rules, IEEE 754 rounding via ref_mul.py), never from ACL2 x86isa and never from x86lean. The referee's
job is to say whether a PROCESSOR agrees with these rules, because sub-group B pins some rows against the
SDM where the reference model disagrees (D265, D266).

MXCSR sticky bits: IE=1 DE=2 ZE=4 OE=8 UE=16 PE=32. Every row runs with all exceptions MASKED.

Two rules below are HYPOTHESES the rows exist to test, and each is named where it is used:
  TINY-AFTER   underflow tininess is detected AFTER rounding (x86isa does this; ref_mul.py's own path
               label is BEFORE, so tininess is recomputed here and ref_mul supplies only the VALUE)
  DE-SUPPRESS  the denormal flag is not raised when an operand is a NaN (x86isa does this)
  ZE-BEFORE-DE (B2) a denormal dividend over zero raises ZE and NOT DE: SDM Vol. 1 §4.9.2 ranks divide-by-zero
               (3) above the denormal-operand exception (4), and a masked (3) returns its special result. The
               first draft said DE as well; Rosetta 2 read ZE alone on both rows before any processor ran.
  DE-WITH-INF  (B2) a denormal operand beside an infinity raises DE (the multiply's rule, now asked of add and div)
  NARROW-NAN   (B3) CVTSD2SS keeps a NaN's sign and the top 23 bits of its fraction, and sets the quiet bit: the
               payload's low 29 bits are dropped, never rounded (SDM Vol. 1 §4.8.3.5 and Table 4-7)
  DE-NARROW    (B3) a binary64 denormal source raises DE (CVTSD2SS lists Denormal; the value is far below binary32's
               range, so it also rounds to a zero or the least subnormal with UE and PE)
  INT-PE-ONLY  (B4) CVTSI2SS / CVTSI2SD from an int32 or int64 raise PE alone, when the integer is not representable:
               no integer is tiny, none overflows (|v| <= 2^63 < FLT_MAX), and an integer is never a denormal operand
  INT-WIDTH    (B4) without REX.W the source is the GPR's low 32 bits, read as signed; the upper 32 are never read
  LANE-OR      (B5) a packed form's MXCSR flags are the OR of its lanes' flags, each lane's computed by the scalar rule
               on that lane alone (all exceptions masked); a flag raised in lane 3 is raised as surely as in lane 0
  LANE-DE      (B5) DE-SUPPRESS and ZE-BEFORE-DE hold PER LANE: a NaN, or a zero divisor, in one lane does not
               withhold DE raised by a denormal in another
Usage: mk_rows.py [--plant | --plant-op | --plant-packed | --plant-pop]   writes C rows on stdout.
  --plant         flips ONE expectation: the referee must report exactly one disagreement (exit 1)
  --plant-op      declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --plant-packed  flips ONE bit of ONE packed row's HIGH quadword: exactly one disagreement (exit 1), which is what
                  proves the 128-bit comparison reads bits 127:64 at all
  --plant-pop     declares ONE packed instruction byte wrong: the probe must refuse to run (exit 2)
"""
import sys
import os as _os
sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))), "scripts"))
import portable as P  # noqa: E402
from fractions import Fraction
import ref_mul as R

IE, DE, ZE, OE, UE, PE = 1, 2, 4, 8, 16, 32
F32, F64 = R.B32, R.B64


def parts(fmt, x):
    return R.parts(fmt, x)


def kind(fmt, x):
    ew, mw = fmt
    s, e, m = parts(fmt, x)
    if e == (1 << ew) - 1:
        if m == 0:
            return "inf"
        return "qnan" if (m >> (mw - 1)) & 1 else "snan"
    if e == 0:
        return "zero" if m == 0 else "den"
    return "norm"


def de_flag(fmt, *xs):
    ks = [kind(fmt, x) for x in xs]
    if any(k in ("qnan", "snan") for k in ks):      # DE-SUPPRESS
        return 0
    return DE if "den" in ks else 0


def tiny_after(fmt, rc, v):
    """TINY-AFTER: round |v| to the format's precision with an UNBOUNDED exponent; tiny iff below 2^emin."""
    ew, mw = fmt
    bias = (1 << (ew - 1)) - 1
    neg = v < 0
    mag = -v if neg else v
    ulp = Fraction(2) ** (R.floor_log2(mag) - mw)
    lo = (mag // ulp) * ulp
    hi = lo + ulp
    if lo == mag:
        r = lo
    elif rc == "nearest":
        d1, d2 = mag - lo, hi - mag
        r = lo if d1 < d2 else hi if d2 < d1 else (lo if int(lo / ulp) % 2 == 0 else hi)
    elif rc == "zero":
        r = lo
    elif rc == "down":
        r = hi if neg else lo
    else:
        r = lo if neg else hi
    return r < Fraction(2) ** (1 - bias)


def mul(fmt, rc, a, b):
    """MULSS/MULSD (SDM Vol. 2B: Overflow, Underflow, Invalid, Precision, Denormal)."""
    bits, path = R.ref_mul(fmt, rc, a, b)
    ka, kb = kind(fmt, a), kind(fmt, b)
    f = IE if (path == "invalid" or "snan" in (ka, kb)) else 0
    f |= de_flag(fmt, a, b)
    if path.startswith("overflow"):
        f |= OE | PE
    elif path not in ("exact", "zero", "inf", "invalid") and not path.startswith("nan"):
        f |= PE
        if tiny_after(fmt, rc, R.value(fmt, a) * R.value(fmt, b)):
            f |= UE
    return bits, f


def arith(op, fmt, rc, a, b):
    """ADDS?/SUBS?/DIVS? (SDM Vol. 2B; B2, D268 s8): exact Fractions rounded by ref_mul.round_to.
    NaN: the first source, else the second, quieted; IE on an SNaN. inf - inf, 0/0 and inf/inf: the negative
    QNaN indefinite and IE. x/0: inf and ZE. An exact zero sum is +0, and -0 under round-down; x + x keeps a
    zero's sign (IEEE 754 6.3). A tiny sum is always exact, so add and sub never raise UE."""
    ew, mw = fmt
    mask = (1 << (1 + ew + mw)) - 1
    a &= mask
    b &= mask
    quiet, infE, sbit = 1 << (mw - 1), ((1 << ew) - 1) << mw, 1 << (ew + mw)
    indef = sbit | infE | quiet
    ka, kb = kind(fmt, a), kind(fmt, b)
    snan = IE if "snan" in (ka, kb) else 0
    if ka in ("qnan", "snan"):
        return a | quiet, snan
    if kb in ("qnan", "snan"):
        return b | quiet, snan
    de = DE if "den" in (ka, kb) else 0                      # DE-WITH-INF
    sa, sb = a >> (ew + mw), b >> (ew + mw)
    if op == "div":
        sg = sbit if sa != sb else 0
        if {ka, kb} == {"inf"} or {ka, kb} == {"zero"}:
            return indef, IE
        if ka == "inf":
            return sg | infE, de
        if kb == "inf":
            return sg, de
        if kb == "zero":
            return sg | infE, ZE                              # ZE-BEFORE-DE
        if ka == "zero":
            return sg, de
        exact = R.value(fmt, a) / R.value(fmt, b)
    else:
        if op == "sub":
            sb ^= 1
        if ka == "inf" and kb == "inf":
            return ((sbit if sa else 0) | infE, 0) if sa == sb else (indef, IE)
        if "inf" in (ka, kb):
            return (sbit if (sa if ka == "inf" else sb) else 0) | infE, de
        exact = R.value(fmt, a) + (-1 if op == "sub" else 1) * R.value(fmt, b)
        if exact == 0:
            if ka == "zero" and kb == "zero" and sa == sb:
                return (sbit if sa else 0), 0
            return (sbit if rc == 1 else 0), de
    bits, path = R.round_to(fmt, MODES[rc], exact)
    if path.startswith("overflow"):
        return bits, OE | PE | de
    if path == "exact":
        return bits, de
    return bits, PE | de | (UE if tiny_after(fmt, MODES[rc], exact) else 0)


def fcmp(fmt, a, b):
    ka, kb = kind(fmt, a), kind(fmt, b)
    if "nan" in ka or "nan" in kb:
        return "unord"
    va, vb = R.value(fmt, a), R.value(fmt, b)
    return "lt" if va < vb else "gt" if va > vb else "eq"


# SDM Vol. 2A COMISD: "If either source operand is a NaN, ... ZF, PF, CF set" (unordered); OF, SF, AF cleared.
EFL = {"unord": 0x45, "gt": 0x00, "lt": 0x01, "eq": 0x40}
EFL_MASK = 0x8D5    # OF SF ZF AF PF CF


def comis(fmt, a, b, ordered):
    """COMIS*: Invalid if SNaN OR QNaN; UCOMIS*: Invalid if SNaN only (SDM Vol. 2A). Both: Denormal."""
    ks = (kind(fmt, a), kind(fmt, b))
    f = IE if ("snan" in ks or (ordered and "qnan" in ks)) else 0
    return EFL[fcmp(fmt, a, b)], f | de_flag(fmt, a, b)


def fmin(fmt, a, b):
    """MINSD/MINSS: DEST < SRC ? DEST : SRC, so a NaN or a pair of zeros returns SRC.
    Invalid including a QNaN source (SDM Vol. 2B); Denormal."""
    ks = (kind(fmt, a), kind(fmt, b))
    r = a if fcmp(fmt, a, b) == "lt" else b
    f = IE if ("snan" in ks or "qnan" in ks) else 0
    return r, f | de_flag(fmt, a, b)


def cvtss2sd(a):
    """Exact widening; an SNaN is quieted with its payload shifted up. Invalid (SNaN), Denormal."""
    x = a & 0xFFFFFFFF
    s, e, m = parts(F32, x)
    k = kind(F32, x)
    if k in ("qnan", "snan"):
        r = (s << 63) | (0x7FF << 52) | (m << 29) | (1 << 51)
        return r, IE if k == "snan" else 0
    if k == "inf":
        return (s << 63) | (0x7FF << 52), 0
    if k == "zero":
        return s << 63, 0
    return R.encode(F64, s == 1, abs(R.value(F32, x))), de_flag(F32, x)


def cvtsd2ss(rc, a):
    """CVTSD2SS (SDM Vol. 2A: Overflow, Underflow, Invalid, Precision, Denormal): binary64 -> binary32 under MXCSR.RC.
    NaN: NARROW-NAN, IE on an SNaN. +-inf and +-0 convert exactly and raise nothing. Otherwise the exact value is
    rounded by ref_mul.round_to: overflow OE|PE; an inexact tiny result UE|PE (TINY-AFTER); an exact one nothing
    new. DE-NARROW on a binary64 denormal. Only the low 32 bits of the destination are written."""
    x = a & ((1 << 64) - 1)
    s, e, m = parts(F64, x)
    k = kind(F64, x)
    sb = s << 31
    if k in ("qnan", "snan"):
        return sb | 0x7F800000 | 0x400000 | (m >> 29), IE if k == "snan" else 0
    if k == "inf":
        return sb | 0x7F800000, 0
    if k == "zero":
        return sb, 0
    de = DE if k == "den" else 0
    v = R.value(F64, x)
    bits, path = R.round_to(F32, MODES[rc], v)
    if path.startswith("overflow"):
        return bits, OE | PE | de
    if path == "exact":
        return bits, de
    return bits, PE | de | (UE if tiny_after(F32, MODES[rc], v) else 0)


def cvtsi2sd32(a):
    """CVTSI2SD from an int32: exact for every input, so RC is never consulted, and integer 0 gives +0
    (a conversion is not a sum; IEEE 754's roundTowardNegative -0 rule is for exact-zero sums).
    No exception. (x86isa gives -0 at RC=down: cvt-spec.lisp sse-cvt-int-to-fp, D266.)"""
    v = a & 0xFFFFFFFF
    v = v - (1 << 32) if v >> 31 else v
    if v == 0:
        return 0, 0
    return R.encode(F64, v < 0, abs(Fraction(v))), 0


def cvtsi2f(fmt, wide, rc, a):
    """CVTSI2SS / CVTSI2SD (SDM Vol. 2A: Precision) from a signed int32 (INT-WIDTH) or int64 under MXCSR.RC. Integer 0
    gives +0 at every mode, as cvtsi2sd32 does. Otherwise the exact integer is rounded by ref_mul.round_to, and PE is
    raised iff that rounding is inexact (INT-PE-ONLY)."""
    w = 64 if wide else 32
    v = a & ((1 << w) - 1)
    v = v - (1 << w) if v >> (w - 1) else v
    if v == 0:
        return 0, 0
    bits, path = R.round_to(fmt, MODES[rc], Fraction(v))
    return bits, 0 if path == "exact" else PE


def cvttsd2si32(a):
    """Truncation toward zero; NaN, infinity or out of int32 range give 0x80000000. Invalid, Precision."""
    k = kind(F64, a)
    if k in ("qnan", "snan", "inf"):
        return 0x80000000, IE
    v = R.value(F64, a)
    t = int(v)
    if not (-(1 << 31) <= t < (1 << 31)):
        return 0x80000000, IE
    return t & 0xFFFFFFFF, PE if v != t else 0


def packed(op, fmt, rc, A, B):
    """B5: MULP?/ADDP?/SUBP?/DIVP? as the scalar rule applied to each lane alone (LANE-OR, LANE-DE). A and B are
    128-bit integers; lane i is bits [w*i, w*i+w). Returns the 128-bit result and the OR of the lanes' flags."""
    w = 1 + fmt[0] + fmt[1]
    m = (1 << w) - 1
    r, f = 0, 0
    for i in range(128 // w):
        a, b = (A >> (w * i)) & m, (B >> (w * i)) & m
        v, g = mul(fmt, MODES[rc], a, b) if op == "mul" else arith(op, fmt, rc, a, b)
        r |= (v & m) << (w * i)
        f |= g
    return r, f


D1 = 0x3FF0000000000000          # 1.0
D2 = 0x4000000000000000          # 2.0
DQ = 0x7FF8000000000000          # QNaN (positive)
DS = 0x7FF0000000000789          # SNaN
DDEN = 0x000FFFFFFFFFFFFF        # largest binary64 denormal
S1, S2 = 0x3F800000, 0x40000000
SQ, SS, SDEN = 0x7FC00000, 0x7F800123, 0x007FFFFF
MODES = R.MODES

# THE INSTRUCTIONS, as the bytes each p_ function in sse_ops.S executes after its two 5-byte loads.
# probe.c refuses to run (exit 2) unless the bytes at that offset are these, so the row's name and the
# instruction the processor ran cannot drift apart.
OPS = {"p_cvtsi2sd": "f20f2ac7",
       "p_mulsd": "f20f59c1", "p_mulss": "f30f59c1", "p_minsd": "f20f5dc1", "p_minss": "f30f5dc1",
       "p_comisd": "660f2fc1", "p_ucomisd": "660f2ec1", "p_comiss": "0f2fc1", "p_ucomiss": "0f2ec1",
       "p_cvtss2sd": "f30f5ac8", "p_cvttsd2si": "f20f2cc0", "p_cvtsd2ss": "f20f5ac8",
       "p_addsd": "f20f58c1", "p_addss": "f30f58c1", "p_subsd": "f20f5cc1", "p_subss": "f30f5cc1",
       "p_divsd": "f20f5ec1", "p_divss": "f30f5ec1",
       "p_cvtsi2ss": "f30f2acf", "p_cvtsi2ssq": "f3480f2acf", "p_cvtsi2sdq": "f2480f2acf"}

# B5: the packed forms, as the bytes each p_ function executes after LOAD4 (offset 28, checked by probe.c).
POPS = {"p_mulps": "0f59c1", "p_mulpd": "660f59c1", "p_addps": "0f58c1", "p_addpd": "660f58c1",
        "p_subps": "0f5cc1", "p_subpd": "660f5cc1", "p_divps": "0f5ec1", "p_divpd": "660f5ec1"}

ROWS = []   # (name, fn, mxcsr_in, a, b, want, want_mask, want_flags)
PROWS = []  # B5: (name, fn, mxcsr_in, A, B, want, want_flags), A B want 128-bit, every bit compared


def add(name, fn, mx, a, b, want, mask, flags):
    ROWS.append((name, fn, mx, a, b, want, mask, flags))


def build():
    # MULSD: D265's ten pairs and the tininess pairs, at every RC
    mpairs = [
        ("exact", D1 | 0x8000000000000, D2), ("tiecarry", 0x3FD5555555555555, 0x4008000000000000),
        ("tieodd", 0x3FF0000000000001, 0x3FF8000000000000), ("negtie", 0xBFF0000000000001, 0x3FF8000000000000),
        ("overflow", 0x7FEFFFFFFFFFFFFF, D2), ("negover", 0xFFEFFFFFFFFFFFFF, D2),
        ("denmin2", 1, 1), ("negsubtie", 0x8000000000000001, 0x3FE0000000000000),
        ("invalid", 0x7FF0000000000000, 0x8000000000000000), ("snanqnan", DS, 0x7FF8000000000ABC),
        ("tinyup", 0x3FF0000000000001, DDEN), ("tinyup_swap", DDEN, 0x3FF0000000000001),
        ("exacttiny", 0x0008000000000000, D1), ("deeptiny", 3, 0x3FE0000000000000),
        ("qnan_den", DQ, DDEN), ("snan_den", DS, DDEN),
    ]
    for name, a, b in mpairs:
        for rc, mode in enumerate(MODES):
            v, f = mul(F64, mode, a, b)
            add("mulsd_%s/%s" % (name, mode), "p_mulsd", 0x1F80 | (rc << 13), a, b, v, (1 << 64) - 1, f)
    for name, a, b in [("exact", 0x3FC00000, S2), ("invalid", 0x7F800000, 0x80000000),
                       ("tinyup", 0x3F800001, SDEN), ("exacttiny", 0x00400000, S1), ("tieodd", 0x3F800001, 0x3FC00000)]:
        for rc, mode in enumerate(MODES):
            v, f = mul(F32, mode, a, b)
            add("mulss_%s/%s" % (name, mode), "p_mulss", 0x1F80 | (rc << 13), a, b, v, 0xFFFFFFFF, f)
    # sticky bits are ORed, never replaced: every flag preset, an exact product raises nothing new
    v, f = mul(F64, "nearest", D1, D2)
    add("mulsd_sticky_or", "p_mulsd", 0x1FBF, D1, D2, v, (1 << 64) - 1, f)
    # COMIS / UCOMIS
    cpairs = [("qnan_one", "Q", "1"), ("one_qnan", "1", "Q"), ("snan_one", "S", "1"), ("den_one", "D", "1"),
              ("qnan_den", "Q", "D"), ("snan_den", "S", "D"), ("one_two", "1", "2"), ("two_one", "2", "1"),
              ("one_one", "1", "1")]
    for fmt, suf, vals in [(F64, "d", {"Q": DQ, "S": DS, "D": DDEN, "1": D1, "2": D2}),
                           (F32, "s", {"Q": SQ, "S": SS, "D": SDEN, "1": S1, "2": S2})]:
        for ordered, op in [(True, "comis"), (False, "ucomis")]:
            for name, x, y in cpairs:
                a, b = vals[x], vals[y]
                e, f = comis(fmt, a, b, ordered)
                add("%s%s_%s" % (op, suf, name), "p_%s%s" % (op, suf), 0x1F80, a, b, e, EFL_MASK, f)
    # MIN
    for fmt, suf, vals, mask in [(F64, "d", {"Q": DQ, "S": DS, "D": DDEN, "1": D1, "2": D2}, (1 << 64) - 1),
                                 (F32, "s", {"Q": SQ, "S": SS, "D": SDEN, "1": S1, "2": S2}, 0xFFFFFFFF)]:
        for name, x, y in [("qnan_one", "Q", "1"), ("one_qnan", "1", "Q"), ("snan_one", "S", "1"),
                           ("den_one", "D", "1"), ("qnan_den", "Q", "D"), ("two_one", "2", "1")]:
            a, b = vals[x], vals[y]
            r, f = fmin(fmt, a, b)
            add("mins%s_%s" % (suf, name), "p_mins%s" % suf, 0x1F80, a, b, r, mask, f)
    # CVTSS2SD
    for name, a in [("snan", SS), ("qnan", SQ), ("den", SDEN), ("one", S1), ("negzero", 0x80000000)]:
        r, f = cvtss2sd(a)
        add("cvtss2sd_%s" % name, "p_cvtss2sd", 0x1F80, a, 0, r, (1 << 64) - 1, f)
    # a sticky flag is history, never an input: every flag preset, including OE (x86isa reads the
    # accumulated OE as this conversion's overflow: cvt-spec.lisp sse-cvt-fp1-to-fp2, D266)
    for name, a in [("one", S1), ("small", 0x11111111), ("negsmall", 0x91111111)]:
        r, f = cvtss2sd(a)
        for mx in (0x1F88, 0x1FBF, 0x5F88, 0x7F88):
            add("cvtss2sd_%s_sticky%04x" % (name, mx), "p_cvtss2sd", mx, a, 0, r, (1 << 64) - 1, f)
    # CVTSI2SD from an int32 at every RC, integer zero first
    for name, a in [("zero", 0), ("one", 1), ("minus1", 0xFFFFFFFF), ("intmin", 0x80000000)]:
        r, f = cvtsi2sd32(a)
        for rc, mode in enumerate(MODES):
            add("cvtsi2sd_%s/%s" % (name, mode), "p_cvtsi2sd", 0x1F80 | (rc << 13), a, 0, r, (1 << 64) - 1, f)
    # CVTTSD2SI (32-bit destination)
    for name, a in [("onehalf", 0x3FF8000000000000), ("neghalf", 0xBFE0000000000000), ("qnan", DQ),
                    ("snan", DS), ("two31", 0x41E0000000000000), ("negtwo31", 0xC1E0000000000000),
                    ("den", DDEN), ("one", D1)]:
        r, f = cvttsd2si32(a)
        add("cvttsd2si_%s" % name, "p_cvttsd2si", 0x1F80, a, 0, r, 0xFFFFFFFF, f)
    # B2 (D268 s8): ADD, SUB, DIV. Every mode where the mode can matter; one row where it cannot.
    DMAX, DMIN = 0x7FEFFFFFFFFFFFFF, 0x0010000000000000
    b64_all = [("add", "exact", D1, D2), ("add", "tie", D1, 0x3CA0000000000000),
               ("add", "tieodd", 0x3FF0000000000001, 0x3CA0000000000000),
               ("add", "sticky", D1, 0x3C30000000000000), ("sub", "sticky", D1, 0x3C30000000000000),
               ("add", "gap55", D1, 0x3C80000000000000), ("sub", "gap56", D1, 0x3C70000000000000),
               ("add", "overflow", DMAX, DMAX), ("sub", "cancel", D1, D1), ("add", "cancel", D1, 1 << 63 | D1),
               ("add", "zeros", 0, 1 << 63),
               ("div", "third", D1, 0x4008000000000000), ("div", "overflow", DMAX, 0x3FE0000000000000),
               ("div", "tiny", DMIN, 0x4008000000000000)]
    b64_one = [("add", "negzeros", 1 << 63, 1 << 63), ("sub", "negzero_zero", 1 << 63, 0),
               ("sub", "infinf", 0x7FF0000000000000, 0x7FF0000000000000),
               ("add", "infinf", 0x7FF0000000000000, 0x7FF0000000000000),
               ("add", "inf_den", 0x7FF0000000000000, DDEN), ("add", "den_den", DDEN, DDEN),
               ("add", "den_zero", DDEN, 0), ("add", "snan_one", DS, D1), ("add", "qnan_snan", DQ, DS),
               ("div", "exact", 0x4008000000000000, D2), ("div", "zero_zero", 0, 0),
               ("div", "inf_inf", 0x7FF0000000000000, 0xFFF0000000000000),
               ("div", "one_zero", D1, 0), ("div", "negone_zero", 1 << 63 | D1, 0),
               ("div", "den_zero", DDEN, 0), ("div", "zero_den", 0, DDEN), ("div", "snan_den", DS, DDEN),
               ("div", "inf_den", 0x7FF0000000000000, DDEN)]
    b32_all = [("add", "exact", 0x3FC00000, S2), ("add", "tie", S1, 0x33800000),
               ("add", "sticky", S1, 0x30000000), ("sub", "cancel", S1, S1),
               ("add", "zeros", 0, 0x80000000), ("add", "overflow", 0x7F7FFFFF, 0x7F7FFFFF),
               ("div", "third", S1, 0x40400000), ("div", "tiny", 0x00800000, 0x40400000)]
    b32_one = [("div", "one_zero", S1, 0), ("div", "den_zero", SDEN, 0),
               ("sub", "infinf", 0x7F800000, 0x7F800000), ("add", "snan_one", SS, S1)]
    for fmt, suf, mask, alls, ones in [(F64, "sd", (1 << 64) - 1, b64_all, b64_one),
                                       (F32, "ss", 0xFFFFFFFF, b32_all, b32_one)]:
        for op, name, a, b in alls:
            for rc, mode in enumerate(MODES):
                v, f = arith(op, fmt, rc, a, b)
                add("%s%s_%s/%s" % (op, suf, name, mode), "p_%s%s" % (op, suf), 0x1F80 | (rc << 13), a, b, v,
                    mask, f)
        for op, name, a, b in ones:
            v, f = arith(op, fmt, 0, a, b)
            add("%s%s_%s" % (op, suf, name), "p_%s%s" % (op, suf), 0x1F80, a, b, v, mask, f)
    # B3: CVTSD2SS. The destination is %xmm1, whose bits 63:32 hold a canary that must survive: the instruction
    # writes the low 32 bits only. Every mode where the mode can matter; one row where it cannot.
    CAN = 0x5A5AC3C3 << 32
    n_all = [("tie", 0x3FF0000010000000), ("tieodd", 0x3FF0000030000000), ("sticky", 0x3FF0000010000001),
             ("negsticky", 0xBFF0000010000001), ("third", 0x3FD5555555555555),
             ("overflow", 0x7FEFFFFFFFFFFFFF), ("negoverflow", 0xFFEFFFFFFFFFFFFF),
             ("maxtie", 0x47EFFFFFF0000000), ("tinyinexact", 0x3800000000080000),
             ("tinyafter", 0x380FFFFFF8000000), ("halfmin", 0x3690000000000000),
             ("den", DDEN), ("negden", 1 << 63 | DDEN), ("deep", DMIN)]
    n_one = [("one", D1), ("zero", 0), ("negzero", 1 << 63), ("inf", 0x7FF0000000000000),
             ("neginf", 0xFFF0000000000000), ("qnan", DQ), ("snan", DS), ("negqnan_payload", 0xFFF8123456789ABC),
             ("snan_payload", 0x7FF4000020000000), ("max", 0x47EFFFFFE0000000), ("minnorm", 0x3810000000000000),
             ("minsub", 0x36A0000000000000), ("exacttiny", 0x3800000000000000)]
    for name, a in n_all:
        for rc, mode in enumerate(MODES):
            v, f = cvtsd2ss(rc, a)
            add("cvtsd2ss_%s/%s" % (name, mode), "p_cvtsd2ss", 0x1F80 | (rc << 13), a, CAN, CAN | v,
                (1 << 64) - 1, f)
    for name, a in n_one:
        v, f = cvtsd2ss(0, a)
        add("cvtsd2ss_%s" % name, "p_cvtsd2ss", 0x1F80, a, CAN, CAN | v, (1 << 64) - 1, f)
    # a sticky flag is history, never an input (cvtss2sd's D266 defect, asked of the narrowing direction)
    for name, a in [("one", D1), ("third", 0x3FD5555555555555)]:
        for mx in (0x1F88, 0x1FBF, 0x5F88, 0x7F88):
            v, f = cvtsd2ss((mx >> 13) & 3, a)
            add("cvtsd2ss_%s_sticky%04x" % (name, mx), "p_cvtsd2ss", mx, a, CAN, CAN | v, (1 << 64) - 1, f)
    # B4: the integer conversions that round. The destination is %xmm1 with the canary in bits 63:32; the
    # binary32 forms must leave it, and CVTSI2SDQ writes all 64 low bits. `a` is %rdi. Negative ties and stickies
    # separate down from zero; the width rows read differently as an int32 and as an int64.
    M31, M63 = 1 << 31, 1 << 63
    i32 = lambda v: v & 0xFFFFFFFF
    i64 = lambda v: v & ((1 << 64) - 1)
    forms = [
        ("cvtsi2ss", "p_cvtsi2ss", F32, False, 0xFFFFFFFF,
         [("tie", 0x01000001), ("tieodd", 0x01000003), ("sticky", 0x02000001), ("above", 0x02000003),
          ("negtie", i32(-0x01000001)), ("negsticky", i32(-0x02000001)), ("max", M31 - 1), ("zero", 0)],
         [("min", M31), ("exact", 0x00FFFFFF), ("one", 1), ("negone", i32(-1)),
          ("hijunk", 0xDEADBEEF00000001), ("hijunkneg", 0x00000001FFFFFFFF)]),
        ("cvtsi2ssq", "p_cvtsi2ssq", F32, True, 0xFFFFFFFF,
         [("tie", (1 << 40) + (1 << 16)), ("sticky", (1 << 40) + 1), ("negtie", i64(-((1 << 40) + (1 << 16)))),
          ("negsticky", i64(-((1 << 40) + 1))), ("max", M63 - 1), ("width", 0xFFFFFFFF), ("zero", 0)],
         [("min", M63), ("exact", 1 << 40), ("one", 1), ("negone", i64(-1))]),
        ("cvtsi2sdq", "p_cvtsi2sdq", F64, True, (1 << 64) - 1,
         [("tie", (1 << 53) + 1), ("tieodd", (1 << 53) + 3), ("sticky", (1 << 54) + 1),
          ("negtie", i64(-((1 << 53) + 1))), ("negsticky", i64(-((1 << 54) + 1))), ("max", M63 - 1), ("zero", 0)],
         [("min", M63), ("exact", (1 << 53) - 1), ("width", 0xFFFFFFFF), ("one", 1), ("negone", i64(-1))]),
    ]
    for nm, fn, fmt, wide, lane, alls, ones in forms:
        keep = CAN & ~lane & ((1 << 64) - 1)
        for name, a in alls:
            for rc, mode in enumerate(MODES):
                v, f = cvtsi2f(fmt, wide, rc, a)
                add("%s_%s/%s" % (nm, name, mode), fn, 0x1F80 | (rc << 13), a, CAN, keep | v, (1 << 64) - 1, f)
        for name, a in ones:
            v, f = cvtsi2f(fmt, wide, 0, a)
            add("%s_%s" % (nm, name), fn, 0x1F80, a, CAN, keep | v, (1 << 64) - 1, f)
        # a sticky flag is history, never an input: an exact and an inexact conversion under preset flags
        for name, a in [("one", 1), ("tie", alls[0][1])]:
            for mx in (0x1F88, 0x1FBF, 0x5F88, 0x7F88):
                v, f = cvtsi2f(fmt, wide, (mx >> 13) & 3, a)
                add("%s_%s_sticky%04x" % (nm, name, mx), fn, mx, a, CAN, keep | v, (1 << 64) - 1, f)


def build_packed():
    """B5 (LANE-OR, LANE-DE). Each lane is a scalar case the B1/B2 rows already name; a row is a choice of case per
    lane. `mix` puts a different flag set in every lane at every mode, with every lane a different value, so a lane
    swap or a dropped lane changes the result. `loud@k` moves one IE lane through every position against silent
    lanes, so a rule that reads lane 0's flags alone fails three of four. `de_split` and `ze_de` are LANE-DE, each
    beside the control that raises the suppressing condition with no denormal elsewhere."""
    SMAX, DMAX = 0x7F7FFFFF, 0x7FEFFFFFFFFFFFFF
    cases = {
        F32: {"exact": {"mul": (0x3FC00000, S2), "add": (0x3FC00000, S2), "sub": (0x40400000, S1), "div": (S2, S1)},
              "round": {"mul": (0x3F800001, 0x3FC00000), "add": (S1, 0x33800000), "sub": (S1, 0x30000000),
                        "div": (S1, 0x40400000)},
              "over": {"mul": (SMAX, S2), "add": (SMAX, SMAX), "sub": (SMAX, 0xFF7FFFFF), "div": (SMAX, 0x3F000000)},
              "snan": (SS, S1), "qnan_den": (SQ, SDEN), "den": (SDEN, S1), "den_zero": (SDEN, 0)},
        F64: {"exact": {"mul": (D1 | 0x8000000000000, D2), "add": (D1, D2), "sub": (0x4008000000000000, D1),
                        "div": (D2, D1)},
              "round": {"mul": (0x3FF0000000000001, 0x3FF8000000000000), "add": (D1, 0x3CA0000000000000),
                        "sub": (D1, 0x3C30000000000000), "div": (D1, 0x4008000000000000)},
              "over": {"mul": (DMAX, D2), "add": (DMAX, DMAX), "sub": (DMAX, 0xFFEFFFFFFFFFFFFF),
                       "div": (DMAX, 0x3FE0000000000000)},
              "snan": (DS, D1), "qnan_den": (DQ, DDEN), "den": (DDEN, D1), "den_zero": (DDEN, 0)},
    }
    for op in ("mul", "add", "sub", "div"):
        for fmt, suf in ((F32, "ps"), (F64, "pd")):
            w = 1 + fmt[0] + fmt[1]
            n = 128 // w
            c = cases[fmt]
            ex, rd, ov = c["exact"][op], c["round"][op], c["over"][op]
            fn = "p_%s%s" % (op, suf)

            def row(name, lanes, mx):
                A = sum(a << (w * i) for i, (a, b) in enumerate(lanes))
                B = sum(b << (w * i) for i, (a, b) in enumerate(lanes))
                v, f = packed(op, fmt, (mx >> 13) & 3, A, B)
                PROWS.append(("%s%s_%s" % (op, suf, name), fn, mx, A, B, v, f))

            mix = [rd, ex, ov, c["qnan_den"]] if n == 4 else [rd, ov]
            for rc, mode in enumerate(MODES):
                row("mix/%s" % mode, mix, 0x1F80 | (rc << 13))
            for k in range(n):
                row("loud@%d" % k, [c["snan"] if i == k else ex for i in range(n)], 0x1F80)
            row("de_split", [c["qnan_den"], c["den"]] + [ex] * (n - 2), 0x1F80)
            row("nan_den_only", [c["qnan_den"]] + [ex] * (n - 1), 0x1F80)
            if op == "div":
                row("ze_de", [c["den_zero"], c["den"]] + [ex] * (n - 2), 0x1F80)
                row("ze_only", [c["den_zero"]] + [ex] * (n - 1), 0x1F80)
            # a sticky flag is history, never an input
            row("sticky1fbf", [ex] * n, 0x1FBF)
            # THE PACKED INDEFINITE, in the TOP lane beside exact lanes: 0/0, inf*0, inf-inf, inf+(-inf). The SDM's
            # indefinite has sign 1 (Vol. 1 §4.8.3.7); x86isa's has none (D265), so these rows are where a lane-level
            # divergence would show, and no B5 vector reaches them (D283 §1).
            inf = 0x7F800000 if w == 32 else 0x7FF0000000000000
            ninf = inf | (1 << (w - 1))
            ind = {"div": (0, 0), "mul": (inf, 0), "sub": (inf, inf), "add": (inf, ninf)}[op]
            row("indef@%d" % (n - 1), [ex] * (n - 1) + [ind], 0x1F80)


def main():
    # ⛔ AN UNKNOWN FLAG USED TO PRINT THE WHOLE GENERATED FILE AND EXIT 0 — and worse, the
    # line below echoes `sys.argv[1:]` into the artifact's OWN PROVENANCE COMMENT, so a typo'd
    # flag was written into a generated C file as the recipe that produced it. Measured:
    # `--definitely-not-a-real-flag-xyz` gave 514 lines, rc 0, and a header claiming it.
    P.strict_flags(__file__)
    build()
    build_packed()
    plant = "--plant" in sys.argv
    print("/* GENERATED by hwprobe/mk_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    print("static const struct row ROWS[] = {")
    for i, (name, fn, mx, a, b, want, mask, flags) in enumerate(ROWS):
        if plant and i == 0:
            flags ^= PE        # the control: one expectation made wrong on purpose
        print('  {"%s", %s, 0x%04x, 0x%016xULL, 0x%016xULL, 0x%016xULL, 0x%016xULL, 0x%02x},'
              % (name, fn, mx, a, b, want & mask, mask, flags))
    print("};")
    print("static const struct op OPS[] = {")
    for i, (fn, bs) in enumerate(OPS.items()):
        b = bytearray.fromhex(bs)
        if "--plant-op" in sys.argv and i == 0:
            b[-1] ^= 0x01      # the control: the declared instruction is not the one in sse_ops.S
        print('  {"%s", %s, %d, {%s}},' % (fn, fn, len(b), ", ".join("0x%02x" % x for x in b)))
    print("};")
    lo = lambda x: x & ((1 << 64) - 1)
    print("static const struct prow PROWS[] = {")
    for i, (name, fn, mx, A, B, want, flags) in enumerate(PROWS):
        if "--plant-packed" in sys.argv and i == 0:
            want ^= 1 << 64    # the control: one bit of the HIGH quadword made wrong on purpose
        print('  {"%s", %s, 0x%04x, 0x%016xULL, 0x%016xULL, 0x%016xULL, 0x%016xULL, 0x%016xULL, 0x%016xULL, 0x%02x},'
              % (name, fn, mx, lo(A), A >> 64, lo(B), B >> 64, lo(want), want >> 64, flags))
    print("};")
    print("static const struct pop POPS[] = {")
    for i, (fn, bs) in enumerate(POPS.items()):
        b = bytearray.fromhex(bs)
        if "--plant-pop" in sys.argv and i == 0:
            b[-1] ^= 0x01      # the control: the declared packed instruction is not the one in sse_ops.S
        print('  {"%s", %s, %d, {%s}},' % (fn, fn, len(b), ", ".join("0x%02x" % x for x in b)))
    print("};")


if __name__ == "__main__":
    main()
