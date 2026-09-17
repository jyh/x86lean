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
Usage: mk_rows.py [--plant | --plant-op]   writes C rows on stdout.
  --plant     flips ONE expectation: the referee must report exactly one disagreement (exit 1)
  --plant-op  declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
"""
import sys
from fractions import Fraction
import ref_mul as R

IE, DE, OE, UE, PE = 1, 2, 8, 16, 32
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


def cvtsi2sd32(a):
    """CVTSI2SD from an int32: exact for every input, so RC is never consulted, and integer 0 gives +0
    (a conversion is not a sum; IEEE 754's roundTowardNegative -0 rule is for exact-zero sums).
    No exception. (x86isa gives -0 at RC=down: cvt-spec.lisp sse-cvt-int-to-fp, D266.)"""
    v = a & 0xFFFFFFFF
    v = v - (1 << 32) if v >> 31 else v
    if v == 0:
        return 0, 0
    return R.encode(F64, v < 0, abs(Fraction(v))), 0


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
       "p_cvtss2sd": "f30f5ac8", "p_cvttsd2si": "f20f2cc0"}

ROWS = []   # (name, fn, mxcsr_in, a, b, want, want_mask, want_flags)


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


def main():
    build()
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


if __name__ == "__main__":
    main()
