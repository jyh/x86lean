#!/usr/bin/env python3
"""K4 — an INDEPENDENT reference for SSE MULSS/MULSD under each MXCSR.RC mode.

Written from IEEE-754 §4.3 / §7.4 and SDM Vol. 1 §4.8.3.5 / Table 4-7 (the SSE NaN rule),
never from the Lean draft. Exact rational arithmetic (fractions.Fraction); the rounding
is done by FLOORING the exact value onto the grid of its own exponent, which is a different
construction from the draft's shift-and-remainder.

Carrier: the operand is a 64-bit integer; only its low w bits are the format (a binary32
carrier holds junk above bit 31, which the rule must not read). The result is the low w
bits only.
"""
from fractions import Fraction
import math

B32 = (8, 23)
B64 = (11, 52)
MODES = ("nearest", "down", "up", "zero")


def parts(fmt, x):
    ew, mw = fmt
    w = 1 + ew + mw
    x &= (1 << w) - 1
    return x >> (ew + mw), (x >> mw) & ((1 << ew) - 1), x & ((1 << mw) - 1)


def value(fmt, x):
    """Exact Fraction of a finite operand (sign applied)."""
    ew, mw = fmt
    bias = (1 << (ew - 1)) - 1
    s, e, m = parts(fmt, x)
    if e == 0:
        v = Fraction(m) * Fraction(2) ** (1 - bias - mw)
    else:
        v = Fraction((1 << mw) | m) * Fraction(2) ** (e - bias - mw)
    return -v if s else v


def floor_log2(v):
    """floor(log2(v)) for a positive Fraction, by integer bit lengths."""
    n, d = v.numerator, v.denominator
    k = n.bit_length() - d.bit_length()
    # 2^k <= n/d < 2^(k+1) may be off by one
    if Fraction(2) ** k > v:
        k -= 1
    assert Fraction(2) ** k <= v < Fraction(2) ** (k + 1)
    return k


def encode(fmt, neg, mag):
    """Encode a representable non-negative Fraction magnitude (below overflow)."""
    ew, mw = fmt
    bias = (1 << (ew - 1)) - 1
    sgn = (1 << (ew + mw)) if neg else 0
    if mag == 0:
        return sgn
    k = floor_log2(mag)
    if k < 1 - bias:                          # subnormal
        q = mag / Fraction(2) ** (1 - bias - mw)
        assert q.denominator == 1 and q < (1 << mw)
        return sgn | int(q)
    q = mag / Fraction(2) ** (k - mw)
    assert q.denominator == 1 and (1 << mw) <= q < (1 << (mw + 1))
    return sgn | ((k + bias) << mw) | (int(q) - (1 << mw))


def round_to(fmt, rc, v):
    """Round a non-zero exact Fraction to the format. Returns (bits, path)."""
    ew, mw = fmt
    bias = (1 << (ew - 1)) - 1
    emax = bias
    neg = v < 0
    mag = -v if neg else v
    k = floor_log2(mag)
    ulp = Fraction(2) ** max(k - mw, 1 - bias - mw)
    lo = math.floor(mag / ulp) * ulp
    hi = lo + ulp
    if lo == mag:
        r, path = lo, "exact"
    else:
        path = "inexact"
        if rc == "nearest":
            d1, d2 = mag - lo, hi - mag
            if d1 < d2:
                r = lo
            elif d2 < d1:
                r = hi
            else:
                r = lo if int(lo / ulp) % 2 == 0 else hi
                path = "tie"
        elif rc == "zero":
            r = lo
        elif rc == "down":
            r = hi if neg else lo
        else:  # up
            r = lo if neg else hi
    top = Fraction(2) ** (emax + 1)
    if r >= top:
        away = rc == "nearest" or (rc == "up" and not neg) or (rc == "down" and neg)
        sgn = (1 << (ew + mw)) if neg else 0
        if away:
            return sgn | (((1 << ew) - 1) << mw), "overflow-inf"
        return sgn | ((((1 << ew) - 1) << mw) - 1), "overflow-max"
    if path != "exact" and k < 1 - bias:
        path += "-tiny"
    if r > 0 and floor_log2(r) > k:
        path += "-carry"
    return encode(fmt, neg, r), path


def ref_mul(fmt, rc, a, b):
    ew, mw = fmt
    w = 1 + ew + mw
    mask = (1 << w) - 1
    quiet = 1 << (mw - 1)
    all1 = (1 << ew) - 1
    sa, ea, fa = parts(fmt, a)
    sb, eb, fb = parts(fmt, b)
    nan_a = ea == all1 and fa != 0
    nan_b = eb == all1 and fb != 0
    if nan_a:                                  # SDM Table 4-7: the FIRST source wins
        return ((a & mask) | quiet), "nan-first"
    if nan_b:
        return ((b & mask) | quiet), "nan-second"
    neg = sa != sb
    sgn = (1 << (ew + mw)) if neg else 0
    inf_a = ea == all1
    inf_b = eb == all1
    zero_a = ea == 0 and fa == 0
    zero_b = eb == 0 and fb == 0
    if inf_a or inf_b:
        if zero_a or zero_b:                   # invalid: the QNaN floating-point indefinite
            return (1 << (ew + mw)) | (all1 << mw) | quiet, "invalid"
        return sgn | (all1 << mw), "inf"
    if zero_a or zero_b:
        return sgn, "zero"
    return round_to(fmt, rc, value(fmt, a) * value(fmt, b))


def _strict():
    """ref_mul takes NO flags, so every flag is unknown. Stated by a call rather than by silence:
    the flag-strictness gate recognises this helper, and a script that simply ignores argv is
    indistinguishable from one that forgot to check it."""
    import os as _o
    import sys as _s
    _s.path.insert(0, _o.path.join(_o.path.dirname(_o.path.dirname(_o.path.abspath(__file__))), "scripts"))
    import portable as _P
    _P.strict_flags(__file__)

if __name__ == "__main__":
    _strict()
    # self-checks on hand-derivable cases
    one = 0x3ff0000000000000
    assert ref_mul(B64, "nearest", one, one) == (one, "exact")
    assert ref_mul(B64, "nearest", 0x3ff0000000000001, 0x3ff8000000000000)[0] == 0x3ff8000000000002
    assert ref_mul(B64, "nearest", 0x3ff0000000000003, 0x3ff8000000000000)[0] == 0x3ff8000000000004
    assert ref_mul(B64, "nearest", 0x7fefffffffffffff, 0x4000000000000000)[0] == 0x7ff0000000000000
    assert ref_mul(B64, "zero", 0x7fefffffffffffff, 0x4000000000000000)[0] == 0x7fefffffffffffff
    assert ref_mul(B64, "up", 1, 1)[0] == 1
    assert ref_mul(B64, "nearest", 1, 1)[0] == 0
    assert ref_mul(B64, "down", 0x8000000000000001, 1)[0] == 0x8000000000000001
    print("ref_mul self-checks OK")
