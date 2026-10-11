#!/usr/bin/env python3
"""hwprobe/mk_int_rows.py — the INTEGER rows the x86-64 referee runs (D330), with expectations DERIVED HERE.

The SSE path (`mk_rows.py`, `probe.c`, `sse_ops.S`) carries values through XMM registers and MXCSR. ADCX, ADOX and
MULX carry them through general-purpose registers and RFLAGS, so they have their own path, beside it and untouched by
it: `int_ops.S` (one function per form, GPRs and RFLAGS in, GPRs and RFLAGS out), `int_probe.c`, and this file.

Every expected value comes from a stated rule in this file (SDM Vol. 2A ADCX and ADOX, Vol. 2B MULX), never from ACL2
x86isa and never from x86lean:

  ADD-CARRY    ADCX: DEST := (DEST + SRC + CF) mod 2^w, and CF := the carry out of that sum. ADOX: the same with OF.
  ONE-FLAG     ADCX writes CF and no other flag; ADOX writes OF and no other flag. The other five arithmetic flags
               (of CF PF AF ZF SF OF) leave the instruction exactly as they entered it.
  MUL-HALVES   MULX: the unsigned product of RDX (EDX at w = 32) and SRC; the high w bits to the ModRM.reg destination
               and the low w bits to the VEX.vvvv destination. No flag is written.
  SAME-DEST    MULX with both destinations the same register leaves the HIGH half in it: the SDM's operation writes
               DEST2 (low) and then DEST1 (high), and says so.
  ZERO-EXT     at w = 32 every destination write clears bits 63:32 (SDM Vol. 1 §3.4.1.1), and only the low 32 bits of
               every source are read: the rows put junk in the upper halves to show both.

RFLAGS is compared on the six arithmetic flags only (mask 0x8d5). Each probe function loads RFLAGS from the row with
those six bits replaced and every other bit left as the process had it.

Usage: mk_int_rows.py [--plant | --plant-op]   writes C rows on stdout.
  --plant      flips CF in ONE expectation: the referee must report exactly one disagreement (exit 1)
  --plant-op   declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "scripts"))
import portable as P  # noqa: E402

CF, PF, AF, ZF, SF, OF = 0x1, 0x4, 0x10, 0x40, 0x80, 0x800
ARITH = CF | PF | AF | ZF | SF | OF          # 0x8d5
ONES = (1 << 64) - 1
CANARY = 0xC3C3C3C3C3C3C3C3                   # MULX's destinations hold this before the instruction

# (form, function, declared bytes, width, kind) — the bytes are the instruction under test, read back by the probe at
# the function's `_at` label; a mismatch refuses the run. Register conventions are int_ops.S's header.
OPS = [
    ("adcxq_rr", "i_adcxq_rr", "66480f38f6c1", 64, "adcx"),   # adcxq %rcx, %rax
    ("adcxq_rm", "i_adcxq_rm", "66480f38f603", 64, "adcx"),   # adcxq (%rbx), %rax
    ("adcxl_rr", "i_adcxl_rr", "660f38f6c1", 32, "adcx"),     # adcxl %ecx, %eax
    ("adcxl_rm", "i_adcxl_rm", "660f38f603", 32, "adcx"),     # adcxl (%rbx), %eax
    ("adoxq_rr", "i_adoxq_rr", "f3480f38f6c1", 64, "adox"),   # adoxq %rcx, %rax
    ("adoxq_rm", "i_adoxq_rm", "f3480f38f603", 64, "adox"),   # adoxq (%rbx), %rax
    ("adoxl_rr", "i_adoxl_rr", "f30f38f6c1", 32, "adox"),     # adoxl %ecx, %eax
    ("adoxl_rm", "i_adoxl_rm", "f30f38f603", 32, "adox"),     # adoxl (%rbx), %eax
    ("mulxq_rr", "i_mulxq_rr", "c462b3f6c1", 64, "mulx"),     # mulxq %rcx, %r9, %r8
    ("mulxq_rm", "i_mulxq_rm", "c462b3f603", 64, "mulx"),     # mulxq (%rbx), %r9, %r8
    ("mulxq_same", "i_mulxq_same", "c462bbf6c1", 64, "mulx1"),  # mulxq %rcx, %r8, %r8
    ("mulxl_rr", "i_mulxl_rr", "c46233f6c1", 32, "mulx"),     # mulxl %ecx, %r9d, %r8d
    ("mulxl_rm", "i_mulxl_rm", "c46233f603", 32, "mulx"),     # mulxl (%rbx), %r9d, %r8d
    ("mulxl_same", "i_mulxl_same", "c4623bf6c1", 32, "mulx1"),  # mulxl %ecx, %r8d, %r8d
]

# ADD-CARRY's operand pairs (a = DEST, b = SRC): zero, all-ones, the sign boundary, a sum of exactly all-ones (which
# carries only with a carry in), and two pairs whose 32-bit halves carry where the 64-bit sum does not, and the reverse.
ADD_PAIRS = [
    ("zero", 0, 0),
    ("zero_ones", 0, ONES),
    ("ones_one", ONES, 1),
    ("ones_ones", ONES, ONES),
    ("sign_sign", 1 << 63, 1 << 63),
    ("max_one", (1 << 63) - 1, 1),
    ("comp", 0x0123456789ABCDEF, 0xFEDCBA9876543210),
    ("lo32carry", 0xDEADBEEFFFFFFFFF, 0x1234567800000001),
    ("hi32only", 0xFFFFFFFF00000000, 0x0000000100000000),
]

# MUL-HALVES' operand pairs (d = RDX, b = SRC). The last two put junk above bit 31 so the 32-bit forms show they read
# only the low halves (ZERO-EXT); at 64 bits they are ordinary products.
MUL_PAIRS = [
    ("zero_ones", 0, ONES),
    ("one_ones", 1, ONES),
    ("ones_ones", ONES, ONES),
    ("sign_two", 1 << 63, 2),
    ("comp", 0x0123456789ABCDEF, 0xFEDCBA9876543210),
    ("lo32ones", 0xFFFFFFFF, 0xFFFFFFFF),
    ("junk_sign32", 0xA5A5A5A580000000, 0x5A5A5A5A80000000),
    ("junk_ones32", 0x12345678FFFFFFFF, 0x9ABCDEF0FFFFFFFF),
]

ROWS = []      # (name, fn, a, b, d, f, want0, want1, two, wantf)


def mask(w):
    return (1 << w) - 1


def add_carry(kind, w, a, b, f):
    """ADD-CARRY and ONE-FLAG. Returns (DEST, flags out)."""
    cbit = CF if kind == "adcx" else OF
    cin = 1 if f & cbit else 0
    s = (a & mask(w)) + (b & mask(w)) + cin
    r = s & mask(w)                           # ZERO-EXT: a 32-bit result leaves bits 63:32 clear
    fo = (f & ~cbit & ARITH) | (cbit if s >> w else 0)
    return r, fo


def mul_halves(w, d, b):
    """MUL-HALVES. Returns (high, low), each zero-extended to 64 bits."""
    p = (d & mask(w)) * (b & mask(w))
    return p >> w, p & mask(w)


def build():
    ROWS.clear()
    for form, fn, _bytes, w, kind in OPS:
        if kind in ("adcx", "adox"):
            cbit = CF if kind == "adcx" else OF
            others = ARITH & ~cbit
            for pn, a, b in ADD_PAIRS:
                for cin in (0, 1):
                    for other in (0, 1):
                        f = (cbit if cin else 0) | (others if other else 0)
                        r, fo = add_carry(kind, w, a, b, f)
                        ROWS.append(("%s_%s_c%d%s" % (form, pn, cin, "_set" if other else ""),
                                     fn, a, b, 0, f, r, 0, 0, fo))
        else:
            for pn, d, b in MUL_PAIRS:
                for f in (0, ARITH):
                    hi, lo = mul_halves(w, d, b)
                    # SAME-DEST: one register holds the high half, and R9 — named by no operand of that form — must
                    # still hold the canary, so the second comparison asks that nothing else was written.
                    w1 = lo if kind == "mulx" else CANARY
                    ROWS.append(("%s_%s%s" % (form, pn, "_set" if f else ""),
                                 fn, CANARY, b, d, f, hi, w1, 1, f))


def main():
    P.strict_flags(__file__)
    build()
    plant = "--plant" in sys.argv
    print("/* GENERATED by hwprobe/mk_int_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    for _form, fn, _b, _w, _k in OPS:
        print("void %s(struct iio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const struct irow IROWS[] = {")
    for i, (name, fn, a, b, d, f, w0, w1, two, wf) in enumerate(ROWS):
        if plant and i == 0:
            wf ^= CF           # the control: one expectation made wrong on purpose
        print('  {"%s", %s, 0x%016xULL, 0x%016xULL, 0x%016xULL, 0x%03x, 0x%016xULL, 0x%016xULL, %d, 0x%03x},'
              % (name, fn, a, b, d, f, w0, w1, two, wf))
    print("};")
    print("static const struct iop IOPS[] = {")
    for i, (_form, fn, bs, _w, _k) in enumerate(OPS):
        bb = bytearray.fromhex(bs)
        if "--plant-op" in sys.argv and i == 0:
            bb[-1] ^= 0x01     # the control: the declared instruction is not the one in int_ops.S
        print('  {"%s", %s_at, %d, {%s}},' % (fn, fn, len(bb), ", ".join("0x%02x" % x for x in bb)))
    print("};")


if __name__ == "__main__":
    main()
