#!/usr/bin/env python3
"""hwprobe/mk_int_rows.py — the INTEGER rows the x86-64 referee runs (D330, D334), with expectations DERIVED HERE.

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

D334 (W1c) adds, from SDM Vol. 2A ANDN, BEXTR, BLSMSK, BLSR, BZHI and Vol. 2B MOVNTI, PDEP, PEXT, RORX (D334 states
each rule in full; `bmi()` below is each, one branch per rule):

  ANDN-RULE    DEST := (NOT SRC1) AND SRC2; SF, ZF from DEST; CF = OF = 0; AF, PF undefined.
  BEXTR-RULE   START = SRC2[7:0], LEN = SRC2[15:8]; DEST := the LEN bits of SRC1 from START (zeros past bit w-1);
               ZF from DEST; CF = OF = 0; AF, SF, PF undefined.
  BZHI-RULE    N = SRC2[7:0]; DEST := SRC1 with bits w-1:N cleared when N < w, unchanged otherwise; CF = (N > w-1);
               SF, ZF from DEST; OF = 0; AF, PF undefined.
  BLSMSK-RULE  DEST := (SRC-1) XOR SRC; SF from DEST; ZF = 0; CF = (SRC = 0); OF = 0; AF, PF undefined.
  BLSR-RULE    DEST := (SRC-1) AND SRC; SF, ZF from DEST; CF = (SRC = 0); OF = 0; AF, PF undefined.
  PDEP-RULE    the low bits of SRC1 deposited, in order, at the set bits of the mask. No flag is written.
  PEXT-RULE    the bits of SRC1 at the set bits of the mask, packed low in order. No flag is written.
  RORX-RULE    rotate right by imm8 AND (w-1). No flag is written.
  NT-STORE     MOVNTI: [RBX] := SRC at w bits (at w = 32 the quadword's high half is untouched). No flag is written.
  NO-FLAGS     a form that writes no flag leaves all six arithmetic flags exactly as they entered.

RFLAGS is compared on the six arithmetic flags (mask 0x8d5) less, per row, those the SDM leaves undefined for its form. Each probe function loads RFLAGS from the row with
those six bits replaced and every other bit left as the process had it.

Usage: mk_int_rows.py [--plant | --plant-op | --plant-new]   writes C rows on stdout.
  --plant      flips CF in ONE expectation: the referee must report exactly one disagreement (exit 1)
  --plant-op   declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --plant-new  flips ZF (a DEFINED flag) in the masked row andnq_rr_zero: exactly that row must disagree (exit 1)
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
    # ══ D334 (W1c). Destination R8 (R8D at 32 bits); R9 is named by no operand and keeps the canary. ══
    ("andnq_rr", "i_andnq_rr", "c462e8f2c1", 64, "andn"),        # andnq %rcx, %rdx, %r8      r8 := ~RDX & RCX
    ("andnq_rm", "i_andnq_rm", "c462e8f203", 64, "andn"),        # andnq (%rbx), %rdx, %r8
    ("andnl_rr", "i_andnl_rr", "c46268f2c1", 32, "andn"),        # andnl %ecx, %edx, %r8d
    ("andnl_rm", "i_andnl_rm", "c46268f203", 32, "andn"),        # andnl (%rbx), %edx, %r8d
    ("bextrq_rr", "i_bextrq_rr", "c462e8f7c1", 64, "bextr"),     # bextrq %rdx, %rcx, %r8     source RCX, control RDX
    ("bextrq_rm", "i_bextrq_rm", "c462e8f703", 64, "bextr"),     # bextrq %rdx, (%rbx), %r8
    ("bextrl_rr", "i_bextrl_rr", "c46268f7c1", 32, "bextr"),     # bextrl %edx, %ecx, %r8d
    ("bextrl_rm", "i_bextrl_rm", "c46268f703", 32, "bextr"),     # bextrl %edx, (%rbx), %r8d
    ("bzhiq_rr", "i_bzhiq_rr", "c462e8f5c1", 64, "bzhi"),        # bzhiq %rdx, %rcx, %r8      source RCX, index RDX
    ("bzhiq_rm", "i_bzhiq_rm", "c462e8f503", 64, "bzhi"),        # bzhiq %rdx, (%rbx), %r8
    ("bzhil_rr", "i_bzhil_rr", "c46268f5c1", 32, "bzhi"),        # bzhil %edx, %ecx, %r8d
    ("bzhil_rm", "i_bzhil_rm", "c46268f503", 32, "bzhi"),        # bzhil %edx, (%rbx), %r8d
    ("blsmskq_rr", "i_blsmskq_rr", "c4e2b8f3d1", 64, "blsmsk"),  # blsmskq %rcx, %r8          source RCX
    ("blsmskq_rm", "i_blsmskq_rm", "c4e2b8f313", 64, "blsmsk"),  # blsmskq (%rbx), %r8
    ("blsmskl_rr", "i_blsmskl_rr", "c4e238f3d1", 32, "blsmsk"),  # blsmskl %ecx, %r8d
    ("blsmskl_rm", "i_blsmskl_rm", "c4e238f313", 32, "blsmsk"),  # blsmskl (%rbx), %r8d
    ("blsrq_rr", "i_blsrq_rr", "c4e2b8f3c9", 64, "blsr"),        # blsrq %rcx, %r8
    ("blsrq_rm", "i_blsrq_rm", "c4e2b8f30b", 64, "blsr"),        # blsrq (%rbx), %r8
    ("blsrl_rr", "i_blsrl_rr", "c4e238f3c9", 32, "blsr"),        # blsrl %ecx, %r8d
    ("blsrl_rm", "i_blsrl_rm", "c4e238f30b", 32, "blsr"),        # blsrl (%rbx), %r8d
    ("pdepq_rr", "i_pdepq_rr", "c462ebf5c1", 64, "pdep"),        # pdepq %rcx, %rdx, %r8      value RDX, mask RCX
    ("pdepq_rm", "i_pdepq_rm", "c462ebf503", 64, "pdep"),        # pdepq (%rbx), %rdx, %r8
    ("pdepl_rr", "i_pdepl_rr", "c4626bf5c1", 32, "pdep"),        # pdepl %ecx, %edx, %r8d
    ("pdepl_rm", "i_pdepl_rm", "c4626bf503", 32, "pdep"),        # pdepl (%rbx), %edx, %r8d
    ("pextq_rr", "i_pextq_rr", "c462eaf5c1", 64, "pext"),        # pextq %rcx, %rdx, %r8      value RDX, mask RCX
    ("pextq_rm", "i_pextq_rm", "c462eaf503", 64, "pext"),        # pextq (%rbx), %rdx, %r8
    ("pextl_rr", "i_pextl_rr", "c4626af5c1", 32, "pext"),        # pextl %ecx, %edx, %r8d
    ("pextl_rm", "i_pextl_rm", "c4626af503", 32, "pext"),        # pextl (%rbx), %edx, %r8d
    ("rorxq_rr_i0", "i_rorxq_rr_i0", "c463fbf0c100", 64, "rorx"),    # rorxq $0, %rcx, %r8
    ("rorxq_rr_i1", "i_rorxq_rr_i1", "c463fbf0c101", 64, "rorx"),    # rorxq $1, %rcx, %r8
    ("rorxq_rr_i63", "i_rorxq_rr_i63", "c463fbf0c13f", 64, "rorx"),  # rorxq $63, %rcx, %r8
    ("rorxq_rr_i69", "i_rorxq_rr_i69", "c463fbf0c145", 64, "rorx"),  # rorxq $69, %rcx, %r8      imm8 AND 3FH = 5
    ("rorxq_rm_i7", "i_rorxq_rm_i7", "c463fbf00307", 64, "rorx"),    # rorxq $7, (%rbx), %r8
    ("rorxl_rr_i0", "i_rorxl_rr_i0", "c4637bf0c100", 32, "rorx"),    # rorxl $0, %ecx, %r8d
    ("rorxl_rr_i1", "i_rorxl_rr_i1", "c4637bf0c101", 32, "rorx"),    # rorxl $1, %ecx, %r8d
    ("rorxl_rr_i31", "i_rorxl_rr_i31", "c4637bf0c11f", 32, "rorx"),  # rorxl $31, %ecx, %r8d
    ("rorxl_rr_i37", "i_rorxl_rr_i37", "c4637bf0c125", 32, "rorx"),  # rorxl $37, %ecx, %r8d     imm8 AND 1FH = 5
    ("rorxl_rm_i7", "i_rorxl_rm_i7", "c4637bf00307", 32, "rorx"),    # rorxl $7, (%rbx), %r8d
    ("movntiq_mr", "i_movntiq_mr", "480fc303", 64, "movnti"),    # movntiq %rax, (%rbx)       store RAX to [RBX]
    ("movntil_mr", "i_movntil_mr", "0fc303", 32, "movnti"),      # movntil %eax, (%rbx)
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

ROWS = []      # (name, fn, a, b, d, f, want0, want1, two, wantf, flagmask)

# ══ D334 (W1c): the operand sets. Every 32-bit form is fed values with junk above bit 31 somewhere in its set, and
# every result is compared at 64 bits, so ZERO-EXT is asked of each form. ══
PAT = 0x0123456789ABCDEF
# ANDN-RULE's pairs (d = RDX = SRC1, b = SRC2).
ANDN_PAIRS = [
    ("zero", 0, 0),
    ("zero_ones", 0, ONES),
    ("ones_ones", ONES, ONES),
    ("ones_zero", ONES, 0),
    ("alt_ones", 0x00FF00FF00FF00FF, ONES),
    ("sign_ones", 1 << 63, ONES),
    ("max_ones", (1 << 63) - 1, ONES),
    ("hi32_mixed", 0xFFFFFFFF00000000, 0x1234567880000001),
    ("junk_sign32", 0xFFFFFFFF7FFFFFFF, 0x00000000FFFFFFFF),
]
# BLSMSK-RULE's and BLSR-RULE's sources (b).
BLS_SRCS = [("zero", 0), ("one", 1), ("ones", ONES), ("sign", 1 << 63), ("bit31", 1 << 31), ("bit4", 0x10),
            ("hi32", 0xFFFFFFFF00000000), ("pat", 0x0123456789ABCDE0)]
# BEXTR-RULE's sources and controls; a control is START | LEN << 8, plus one with junk above bit 15.
EXT_SRCS = [("ones", ONES), ("pat", PAT)]


def bextr_ctls(w):
    return [("s0l0", 0x0000), ("s0l8", 0x0800), ("s4l8", 0x0804), ("s0lw", w << 8), ("s0l255", 0xFF00),
            ("stopl1", 0x0100 | (w - 1)), ("s%dl16" % (w - 8), 0x1000 | (w - 8)), ("swl1", 0x0100 | w),
            ("s200l10", 0x0AC8), ("s32l16", 0x1020), ("junk_s4l8", 0xFFFFFFFFFFFF0804)]


def bzhi_idxs(w):
    return [("n0", 0), ("n1", 1), ("nhalf", w // 2), ("ntop", w - 1), ("nw", w), ("nw1", w + 1), ("n128", 128),
            ("n255", 255), ("junk_n5", 0xFFFFFFFFFFFFFF05), ("n256", 0x100)]


# PDEP-RULE's and PEXT-RULE's masks (b) and values (d).
PBIT_MASKS = [("m0", 0), ("mones", ONES), ("m55", 0x5555555555555555), ("maa", 0xAAAAAAAAAAAAAAAA),
              ("msparse", 0x8000000100000001), ("mf0", 0xF0F0F0F0F0F0F0F0), ("msign", 1 << 63),
              ("mlo32", 0x00000000FFFFFFFF)]
PBIT_VALS = [("vones", ONES), ("vpat", PAT)]
ROR_SRCS = [("pat", PAT), ("one", 1), ("ends", 0x8000000000000001), ("junk_one32", 0xFFFFFFFF00000001)]
# MOVNTI's (a = the stored register, b = the quadword in memory before the store).
NT_PAIRS = [("pat_ones", PAT, ONES), ("zero_ones", 0, ONES), ("ones_zero", ONES, 0),
            ("ends_mixed", 0x8000000000000001, 0x123456789ABCDEF0)]


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


def szf(w, r):
    """SF and ZF of a w-bit result."""
    return (SF if r >> (w - 1) & 1 else 0) | (ZF if r == 0 else 0)


def bmi(kind, w, b, d, imm=0):
    """D334's rules. Returns (DEST, flags written, the flags the SDM leaves undefined)."""
    s, ctl = b & mask(w), d & mask(w)
    if kind == "andn":                        # ANDN-RULE
        r = ~ctl & s & mask(w)
        return r, szf(w, r), AF | PF
    if kind == "bextr":                       # BEXTR-RULE
        start, ln = ctl & 0xFF, (ctl >> 8) & 0xFF
        r = (s >> start) & mask(ln)
        return r, (ZF if r == 0 else 0), AF | PF | SF
    if kind == "bzhi":                        # BZHI-RULE
        n = ctl & 0xFF
        r = s & mask(n) if n < w else s
        return r, szf(w, r) | (CF if n > w - 1 else 0), AF | PF
    if kind == "blsmsk":                      # BLSMSK-RULE
        r = ((s - 1) ^ s) & mask(w)
        return r, (SF if r >> (w - 1) & 1 else 0) | (CF if s == 0 else 0), AF | PF
    if kind == "blsr":                        # BLSR-RULE
        r = ((s - 1) & s) & mask(w)
        return r, szf(w, r) | (CF if s == 0 else 0), AF | PF
    if kind in ("pdep", "pext"):              # PDEP-RULE / PEXT-RULE: SRC1 = d (the value), SRC2 = b (the mask)
        r, k = 0, 0
        for m in range(w):
            if s >> m & 1:
                if kind == "pdep":
                    r |= (ctl >> k & 1) << m
                else:
                    r |= (ctl >> m & 1) << k
                k += 1
        return r, None, 0
    if kind == "rorx":                        # RORX-RULE
        y = imm & (w - 1)
        return ((s >> y) | (s << (w - y))) & mask(w), None, 0
    raise SystemExit("mk_int_rows: no rule for %s" % kind)


def build():
    ROWS.clear()
    for form, fn, bs, w, kind in OPS:
        if kind in ("adcx", "adox"):
            cbit = CF if kind == "adcx" else OF
            others = ARITH & ~cbit
            for pn, a, b in ADD_PAIRS:
                for cin in (0, 1):
                    for other in (0, 1):
                        f = (cbit if cin else 0) | (others if other else 0)
                        r, fo = add_carry(kind, w, a, b, f)
                        ROWS.append(("%s_%s_c%d%s" % (form, pn, cin, "_set" if other else ""),
                                     fn, a, b, 0, f, r, 0, 0, fo, ARITH))
        elif kind in ("mulx", "mulx1"):
            for pn, d, b in MUL_PAIRS:
                for f in (0, ARITH):
                    hi, lo = mul_halves(w, d, b)
                    # SAME-DEST: one register holds the high half, and R9 — named by no operand of that form — must
                    # still hold the canary, so the second comparison asks that nothing else was written.
                    w1 = lo if kind == "mulx" else CANARY
                    ROWS.append(("%s_%s%s" % (form, pn, "_set" if f else ""),
                                 fn, CANARY, b, d, f, hi, w1, 1, f, ARITH))
        elif kind == "movnti":
            # NT-STORE: [RBX] := RAX at w bits; at w = 32 the quadword's high half is the memory's own, untouched.
            for pn, a, b in NT_PAIRS:
                for f in (0, ARITH):
                    m = a if w == 64 else (b & ~mask(32) & ONES) | (a & mask(32))
                    ROWS.append(("%s_%s%s" % (form, pn, "_set" if f else ""),
                                 fn, a, b, 0, f, m, a, 1, f, ARITH))
        else:
            imm = bytearray.fromhex(bs)[-1] if kind == "rorx" else 0
            if kind == "andn":
                ops = [(pn, d, b) for pn, d, b in ANDN_PAIRS]
            elif kind in ("blsmsk", "blsr"):
                ops = [(pn, 0, b) for pn, b in BLS_SRCS]
            elif kind == "bextr":
                ops = [(sn + "_" + cn, c, b) for sn, b in EXT_SRCS for cn, c in bextr_ctls(w)]
            elif kind == "bzhi":
                ops = [(sn + "_" + cn, c, b) for sn, b in EXT_SRCS for cn, c in bzhi_idxs(w)]
            elif kind in ("pdep", "pext"):
                ops = [(vn + "_" + mn, v, m) for vn, v in PBIT_VALS for mn, m in PBIT_MASKS]
            elif kind == "rorx":
                ops = [(sn, 0, b) for sn, b in ROR_SRCS]
            else:
                raise SystemExit("mk_int_rows: no operand set for %s" % kind)
            for pn, d, b in ops:
                for f in (0, ARITH):
                    r, written, undef = bmi(kind, w, b, d, imm)
                    # NO-FLAGS: a form that writes no flag leaves all six as they entered. A flag-writing form
                    # writes all six; the SDM leaves `undef` undefined, so those bits are not compared.
                    wf = f if written is None else written
                    ROWS.append(("%s_%s%s" % (form, pn, "_set" if f else ""),
                                 fn, CANARY, b, d, f, r, CANARY, 1, wf & ~undef, ARITH & ~undef))


# The third control's row (D334): a W1c row whose comparison is MASKED, so the plant asks that a defined flag of a
# masked family is still compared. It flips ZF, which ANDN defines.
PLANT_NEW = "andnq_rr_zero"


def main():
    P.strict_flags(__file__)
    build()
    plant = "--plant" in sys.argv
    plant_new = "--plant-new" in sys.argv
    print("/* GENERATED by hwprobe/mk_int_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    for _form, fn, _b, _w, _k in OPS:
        print("void %s(struct iio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const struct irow IROWS[] = {")
    for i, (name, fn, a, b, d, f, w0, w1, two, wf, fm) in enumerate(ROWS):
        if plant and i == 0:
            wf ^= CF           # the control: one expectation made wrong on purpose
        if plant_new and name == PLANT_NEW:
            if not fm & ZF:
                raise SystemExit("mk_int_rows: the --plant-new row does not compare ZF")
            wf ^= ZF
        print('  {"%s", %s, 0x%016xULL, 0x%016xULL, 0x%016xULL, 0x%03x, 0x%016xULL, 0x%016xULL, %d, 0x%03x, 0x%03x},'
              % (name, fn, a, b, d, f, w0, w1, two, wf, fm))
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
