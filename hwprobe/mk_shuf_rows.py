#!/usr/bin/env python3
"""hwprobe/mk_shuf_rows.py — the V1b rows the x86-64 referee runs (D336), with expectations DERIVED HERE.

PSHUFB, PALIGNR, PINSRD, PINSRQ, PEXTRD and PEXTRQ (legacy SSE) carry values between XMM registers, memory and GPRs, so
they have their own path, beside the SSE, integer and bit-string ones and untouched by them: `shuf_ops.S` (one function
per form and imm8), `shuf_probe.c`, and this file.

Every expected value comes from a stated rule in this file (SDM Vol. 2B PSHUFB, PALIGNR, PINSRB/PINSRD/PINSRQ,
PEXTRB/PEXTRD/PEXTRQ), never from ACL2 x86isa (which refuses all six) and never from x86lean:

  SHUFB-RULE   result byte i := 0 if SRC byte i has bit 7 set, else DEST byte (SRC byte i AND 0FH) — DEST's ORIGINAL
               value; bits 6:4 of the control byte are ignored.
  ALIGNR-RULE  result := (((DEST << 128) OR SRC) >> (imm8 * 8)) AND (2^128 - 1); imm8 >= 32 gives zero.
  INSR-RULE    lane SEL of DEST := the w-bit source, SEL = imm8[1:0] (w = 32) or imm8[0] (w = 64); other lanes kept.
  EXTR-RULE    DEST := lane SEL of SRC, zero-extended to 64 bits (a 32-bit GPR write clears bits 63:32).
  NO-FLAGS     none of the six writes a flag: the six arithmetic flags leave as they entered.
  FRAME        every row compares ALL of XMM0 and RAX: a form whose destination is XMM0 must leave RAX's canary, and
               PEXTRD/Q (destination RAX) must leave XMM0 as it was.

Usage: mk_shuf_rows.py [--plant | --plant-op | --plant-zx]   writes C rows on stdout.
  --plant      flips bit 64 of row 0's expected XMM0 (the HIGH quadword): exactly one disagreement (exit 1)
  --plant-op   declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --plant-zx   sets bit 32 of the expected RAX in the row PLANT_ZX (a PEXTRD row): exactly that row must disagree
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "scripts"))
import portable as P  # noqa: E402

ARITH = 0x8d5
M64 = (1 << 64) - 1
M128 = (1 << 128) - 1
CANARY = 0xC3C3C3C3C3C3C3C3       # RAX before the instruction

# The encodings the assembler gives each shape (register conventions in shuf_ops.S's header), the imm8 appended.
ENC = {
    ("pshufb", "rr"): "660f3800c1",   # pshufb %xmm1, %xmm0
    ("pshufb", "rm"): "660f380003",   # pshufb (%rbx), %xmm0
    ("palignr", "rr"): "660f3a0fc1",  # palignr $i, %xmm1, %xmm0
    ("palignr", "rm"): "660f3a0f03",  # palignr $i, (%rbx), %xmm0
    ("pinsrd", "rr"): "660f3a22c1",   # pinsrd $i, %ecx, %xmm0
    ("pinsrd", "rm"): "660f3a2203",   # pinsrd $i, (%rbx), %xmm0
    ("pinsrq", "rr"): "66480f3a22c1",  # pinsrq $i, %rcx, %xmm0
    ("pextrd", "rr"): "660f3a16c8",   # pextrd $i, %xmm1, %eax
    ("pextrq", "rr"): "66480f3a16c8",  # pextrq $i, %xmm1, %rax
}

# (mnemonic, shape, imm8s) — one function per imm8 (None: the form has no immediate).
FUNCS = [
    ("pshufb", "rr", [None]),
    ("pshufb", "rm", [None]),
    ("palignr", "rr", [0, 1, 4, 8, 15, 16, 17, 24, 31, 32, 33, 128, 255]),
    ("palignr", "rm", [5, 16, 20]),
    ("pinsrd", "rr", [0, 1, 2, 3, 4, 7, 254]),
    ("pinsrd", "rm", [1, 6]),
    ("pinsrq", "rr", [0, 1, 2, 255]),
    ("pextrd", "rr", [0, 1, 2, 3, 5, 255]),
    ("pextrq", "rr", [0, 1, 3, 128]),
]


def fn_name(mn, shape, imm):
    return "s_%s_%s" % (mn, shape) + ("" if imm is None else "_i%d" % imm)


OPS = []    # (fn, declared bytes, mnemonic, shape, imm)
for _mn, _sh, _imms in FUNCS:
    for _i in _imms:
        OPS.append((fn_name(_mn, _sh, _i), ENC[(_mn, _sh)] + ("" if _i is None else "%02x" % _i), _mn, _sh, _i))


def from_bytes(bs):
    return sum(b << (8 * i) for i, b in enumerate(bs))


# The data. Every byte of A1/B1 names its own position, so a wrong lane reads as a wrong NAME in the listing.
A1 = from_bytes([0xA0 + i for i in range(16)])
B1 = from_bytes([0xB0 + i for i in range(16)])
A2 = 0xFEDCBA98765432100123456789ABCDEF
B2 = 0x8899AABBCCDDEEFF0011223344556677
G1 = 0xDEADBEEF89ABCDEF           # junk above bit 31, so PINSRD reads only the low half
G2 = 0x7FFFFFFF80000001
PAIRS = [("p1", A1, B1, G1), ("p2", A2, B2, G2)]

# PSHUFB's controls (SRC bytes, i = 0..15).
CONTROLS = [
    ("ident", [i for i in range(16)]),
    ("rev", [15 - i for i in range(16)]),
    ("allhi", [0x80] * 16),
    ("althi", [(0x80 | i) if i % 2 == 0 else i for i in range(16)]),
    ("junk64", [0x70 | (15 - i) for i in range(16)]),     # bits 6:4 set, bit 7 clear: the index is the low nibble
    ("bcast0", [0x00] * 16),
    ("bcast15", [0x0F] * 16),
    ("mixed", [(i * 0x35 + 0x1B) & 0xFF for i in range(16)]),
]
DESTS = [("a1", A1), ("a2", A2)]


def shufb(a, ctl):
    """SHUFB-RULE."""
    out = 0
    for i in range(16):
        c = (ctl >> (8 * i)) & 0xFF
        if not c & 0x80:
            out |= ((a >> (8 * (c & 0x0F))) & 0xFF) << (8 * i)
    return out


def alignr(a, b, imm):
    """ALIGNR-RULE."""
    return (((a << 128) | b) >> (imm * 8)) & M128


def insr(w, a, v, imm):
    """INSR-RULE."""
    sel = imm % (128 // w)
    m = ((1 << w) - 1) << (sel * w)
    return (a & ~m & M128) | ((v & ((1 << w) - 1)) << (sel * w))


def extr(w, b, imm):
    """EXTR-RULE: zero-extended to 64."""
    return (b >> (w * (imm % (128 // w)))) & ((1 << w) - 1)


ROWS = []   # (name, fn, a, b, g, f, want_xmm0, want_rax)


def build():
    ROWS.clear()
    for fn, _bs, mn, shape, imm in OPS:
        if mn == "pshufb":
            cases = [(dn + "_" + cn, a, from_bytes(c), G1) for dn, a in DESTS for cn, c in CONTROLS]
        else:
            cases = [(pn, a, b, g) for pn, a, b, g in PAIRS]
        for cn, a, b, g in cases:
            for f in (0, ARITH):
                if mn == "pshufb":
                    r, ax = shufb(a, b), CANARY
                elif mn == "palignr":
                    r, ax = alignr(a, b, imm), CANARY
                elif mn == "pinsrd":
                    r, ax = insr(32, a, g if shape == "rr" else b, imm), CANARY   # m32 is the low dword at [RBX] = b
                elif mn == "pinsrq":
                    r, ax = insr(64, a, g, imm), CANARY
                elif mn == "pextrd":
                    r, ax = a, extr(32, b, imm)
                elif mn == "pextrq":
                    r, ax = a, extr(64, b, imm)
                else:
                    raise SystemExit("mk_shuf_rows: no rule for %s" % mn)
                ROWS.append(("%s_%s%s" % (fn[2:], cn, "_set" if f else ""), fn, a, b, g, f, r, ax))


# The third control's row: a PEXTRD row, whose expected RAX has bits 63:32 zero by the zero-extension.
PLANT_ZX = "pextrd_rr_i1_p1"


def main():
    P.strict_flags(__file__)
    build()
    plant = "--plant" in sys.argv
    plant_zx = "--plant-zx" in sys.argv
    print("/* GENERATED by hwprobe/mk_shuf_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    for fn, _b, _m, _s, _i in OPS:
        print("void %s(struct sio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const struct srow SROWS[] = {")
    hit = False
    for i, (name, fn, a, b, g, f, r, ax) in enumerate(ROWS):
        if plant and i == 0:
            r ^= 1 << 64       # the control: one expectation made wrong on purpose, in the HIGH quadword
        if plant_zx and name == PLANT_ZX:
            if ax >> 32:
                raise SystemExit("mk_shuf_rows: the --plant-zx row's expected RAX is not zero above bit 31")
            ax |= 1 << 32
            hit = True
        print('  {"%s", %s, 0x%016xULL, 0x%016xULL, 0x%016xULL, 0x%016xULL, 0x%016xULL, 0x%03x, '
              '0x%016xULL, 0x%016xULL, 0x%016xULL},'
              % (name, fn, a & M64, a >> 64, b & M64, b >> 64, g, f, r & M64, r >> 64, ax))
    if plant_zx and not hit:
        raise SystemExit("mk_shuf_rows: the --plant-zx row %s does not exist" % PLANT_ZX)
    print("};")
    print("static const struct sop SOPS[] = {")
    for i, (fn, bs, _m, _s, _i) in enumerate(OPS):
        bb = bytearray.fromhex(bs)
        if "--plant-op" in sys.argv and i == 0:
            bb[-1] ^= 0x01     # the control: the declared instruction is not the one in shuf_ops.S
        print('  {"%s", %s_at, %d, {%s}},' % (fn, fn, len(bb), ", ".join("0x%02x" % x for x in bb)))
    print("};")


if __name__ == "__main__":
    main()
