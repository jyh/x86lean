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
  STORE        (D362) PEXTRD/Q to memory writes the w-bit lane to the w/8 bytes at [RBX] and nothing else; every row
               compares ALL 16 bytes at [RBX] after the instruction, so a store is compared beyond its width and a
               form that should not write memory is asked not to.

Usage: mk_shuf_rows.py [--plant | --plant-op | --plant-zx | --plant-mem]   writes C rows on stdout.
       mk_shuf_rows.py --refuse-wrong   (D362) each named wrong rule must disagree with the rules here on a named row
  --plant      flips bit 64 of row 0's expected XMM0 (the HIGH quadword): exactly one disagreement (exit 1)
  --plant-op   declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --plant-zx   sets bit 32 of the expected RAX in the row PLANT_ZX (a PEXTRD row): exactly that row must disagree
  --plant-mem  (D362) flips bit 0 of the expected memory in the row PLANT_MEM (a PEXTRD store row): exactly that row
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
    # D362: the memory shapes D336 did not take. The STORES extract from XMM0 = a, never XMM1 = b: [RBX] holds b, so a
    # store of b's own low lane rewrites the bytes already there and a dropped store would pass (D358's blind spot).
    ("pextrd", "mr"): "660f3a1603",   # pextrd $i, %xmm0, (%rbx)
    ("pextrq", "mr"): "66480f3a1603",  # pextrq $i, %xmm0, (%rbx)
    ("pinsrq", "rm"): "66480f3a2203",  # pinsrq $i, (%rbx), %xmm0
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
    ("pextrd", "mr", [0, 1, 2, 3, 5, 255]),
    ("pextrq", "mr", [0, 1, 3, 128]),
    ("pinsrq", "rm", [0, 1, 2, 255]),
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


def store(w, mem, v):
    """STORE: the w-bit value replaces the low w/8 bytes of the 16 at [RBX]; the other bytes are kept."""
    m = (1 << w) - 1
    return (mem & ~m & M128) | (v & m)


ROWS = []   # (name, fn, a, b, g, f, want_xmm0, want_rax, want_mem)

# The rules, by name, so --refuse-wrong can replace exactly one. Each takes (shape, a, b, g, imm) -> (xmm0, rax, mem).
def _rule_pextr(w):
    def f(shape, a, b, g, imm):
        if shape == "mr":
            return a, CANARY, store(w, b, extr(w, a, imm))
        return a, extr(w, b, imm), b
    return f


RULES = {
    "pshufb": lambda shape, a, b, g, imm: (shufb(a, b), CANARY, b),
    "palignr": lambda shape, a, b, g, imm: (alignr(a, b, imm), CANARY, b),
    "pinsrd": lambda shape, a, b, g, imm: (insr(32, a, g if shape == "rr" else b, imm), CANARY, b),  # m32 = b's low dword
    "pinsrq": lambda shape, a, b, g, imm: (insr(64, a, g if shape == "rr" else b, imm), CANARY, b),  # m64 = b's low qword
    "pextrd": _rule_pextr(32),
    "pextrq": _rule_pextr(64),
}


def build(rules=None):
    rules = RULES if rules is None else rules
    ROWS.clear()
    for fn, _bs, mn, shape, imm in OPS:
        if mn == "pshufb":
            cases = [(dn + "_" + cn, a, from_bytes(c), G1) for dn, a in DESTS for cn, c in CONTROLS]
        else:
            cases = [(pn, a, b, g) for pn, a, b, g in PAIRS]
        for cn, a, b, g in cases:
            for f in (0, ARITH):
                if mn not in rules:
                    raise SystemExit("mk_shuf_rows: no rule for %s" % mn)
                r, ax, wm = rules[mn](shape, a, b, g, imm)
                name = "%s_%s%s" % (fn[2:], cn, "_set" if f else "")
                # D362: a store row whose expected memory equals the memory it started with cannot tell a store from
                # no store (D358). Refuse it here, before any processor or pin sees it.
                if shape == "mr" and rules is RULES and wm == b:
                    raise SystemExit("mk_shuf_rows: the store row %s writes the bytes already at [RBX]: a dropped "
                                     "store would pass" % name)
                ROWS.append((name, fn, a, b, g, f, r, ax, wm))


# The third control's row: a PEXTRD row, whose expected RAX has bits 63:32 zero by the zero-extension.
PLANT_ZX = "pextrd_rr_i1_p1"
# D362's control: a PEXTRD STORE row, one bit of its expected memory made wrong.
PLANT_MEM = "pextrd_mr_i1_p1"

# D362: the wrong rules --refuse-wrong must refuse, each on a named row (prediction 1).
def _wrong_store8(shape, a, b, g, imm):          # (a) the store zero-extended to 8 bytes, as the GPR write is
    if shape == "mr":
        return a, CANARY, store(64, b, extr(32, a, imm))
    return RULES["pextrd"](shape, a, b, g, imm)


def _wrong_dropped(w):                             # (b) the store writes nothing
    def f(shape, a, b, g, imm):
        if shape == "mr":
            return a, CANARY, b
        return RULES["pextr" + ("d" if w == 32 else "q")](shape, a, b, g, imm)
    return f


def _wrong_sel3(shape, a, b, g, imm):             # (c) PEXTRD selecting by imm[2:0]
    sel = imm & 7
    lane = (a >> (32 * sel)) & 0xFFFFFFFF if sel < 4 else 0
    if shape == "mr":
        return a, CANARY, store(32, b, lane)
    return RULES["pextrd"](shape, a, b, g, imm)


def _wrong_insr4(shape, a, b, g, imm):            # (d) PINSRQ from memory reading 4 bytes
    if shape == "rm":
        return insr(64, a, b & 0xFFFFFFFF, imm), CANARY, b
    return RULES["pinsrq"](shape, a, b, g, imm)


def _wrong_sel2q(shape, a, b, g, imm):            # (e) PEXTRQ selecting by imm[1:0] over DWORD lanes
    if shape == "mr":
        return a, CANARY, store(64, b, (a >> (32 * (imm & 3))) & M64)
    return RULES["pextrq"](shape, a, b, g, imm)


WRONG = [
    ("a", "pextrd to memory stores 8 bytes", "pextrd", _wrong_store8),
    ("b-d", "pextrd to memory stores nothing", "pextrd", _wrong_dropped(32)),
    ("b-q", "pextrq to memory stores nothing", "pextrq", _wrong_dropped(64)),
    ("c", "pextrd selects its lane by imm[2:0]", "pextrd", _wrong_sel3),
    ("d", "pinsrq from memory reads 4 bytes", "pinsrq", _wrong_insr4),
    ("e", "pextrq selects by imm[1:0] over dword lanes", "pextrq", _wrong_sel2q),
]


def refuse_wrong():
    """Each wrong rule must disagree with RULES on at least one row, named here; a wrong rule that agrees everywhere is
    a rule the rows cannot tell from the right one, and this exits 1."""
    build()
    right = [tuple(r) for r in ROWS]
    failed = 0
    for tag, what, mn, fn in WRONG:
        rules = dict(RULES)
        rules[mn] = fn
        build(rules)
        diff = [w[0] for w, r in zip(ROWS, right) if w != r]
        if diff:
            print("REFUSED (%s) %s: %d row(s) disagree, first %s" % (tag, what, len(diff), diff[0]))
        else:
            print("NOT REFUSED (%s) %s: every row agrees" % (tag, what))
            failed += 1
    build()
    print("refuse-wrong: %d of %d refused" % (len(WRONG) - failed, len(WRONG)))
    return 1 if failed else 0


def main():
    P.strict_flags(__file__)
    if "--refuse-wrong" in sys.argv:
        raise SystemExit(refuse_wrong())
    build()
    plant = "--plant" in sys.argv
    plant_zx = "--plant-zx" in sys.argv
    plant_mem = "--plant-mem" in sys.argv
    print("/* GENERATED by hwprobe/mk_shuf_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    for fn, _b, _m, _s, _i in OPS:
        print("void %s(struct sio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const struct srow SROWS[] = {")
    hit = hit_mem = False
    for i, (name, fn, a, b, g, f, r, ax, wm) in enumerate(ROWS):
        if plant and i == 0:
            r ^= 1 << 64       # the control: one expectation made wrong on purpose, in the HIGH quadword
        if plant_zx and name == PLANT_ZX:
            if ax >> 32:
                raise SystemExit("mk_shuf_rows: the --plant-zx row's expected RAX is not zero above bit 31")
            ax |= 1 << 32
            hit = True
        if plant_mem and name == PLANT_MEM:
            wm ^= 1            # the control: one expected memory bit made wrong, inside the stored dword
            hit_mem = True
        print('  {"%s", %s, 0x%016xULL, 0x%016xULL, 0x%016xULL, 0x%016xULL, 0x%016xULL, 0x%03x, '
              '0x%016xULL, 0x%016xULL, 0x%016xULL, 0x%016xULL, 0x%016xULL},'
              % (name, fn, a & M64, a >> 64, b & M64, b >> 64, g, f, r & M64, r >> 64, ax, wm & M64, wm >> 64))
    if plant_zx and not hit:
        raise SystemExit("mk_shuf_rows: the --plant-zx row %s does not exist" % PLANT_ZX)
    if plant_mem and not hit_mem:
        raise SystemExit("mk_shuf_rows: the --plant-mem row %s does not exist" % PLANT_MEM)
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
