#!/usr/bin/env python3
"""hwprobe/mk_vexsile_rows.py — D361 (V10): the VEX MEMORY forms of the silicon rows, the rows the x86-64 referee runs,
with expectations DERIVED HERE.

The forms (x86isa refuses all of them, D361 P1):
  VEX.128 only       vpshufb m · vpalignr imm, m   (imm8 ∈ {0, 5, 16, 20, 33})
  VEX.128 + VEX.256  vaddps m · vsubps m · vmulps m · vpsrad m (the COUNT from m128) · vpunpcklwd m · vpunpckhwd m ·
                     vpunpcklbw m · vpackuswb m
An eleventh probe path, sharing nothing with the others: `vexsile_ops.S`, `vexsile_probe.c` (V8c's, restated), and this
file. One 64-byte buffer per row, `RBX = &mem[off]`, and every memory case runs twice: at offset 0 and at an odd offset.

Every expected value comes from a stated rule, never from ACL2 x86isa and never from x86lean. The register forms' rules
are D345's (`mk_vexsil_rows.py`, which carries its own independent textbook) and D342's (`mk_aes_rows.py`, PSHUFB and
PALIGNR); this file adds the memory operand. It is extracted TWICE (the rule slices one big integer, the textbook a byte
list), and PSHUFB/PALIGNR get a byte-list textbook of their own here, since D342's file has none for them.

THE RULES (`rule`). A = SRC1 (VEX.vvvv, YMM1); M = the memory operand, the bytes at `mem[off:]`:
  vpshufb        DEST[127:0] := PSHUFB(data A, control M[127:0]); DEST[255:128] := 0
  vpalignr imm   DEST[127:0] := ((A << 128) | M[127:0]) >> 8·imm, low 128 bits; DEST[255:128] := 0
  vpsrad         the COUNT is M[63:0], M the 16 bytes at off, AT BOTH WIDTHS (the VEX.256 count operand is xmm3/m128)
  the others     D345's rule with SRC2 := M (16 bytes at VEX.128, 32 at VEX.256, the high lane's operand bytes 31:16)
  NO-ALIGN       no row faults on an unaligned `off` (VEX memory operands of these classes; D342's `vexbinm` rule)
  NO-OTHERS      flags, RAX, YMM1, YMM2 and the 64-byte buffer unchanged; MXCSR := mx | the six sticky flags (FP only)

Usage: mk_vexsile_rows.py [--plant | --plant-op | --plant-hi | --summary | --reach | --refuse-wrong | --selftest]
  --plant         flips bit 128 (the HIGH lane) of one VEX.256 row's expectation: exactly that row must disagree (exit 1)
  --plant-op      declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --plant-hi      one VEX.128 row's expectation keeps the destination's upper half: exactly that row must disagree
  --summary       per-function row counts, not C
  --reach         per wrong rule and mutant, how many rows it disagrees on
  --refuse-wrong  builds the rows under each wrong rule D361 names and shows `build` REFUSE it on its named row
  --selftest      hand-derived cases, a sweep, every row's two derivations, the refusals, the mutants' exact reach, plants
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "scripts"))
sys.path.insert(0, HERE)
import portable as P  # noqa: E402
import mk_vexsil_rows as V  # noqa: E402  (D345's per-lane rules, cases and textbook)
import mk_aes_rows as A  # noqa: E402  (D342's PSHUFB / PALIGNR)

ARITH = 0x8d5
M64 = (1 << 64) - 1
M128 = (1 << 128) - 1
M256 = (1 << 256) - 1

# clang's bytes for each `vexsile_ops.S` line (`clang -target x86_64-unknown-linux-gnu -c`, read with `objdump -d`).
ENC = {
    ("vpshufb_m", 128): "c4e271001b",
    ("vaddps_m", 128): "c5f0581b", ("vaddps_m", 256): "c5f4581b",
    ("vsubps_m", 128): "c5f05c1b", ("vsubps_m", 256): "c5f45c1b",
    ("vmulps_m", 128): "c5f0591b", ("vmulps_m", 256): "c5f4591b",
    ("vpsrad_m", 128): "c5f1e21b", ("vpsrad_m", 256): "c5f5e21b",
    ("vpunpcklwd_m", 128): "c5f1611b", ("vpunpcklwd_m", 256): "c5f5611b",
    ("vpunpckhwd_m", 128): "c5f1691b", ("vpunpckhwd_m", 256): "c5f5691b",
    ("vpunpcklbw_m", 128): "c5f1601b", ("vpunpcklbw_m", 256): "c5f5601b",
    ("vpackuswb_m", 128): "c5f1671b", ("vpackuswb_m", 256): "c5f5671b",
}
ALIGNR_IMMS = [0, 5, 16, 20, 33]
ALIGNR_ENC = "c4e3710f1b"            # + imm8
TWINS = ["vaddps_m", "vsubps_m", "vmulps_m", "vpsrad_m", "vpunpcklwd_m", "vpunpckhwd_m", "vpunpcklbw_m", "vpackuswb_m"]
UNALIGNED = [1, 13, 7, 29]           # ODD offsets: unaligned for every operand size; each memory case runs at 0 AND one


def mnemonic(form):
    return form.split("_")[0]


def v7_form(form):
    """The D345 register form whose rule this memory form shares."""
    return "vpsrad_x" if form == "vpsrad_m" else mnemonic(form)


def mem_len(form, L):
    """The bytes the memory operand covers: 16 for the VEX.128-only forms and for VPSRAD's m128 count, else L/8."""
    return 16 if form in ("vpshufb_m", "vpalignr_m", "vpsrad_m") else L // 8


OPS = [("x_vpshufb128_m", "vpshufb_m", 128, ENC[("vpshufb_m", 128)], None)]
for _i in ALIGNR_IMMS:
    OPS.append(("x_vpalignr128_m_i%d" % _i, "vpalignr_m", 128, ALIGNR_ENC + "%02x" % _i, _i))
for _f in TWINS:
    for _L in (128, 256):
        OPS.append(("x_%s%d_m" % (mnemonic(_f), _L), _f, _L, ENC[(_f, _L)], None))

PLANT_ROW = "vmulps256_m_hionly_IE_a"   # --plant: bit 128 of its expectation (the first aligned VEX.256 vmulps row)
PLANT_HI = "vpshufb128_m_ident_a"      # --plant-hi: its expectation keeps YMM3's upper half


# ── THE RULE ─────────────────────────────────────────────────────────────────────────────────────────────────────

def mem_operand(mem, off, n):
    """The n bytes at `off`, read as ONE little-endian integer out of the 64-byte buffer held as an integer."""
    return (mem >> (8 * off)) & ((1 << (8 * n)) - 1)


def rule(form, L, y1, y2, y3, imm, mx, rax, mem, off):
    """-> (YMM3, RAX, MXCSR's six sticky flags)."""
    m = mem_operand(mem, off, mem_len(form, L))
    if form == "vpshufb_m":
        return A.rule("vpshufb", y1 & M128, m, None), rax, 0
    if form == "vpalignr_m":
        return A.rule("vpalignr", y1 & M128, m, imm), rax, 0
    return V.rule(v7_form(form), L, y1, m, y3, imm, mx, rax)


# ── THE WRONG RULES D361 NAMES ───────────────────────────────────────────────────────────────────────────────────

def w_shufb_swapped(form, L, y1, y2, y3, imm, mx, rax, mem, off):
    """(a) vpshufb from memory with the operands swapped: memory as the DATA, src1 as the control."""
    if form == "vpshufb_m":
        return A.rule("vpshufb", mem_operand(mem, off, 16), y1 & M128, None), rax, 0
    return rule(form, L, y1, y2, y3, imm, mx, rax, mem, off)


def w_hi_from_low(form, L, y1, y2, y3, imm, mx, rax, mem, off):
    """(b) a VEX.256 vmulps from m256 whose high lane reads bytes 15:0 again instead of 31:16."""
    if form == "vmulps_m" and L == 256:
        lo = mem_operand(mem, off, 16)
        return V.rule("vmulps", L, y1, lo | (lo << 128), y3, imm, mx, rax)
    return rule(form, L, y1, y2, y3, imm, mx, rax, mem, off)


def w_count128(form, L, y1, y2, y3, imm, mx, rax, mem, off):
    """(c) VEX.256 vpsrad from memory reading its count from all 128 bits (an upper qword ≠ 0 saturates the shift)."""
    if form == "vpsrad_m" and L == 256:
        c = mem_operand(mem, off, 16)
        return V.r_psra(y1 & M128, c, 32) | (V.r_psra(y1 >> 128, c, 32) << 128), rax, 0
    return rule(form, L, y1, y2, y3, imm, mx, rax, mem, off)


def w_drop_hi_flags(form, L, y1, y2, y3, imm, mx, rax, mem, off):
    """(d) VEX.256 vaddps from m256 dropping a flag raised in the high lane only."""
    if form == "vaddps_m" and L == 256:
        m = mem_operand(mem, off, 32)
        rc = V.rc_of(mx)
        lo, f = V.lane128("vaddps", y1 & M128, m & M128, imm, rc)
        hi, _g = V.lane128("vaddps", y1 >> 128, m >> 128, imm, rc)
        return lo | (hi << 128), rax, f
    return rule(form, L, y1, y2, y3, imm, mx, rax, mem, off)


def w_alignr_mem_high(form, L, y1, y2, y3, imm, mx, rax, mem, off):
    """(e) vpalignr from memory with memory as the HIGH half of the concatenation."""
    if form == "vpalignr_m":
        return A.rule("vpalignr", mem_operand(mem, off, 16), y1 & M128, imm), rax, 0
    return rule(form, L, y1, y2, y3, imm, mx, rax, mem, off)


WRONG = [   # (letter, label, rule, the row `build` must name on refusing it)
    ("a", "vpshufb from memory, operands swapped", w_shufb_swapped, "vpshufb128_m_ident_a"),
    ("b", "a VEX.256 vmulps m256 high lane read from bytes 15:0", w_hi_from_low, "vmulps256_m_hionly_IE_a"),
    ("c", "VEX.256 vpsrad m128 count read from all 128 bits", w_count128, "vpsrad256_m_c0_edge_a"),
    ("d", "VEX.256 vaddps m256 dropping a high-lane-only flag", w_drop_hi_flags, "vaddps256_m_hionly_IE_a"),
    ("e", "vpalignr from memory, memory as the HIGH half", w_alignr_mem_high, "vpalignr128_m_i0_p0_a"),
]


def m_keep_upper(form, L, y1, y2, y3, imm, mx, rax, mem, off):
    """(reach only) the VEX.128 red-backwards mutant: the destination's upper half preserved."""
    d, r, m = rule(form, L, y1, y2, y3, imm, mx, rax, mem, off)
    return (d | (y3 >> 128 << 128) if L == 128 else d), r, m


def m_copy_low(form, L, y1, y2, y3, imm, mx, rax, mem, off):
    """(reach only) the VEX.256 red-backwards mutant: the low lane's result copied into the high lane."""
    d, r, m = rule(form, L, y1, y2, y3, imm, mx, rax, mem, off)
    return ((d & M128) | ((d & M128) << 128) if L == 256 else d), r, m


MUTANTS = [("VEX.128 upper half preserved", m_keep_upper), ("VEX.256 low lane copied into the high lane", m_copy_low)]


# ── THE TEXTBOOK: byte lists ────────────────────────────────────────────────────────────────────────────────────

def tb_pshufb(data, ctl):
    return [0 if c & 0x80 else data[c & 0x0f] for c in ctl]


def tb_palignr(hi, lo, imm):
    cat = lo + hi                                  # bytes 0..15 the LOW source (memory), 16..31 the HIGH (src1)
    return [cat[i + imm] if i + imm < 32 else 0 for i in range(16)]


def textbook(form, L, y1, y2, y3, imm, mx, rax, mem, off):
    buf = list(mem.to_bytes(64, "little"))
    n = mem_len(form, L)
    op = buf[off:off + n] + [0] * (32 - n)
    a = V.tb_bytes(y1)
    if form == "vpshufb_m":
        return V.tb_int(tb_pshufb(a[0:16], op[0:16]) + [0] * 16), rax, 0
    if form == "vpalignr_m":
        return V.tb_int(tb_palignr(a[0:16], op[0:16], imm) + [0] * 16), rax, 0
    return V.textbook(v7_form(form), L, y1, V.tb_int(op), y3, imm, mx, rax)


# ── the rows ────────────────────────────────────────────────────────────────────────────────────────────────────

ROWS = []   # (name, fn, form, L, y1, y2, y3, imm, f, mx, rax, mem, off, w3, wrax, wfl)

SHUFB_CTLS = [   # D336's eight controls, as the memory operand
    ("ident", list(range(16))), ("rev", list(range(15, -1, -1))), ("bit7", [0x80] * 16),
    ("alt7", [0x80 if i % 2 else i for i in range(16)]), ("junk64", [0x70 | (15 - i) for i in range(16)]),
    ("bcast0", [0] * 16), ("bcast15", [15] * 16), ("mixed", [0x03, 0x8f, 0x1c, 0x05, 0xf0, 0x2a, 0x07, 0x99,
                                                             0x0e, 0x41, 0x80, 0x0b, 0x6d, 0x00, 0xff, 0x09])]


class Refused(SystemExit):
    def __init__(self, row, msg):
        super().__init__(msg)
        self.row = row


def place(mem, off, value, n):
    """`mem` with the n bytes at off replaced by `value` (little-endian)."""
    mask = ((1 << (8 * n)) - 1) << (8 * off)
    return (mem & ~mask & ((1 << 512) - 1)) | ((value & ((1 << (8 * n)) - 1)) << (8 * off))


def cases_for(form, L, imm, rng):
    """(name, y1 data, memory operand, rc or None)."""
    if form == "vpshufb_m":
        return [(nm, rng.getrandbits(256), V.tb_int(c + [0] * 16), None) for nm, c in SHUFB_CTLS]
    if form == "vpalignr_m":
        return [("p%d" % i, rng.getrandbits(256), rng.getrandbits(128), None) for i in range(2)]
    out = []
    for nm, a, b, rc in V.cases_for(v7_form(form), L, None, rng):
        if not keep(form, nm):
            continue
        out.append((nm, a, b & ((1 << (8 * mem_len(form, L))) - 1), rc))
    return out


def keep(form, nm):
    """D345's register cases, THINNED for the memory twin: its arithmetic is D345's, already pinned there under every
    rounding mode, so a memory row has to show only the operand read, the lane split and the flag OR. Kept: every
    flag row (`hionly_*`, `loonly_*`, `lane3_*`), each FP case group under ONE rounding mode (`case<g>_<first mode>`),
    two random FP cases, and VPSRAD's sixteen `_edge` counts (whose upper qwords are junk, which (c) needs)."""
    if form in ("vaddps_m", "vsubps_m", "vmulps_m"):
        return (nm.startswith(("hionly_", "loonly_", "lane3_")) or nm.endswith("_" + V.MODES[0])
                or nm.split("_")[0] in ("rand0", "rand1"))
    if form == "vpsrad_m":
        return nm.endswith("_edge")
    return True


def build(rl=None):
    rl = rl or rule
    ROWS.clear()
    for k, (fn, form, L, _bs, imm) in enumerate(OPS):
        rng = random.Random(361000 + k)
        cases = cases_for(form, L, imm, rng)
        variants = [(c, v, 0 if v == "a" else UNALIGNED[j % len(UNALIGNED)]) for j, c in enumerate(cases) for v in "au"]
        for i, ((nm, a, opnd, rc), var, off) in enumerate(variants):
            hi1 = rng.getrandbits(128) | 1
            y3 = rng.getrandbits(256) | (1 << 128) | 1
            rax = rng.getrandbits(64) | (1 << 63)
            y1 = V.ymm(a & M128, hi1) if L == 128 else a & M256
            y2 = rng.getrandbits(256) | 1 | (1 << 128)        # an unread register, seeded whole
            mem = place(rng.getrandbits(512), off, opnd, mem_len(form, L))
            mx = 0x1f80 | ((rc if rc is not None else (i // 2) % 4) << 13)
            f = ARITH if (i // 2) % 2 else 0
            name = "%s_%s_%s" % (fn[2:], nm, var)
            got = rl(form, L, y1, y2, y3, imm, mx, rax, mem, off)
            want = textbook(form, L, y1, y2, y3, imm, mx, rax, mem, off)
            if got != want:
                raise Refused(name, "mk_vexsile_rows: ⛔ row %s: the RULE gives ymm3 %064x flags %02x, the TEXTBOOK "
                                    "%064x flags %02x" % (name, got[0], got[2], want[0], want[2]))
            ROWS.append((name, fn, form, L, y1, y2, y3, imm, f, mx, rax, mem, off, got[0], got[1], got[2]))


def q(v, n):
    return ", ".join("0x%016xULL" % ((v >> (64 * i)) & M64) for i in range(n))


def disagreements(rl):
    return {r[0] for r in ROWS
            if rl(r[2], r[3], r[4], r[5], r[6], r[7], r[9], r[10], r[11], r[12]) != (r[13], r[14], r[15])}


def refusals(quiet=False):
    missed = 0
    for letter, label, rl, row in WRONG:
        try:
            build(rl)
        except Refused as e:
            if e.row == row:
                if not quiet:
                    print("  ✔ (%s) refused on %s — %s" % (letter, e.row, label))
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

    # hand-derived: PSHUFB with a reversal control from an unaligned m128; PALIGNR imm 5 with memory as the LOW half;
    # VPSRAD ymm with a count of 4 whose upper qword is junk (the junk must not saturate the shift)
    data = list(range(0x10, 0x20))
    mem = place(0, 13, V.tb_int(list(range(15, -1, -1)) + [0] * 16), 16)
    want = V.tb_int(data[::-1] + [0] * 16)
    say(rule("vpshufb_m", 128, V.tb_int(data + [0] * 16), 0, 0, None, 0x1f80, 0, mem, 13)[0] == want
        == textbook("vpshufb_m", 128, V.tb_int(data + [0] * 16), 0, 0, None, 0x1f80, 0, mem, 13)[0],
        "hand: vpshufb xmm, m128 at offset 13 with a reversal control reverses src1's bytes, both references")
    lo, hi = list(range(0x00, 0x10)), list(range(0x80, 0x90))
    mem = place(0, 1, V.tb_int(lo + [0] * 16), 16)
    want = V.tb_int(lo[5:] + hi[:5] + [0] * 16)
    say(rule("vpalignr_m", 128, V.tb_int(hi + [0] * 16), 0, 0, 5, 0x1f80, 0, mem, 1)[0] == want
        == textbook("vpalignr_m", 128, V.tb_int(hi + [0] * 16), 0, 0, 5, 0x1f80, 0, mem, 1)[0],
        "hand: vpalignr $5, m128 (the LOW half) at offset 1 = memory bytes 5..15 then src1 bytes 0..4, both references")
    y1 = V.of_els([0x80000000] * 8, 32)
    mem = place(0, 7, 4 | (0xdead << 64), 16)
    want = V.of_els([0xf8000000] * 8, 32)
    say(rule("vpsrad_m", 256, y1, 0, 0, None, 0x1f80, 0, mem, 7)[0] == want
        == textbook("vpsrad_m", 256, y1, 0, 0, None, 0x1f80, 0, mem, 7)[0],
        "hand: vpsrad ymm, m128 count 4 with junk in bits 127:64 shifts every dword by 4, both references")
    rng = random.Random(361999)
    nd = 0
    for i in range(3000):
        fn, form, L, _b, imm = OPS[i % len(OPS)]
        a, m = rng.getrandbits(256), rng.getrandbits(512)
        off = rng.choice([0] + UNALIGNED)
        mx = 0x1f80 | (rng.randrange(4) << 13)
        nd += rule(form, L, a, 0, 0, imm, mx, 0, m, off) != textbook(form, L, a, 0, 0, imm, mx, 0, m, off)
    say(nd == 0, "the rule and the textbook agree on 3,000 swept (form, length, operands, buffer, offset) cases")
    build()
    say(len(ROWS) > 0, "%d rows built, every one equal under the rule and the textbook" % len(ROWS))
    say(refusals(quiet=True) == 0, "each of the %d wrong rules (a)-(e) is REFUSED on its named row" % len(WRONG))
    reach = {m_keep_upper: {r[0] for r in ROWS if r[3] == 128},
             m_copy_low: {r[0] for r in ROWS if r[3] == 256 and (r[13] >> 128) != (r[13] & M128)}}
    for label, rl in MUTANTS:
        hit = disagreements(rl)
        say(hit == reach[rl] and hit, "mutant '%s' disagrees on exactly the %d rows it reaches" % (label, len(hit)))
    pairs = {}
    for r in ROWS:
        pairs.setdefault(r[0][:-2], {})[r[0][-1]] = r
    say(all(set(v) == {"a", "u"} and v["a"][12] == 0 and v["u"][12] % 2 == 1
            and (v["a"][13], v["a"][15]) == (v["u"][13], v["u"][15]) for v in pairs.values()),
        "every one of the %d memory cases runs twice, at offset 0 and at an ODD offset, expecting the SAME result" % len(pairs))
    say(all(r[12] + mem_len(r[2], r[3]) <= 64 for r in ROWS), "every memory operand lies inside the 64-byte buffer")
    pk = [r for r in ROWS if r[0] == PLANT_ROW]
    say(len(pk) == 1 and pk[0][3] == 256, "--plant's row %s exists once and is VEX.256" % PLANT_ROW)
    ph = [r for r in ROWS if r[0] == PLANT_HI]
    say(len(ph) == 1 and ph[0][3] == 128 and ph[0][13] >> 128 == 0,
        "--plant-hi's row %s exists, VEX.128, upper half expected zero" % PLANT_HI)
    say(all(r[13] >> 128 == 0 for r in ROWS if r[3] == 128), "every VEX.128 row expects YMM3[255:128] = 0")
    say(any(r[15] for r in ROWS) and all(r[15] == 0 for r in ROWS if r[2] not in ("vaddps_m", "vsubps_m", "vmulps_m")),
        "some FP row raises a sticky flag, and no non-FP row expects one")
    say({(f, L) for _n, _fn, f, L, *_ in ROWS} == set(ENC) | {("vpalignr_m", 128)},
        "the rows cover exactly the %d encodings' forms" % (len(ENC) + 1))
    print("✅ mk_vexsile_rows selftest" if not bad else "⛔ mk_vexsile_rows selftest FAILED")
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
        for fn, _f, _L, _b, _i in OPS:
            print("%-28s %3d" % (fn, sum(1 for r in ROWS if r[1] == fn)))
        print("rows %d functions %d" % (len(ROWS), len(OPS)))
        return 0
    if "--reach" in sys.argv:
        for label, rl in [(w[1], w[2]) for w in WRONG] + MUTANTS:
            print("%-56s disagrees on %3d rows" % (label, len(disagreements(rl))))
        return 0
    plant, plant_hi = "--plant" in sys.argv, "--plant-hi" in sys.argv
    print("/* GENERATED by hwprobe/mk_vexsile_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    for fn, _f, _L, _b, _i in OPS:
        print("void %s(struct xio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const struct xrow XROWS[] = {")
    for name, fn, form, L, y1, y2, y3, imm, f, mx, rax, mem, off, w3, wrax, wfl in ROWS:
        if plant and name == PLANT_ROW:
            w3 ^= 1 << 128
        if plant_hi and name == PLANT_HI:
            w3 |= y3 >> 128 << 128
        print('  {"%s", %s, {%s}, {%s}, {%s}, 0x%03x, 0x%04x, 0x%016xULL, {%s}, %d, {%s}, 0x%016xULL, 0x%04x},' % (
            name, fn, q(y1, 4), q(y2, 4), q(y3, 4), f, mx, rax, q(mem, 8), off, q(w3, 4), wrax, mx | wfl))
    print("};")
    print("static const struct xop XOPS[] = {")
    for i, (fn, _f, _L, bs, _i) in enumerate(OPS):
        bb = bytearray.fromhex(bs)
        if "--plant-op" in sys.argv and i == 0:
            bb[-1] ^= 0x01
        print('  {"%s", %s_at, %d, {%s}},' % (fn, fn, len(bb), ", ".join("0x%02x" % x for x in bb)))
    print("};")
    return 0


if __name__ == "__main__":
    sys.exit(main())
