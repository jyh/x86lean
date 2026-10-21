#!/usr/bin/env python3
"""hwprobe/mk_vexsilc_rows.py — D350 (V8c): VPBROADCASTD (from xmm and from m32) and the VEX.128 / VEX.256 MEMORY forms of
V8b's four twins, the rows the x86-64 referee runs, with expectations DERIVED HERE.

The forms (x86isa refuses all 12 encodings, D350 P1):
  vpbroadcastd xmm·m32 · vpmaddwd m · vpmulhrsw m · vpmaddubsw m · vpackssdw m      each at VEX.128 and VEX.256
A tenth probe path, sharing nothing with the others: `vexsilc_ops.S`, `vexsilc_probe.c`, and this file. It is the first VEX
path with a MEMORY operand: one 64-byte buffer per row, `RBX = &mem[off]`, and `off` unaligned on most memory rows.

Every expected value comes from a stated rule (SDM Vol. 2B VPBROADCAST, and D348's rules for the four twins with the second
source read from memory), never from ACL2 x86isa and never from x86lean.

THE RULES (`rule`). A = SRC1 (VEX.vvvv, YMM1); the memory operand is SRC2, the bytes at `mem[off:]`.
  twin, VEX.128   DEST[127:0] := F(A[127:0], M[127:0]) with M the 16 bytes at off;  DEST[255:128] := 0
  twin, VEX.256   DEST := F per lane, M the 32 bytes at off, the high lane's operand bytes 31:16 of it
  VPBROADCASTD    every dword of DEST := S, S = XMM2[31:0] (register form) or the 4 bytes at off (m32);
                  four dwords at VEX.128 (bits 255:128 := 0), eight at VEX.256
  NO-ALIGN        no row faults on an unaligned `off` (VEX memory operands of these classes; D342's `vexbinm` rule)
  NO-OTHERS       flags, MXCSR, RAX, YMM1, YMM2 and the 64-byte buffer unchanged
F is D348's per-lane function, imported from mk_vexsilb_rows.py together with its independent textbook; the memory
operand is extracted TWICE here (the rule slices one big integer, the textbook slices a byte list) so a misread offset or
length is refused by `build`.

Usage: mk_vexsilc_rows.py [--plant | --plant-op | --plant-hi | --summary | --reach | --refuse-wrong | --selftest]
  --plant         flips bit 128 (the HIGH lane) of one VEX.256 row's expectation: exactly that row must disagree (exit 1)
  --plant-op      declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --plant-hi      one VEX.128 row's expectation keeps the destination's upper half: exactly that row must disagree
  --summary       per-form row counts, not C
  --reach         per wrong rule and mutant, how many rows it disagrees on
  --refuse-wrong  builds the rows under each wrong rule D350 names and shows `build` REFUSE it on its named row
  --selftest      hand-derived cases, a sweep, every row's two derivations, the refusals, the mutants' exact reach, plants
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "scripts"))
sys.path.insert(0, HERE)
import portable as P  # noqa: E402
import mk_vexsilb_rows as B  # noqa: E402  (D348's per-lane rule and textbook)

ARITH = 0x8d5
M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
M128 = (1 << 128) - 1
M256 = (1 << 256) - 1

# clang's bytes for each `vexsilc_ops.S` line (`clang -target x86_64-unknown-linux-gnu -c`, read with `objdump -d`).
ENC = {
    ("vpbroadcastd_r", 128): "c4e27958da", ("vpbroadcastd_r", 256): "c4e27d58da",
    ("vpbroadcastd_m", 128): "c4e279581b", ("vpbroadcastd_m", 256): "c4e27d581b",
    ("vpmaddwd_m", 128): "c5f1f51b", ("vpmaddwd_m", 256): "c5f5f51b",
    ("vpmulhrsw_m", 128): "c4e2710b1b", ("vpmulhrsw_m", 256): "c4e2750b1b",
    ("vpmaddubsw_m", 128): "c4e271041b", ("vpmaddubsw_m", 256): "c4e275041b",
    ("vpackssdw_m", 128): "c5f16b1b", ("vpackssdw_m", 256): "c5f56b1b",
}
FORMS = ["vpbroadcastd_r", "vpbroadcastd_m", "vpmaddwd_m", "vpmulhrsw_m", "vpmaddubsw_m", "vpackssdw_m"]
UNALIGNED = [1, 13, 7, 29]             # ODD offsets: unaligned for every operand size; each memory case runs at 0 AND one of these


def mnemonic(form):
    return form.split("_")[0]


def is_mem(form):
    return form.endswith("_m")


OPS = []   # (fn, form, L, declared bytes hex, None)
for _L in (128, 256):
    for _f in ("vpbroadcastd_r", "vpbroadcastd_m"):
        OPS.append(("x_vpbroadcastd%d_%s" % (_L, _f[-1]), _f, _L, ENC[(_f, _L)], None))
for _f in FORMS[2:]:
    for _L in (128, 256):
        OPS.append(("x_%s%d_m" % (mnemonic(_f), _L), _f, _L, ENC[(_f, _L)], None))

PLANT_ROW = "vpmaddwd256_m_lane_u"   # --plant: bit 128 of its expectation
PLANT_HI = "vpbroadcastd128_m_k1_a"  # --plant-hi: its expectation keeps YMM3's upper half


# ── THE RULE ─────────────────────────────────────────────────────────────────────────────────────────────────────

def mem_operand(mem, off, n):
    """The n bytes at `off`, read as ONE little-endian integer out of the 64-byte buffer held as an integer."""
    return (mem >> (8 * off)) & ((1 << (8 * n)) - 1)


def bcast(d, L):
    return B.of_els([d] * (L // 32), 32)


def rule(form, L, y1, y2, y3, mx, rax, mem, off):
    """-> (YMM3, RAX, MXCSR)."""
    if form == "vpbroadcastd_r":
        return bcast(y2 & M32, L), rax, mx
    if form == "vpbroadcastd_m":
        return bcast(mem_operand(mem, off, 4), L), rax, mx
    return B.rule(mnemonic(form), L, y1, mem_operand(mem, off, L // 8), y3, mx, rax)


# ── THE WRONG RULES D350 NAMES ───────────────────────────────────────────────────────────────────────────────────

def w_bcast_dword1(form, L, y1, y2, y3, mx, rax, mem, off):
    """(a) vpbroadcastd broadcasting the source's dword 1 instead of dword 0."""
    if form == "vpbroadcastd_r":
        return bcast((y2 >> 32) & M32, L), rax, mx
    if form == "vpbroadcastd_m":
        return bcast(mem_operand(mem, off + 4, 4), L), rax, mx
    return rule(form, L, y1, y2, y3, mx, rax, mem, off)


def w_hi_from_low(form, L, y1, y2, y3, mx, rax, mem, off):
    """(b) a VEX.256 memory twin whose high lane reads bytes 15:0 again instead of 31:16."""
    if is_mem(form) and form != "vpbroadcastd_m" and L == 256:
        lo = mem_operand(mem, off, 16)
        return B.rule(mnemonic(form), L, y1, lo | (lo << 128), y3, mx, rax)
    return rule(form, L, y1, y2, y3, mx, rax, mem, off)


def w_mem_as_src1(form, L, y1, y2, y3, mx, rax, mem, off):
    """(c) the memory operand taken as SRC1: vpmaddubsw's memory bytes read UNSIGNED and YMM1's SIGNED."""
    if form == "vpmaddubsw_m":
        return B.rule("vpmaddubsw", L, mem_operand(mem, off, L // 8), y1, y3, mx, rax)
    return rule(form, L, y1, y2, y3, mx, rax, mem, off)


def w_m64(form, L, y1, y2, y3, mx, rax, mem, off):
    """(d) vpbroadcastd from m32 reading 64 bits: a QWORD broadcast."""
    if form == "vpbroadcastd_m":
        q = mem_operand(mem, off, 8)
        return B.of_els([q] * (L // 64), 64), rax, mx
    return rule(form, L, y1, y2, y3, mx, rax, mem, off)


WRONG = [   # (letter, label, rule, the row `build` must name on refusing it)
    ("a", "vpbroadcastd broadcasting dword 1", w_bcast_dword1, "vpbroadcastd128_r_k0"),
    # (b) is first refused on `lane`: every edge row of vpmaddwd has EQUAL lanes, so reading bytes 15:0 twice is invisible
    ("b", "a VEX.256 memory twin's high lane read from bytes 15:0", w_hi_from_low, "vpmaddwd256_m_lane_a"),
    ("c", "the memory operand taken as src1 (vpmaddubsw)", w_mem_as_src1, "vpmaddubsw128_m_edge0_a"),
    ("d", "vpbroadcastd m32 read as 64 bits", w_m64, "vpbroadcastd128_m_k0_a"),
]


def m_keep_upper(form, L, y1, y2, y3, mx, rax, mem, off):
    """(reach only) the VEX.128 red-backwards mutant: the destination's upper half preserved."""
    d, r, m = rule(form, L, y1, y2, y3, mx, rax, mem, off)
    return (d | (y3 >> 128 << 128) if L == 128 else d), r, m


def m_copy_low(form, L, y1, y2, y3, mx, rax, mem, off):
    """(reach only) the VEX.256 red-backwards mutant: the low lane's result copied into the high lane."""
    d, r, m = rule(form, L, y1, y2, y3, mx, rax, mem, off)
    return ((d & M128) | ((d & M128) << 128) if L == 256 else d), r, m


MUTANTS = [("VEX.128 upper half preserved", m_keep_upper), ("VEX.256 low lane copied into the high lane", m_copy_low)]


# ── THE TEXTBOOK: byte lists ────────────────────────────────────────────────────────────────────────────────────

def textbook(form, L, y1, y2, y3, mx, rax, mem, off):
    buf = list(mem.to_bytes(64, "little"))
    if form.startswith("vpbroadcastd"):
        src4 = buf[off:off + 4] if form == "vpbroadcastd_m" else B.tb_bytes(y2)[0:4]
        dest = src4 * (L // 32) + [0] * (32 - L // 8)
        return B.tb_int(dest), rax, mx
    op = buf[off:off + L // 8] + [0] * (32 - L // 8)
    return B.textbook(mnemonic(form), L, y1, B.tb_int(op), y3, mx, rax)


# ── the rows ────────────────────────────────────────────────────────────────────────────────────────────────────

ROWS = []   # (name, fn, form, L, y1, y2, y3, f, mx, rax, mem, off, w3, wrax, wmx)


class Refused(SystemExit):
    def __init__(self, row, msg):
        super().__init__(msg)
        self.row = row


def place(mem, off, value, n):
    """`mem` with the n bytes at off replaced by `value` (little-endian)."""
    mask = ((1 << (8 * n)) - 1) << (8 * off)
    return (mem & ~mask & ((1 << 512) - 1)) | ((value & ((1 << (8 * n)) - 1)) << (8 * off))


def cases_for(form, L, rng):
    """(name, y1, y2, operand value or None) — the operand is placed into the buffer at the row's offset."""
    out = []
    if form.startswith("vpbroadcastd"):
        out += [("k0", 0, B.of_els([0x80000001, 0x7ffffffe, 0x12345678, 0xdeadbeef], 32),
                 B.of_els([0x80000001, 0x7ffffffe], 32)),
                ("k1", 0, B.of_els([0xffffffff, 0, 0x1, 0x2], 32), B.of_els([0xffffffff, 0x0], 32))]
        for i in range(4):
            out.append(("rand%d" % i, rng.getrandbits(256), rng.getrandbits(256), rng.getrandbits(64)))
        return out
    for nm, a, b in B.cases_for(mnemonic(form), L, rng):
        out.append((nm, a, rng.getrandbits(256), b))
    return out


def build(rl=None):
    rl = rl or rule
    ROWS.clear()
    for k, (fn, form, L, _bs, _i) in enumerate(OPS):
        rng = random.Random(350000 + k)
        cases = cases_for(form, L, rng)
        # every MEMORY case twice, with the same operand: at offset 0 and at an odd offset (prediction 1)
        variants = ([(c, v, 0 if v == "a" else UNALIGNED[j % len(UNALIGNED)]) for j, c in enumerate(cases) for v in "au"]
                    if is_mem(form) else [(c, None, 0) for c in cases])
        for i, ((nm, a, y2, opnd), var, off) in enumerate(variants):
            hi1 = rng.getrandbits(128) | 1
            y3 = rng.getrandbits(256) | (1 << 128) | 1
            rax = rng.getrandbits(64) | (1 << 63)
            y1 = B.ymm(a, hi1) if L == 128 else a & M256
            y2 = y2 | 1 | (1 << 128)                       # an operand register, seeded whole
            mem = rng.getrandbits(512)
            if is_mem(form) and opnd is not None:
                n = 4 if form == "vpbroadcastd_m" else L // 8
                if form == "vpbroadcastd_m":
                    mem = place(mem, off, opnd, 8)        # the dword AND the next one, so (a)/(d) see a difference
                else:
                    mem = place(mem, off, opnd, n)
            elif form == "vpbroadcastd_r" and opnd is not None:
                y2 = (y2 & ~M64) | (opnd & M64)
            mx = 0x1f80 | ((i % 4) << 13)
            f = ARITH if i % 2 else 0
            name = "%s_%s" % (fn[2:], nm) + ("" if var is None else "_" + var)
            got = rl(form, L, y1, y2, y3, mx, rax, mem, off)
            want = textbook(form, L, y1, y2, y3, mx, rax, mem, off)
            if got != want:
                raise Refused(name, "mk_vexsilc_rows: ⛔ row %s: the RULE gives ymm3 %064x, the TEXTBOOK %064x" % (
                    name, got[0], want[0]))
            ROWS.append((name, fn, form, L, y1, y2, y3, f, mx, rax, mem, off, got[0], got[1], got[2]))


def q(v, n):
    return ", ".join("0x%016xULL" % ((v >> (64 * i)) & M64) for i in range(n))


def disagreements(rl):
    return {r[0] for r in ROWS if rl(r[2], r[3], r[4], r[5], r[6], r[8], r[9], r[10], r[11]) != (r[12], r[13], r[14])}


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

    # hand-derived: a broadcast of 0x80000001 from an unaligned m32, and a VEX.256 memory twin's lane split
    mem = place(0, 13, 0x7ffffffe80000001, 8)
    say(rule("vpbroadcastd_m", 256, 0, 0, 0, 0, 0, mem, 13)[0] == B.of_els([0x80000001] * 8, 32)
        == textbook("vpbroadcastd_m", 256, 0, 0, 0, 0, 0, mem, 13)[0],
        "hand: vpbroadcastd ymm from m32 at offset 13 = eight copies of 0x80000001, both references")
    lo, hi = B.of_els([0x8000] * 8, 16), B.of_els([0x0001] * 8, 16)
    mem = place(0, 1, lo | (hi << 128), 32)
    y1 = B.of_els([0x8000] * 8 + [0x0003] * 8, 16)
    want = B.of_els([0x80000000] * 4 + [0x00000006] * 4, 32)
    say(rule("vpmaddwd_m", 256, y1, 0, 0, 0, 0, mem, 1)[0] == want == textbook("vpmaddwd_m", 256, y1, 0, 0, 0, 0, mem, 1)[0],
        "hand: vpmaddwd ymm, m256 at offset 1: low lane wraps to 0x80000000, high lane 3·1+3·1 = 6, both references")
    rng = random.Random(350999)
    nd = 0
    for i in range(3000):
        form = FORMS[i % len(FORMS)]
        L = 128 if (i // len(FORMS)) % 2 else 256
        a, y2, m = rng.getrandbits(256), rng.getrandbits(256), rng.getrandbits(512)
        off = rng.choice([0] + UNALIGNED) if is_mem(form) else 0
        nd += rule(form, L, a, y2, 0, 0x1f80, 0, m, off) != textbook(form, L, a, y2, 0, 0x1f80, 0, m, off)
    say(nd == 0, "the rule and the textbook agree on 3,000 swept (form, length, operands, buffer, offset) cases")
    build()
    say(len(ROWS) > 0, "%d rows built, every one equal under the rule and the textbook" % len(ROWS))
    say(refusals(quiet=True) == 0, "each of the %d wrong rules (a)-(d) is REFUSED on its named row" % len(WRONG))
    reach = {m_keep_upper: {r[0] for r in ROWS if r[3] == 128},
             m_copy_low: {r[0] for r in ROWS if r[3] == 256 and (r[12] >> 128) != (r[12] & M128)}}
    for label, rl in MUTANTS:
        hit = disagreements(rl)
        say(hit == reach[rl] and hit, "mutant '%s' disagrees on exactly the %d rows it reaches" % (label, len(hit)))
    mrows = [r for r in ROWS if is_mem(r[2])]
    pairs = {}
    for r in mrows:
        pairs.setdefault(r[0][:-2], {})[r[0][-1]] = r
    say(all(set(v) == {"a", "u"} and v["a"][11] == 0 and v["u"][11] % 2 == 1 and v["a"][12] == v["u"][12]
            for v in pairs.values()),
        "every one of the %d memory cases runs twice, at offset 0 and at an ODD offset, expecting the SAME result" % len(pairs))
    say(all(r[11] + (4 if r[2] == "vpbroadcastd_m" else r[3] // 8) <= 64 for r in mrows),
        "every memory operand lies inside the 64-byte buffer")
    pk = [r for r in ROWS if r[0] == PLANT_ROW]
    say(len(pk) == 1 and pk[0][3] == 256, "--plant's row %s exists once and is VEX.256" % PLANT_ROW)
    ph = [r for r in ROWS if r[0] == PLANT_HI]
    say(len(ph) == 1 and ph[0][3] == 128 and ph[0][12] >> 128 == 0, "--plant-hi's row %s exists, VEX.128, upper half "
        "expected zero" % PLANT_HI)
    say(all(r[12] >> 128 == 0 for r in ROWS if r[3] == 128), "every VEX.128 row expects YMM3[255:128] = 0")
    say({(r[2], r[3]) for r in ROWS} == set(ENC), "the rows cover exactly the %d encodings" % len(ENC))
    print("✅ mk_vexsilc_rows selftest" if not bad else "⛔ mk_vexsilc_rows selftest FAILED")
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
            print("%-26s %3d" % (fn, sum(1 for r in ROWS if r[1] == fn)))
        print("rows %d functions %d encodings %d" % (len(ROWS), len(OPS), len(ENC)))
        return 0
    if "--reach" in sys.argv:
        for label, rl in [(w[1], w[2]) for w in WRONG] + MUTANTS:
            print("%-56s disagrees on %3d rows" % (label, len(disagreements(rl))))
        return 0
    plant, plant_hi = "--plant" in sys.argv, "--plant-hi" in sys.argv
    print("/* GENERATED by hwprobe/mk_vexsilc_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    for fn, _f, _L, _b, _i in OPS:
        print("void %s(struct xio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const struct xrow XROWS[] = {")
    for name, fn, form, L, y1, y2, y3, f, mx, rax, mem, off, w3, wrax, wmx in ROWS:
        if plant and name == PLANT_ROW:
            w3 ^= 1 << 128
        if plant_hi and name == PLANT_HI:
            w3 |= y3 >> 128 << 128
        print('  {"%s", %s, {%s}, {%s}, {%s}, 0x%03x, 0x%04x, 0x%016xULL, {%s}, %d, {%s}, 0x%016xULL, 0x%04x},' % (
            name, fn, q(y1, 4), q(y2, 4), q(y3, 4), f, mx, rax, q(mem, 8), off, q(w3, 4), wrax, wmx))
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
