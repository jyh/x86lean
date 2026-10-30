#!/usr/bin/env python3
"""hwprobe/mk_vexsilf_rows.py — D371: VEX `vmovd`/`vmovq` between an XMM register and a GPR or memory, the rows the
x86-64 referee runs, with expectations DERIVED HERE.

The forms (x86isa refuses all eight, D371 P1), all VEX.128 (VEX.L = 1 is #UD for MOVD/MOVQ):
  vmovd/vmovq r → xmm     `vmovd %eax, %xmm3`   `vmovq %rax, %xmm3`
  vmovd/vmovq xmm → r     `vmovd %xmm1, %eax`   `vmovq %xmm1, %rax`
  vmovd/vmovq m → xmm     `vmovd (%rbx), %xmm3` `vmovq (%rbx), %xmm3`   (the vmovq load assembles as F3 0F 7E)
  vmovd/vmovq xmm → m     `vmovd %xmm1, (%rbx)` `vmovq %xmm1, (%rbx)`   (the vmovq store assembles as 66 0F D6)
A thirteenth probe path: `vexsilf_ops.S`, `vexsilf_probe.c` (V10's probe with an EXPECTED BUFFER added, since two of these
forms write memory), and this file. One 64-byte buffer per row, `RBX = &mem[off]`, and every memory case runs twice: at
offset 0 and at an odd offset.

Every expected value comes from a stated rule, never from ACL2 x86isa and never from x86lean, and is extracted TWICE: the
rule slices integers, the textbook moves byte lists.

THE RULES (`rule`). w = 32 (vmovd) or 64 (vmovq); A = YMM1 (the xmm source); R = RAX; M = the w/8 bytes at `mem[off:]`:
  r → xmm     YMM3 := R[w-1:0], zero-extended to 256 bits (VEX.128: bits 255:128 are zeroed as well as 127:w)
  xmm → r     RAX := A[w-1:0], zero-extended to 64 bits (a 32-bit GPR write clears bits 63:32)
  m → xmm     YMM3 := M, zero-extended to 256 bits
  xmm → m     the w/8 bytes at mem[off] := A[w-1:0]; nothing else in the buffer moves
  NO-ALIGN    no row faults on an unaligned `off`
  NO-OTHERS   flags, MXCSR, YMM1, YMM2 unchanged; YMM3 unchanged where it is not the destination, RAX where it is not

Usage: mk_vexsilf_rows.py [--plant | --plant-op | --plant-hi | --plant-mem | --summary | --reach | --refuse-wrong |
                           --selftest]
  --plant         flips bit 32 of one vmovd load row's expected YMM3: exactly that row must disagree (exit 1)
  --plant-op      declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --plant-hi      one r → xmm row's expectation keeps YMM3's upper half: exactly that row must disagree
  --plant-mem     flips one bit of one store row's expected buffer, BEYOND the stored bytes: exactly that row
                  must disagree (the buffer comparison's own control, which V8c's and V10's probes lacked)
  --summary       per-function row counts, not C
  --reach         per wrong rule and mutant, how many rows it disagrees on
  --refuse-wrong  builds the rows under each wrong rule D371 names and shows `build` REFUSE it on its named row
  --selftest      hand-derived cases, a sweep, every row's two derivations, the refusals, the mutants' exact reach, plants
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "scripts"))
import portable as P  # noqa: E402

ARITH = 0x8d5
M64 = (1 << 64) - 1
M128 = (1 << 128) - 1
M256 = (1 << 256) - 1

# clang's bytes for each `vexsilf_ops.S` line (`clang -target x86_64-unknown-linux-gnu -c`, read with `objdump -d`).
OPS = [   # (function, form, width, bytes)
    ("x_vmovd_gx", "gx", 32, "c5f96ed8"), ("x_vmovq_gx", "gx", 64, "c4e1f96ed8"),
    ("x_vmovd_xg", "xg", 32, "c5f97ec8"), ("x_vmovq_xg", "xg", 64, "c4e1f97ec8"),
    ("x_vmovd_ld", "ld", 32, "c5f96e1b"), ("x_vmovq_ld", "ld", 64, "c5fa7e1b"),
    ("x_vmovd_st", "st", 32, "c5f97e0b"), ("x_vmovq_st", "st", 64, "c5f9d60b"),
]
MEMORY = ("ld", "st")
UNALIGNED = [1, 13, 7, 29]           # ODD offsets: unaligned for both operand sizes; each memory case runs at 0 AND one

PLANT_ROW = "vmovd_ld_ones_a"        # --plant: bit 32 of its expected YMM3 (a vmovd load must zero bits 127:32)
PLANT_HI = "vmovq_gx_ones_r"         # --plant-hi: its expectation keeps YMM3's upper half
PLANT_MEM = "vmovd_st_ones_u"        # --plant-mem: a bit of its expected buffer just past the four stored bytes


def mnemonic(fn):
    return fn[2:7]


# ── THE RULE ─────────────────────────────────────────────────────────────────────────────────────────────────────

def mem_operand(mem, off, n):
    """The n bytes at `off`, read as ONE little-endian integer out of the 64-byte buffer held as an integer."""
    return (mem >> (8 * off)) & ((1 << (8 * n)) - 1)


def place(mem, off, value, n):
    """`mem` with the n bytes at off replaced by `value` (little-endian)."""
    mask = ((1 << (8 * n)) - 1) << (8 * off)
    return (mem & ~mask & ((1 << 512) - 1)) | ((value & ((1 << (8 * n)) - 1)) << (8 * off))


def rule(form, w, y1, y3, rax, mem, off):
    """-> (YMM3, RAX, the buffer)."""
    lo = (1 << w) - 1
    if form == "gx":
        return rax & lo, rax, mem
    if form == "xg":
        return y3, y1 & lo, mem
    if form == "ld":
        return mem_operand(mem, off, w // 8), rax, mem
    return y3, rax, place(mem, off, y1 & lo, w // 8)


# ── THE WRONG RULES D371 NAMES ───────────────────────────────────────────────────────────────────────────────────

def w_legacy_upper(form, w, y1, y3, rax, mem, off):
    """(a) a VEX form that leaves YMM 255:128 untouched (the legacy SSE rule)."""
    d, r, m = rule(form, w, y1, y3, rax, mem, off)
    return (d | (y3 >> 128 << 128) if form in ("gx", "ld") else d), r, m


def w_merge_load(form, w, y1, y3, rax, mem, off):
    """(b) a vmovd load that merges bits 127:32 from the old destination instead of zeroing them."""
    d, r, m = rule(form, w, y1, y3, rax, mem, off)
    if form == "ld" and w == 32:
        d |= y3 & M128 & ~((1 << 32) - 1)
    return d, r, m


def w_store16(form, w, y1, y3, rax, mem, off):
    """(c) a vmovq store that writes 16 bytes (the whole xmm) instead of 8."""
    if form == "st" and w == 64:
        return y3, rax, place(mem, off, y1 & M128, 16)
    return rule(form, w, y1, y3, rax, mem, off)


def w_r32_keeps_high(form, w, y1, y3, rax, mem, off):
    """(d) a vmovd xmm → r32 that leaves bits 63:32 of the GPR instead of clearing them."""
    if form == "xg" and w == 32:
        return y3, (rax & ~((1 << 32) - 1) & M64) | (y1 & ((1 << 32) - 1)), mem
    return rule(form, w, y1, y3, rax, mem, off)


WRONG = [   # (letter, label, rule, the row `build` must name on refusing it)
    ("a", "a VEX form leaving YMM 255:128 untouched", w_legacy_upper, "vmovd_gx_zero_r"),
    ("b", "a vmovd load merging bits 127:32", w_merge_load, "vmovd_ld_zero_a"),
    ("c", "a vmovq store writing 16 bytes", w_store16, "vmovq_st_zero_a"),
    ("d", "a vmovd xmm → r32 keeping bits 63:32", w_r32_keeps_high, "vmovd_xg_zero_r"),
]


def m_keep_upper(form, w, y1, y3, rax, mem, off):
    """(reach only) the red-backwards mutant on the model: the destination YMM's upper half preserved."""
    return w_legacy_upper(form, w, y1, y3, rax, mem, off)


def m_store_one_short(form, w, y1, y3, rax, mem, off):
    """(reach only) a store that writes one byte too few."""
    if form == "st":
        return y3, rax, place(mem, off, y1, w // 8 - 1)
    return rule(form, w, y1, y3, rax, mem, off)


MUTANTS = [("the destination's upper half preserved", m_keep_upper), ("a store one byte short", m_store_one_short)]


# ── THE TEXTBOOK: byte lists ────────────────────────────────────────────────────────────────────────────────────

def tb_bytes(v, n):
    return [(v >> (8 * i)) & 0xff for i in range(n)]


def tb_int(bs):
    return sum(b << (8 * i) for i, b in enumerate(bs))


def textbook(form, w, y1, y3, rax, mem, off):
    n = w // 8
    buf = tb_bytes(mem, 64)
    a, r = tb_bytes(y1, 32), tb_bytes(rax, 8)
    if form == "gx":
        return tb_int(r[:n] + [0] * (32 - n)), rax, mem
    if form == "xg":
        return y3, tb_int(a[:n] + [0] * (8 - n)), mem
    if form == "ld":
        return tb_int(buf[off:off + n] + [0] * (32 - n)), rax, mem
    return y3, rax, tb_int(buf[:off] + a[:n] + buf[off + n:])


# ── the rows ────────────────────────────────────────────────────────────────────────────────────────────────────

ROWS = []   # (name, fn, form, w, y1, y2, y3, f, rax, mem, off, w3, wrax, wmem)


class Refused(SystemExit):
    def __init__(self, row, msg):
        super().__init__(msg)
        self.row = row


def cases(rng):
    """(name, the value moved). `zero` makes every wrong rule's difference come from the OTHER operand alone;
    `ones` sets every bit the width reaches; `sign` the top bit only; the rest random."""
    return [("zero", 0), ("ones", M128), ("sign", 1 << 63 | 1 << 31)] + [("rand%d" % i, rng.getrandbits(128))
                                                                         for i in range(3)]


def build(rl=None):
    rl = rl or rule
    ROWS.clear()
    for k, (fn, form, w, _bs) in enumerate(OPS):
        rng = random.Random(371000 + k)
        variants = "au" if form in MEMORY else "r"
        for j, (nm, v) in enumerate(cases(rng)):
            for var in variants:
                off = UNALIGNED[j % len(UNALIGNED)] if var == "u" else 0
                # every register and buffer byte that is NOT the moved value is seeded NONZERO, so a wrong rule that
                # keeps an old bit instead of clearing it has a bit to keep
                y1 = (v if form in ("xg", "st") else rng.getrandbits(256)) | ((rng.getrandbits(128) | 1) << 128)
                y2 = rng.getrandbits(256) | 1 | (1 << 128)
                y3 = rng.getrandbits(256) | (1 << 128) | (1 << 64) | (1 << 32) | 1
                rax = (v & M64) if form == "gx" else rng.getrandbits(64) | (1 << 63) | (1 << 32)
                mem = rng.getrandbits(512) | (1 << 511)
                if form == "ld":
                    mem = place(mem, off, v, w // 8)
                f = ARITH if j % 2 else 0
                name = "%s_%s_%s" % (fn[2:], nm, var)
                got = rl(form, w, y1, y3, rax, mem, off)
                want = textbook(form, w, y1, y3, rax, mem, off)
                if got != want:
                    raise Refused(name, "mk_vexsilf_rows: ⛔ row %s: the RULE gives ymm3 %064x rax %016x, the "
                                        "TEXTBOOK ymm3 %064x rax %016x (buffers %s)" % (
                                            name, got[0], got[1], want[0], want[1],
                                            "equal" if got[2] == want[2] else "DIFFER"))
                ROWS.append((name, fn, form, w, y1, y2, y3, f, rax, mem, off, got[0], got[1], got[2]))


def q(v, n):
    return ", ".join("0x%016xULL" % ((v >> (64 * i)) & M64) for i in range(n))


def disagreements(rl):
    return {r[0] for r in ROWS if rl(r[2], r[3], r[4], r[6], r[8], r[9], r[10]) != (r[11], r[12], r[13])}


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

    # hand-derived, each against both references
    y3 = M256
    say(rule("gx", 32, 0, y3, 0xdeadbeef_cafef00d, 0, 0)[0] == 0xcafef00d
        == textbook("gx", 32, 0, y3, 0xdeadbeef_cafef00d, 0, 0)[0],
        "hand: vmovd %eax, %xmm3 over an all-ones YMM3 leaves exactly 0xcafef00d, both references")
    say(rule("xg", 32, 0x11223344_55667788 | (5 << 200), 0, M64, 0, 0)[1] == 0x55667788
        == textbook("xg", 32, 0x11223344_55667788 | (5 << 200), 0, M64, 0, 0)[1],
        "hand: vmovd %xmm1, %eax over an all-ones RAX leaves RAX = 0x55667788, both references")
    mem = place(0, 13, 0x0123456789abcdef, 8)
    say(rule("ld", 64, 0, y3, 0, mem, 13)[0] == 0x0123456789abcdef
        == textbook("ld", 64, 0, y3, 0, mem, 13)[0],
        "hand: vmovq (%rbx), %xmm3 at offset 13 reads the eight bytes there and nothing above, both references")
    mem = (1 << 512) - 1
    want = mem & ~(((1 << 32) - 1) << 8)
    say(rule("st", 32, 0, 0, 0, mem, 1)[2] == want == textbook("st", 32, 0, 0, 0, mem, 1)[2],
        "hand: vmovd %xmm1 (= 0), (%rbx) at offset 1 clears exactly bytes 1..4 of an all-ones buffer, both references")
    rng = random.Random(371999)
    nd = 0
    for i in range(3000):
        _fn, form, w, _b = OPS[i % len(OPS)]
        a, y3, rax, m = rng.getrandbits(256), rng.getrandbits(256), rng.getrandbits(64), rng.getrandbits(512)
        off = rng.choice([0] + UNALIGNED)
        nd += rule(form, w, a, y3, rax, m, off) != textbook(form, w, a, y3, rax, m, off)
    say(nd == 0, "the rule and the textbook agree on 3,000 swept (form, width, registers, buffer, offset) cases")
    build()
    say(len(ROWS) > 0, "%d rows built, every one equal under the rule and the textbook" % len(ROWS))
    say(refusals(quiet=True) == 0, "each of the %d wrong rules (a)-(d) is REFUSED on its named row" % len(WRONG))
    reach = {m_keep_upper: {r[0] for r in ROWS if r[2] in ("gx", "ld")},
             m_store_one_short: {r[0] for r in ROWS if r[2] == "st"
                                 and (r[4] >> (r[3] - 8)) & 0xff != (r[9] >> (8 * (r[10] + r[3] // 8 - 1))) & 0xff}}
    for label, rl in MUTANTS:
        hit = disagreements(rl)
        say(hit == reach[rl] and hit, "mutant '%s' disagrees on exactly the %d rows it reaches" % (label, len(hit)))
    pairs = {}
    for r in ROWS:
        if r[2] in MEMORY:
            pairs.setdefault(r[0][:-2], {})[r[0][-1]] = r
    say(all(set(v) == {"a", "u"} and v["a"][10] == 0 and v["u"][10] % 2 == 1 for v in pairs.values()),
        "every one of the %d memory cases runs twice, at offset 0 and at an ODD offset" % len(pairs))
    say(all(r[10] + r[3] // 8 <= 64 for r in ROWS), "every memory operand lies inside the 64-byte buffer")
    say(all(r[11] >> 128 == 0 for r in ROWS if r[2] in ("gx", "ld")) and all(r[6] >> 128 for r in ROWS),
        "every r → xmm and m → xmm row expects YMM3[255:128] = 0, over a YMM3 seeded nonzero there")
    say(all(r[13] == r[9] for r in ROWS if r[2] != "st") and all(r[13] != r[9] or r[4] & ((1 << r[3]) - 1)
                                                                 == mem_operand(r[9], r[10], r[3] // 8)
                                                                 for r in ROWS if r[2] == "st"),
        "only the store rows expect the buffer to change, and each changes it unless it stores what was there")
    for nm, form in ((PLANT_ROW, "ld"), (PLANT_HI, "gx"), (PLANT_MEM, "st")):
        pk = [r for r in ROWS if r[0] == nm]
        say(len(pk) == 1 and pk[0][2] == form, "the plant row %s exists once and is a %s row" % (nm, form))
    say({(fn, f, w) for _n, fn, f, w, *_ in ROWS} == {(fn, f, w) for fn, f, w, _b in OPS},
        "the rows cover exactly the %d encodings" % len(OPS))
    print("✅ mk_vexsilf_rows selftest" if not bad else "⛔ mk_vexsilf_rows selftest FAILED")
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
        for fn, _f, _w, _b in OPS:
            print("%-14s %3d" % (fn, sum(1 for r in ROWS if r[1] == fn)))
        print("rows %d functions %d" % (len(ROWS), len(OPS)))
        return 0
    if "--reach" in sys.argv:
        for label, rl in [(w[1], w[2]) for w in WRONG] + MUTANTS:
            print("%-44s disagrees on %3d rows" % (label, len(disagreements(rl))))
        return 0
    plant, plant_hi, plant_mem = "--plant" in sys.argv, "--plant-hi" in sys.argv, "--plant-mem" in sys.argv
    print("/* GENERATED by hwprobe/mk_vexsilf_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    for fn, _f, _w, _b in OPS:
        print("void %s(struct xio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const struct xrow XROWS[] = {")
    for name, fn, form, w, y1, y2, y3, f, rax, mem, off, w3, wrax, wmem in ROWS:
        if plant and name == PLANT_ROW:
            w3 ^= 1 << 32
        if plant_hi and name == PLANT_HI:
            w3 |= y3 >> 128 << 128
        if plant_mem and name == PLANT_MEM:
            wmem ^= 1 << (8 * (off + w // 8))
        print('  {"%s", %s, {%s}, {%s}, {%s}, 0x%03x, 0x%016xULL, {%s}, %d, {%s}, 0x%016xULL, {%s}},' % (
            name, fn, q(y1, 4), q(y2, 4), q(y3, 4), f, rax, q(mem, 8), off, q(w3, 4), wrax, q(wmem, 8)))
    print("};")
    print("static const struct xop XOPS[] = {")
    for i, (fn, _f, _w, bs) in enumerate(OPS):
        bb = bytearray.fromhex(bs)
        if "--plant-op" in sys.argv and i == 0:
            bb[-1] ^= 0x01
        print('  {"%s", %s_at, %d, {%s}},' % (fn, fn, len(bb), ", ".join("0x%02x" % x for x in bb)))
    print("};")
    return 0


if __name__ == "__main__":
    sys.exit(main())
