#!/usr/bin/env python3
"""hwprobe/mk_vexsilh_rows.py — D375: the VEX.256 128-bit lane INSERT and EXTRACT, the rows the x86-64 referee runs, with
expectations DERIVED HERE.

The forms (x86isa refuses all eight encodings, D375 P1), each at imm8 ∈ {0, 1, 2, 3, 0xfe, 0xff}:
  vinserti128 / vinsertf128   imm, xmm2 | m128, ymm1, ymm3       DEST := SRC1 with lane imm[0] := SRC2[127:0]
  vextracti128 / vextractf128 imm, ymm1, xmm3 | m128             DEST := SRC lane imm[0]
The probe is D371's (`vexsilf_probe.c`, compiled against `vexsilh_rows.h`): YMM1/YMM2/YMM3, RAX, the six flags and a
64-byte buffer from the row, RBX = &mem[off], and an EXPECTED buffer, because the two extract-to-memory forms store.

THE RULES (SDM Vol. 2C, VINSERTI128/VINSERTF128, VEXTRACTI128/VEXTRACTF128; VEX.256 only). Lane i of a 256-bit value is
bits 128(i+1)-1 : 128i; only imm[0] selects, imm[7:1] are ignored.
  INSERT       DEST := SRC1;  DEST.lane[imm[0]] := SRC2[127:0]  (SRC2 the xmm register or the 16 bytes at mem[off])
  EXTRACT      DEST[127:0] := SRC.lane[imm[0]];  DEST[255:128] := 0  (the VEX.128 register write)
  STORE        mem[off : off+16] := SRC.lane[imm[0]];  no other byte, no register written
  NO-ALIGN     no row faults at an odd `off`
  NO-OTHERS    flags, MXCSR (0x1F80 in and out), RAX, YMM1 and YMM2 unchanged; the buffer unchanged except a store's bytes
`textbook` re-derives each row from byte lists (lanes cut as 16-byte slices); every row must agree or the build refuses.
The integer and FP spellings are one function at two opcodes: their rows are the same rule.

THE BYTES are derived from the SDM's VEX rule: C4, E3 (R̄X̄B̄ = 111, map 0F3A), then W=0 · vvvv̄ · L=1 · pp=01 — 75 for an
insert (vvvv = YMM1) and 7D for an extract (vvvv unused, 1111) — the opcode (38/18 insert, 39/19 extract, integer/FP),
ModRM (DA: reg YMM3, rm XMM2 · 1B: reg YMM3, [RBX] · CB: reg YMM1, rm XMM3 · 0B: reg YMM1, [RBX]) and imm8.

Usage: mk_vexsilh_rows.py [--plant | --plant-op | --plant-hi | --plant-mem | --summary | --reach | --selftest]
  --plant      flips bit 128 of one insert row's expected YMM3: exactly that row must disagree (exit 1)
  --plant-op   declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --plant-hi   one extract-to-xmm row's expectation keeps YMM3's upper half: exactly that row must disagree
  --plant-mem  flips a bit of one store row's expected buffer just past the 16 stored bytes: exactly that row
  --reach      per named wrong rule, how many rows it disagrees on (every count must be non-zero)
  --selftest   the bytes against clang's, every row's two derivations, the wrong rules' reach, the plants
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "scripts"))
import portable as P  # noqa: E402

M64 = (1 << 64) - 1
M128 = (1 << 128) - 1
M256 = (1 << 256) - 1
M512 = (1 << 512) - 1
IMMS = [0, 1, 2, 3, 0xfe, 0xff]
UNALIGNED = [1, 7, 13, 33]
N_CASES = 4
OPC = {("ins", False): "38", ("ins", True): "18", ("ext", False): "39", ("ext", True): "19"}
MNEM = {("ins", False): "vinserti128", ("ins", True): "vinsertf128",
        ("ext", False): "vextracti128", ("ext", True): "vextractf128"}
PLANT_ROW = "vinserti128_r_i1_c0"
PLANT_HI = "vextracti128_r_i1_c0"
PLANT_MEM = "vextracti128_m_i1_c0_u"


def enc(op, fp, shape, imm):
    b2 = "75" if op == "ins" else "7d"
    modrm = {("ins", "r"): "da", ("ins", "m"): "1b", ("ext", "r"): "cb", ("ext", "m"): "0b"}[(op, shape)]
    return "c4e3" + b2 + OPC[(op, fp)] + modrm + "%02x" % imm


OPS = []   # (function, op, fp, shape, imm, declared bytes)
for _op in ("ins", "ext"):
    for _fp in (False, True):
        for _s in ("r", "m"):
            for _i in IMMS:
                OPS.append(("x_%s_%s_i%x" % (MNEM[(_op, _fp)], _s, _i), _op, _fp, _s, _i, enc(_op, _fp, _s, _i)))


def lane(v, i):
    return (v >> (128 * i)) & M128


def rule(op, shape, imm, y1, y2, y3, mem, off):
    """(YMM3, the buffer) after the instruction."""
    sel = imm & 1
    if op == "ins":
        src = y2 & M128 if shape == "r" else (mem >> (8 * off)) & M128
        return (y1 & ~(M128 << (128 * sel)) & M256) | (src << (128 * sel)), mem
    v = lane(y1, sel)
    if shape == "r":
        return v, mem
    mask = M128 << (8 * off)
    return y3, (mem & ~mask & M512) | (v << (8 * off))


def le(v, n):
    return [(v >> (8 * i)) & 0xff for i in range(n)]


def un(bs):
    return sum(x << (8 * i) for i, x in enumerate(bs))


def textbook(op, shape, imm, y1, y2, y3, mem, off):
    """The same from byte lists: a lane is a 16-byte slice, a store overwrites 16 list entries."""
    a, m, s = le(y1, 32), le(mem, 64), (imm & 1) * 16
    if op == "ins":
        src = le(y2, 32)[:16] if shape == "r" else m[off:off + 16]
        return un(a[:s] + src + a[s + 16:]), mem
    v = a[s:s + 16]
    if shape == "r":
        return un(v + [0] * 16), mem
    return y3, un(m[:off] + v + m[off + 16:])


def w_imm_two_bits(op, shape, imm, y1, y2, y3, mem, off):      # (a) imm[1] selects the lane
    return rule(op, shape, (imm >> 1) & 1, y1, y2, y3, mem, off)


def w_ext_keep_upper(op, shape, imm, y1, y2, y3, mem, off):    # (b) an extract to xmm leaves YMM3[255:128]
    r, m = rule(op, shape, imm, y1, y2, y3, mem, off)
    return (r | (y3 >> 128 << 128) if (op, shape) == ("ext", "r") else r), m


def w_ins_wrong_lane(op, shape, imm, y1, y2, y3, mem, off):    # (c) an insert into the other lane
    return rule(op, shape, imm ^ 1, y1, y2, y3, mem, off) if op == "ins" else rule(op, shape, imm, y1, y2, y3, mem, off)


def w_store_32(op, shape, imm, y1, y2, y3, mem, off):          # (d) a store that writes 32 bytes (the whole YMM)
    if (op, shape) != ("ext", "m"):
        return rule(op, shape, imm, y1, y2, y3, mem, off)
    v = y1 if imm & 1 == 0 else (lane(y1, 1) | (lane(y1, 0) << 128))
    mask = M256 << (8 * off)
    return y3, (mem & ~mask & M512) | ((v << (8 * off)) & M512)


WRONG = [("(a) imm[1] selects the lane", w_imm_two_bits), ("(b) an extract to xmm keeps YMM3[255:128]", w_ext_keep_upper),
         ("(c) an insert into the other lane", w_ins_wrong_lane), ("(d) a store of 32 bytes", w_store_32)]

ROWS = []   # (name, fn, op, fp, shape, imm, y1, y2, y3, f, rax, mem, off, w3, wmem)


def build():
    ROWS.clear()
    for k, (fn, op, fp, shape, imm, _bs) in enumerate(OPS):
        rng = random.Random(375000 + k)
        variants = [(c, "a", 0) for c in range(N_CASES)] if shape == "r" else \
            [(c, v, 0 if v == "a" else UNALIGNED[c % len(UNALIGNED)]) for c in range(N_CASES) for v in "au"]
        for i, (c, v, off) in enumerate(variants):
            y1 = rng.getrandbits(256) | 1 | (1 << 128)
            y2 = rng.getrandbits(256) | 1 | (1 << 128)
            y3 = rng.getrandbits(256) | 1 | (1 << 128)
            rax = rng.getrandbits(64) | (1 << 63)
            mem = rng.getrandbits(512) | 1
            f = 0x8d5 if i % 2 else 0
            name = "%s_c%d%s" % (fn[2:], c, "" if shape == "r" else "_" + v)
            got = rule(op, shape, imm, y1, y2, y3, mem, off)
            tb = textbook(op, shape, imm, y1, y2, y3, mem, off)
            if got != tb:
                raise SystemExit("mk_vexsilh_rows: ⛔ row %s: the rule and the textbook disagree" % name)
            ROWS.append((name, fn, op, fp, shape, imm, y1, y2, y3, f, rax, mem, off, got[0], got[1]))


def disagreements(rl):
    return [r[0] for r in ROWS if rl(r[2], r[4], r[5], r[6], r[7], r[8], r[11], r[12]) != (r[13], r[14])]


def q(v, n):
    return ", ".join("0x%016xULL" % ((v >> (64 * i)) & M64) for i in range(n))


def selftest():
    ok = True

    def say(c, what):
        nonlocal ok
        print(("  ✔ " if c else "  ✖ ") + what)
        ok = ok and c
    clang = {("ins", False, "r", 1): "c4e37538da01", ("ins", False, "m", 0): "c4e375381b00",
             ("ins", True, "r", 1): "c4e37518da01", ("ins", True, "m", 0): "c4e375181b00",
             ("ext", False, "r", 1): "c4e37d39cb01", ("ext", False, "m", 1): "c4e37d390b01",
             ("ext", True, "r", 1): "c4e37d19cb01", ("ext", True, "m", 1): "c4e37d190b01"}
    for (op, fp, s, i), want in clang.items():
        say(enc(op, fp, s, i) == want, "%s %s imm %d: the SDM derivation gives clang's %s (D375 P1)" % (
            MNEM[(op, fp)], s, i, want))
    build()
    say(len(ROWS) == len(IMMS) * 4 * (N_CASES + 2 * N_CASES), "%d rows = 6 imms × 4 mnemonics × (4 + 8)" % len(ROWS))
    for label, rl in WRONG:
        n = len(disagreements(rl))
        say(n > 0, "%s disagrees on %d rows" % (label, n))
    names = {r[0] for r in ROWS}
    say(PLANT_ROW in names and PLANT_HI in names and PLANT_MEM in names, "the three plant rows exist")
    print("✅ mk_vexsilh_rows selftest" if ok else "⛔ mk_vexsilh_rows selftest FAILED")
    return 0 if ok else 1


def main():
    P.strict_flags(__file__)
    if "--selftest" in sys.argv:
        return selftest()
    build()
    if "--summary" in sys.argv:
        for fn, *_ in OPS:
            print("%-28s %3d" % (fn, sum(1 for r in ROWS if r[1] == fn)))
        print("rows %d functions %d" % (len(ROWS), len(OPS)))
        return 0
    if "--reach" in sys.argv:
        bad = 0
        for label, rl in WRONG:
            n = len(disagreements(rl))
            print("%-44s disagrees on %4d of %d rows" % (label, n, len(ROWS)))
            bad += n == 0
        return 1 if bad else 0
    plant, plant_hi, plant_mem = "--plant" in sys.argv, "--plant-hi" in sys.argv, "--plant-mem" in sys.argv
    print("/* GENERATED by hwprobe/mk_vexsilh_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    for fn, *_ in OPS:
        print("void %s(struct xio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const struct xrow XROWS[] = {")
    for name, fn, _o, _fp, _s, _i, y1, y2, y3, f, rax, mem, off, w3, wmem in ROWS:
        if plant and name == PLANT_ROW:
            w3 ^= 1 << 128
        if plant_hi and name == PLANT_HI:
            w3 |= y3 >> 128 << 128
        if plant_mem and name == PLANT_MEM:
            wmem ^= 1 << (8 * (off + 16))
        print('  {"%s", %s, {%s}, {%s}, {%s}, 0x%03x, 0x%016xULL, {%s}, %d, {%s}, 0x%016xULL, {%s}},' % (
            name, fn, q(y1, 4), q(y2, 4), q(y3, 4), f, rax, q(mem, 8), off, q(w3, 4), rax, q(wmem, 8)))
    print("};")
    print("static const struct xop XOPS[] = {")
    for i, (fn, _o, _fp, _s, _imm, bs) in enumerate(OPS):
        bb = bytearray.fromhex(bs)
        if "--plant-op" in sys.argv and i == 0:
            bb[-1] ^= 0x01
        print('  {"%s", %s_at, %d, {%s}},' % (fn, fn, len(bb), ", ".join("0x%02x" % x for x in bb)))
    print("};")
    return 0


if __name__ == "__main__":
    sys.exit(main())
