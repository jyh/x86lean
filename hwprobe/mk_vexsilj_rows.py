#!/usr/bin/env python3
"""hwprobe/mk_vexsilj_rows.py — D379: `pabs{b,w,d}` and `pmulld`, legacy and VEX (128 and 256), the rows the x86-64
referee runs, with expectations DERIVED HERE.

The forms (x86isa refuses all ten encodings probed, D379 P1), each as a register and a memory form:
  pabs{b,w,d} %xmm1|(%rbx), %xmm3                 SSSE3, legacy: YMM3[255:128] PRESERVED; m128 16-byte aligned
  pmulld      %xmm1|(%rbx), %xmm3                 SSE4.1, legacy: XMM3 := XMM3 × SRC (low 32 of each lane)
  vpabs{b,w,d} %xmm1|(%rbx), %xmm3                VEX.128: YMM3[255:128] ZEROED; no alignment check
  vpmulld     %xmm2|(%rbx), %xmm1, %xmm3          VEX.128: XMM3 := XMM1 × SRC2; YMM3[255:128] ZEROED
  vpabs{b,w,d} %ymm1|(%rbx), %ymm3                VEX.256: all 256 bits
  vpmulld     %ymm2|(%rbx), %ymm1, %ymm3          VEX.256
The probe is D371's (`vexsilf_probe.c`, compiled against `vexsilj_rows.h`): YMM1/YMM2/YMM3, RAX, the six flags and a
64-byte buffer from the row, RBX = &mem[off], and an EXPECTED buffer (no form here writes memory, so it equals the
buffer; `--plant-mem` proves the probe compares it).

THE RULES (SDM Vol. 2B PABSB/PABSW/PABSD, PMULLD). A lane of width w is read as a SIGNED integer.
  PABS*        each lane := |lane| as an UNSIGNED w-bit result, so |−2^(w−1)| = 2^(w−1): the same bit pattern (it WRAPS;
               it does not saturate)
  PMULLD       each 32-bit lane := the LOW 32 bits of the 64-bit product of the two signed lanes
  legacy       YMM3[127:0] := result;  YMM3[255:128] PRESERVED
  VEX.128      YMM3[127:0] := result;  YMM3[255:128] := 0
  VEX.256      YMM3[255:0] := result
  NO-OTHERS    flags, MXCSR (0x1F80), RAX, YMM1, YMM2 and the buffer unchanged
`textbook` re-derives each row from byte lists with signed lane reads; every row must agree or the build refuses.

SEEDING: every source (the register and the memory operand) carries, in its first four lanes of each width, that
width's MINIMUM, 0, −1 and MAXIMUM, so a saturating abs disagrees on every abs row by construction; the other lanes are
random. OFFSETS: legacy memory rows at 0, 16 and 32 only (an unaligned legacy m128 is #GP(0), which the probe cannot read
as a value; that rule is the model's `decide` row, D379 prediction 2(e)); VEX.128 memory rows at 0 and odd offsets;
VEX.256 memory rows at offsets ≤ 32, so 32 bytes stay inside the 64-byte buffer. Register rows run at offset 0.

THE BYTES are the SDM's encodings: legacy 66 0F 38 {1C,1D,1E,40} /r; VEX C4, then R̄X̄B̄ m-mmmm = E2 (0F38), then
W vvvv̄ L pp (pp = 01; vvvv = 1111 for the unary abs, YMM1 for pmulld; L = 1 for 256), then the opcode and ModRM D9
(reg 3, rm 1), DA (reg 3, rm 2) or 1B (reg 3, [RBX]).

Usage: mk_vexsilj_rows.py [--plant | --plant-op | --plant-hi | --plant-mem | --summary | --reach | --selftest]
  --plant      flips bit 64 of one abs row's expected YMM3: exactly that row must disagree (exit 1)
  --plant-op   declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --plant-hi   one VEX.128 row's expectation keeps YMM3's upper half: exactly that row must disagree
  --plant-mem  flips one bit of one memory row's expected buffer: exactly that row must disagree
  --reach      per named wrong rule, how many rows it disagrees on (every count must be non-zero)
  --selftest   the bytes against clang's, every row's two derivations, the wrong rules' reach, the plants
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "scripts"))
import portable as P  # noqa: E402

M128 = (1 << 128) - 1
M256 = (1 << 256) - 1
M512 = (1 << 512) - 1
M64 = (1 << 64) - 1
N_CASES = 6
OFFS = {"L": [0, 16, 32], "V": [0, 1, 7, 13, 33, 48], "Y": [0, 1, 7, 13, 32]}
PLANT_ROW = "vpabsw_r_c0_o0"
PLANT_HI = "vpmulld_r_c0_o0"
PLANT_MEM = "pabsw_m_c0_o0"

OPC = {"abs8": "1c", "abs16": "1d", "abs32": "1e", "mulld": "40"}
MN = {"abs8": "pabsb", "abs16": "pabsw", "abs32": "pabsd", "mulld": "pmulld"}


def encode(op, mode, shape):
    """The SDM encoding (see the docstring), never clang's."""
    if mode == "L":
        return "660f38" + OPC[op] + ("d9" if shape == "r" else "1b")
    unary = op != "mulld"
    b3 = (0x79 if unary else 0x71) | (0x04 if mode == "Y" else 0)
    modrm = ("d9" if unary else "da") if shape == "r" else "1b"
    return "c4e2%02x" % b3 + OPC[op] + modrm


# (function, mnemonic, op, mode, shape, declared bytes); mode L legacy · V VEX.128 · Y VEX.256
OPS = []
for _mode in "LVY":
    for _op in ("abs8", "abs16", "abs32", "mulld"):
        for _shape in "rm":
            _mn = ("v" if _mode != "L" else "") + MN[_op]
            _fn = "x_%s%s_%s" % (_mn, "y" if _mode == "Y" else "", _shape)
            OPS.append((_fn, _mn, _op, _mode, _shape, encode(_op, _mode, _shape)))


def width(op):
    return 32 if op == "mulld" else int(op[3:])


def lanes(v, w, n):
    return [(v >> (w * i)) & ((1 << w) - 1) for i in range(n // w)]


def pack(ls, w):
    return sum(x << (w * i) for i, x in enumerate(ls))


def sgn(x, w):
    return x - (1 << w) if x >> (w - 1) else x


def lane_fn(op, a, b):
    """One lane of the rule: `a` the destination-side source (pmulld only), `b` the source."""
    w = width(op)
    if op == "mulld":
        return (sgn(a, 32) * sgn(b, 32)) & 0xFFFFFFFF
    return abs(sgn(b, w)) & ((1 << w) - 1)


def compute(op, mode, a, b, lane=lane_fn):
    n = 256 if mode == "Y" else 128
    w = width(op)
    return pack([lane(op, x, y) for x, y in zip(lanes(a, w, n), lanes(b, w, n))], w)


def operands(op, mode, shape, y1, y2, y3, mem, off):
    """(the destination-side source a, the source b) as the instruction reads them."""
    n = 32 if mode == "Y" else 16
    m = (mem >> (8 * off)) & ((1 << (8 * n)) - 1)
    if op == "mulld":
        a = y3 if mode == "L" else y1
        b = (y1 if mode == "L" else y2) if shape == "r" else m
    else:
        a, b = 0, (y1 if shape == "r" else m)
    return a, b


def rule(op, mode, shape, y1, y2, y3, mem, off):
    """(YMM3, the buffer) after the instruction."""
    a, b = operands(op, mode, shape, y1, y2, y3, mem, off)
    r = compute(op, mode, a, b)
    if mode == "L":
        return (y3 & ~M128 & M256) | (r & M128), mem
    return r & (M128 if mode == "V" else M256), mem


def le(v, n):
    return [(v >> (8 * i)) & 0xff for i in range(n)]


def un(bs):
    return sum(x << (8 * i) for i, x in enumerate(bs))


def textbook(op, mode, shape, y1, y2, y3, mem, off):
    """The same rule from byte lists: lanes cut from bytes, signed by int.from_bytes."""
    n = 32 if mode == "Y" else 16
    w = width(op) // 8
    mb = le(mem, 64)[off:off + n]
    src = mb if shape == "m" else le(y1 if (op != "mulld" or mode == "L") else y2, 32)[:n]
    dst_side = le(y3 if mode == "L" else y1, 32)[:n]
    out = []
    for i in range(0, n, w):
        s = int.from_bytes(bytes(src[i:i + w]), "little", signed=True)
        if op == "mulld":
            d = int.from_bytes(bytes(dst_side[i:i + w]), "little", signed=True)
            v = (d * s) % (1 << 32)
        else:
            v = abs(s) % (1 << (8 * w))
        out += list(v.to_bytes(w, "little"))
    upper = le(y3, 32)[16:32] if mode == "L" else ([0] * 16 if mode == "V" else [])
    return un(out + upper), mem


def seed(v, bits):
    """Each width's MINIMUM, 0, −1 and MAXIMUM in the first four lanes of that width (b at bytes 0-3, w at bytes 4-11,
    d at bytes 12-27), the rest of `v` untouched."""
    for w, base in ((8, 0), (16, 32), (32, 96)):
        for k, x in enumerate((1 << (w - 1), 0, (1 << w) - 1, (1 << (w - 1)) - 1)):
            sh = base + w * k
            v = (v & ~(((1 << w) - 1) << sh)) | (x << sh)
    return v & ((1 << bits) - 1)


def w_saturate(op, a, b):                                   # (a) a saturating abs: |min| = max
    w = width(op)
    if op != "mulld" and b == 1 << (w - 1):
        return (1 << (w - 1)) - 1
    return lane_fn(op, a, b)


def w_high(op, a, b):                                       # (b) pmulld keeps the HIGH 32 bits
    if op == "mulld":
        return ((sgn(a, 32) * sgn(b, 32)) >> 32) & 0xFFFFFFFF
    return lane_fn(op, a, b)


def wrong_lane(lane):
    def f(op, mode, shape, y1, y2, y3, mem, off):
        a, b = operands(op, mode, shape, y1, y2, y3, mem, off)
        r = compute(op, mode, a, b, lane)
        if mode == "L":
            return (y3 & ~M128 & M256) | (r & M128), mem
        return r & (M128 if mode == "V" else M256), mem
    return f


def w_keep_upper(op, mode, shape, y1, y2, y3, mem, off):   # (c) a VEX.128 form keeps YMM3[255:128]
    r, m = rule(op, mode, shape, y1, y2, y3, mem, off)
    return (r | (y3 >> 128 << 128) if mode == "V" else r), m


def w_zero_upper(op, mode, shape, y1, y2, y3, mem, off):   # (d) a legacy form zeroes YMM3[255:128]
    r, m = rule(op, mode, shape, y1, y2, y3, mem, off)
    return (r & M128 if mode == "L" else r), m


def w_low_lane(op, mode, shape, y1, y2, y3, mem, off):     # (f) a VEX.256 form computes only the low lane
    r, m = rule(op, mode, shape, y1, y2, y3, mem, off)
    return (r & M128 if mode == "Y" else r), m


WRONG = [("(a) a saturating abs (|min| = max)", wrong_lane(w_saturate)),
         ("(b) pmulld keeps the HIGH 32 bits", wrong_lane(w_high)),
         ("(c) a VEX.128 form keeps YMM3[255:128]", w_keep_upper),
         ("(d) a legacy form zeroes YMM3[255:128]", w_zero_upper),
         ("(f) a VEX.256 form computes only the low lane", w_low_lane)]

ROWS = []   # (name, fn, op, mode, shape, y1, y2, y3, f, rax, mem, off, w3, wmem)


def build():
    ROWS.clear()
    for k, (fn, mn, op, mode, shape, _bs) in enumerate(OPS):
        rng = random.Random(379000 + k)
        offs = OFFS[mode] if shape == "m" else [0]
        cases = N_CASES if shape == "m" else 2 * N_CASES
        for c in range(cases):
            for off in offs:
                y1 = seed(rng.getrandbits(256), 256)
                y2 = seed(rng.getrandbits(256), 256)
                y3 = rng.getrandbits(256) | 1 | (1 << 64) | (1 << 128)
                rax = rng.getrandbits(64) | (1 << 63)
                mem = rng.getrandbits(512)
                mem = (mem & ~(M256 << (8 * off)) & M512) | (seed((mem >> (8 * off)) & M256, 256) << (8 * off))
                mem &= M512
                f = 0x8d5 if (c + off) % 2 else 0
                name = "%s%s_%s_c%d_o%d" % (mn, "y" if mode == "Y" else "", shape, c, off)
                got = rule(op, mode, shape, y1, y2, y3, mem, off)
                if got != textbook(op, mode, shape, y1, y2, y3, mem, off):
                    raise SystemExit("mk_vexsilj_rows: ⛔ row %s: the rule and the textbook disagree" % name)
                ROWS.append((name, fn, op, mode, shape, y1, y2, y3, f, rax, mem, off, got[0], got[1]))


def disagreements(rl):
    return [r[0] for r in ROWS if rl(r[2], r[3], r[4], r[5], r[6], r[7], r[10], r[11]) != (r[12], r[13])]


def q(v, n):
    return ", ".join("0x%016xULL" % ((v >> (64 * i)) & M64) for i in range(n))


def selftest():
    ok = True

    def say(c, what):
        nonlocal ok
        print(("  ✔ " if c else "  ✖ ") + what)
        ok = ok and c
    # clang's bytes for these lines (`clang -target x86_64-unknown-linux-gnu -c`, objdump), read when this was written
    clang = {"x_pabsb_r": "660f381cd9", "x_pabsb_m": "660f381c1b", "x_pabsw_r": "660f381dd9",
             "x_pabsw_m": "660f381d1b", "x_pabsd_r": "660f381ed9", "x_pabsd_m": "660f381e1b",
             "x_pmulld_r": "660f3840d9", "x_pmulld_m": "660f38401b",
             "x_vpabsb_r": "c4e2791cd9", "x_vpabsb_m": "c4e2791c1b", "x_vpabsw_r": "c4e2791dd9",
             "x_vpabsw_m": "c4e2791d1b", "x_vpabsd_r": "c4e2791ed9", "x_vpabsd_m": "c4e2791e1b",
             "x_vpmulld_r": "c4e27140da", "x_vpmulld_m": "c4e271401b",
             "x_vpabsby_r": "c4e27d1cd9", "x_vpabsby_m": "c4e27d1c1b", "x_vpabswy_r": "c4e27d1dd9",
             "x_vpabswy_m": "c4e27d1d1b", "x_vpabsdy_r": "c4e27d1ed9", "x_vpabsdy_m": "c4e27d1e1b",
             "x_vpmulldy_r": "c4e27540da", "x_vpmulldy_m": "c4e275401b"}
    say(len(OPS) == 24 and len(clang) == 24, "24 functions, 24 clang encodings")
    for fn, _mn, _op, _mode, _shape, bs in OPS:
        say(clang.get(fn) == bs, "%s: the SDM derivation %s equals clang's %s" % (fn, bs, clang.get(fn)))
    build()
    want = sum((N_CASES * len(OFFS[m]) if s == "m" else 2 * N_CASES) for _f, _n, _o, m, s, _b in OPS)
    say(len(ROWS) == want, "%d rows = Σ (memory: 6 × offsets; register: 12)" % len(ROWS))
    for label, rl in WRONG:
        n = len(disagreements(rl))
        say(n > 0, "%s disagrees on %d rows" % (label, n))
    abs_rows = sum(1 for r in ROWS if r[2] != "mulld")
    say(len(disagreements(WRONG[0][1])) == abs_rows, "(a) disagrees on EVERY abs row (%d): the seeding reaches it"
        % abs_rows)
    names = {r[0] for r in ROWS}
    say(all(p in names for p in (PLANT_ROW, PLANT_HI, PLANT_MEM)), "the three plant rows exist")
    print("✅ mk_vexsilj_rows selftest" if ok else "⛔ mk_vexsilj_rows selftest FAILED")
    return 0 if ok else 1


def main():
    P.strict_flags(__file__)
    if "--selftest" in sys.argv:
        return selftest()
    build()
    if "--summary" in sys.argv:
        for fn, *_ in OPS:
            print("%-20s %3d" % (fn, sum(1 for r in ROWS if r[1] == fn)))
        print("rows %d functions %d" % (len(ROWS), len(OPS)))
        return 0
    if "--reach" in sys.argv:
        bad = 0
        for label, rl in WRONG:
            n = len(disagreements(rl))
            print("%-48s disagrees on %4d of %d rows" % (label, n, len(ROWS)))
            bad += n == 0
        return 1 if bad else 0
    plant, plant_hi, plant_mem = "--plant" in sys.argv, "--plant-hi" in sys.argv, "--plant-mem" in sys.argv
    print("/* GENERATED by hwprobe/mk_vexsilj_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    for fn, *_ in OPS:
        print("void %s(struct xio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const struct xrow XROWS[] = {")
    for name, fn, _o, _m, _s, y1, y2, y3, f, rax, mem, off, w3, wmem in ROWS:
        if plant and name == PLANT_ROW:
            w3 ^= 1 << 64
        if plant_hi and name == PLANT_HI:
            w3 |= y3 >> 128 << 128
        if plant_mem and name == PLANT_MEM:
            wmem ^= 1 << (8 * off + 3)
        print('  {"%s", %s, {%s}, {%s}, {%s}, 0x%03x, 0x%016xULL, {%s}, %d, {%s}, 0x%016xULL, {%s}},' % (
            name, fn, q(y1, 4), q(y2, 4), q(y3, 4), f, rax, q(mem, 8), off, q(w3, 4), rax, q(wmem, 8)))
    print("};")
    print("static const struct xop XOPS[] = {")
    for i, (fn, _mn, _o, _m, _s, bs) in enumerate(OPS):
        bb = bytearray.fromhex(bs)
        if "--plant-op" in sys.argv and i == 0:
            bb[-1] ^= 0x01
        print('  {"%s", %s_at, %d, {%s}},' % (fn, fn, len(bb), ", ".join("0x%02x" % x for x in bb)))
    print("};")
    return 0


if __name__ == "__main__":
    sys.exit(main())
