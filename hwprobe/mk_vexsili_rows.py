#!/usr/bin/env python3
"""hwprobe/mk_vexsili_rows.py — D376: `movntdqa` and the VEX half-moves, the rows the x86-64 referee runs, with
expectations DERIVED HERE.

The forms (x86isa refuses all nine encodings, D376 P1):
  movntdqa (%rbx), %xmm3                         SSE4.1, a legacy write; m128 16-byte aligned (#GP otherwise)
  vmov{h,l}p{s,d} (%rbx), %xmm1, %xmm3           VEX.128 load: SRC1 merged with m64, YMM3[255:128] zeroed
  vmov{h,l}p{s,d} %xmm1, (%rbx)                  VEX.128 store: 8 bytes of SRC
The probe is D371's (`vexsilf_probe.c`, compiled against `vexsili_rows.h`): YMM1/YMM2/YMM3, RAX, the six flags and a
64-byte buffer from the row, RBX = &mem[off], and an EXPECTED buffer, because the stores write it.

THE RULES (SDM Vol. 2B MOVNTDQA, MOVHPS/MOVHPD/MOVLPS/MOVLPD "VEX.128 encoded version"). A 128-bit value's high quadword
is bits 127:64, its low quadword bits 63:0. M = the 8 (half-moves) or 16 (movntdqa) bytes at mem[off].
  MOVNTDQA     YMM3[127:0] := M;  YMM3[255:128] PRESERVED (a legacy SSE write)
  VMOVHP* m    YMM3[127:64] := M;  YMM3[63:0] := SRC1[63:0];  YMM3[255:128] := 0
  VMOVLP* m    YMM3[63:0] := M;   YMM3[127:64] := SRC1[127:64];  YMM3[255:128] := 0
  VMOVHP* st   mem[off : off+8] := SRC[127:64];  no register written
  VMOVLP* st   mem[off : off+8] := SRC[63:0]
  NO-OTHERS    flags, MXCSR (0x1F80), RAX, YMM1 and YMM2 unchanged; the buffer unchanged except a store's 8 bytes
The PS and PD spellings are one function at two prefixes: their rows are the same rule.
`textbook` re-derives each row from byte lists; every row must agree or the build refuses.

OFFSETS: the VEX forms run at 0 and at odd offsets (no alignment check); `movntdqa` only at 0, 16 and 32, because an
unaligned one is #GP(0), a fault the probe cannot read as a value.

THE BYTES are the SDM's encodings: MOVNTDQA = 66 0F 38 2A /r (ModRM 1B: reg XMM3, [RBX]); the VEX half-moves are C5,
then R̄ vvvv̄ L pp (L = 0; pp = 00 for PS, 01 for PD; vvvv = YMM1 for a load, 1111 for a store), then 0F 16/17 (high)
or 12/13 (low), then ModRM 1B (load: reg XMM3, [RBX]) or 0B (store: reg XMM1, [RBX]).

Usage: mk_vexsili_rows.py [--plant | --plant-op | --plant-hi | --plant-mem | --summary | --reach | --selftest]
  --plant      flips bit 64 of one VEX load row's expected YMM3: exactly that row must disagree (exit 1)
  --plant-op   declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --plant-hi   one VEX load row's expectation keeps YMM3's upper half: exactly that row must disagree
  --plant-mem  flips a bit of one store row's expected buffer just past the 8 stored bytes: exactly that row
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
N_CASES = 6
VEX_OFFS = [0, 1, 7, 13, 33, 56]
NT_OFFS = [0, 16, 32]
PLANT_ROW = "vmovhps_ld_c0_o0"
PLANT_HI = "vmovlps_ld_c0_o0"
PLANT_MEM = "vmovhpd_st_c0_o1"

# (function, mnemonic, kind, half, declared bytes): kind "nt" | "ld" | "st", half "h" | "l" | None
OPS = [("x_movntdqa", "movntdqa", "nt", None, "660f382a1b")]
for _mn, _h, _pp in (("vmovhps", "h", "f0"), ("vmovhpd", "h", "f1"), ("vmovlps", "l", "f0"), ("vmovlpd", "l", "f1")):
    _ld = {"h": "16", "l": "12"}[_h]
    OPS.append(("x_%s_ld" % _mn, _mn, "ld", _h, "c5" + _pp + _ld + "1b"))
    # the store's vvvv is 1111: R̄ 1111 L pp = f8 (PS) / f9 (PD)
    OPS.append(("x_%s_st" % _mn, _mn, "st", _h, "c5" + {"f0": "f8", "f1": "f9"}[_pp] + "%02x" % (int(_ld, 16) + 1) + "0b"))


def q_hi(v):
    return (v >> 64) & M64


def q_lo(v):
    return v & M64


def rule(kind, half, y1, y3, mem, off):
    """(YMM3, the buffer) after the instruction."""
    if kind == "nt":
        return (y3 & ~M128 & M256) | ((mem >> (8 * off)) & M128), mem
    if kind == "ld":
        m = (mem >> (8 * off)) & M64
        return ((m << 64) | q_lo(y1)) if half == "h" else ((q_hi(y1) << 64) | m), mem
    v = q_hi(y1) if half == "h" else q_lo(y1)
    return y3, (mem & ~(M64 << (8 * off)) & M512) | (v << (8 * off))


def le(v, n):
    return [(v >> (8 * i)) & 0xff for i in range(n)]


def un(bs):
    return sum(x << (8 * i) for i, x in enumerate(bs))


def textbook(kind, half, y1, y3, mem, off):
    a, d, m = le(y1, 32), le(y3, 32), le(mem, 64)
    if kind == "nt":
        return un(m[off:off + 16] + d[16:32]), mem
    if kind == "ld":
        lo, hi = (a[0:8], m[off:off + 8]) if half == "h" else (m[off:off + 8], a[8:16])
        return un(lo + hi + [0] * 16), mem
    v = a[8:16] if half == "h" else a[0:8]
    return y3, un(m[:off] + v + m[off + 8:])


def w_nt_zero_upper(kind, half, y1, y3, mem, off):     # (a) movntdqa zeroes YMM3[255:128]
    r, mm = rule(kind, half, y1, y3, mem, off)
    return (r & M128 if kind == "nt" else r), mm


def w_merge_dest(kind, half, y1, y3, mem, off):        # (b) a VEX load merges with DEST (the legacy rule)
    return rule(kind, half, y3, y3, mem, off) if kind == "ld" else rule(kind, half, y1, y3, mem, off)


def w_keep_upper(kind, half, y1, y3, mem, off):        # (c) a VEX load keeps YMM3[255:128]
    r, mm = rule(kind, half, y1, y3, mem, off)
    return (r | (y3 >> 128 << 128) if kind == "ld" else r), mm


def w_store_16(kind, half, y1, y3, mem, off):          # (d) a store of 16 bytes (the whole XMM)
    if kind != "st":
        return rule(kind, half, y1, y3, mem, off)
    return y3, (mem & ~(M128 << (8 * off)) & M512) | (((y1 & M128) << (8 * off)) & M512)


WRONG = [("(a) movntdqa zeroes YMM3[255:128]", w_nt_zero_upper), ("(b) a VEX load merges with DEST", w_merge_dest),
         ("(c) a VEX load keeps YMM3[255:128]", w_keep_upper), ("(d) a store of 16 bytes", w_store_16)]

ROWS = []   # (name, fn, kind, half, y1, y2, y3, f, rax, mem, off, w3, wmem)


def build():
    ROWS.clear()
    for k, (fn, mn, kind, half, _bs) in enumerate(OPS):
        rng = random.Random(376000 + k)
        offs = NT_OFFS if kind == "nt" else VEX_OFFS
        for c in range(N_CASES):
            for off in offs:
                y1 = rng.getrandbits(256) | 1 | (1 << 64) | (1 << 128)
                y2 = rng.getrandbits(256) | 1 | (1 << 128)
                y3 = rng.getrandbits(256) | 1 | (1 << 64) | (1 << 128)
                rax = rng.getrandbits(64) | (1 << 63)
                mem = rng.getrandbits(512) | 1
                f = 0x8d5 if (c + off) % 2 else 0
                name = "%s_%s_c%d_o%d" % (mn, kind, c, off) if kind != "nt" else "%s_c%d_o%d" % (mn, c, off)
                got = rule(kind, half, y1, y3, mem, off)
                if got != textbook(kind, half, y1, y3, mem, off):
                    raise SystemExit("mk_vexsili_rows: ⛔ row %s: the rule and the textbook disagree" % name)
                ROWS.append((name, fn, kind, half, y1, y2, y3, f, rax, mem, off, got[0], got[1]))


def disagreements(rl):
    return [r[0] for r in ROWS if rl(r[2], r[3], r[4], r[6], r[9], r[10]) != (r[11], r[12])]


def q(v, n):
    return ", ".join("0x%016xULL" % ((v >> (64 * i)) & M64) for i in range(n))


def selftest():
    ok = True

    def say(c, what):
        nonlocal ok
        print(("  ✔ " if c else "  ✖ ") + what)
        ok = ok and c
    # clang's bytes for these lines (`clang -target x86_64-unknown-linux-gnu -c`, objdump), read when this was written
    clang = {"x_movntdqa": "660f382a1b", "x_vmovhps_ld": "c5f0161b", "x_vmovhps_st": "c5f8170b",
             "x_vmovhpd_ld": "c5f1161b", "x_vmovhpd_st": "c5f9170b", "x_vmovlps_ld": "c5f0121b",
             "x_vmovlps_st": "c5f8130b", "x_vmovlpd_ld": "c5f1121b", "x_vmovlpd_st": "c5f9130b"}
    for fn, _mn, _k, _h, bs in OPS:
        say(clang.get(fn) == bs, "%s: the SDM derivation %s equals clang's %s" % (fn, bs, clang.get(fn)))
    build()
    say(len(ROWS) == N_CASES * (len(NT_OFFS) + 8 * len(VEX_OFFS)), "%d rows = 6 × (3 + 8 × 6)" % len(ROWS))
    for label, rl in WRONG:
        n = len(disagreements(rl))
        say(n > 0, "%s disagrees on %d rows" % (label, n))
    names = {r[0] for r in ROWS}
    say(all(p in names for p in (PLANT_ROW, PLANT_HI, PLANT_MEM)), "the three plant rows exist")
    print("✅ mk_vexsili_rows selftest" if ok else "⛔ mk_vexsili_rows selftest FAILED")
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
            print("%-40s disagrees on %4d of %d rows" % (label, n, len(ROWS)))
            bad += n == 0
        return 1 if bad else 0
    plant, plant_hi, plant_mem = "--plant" in sys.argv, "--plant-hi" in sys.argv, "--plant-mem" in sys.argv
    print("/* GENERATED by hwprobe/mk_vexsili_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    for fn, *_ in OPS:
        print("void %s(struct xio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const struct xrow XROWS[] = {")
    for name, fn, _k, _h, y1, y2, y3, f, rax, mem, off, w3, wmem in ROWS:
        if plant and name == PLANT_ROW:
            w3 ^= 1 << 64
        if plant_hi and name == PLANT_HI:
            w3 |= y3 >> 128 << 128
        if plant_mem and name == PLANT_MEM:
            wmem ^= 1 << (8 * (off + 8))
        print('  {"%s", %s, {%s}, {%s}, {%s}, 0x%03x, 0x%016xULL, {%s}, %d, {%s}, 0x%016xULL, {%s}},' % (
            name, fn, q(y1, 4), q(y2, 4), q(y3, 4), f, rax, q(mem, 8), off, q(w3, 4), rax, q(wmem, 8)))
    print("};")
    print("static const struct xop XOPS[] = {")
    for i, (fn, _mn, _k, _h, bs) in enumerate(OPS):
        bb = bytearray.fromhex(bs)
        if "--plant-op" in sys.argv and i == 0:
            bb[-1] ^= 0x01
        print('  {"%s", %s_at, %d, {%s}},' % (fn, fn, len(bb), ", ".join("0x%02x" % x for x in bb)))
    print("};")
    return 0


if __name__ == "__main__":
    sys.exit(main())
