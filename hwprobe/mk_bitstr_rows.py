#!/usr/bin/env python3
"""hwprobe/mk_bitstr_rows.py — D333: the BIT-STRING rows (BT/BTS/BTR/BTC with a memory base and a REGISTER offset)
the x86-64 referee runs, with expectations DERIVED HERE.

Every expected value comes from the rule stated below (SDM Vol. 2A §3.1.1.9 and Table 3-2; the BT, BTS, BTR and BTC
pages), never from ACL2 x86isa and never from x86lean:

  SIGNED-OFFSET   the register offset is read at the OPERAND SIZE and is SIGNED (−2^15..2^15−1 at 16 bits,
                  −2^31..2^31−1 at 32, −2^63..2^63−1 at 64). Bits of the register above the operand size are not
                  read: the 16- and 32-bit rows put junk there.
  BIT-STRING      the addressed bit is bit (offset AND 7) of the byte at EA + (offset SAR 3) — the SDM's
                  "bit (offset MOD 8) of the byte at BitBase + (offset DIV 8)" with DIV toward −infinity and MOD
                  non-negative, written in two's complement.
  CF              CF := the selected bit BEFORE any write. ZF is unchanged. OF, SF, AF, PF are undefined and are
                  not compared.
  WRITE-BACK      BT writes nothing; BTS sets the selected bit, BTR clears it, BTC complements it. NO OTHER BYTE of
                  memory changes: the probe compares the whole buffer, so a write to the wrong byte is a DIFF.

Beside each expectation this file computes what ACL2 x86isa's memory/register-offset rule predicts
(`machine/instructions/bit.lisp`: byte address `addr + floor(offset/8)`, bit number `(mod (abs offset) 8)`), so the
probe can print, per row, whether the processor matched that rule too. The x86isa column is a PREDICTION OF A
DISAGREEMENT, not an expectation: the referee's verdict (exit 0/1) is the SDM column alone.

The buffer: `BUF` bytes filled with PATTERN (derived here from a stated formula, emitted as data, never typed), the
base pointer at BUF/2, and each row overrides exactly ONE byte — the addressed byte — with a chosen pre-value, so the
row's bit takes both values and (in two of four variants) the two rules' bits disagree. The offsets reach at most
±4097 bytes from the base; everything further out on either side is a guard region the comparison covers.

Usage: mk_bitstr_rows.py [--plant | --plant-mem | --plant-stray | --plant-op | --summary]   writes C rows on stdout.
  --plant      flips CF in ONE expectation: the referee must report exactly one disagreement (exit 1)
  --plant-mem  replaces ONE BTS row's expected byte by the x86isa rule's: exactly one disagreement, through the
               MEMORY channel (exit 1)
  --plant-stray  moves ONE BTC row's addressed-byte index up by one, so the probe overrides the wrong byte and the
               instruction's real write lands where the comparison expects PATTERN: exactly one disagreement, and it
               names a STRAY WRITE (exit 1). Added after D333's pre-registration, before any push.
  --plant-op   declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --summary    prints the per-form counts (rows, rows where the two rules differ) and the per-row table, not C
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "scripts"))
import portable as P  # noqa: E402

CF, PF, AF, ZF, SF, OF = 0x1, 0x4, 0x10, 0x40, 0x80, 0x800
ARITH = CF | PF | AF | ZF | SF | OF          # 0x8d5
CMP = CF | ZF                                # the two DEFINED flags: CF written, ZF unchanged
BUF = 16384
BASE = BUF // 2
JUNK = 0xA5A5A5A5A5A5A5A5                    # bits above the operand size, which the 16/32-bit forms must not read

# (form, function, declared bytes, width, kind). ModRM 0x0b = mod 00, reg = rcx/ecx/cx, r/m = (%rbx).
OPS = []
for kind, opc in (("bt", "a3"), ("bts", "ab"), ("btr", "b3"), ("btc", "bb")):
    for w, pfx, suf in ((16, "66", "w"), (32, "", "l"), (64, "48", "q")):
        OPS.append(("%s%s_mr" % (kind, suf), "b_%s%s_mr" % (kind, suf), "%s0f%s0b" % (pfx, opc), w, kind))

POS = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 255, 256,
       4095, 4096, 4097, 32767]
NEG = list(range(-1, -17, -1)) + [-17, -31, -32, -33, -63, -64, -65, -127, -128, -129,
                                  -255, -256, -257, -4095, -4096, -4097, -32768]
WIDE = [32768, -32769]                        # beyond 16 bits: the 32- and 64-bit forms only


def offsets(w):
    return POS + NEG + (WIDE if w > 16 else [])


def pattern(i):
    """PATTERN[i]: a fixed byte sequence with both values of every bit, from a stated 32-bit LCG (Numerical
    Recipes' constants) taking the top byte. Any sequence would do: the point is that it is NOT uniform, so a write
    to the wrong byte changes a byte whose value the comparison knows."""
    x = (i * 1664525 + 1013904223) & 0xFFFFFFFF
    x = (x * 1664525 + 1013904223) & 0xFFFFFFFF
    return x >> 24


def sdm_rule(off):
    return off >> 3, off & 7                  # Python's >> on a negative int is arithmetic: SAR


def x86isa_rule(off):
    return off >> 3, abs(off) % 8             # floor(off/8) is off >> 3; the bit number is (mod (abs off) 8)


def apply(kind, pre, bit):
    """CF and WRITE-BACK. Returns (CF, byte after)."""
    c = (pre >> bit) & 1
    m = 1 << bit
    post = {"bt": pre, "bts": pre | m, "btr": pre & ~m & 0xFF, "btc": pre ^ m}[kind]
    return c, post


ROWS = []   # (name, fn, reg, idx, pre, f, want_cf, want_byte, x_cf, x_byte, rules_differ)


def build():
    ROWS.clear()
    for form, fn, _bytes, w, kind in OPS:
        for off in offsets(w):
            assert -(1 << (w - 1)) <= off < (1 << (w - 1))
            reg = off & ((1 << w) - 1)
            if w < 64:
                reg |= JUNK & ~((1 << w) - 1) & ((1 << 64) - 1)   # SIGNED-OFFSET: these bits must be ignored
            boff, bit = sdm_rule(off)
            xoff, xbit = x86isa_rule(off)
            assert xoff == boff                    # the two rules address the SAME byte; only the bit can differ
            idx = BASE + boff
            assert 64 <= idx and idx + 8 <= BUF - 64, (form, off)
            # Four pre-values of the addressed byte, each with its flags-in. f = ARITH puts CF=1, ZF=1 in; f = 0
            # puts both 0 in, so CF is seen changing in both directions and ZF is seen held at both values.
            variants = [("v00", 0x00, ARITH), ("vff", 0xFF, 0),
                        ("vonly", 1 << bit, 0), ("vallbut", 0xFF ^ (1 << bit), ARITH)]
            for vn, pre, f in variants:
                c, post = apply(kind, pre, bit)
                xc, xpost = apply(kind, pre, xbit)
                differ = (c, post) != (xc, xpost)
                want_f = (f & ZF) | (CF if c else 0)
                x_f = (f & ZF) | (CF if xc else 0)
                name = "%s_%s%d_%s" % (form, "m" if off < 0 else "p", abs(off), vn)
                ROWS.append((name, fn, reg, idx, pre, f, want_f, post, x_f, xpost, differ))


def summary():
    total = sum(1 for _ in ROWS)
    diff = sum(1 for r in ROWS if r[10])
    print("rows %d  rules-differ %d  (BUF %d, base +%d)" % (total, diff, BUF, BASE))
    for form, _fn, _b, w, _k in OPS:
        rs = [r for r in ROWS if r[0].startswith(form + "_")]
        neg = [r for r in rs if "_m" in r[0][len(form):]]
        print("  %-9s rows %3d  negative-offset rows %3d  rules-differ %3d  (cf %d, byte %d)"
              % (form, len(rs), len(neg), sum(1 for r in rs if r[10]),
                 sum(1 for r in rs if (r[6] & CF) != (r[8] & CF)), sum(1 for r in rs if r[7] != r[9])))
    pos_diff = sum(1 for r in ROWS if r[10] and "_p" in r[0])
    print("rules-differ on a non-negative offset: %d (must be 0)" % pos_diff)
    if "--rows" in sys.argv:
        for r in ROWS:
            print("%-26s idx %+5d pre %02x  sdm cf %d byte %02x  x86isa cf %d byte %02x  %s"
                  % (r[0], r[3] - BASE, r[4], r[6] & 1, r[7], r[8] & 1, r[9], "DIFFER" if r[10] else "same"))


def main():
    P.strict_flags(__file__)
    build()
    if "--summary" in sys.argv:
        summary()
        return
    plant = "--plant" in sys.argv
    plant_mem = "--plant-mem" in sys.argv
    mem_row = next(i for i, r in enumerate(ROWS) if r[0] == "btsw_mr_m1_v00")
    stray_row = next(i for i, r in enumerate(ROWS) if r[0] == "btcw_mr_p0_v00")
    plant_stray = "--plant-stray" in sys.argv
    print("/* GENERATED by hwprobe/mk_bitstr_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    print("#define BUF %d" % BUF)
    print("#define BASE %d" % BASE)
    for _form, fn, _b, _w, _k in OPS:
        print("void %s(struct bio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const unsigned char PATTERN[BUF] = {")
    for i in range(0, BUF, 32):
        print("  " + ",".join("0x%02x" % pattern(j) for j in range(i, i + 32)) + ",")
    print("};")
    print("static const struct brow BROWS[] = {")
    for i, (name, fn, reg, idx, pre, f, wf, wb, xf, xb, differ) in enumerate(ROWS):
        if plant and i == 0:
            wf ^= CF           # the control: one expectation made wrong on purpose
        if plant_mem and i == mem_row:
            wb = xb            # the control: one row expects the x86isa rule's byte
        if plant_stray and i == stray_row:
            idx += 1           # the control: the probe watches the wrong byte; BTC's real write becomes a stray
        print('  {"%s", %s, 0x%016xULL, %d, 0x%02x, 0x%03x, 0x%03x, 0x%02x, 0x%03x, 0x%02x, %d},'
              % (name, fn, reg, idx, pre, f, wf, wb, xf, xb, 1 if differ else 0))
    print("};")
    print("static const struct bop BOPS[] = {")
    for i, (_form, fn, bs, _w, _k) in enumerate(OPS):
        bb = bytearray.fromhex(bs)
        if "--plant-op" in sys.argv and i == 0:
            bb[-1] ^= 0x01     # the control: the declared instruction is not the one in bitstr_ops.S
        print('  {"%s", %s_at, %d, {%s}},' % (fn, fn, len(bb), ", ".join("0x%02x" % x for x in bb)))
    print("};")


if __name__ == "__main__":
    main()
