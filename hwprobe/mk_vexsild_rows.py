#!/usr/bin/env python3
"""hwprobe/mk_vexsild_rows.py — D354 (V9b): the VEX.128 and VEX.256 MEMORY forms of the six packed moves, loads and stores,
the rows the x86-64 referee runs, with expectations DERIVED HERE — and the first probe path with FAULT ROWS.

The forms: vmovdqa vmovdqu vmovaps vmovups vmovapd vmovupd, each at VEX.128 and VEX.256, load `(%rbx) -> YMM3` and store
`YMM2 -> (%rbx)`. An eleventh probe path, sharing nothing with the others: `vexsild_ops.S`, `vexsild_probe.c`, this file.

Why silicon: x86isa EXECUTES every one of these encodings at a misaligned address (D354 P1), including the legacy
`movdqa 0x1(%rbx)` the SDM calls #GP (D91), so the aligned kinds' fault can never be seen by the differential. A processor
is the only second source the rule can have.

Every expected value comes from a stated rule (SDM Vol. 2B, the six MOV entries' VEX rows; Vol. 1 §14.1.2), never from ACL2
x86isa and never from x86lean.

THE RULES (`rule`). M = the bytes at mem[off:], n = L/8 (16 or 32).
  load, VEX.128   YMM3[127:0] := M[127:0]; YMM3[255:128] := 0
  load, VEX.256   YMM3[255:0] := M[255:0]
  store           mem[off:off+n] := YMM2[8n-1:0]; every other byte of the buffer unchanged; no register written
  ALIGN           an ALIGNED kind (dqa, aps, apd) at an address that is not a multiple of n raises #GP(0) and writes nothing;
                  an UNALIGNED kind (dqu, ups, upd) never faults on alignment. `mem` is 32-byte aligned, so the address's
                  alignment is `off`'s.
  NO-OTHERS       flags, MXCSR, RAX, YMM1, YMM2 (and YMM3 on a store) unchanged
The rule slices one big integer; the TEXTBOOK (`textbook`) slices a byte list and decides alignment from the address's low
bits by a different expression, so a misread offset, length or alignment is refused by `build`.

Usage: mk_vexsild_rows.py [--plant | --plant-op | --plant-nf | --plant-a0 | --plant-f | --summary | --reach |
                           --refuse-wrong | --selftest]
  --plant         flips bit 128 of one VEX.256 load row's expectation: exactly that row must disagree (exit 1)
  --plant-op      declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --plant-nf      one UNALIGNED kind's misaligned row is expected to FAULT: exactly that row must disagree (it runs)
  --plant-a0      one ALIGNED kind's offset-0 row is expected to FAULT: exactly that row must disagree (it runs)
  --plant-f       one FAULT row is expected to RUN: exactly that row must disagree (it faults)
  --summary       per-function row counts, not C
  --reach         per wrong rule and mutant, how many rows it disagrees on
  --refuse-wrong  builds the rows under each wrong rule D354 names and shows `build` REFUSE it on its named row
  --selftest      hand cases, a sweep, every row's two derivations, the refusals, the mutants' exact reach, the plants
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
M512 = (1 << 512) - 1

# clang's bytes for each `vexsild_ops.S` line (`clang -target x86_64-unknown-linux-gnu -c`, read with `objdump -d`).
ENC = {
    "x_vmovdqa128_ld": "c5f96f1b",
    "x_vmovdqa128_st": "c5f97f13",
    "x_vmovdqa256_ld": "c5fd6f1b",
    "x_vmovdqa256_st": "c5fd7f13",
    "x_vmovdqu128_ld": "c5fa6f1b",
    "x_vmovdqu128_st": "c5fa7f13",
    "x_vmovdqu256_ld": "c5fe6f1b",
    "x_vmovdqu256_st": "c5fe7f13",
    "x_vmovaps128_ld": "c5f8281b",
    "x_vmovaps128_st": "c5f82913",
    "x_vmovaps256_ld": "c5fc281b",
    "x_vmovaps256_st": "c5fc2913",
    "x_vmovups128_ld": "c5f8101b",
    "x_vmovups128_st": "c5f81113",
    "x_vmovups256_ld": "c5fc101b",
    "x_vmovups256_st": "c5fc1113",
    "x_vmovapd128_ld": "c5f9281b",
    "x_vmovapd128_st": "c5f92913",
    "x_vmovapd256_ld": "c5fd281b",
    "x_vmovapd256_st": "c5fd2913",
    "x_vmovupd128_ld": "c5f9101b",
    "x_vmovupd128_st": "c5f91113",
    "x_vmovupd256_ld": "c5fd101b",
    "x_vmovupd256_st": "c5fd1113",
}
KINDS = ["dqa", "dqu", "aps", "ups", "apd", "upd"]
ALIGNED = {"dqa", "aps", "apd"}

OPS = []   # (fn, kind, L, direction, declared bytes hex)
for _k in KINDS:
    for _L in (128, 256):
        for _d in ("ld", "st"):
            _fn = "x_vmov%s%d_%s" % (_k, _L, _d)
            OPS.append((_fn, _k, _L, _d, ENC[_fn]))

PLANT_ROW = "vmovdqu256_ld_a0_r0"      # --plant: bit 128 of its expectation
PLANT_NF = "vmovups128_ld_u1_r0"       # --plant-nf: an unaligned kind, misaligned, expected (wrongly) to fault
PLANT_A0 = "vmovaps256_st_a0_r0"       # --plant-a0: an aligned kind at offset 0, expected (wrongly) to fault
PLANT_F = "vmovapd256_ld_f16"          # --plant-f: a fault row expected (wrongly) to run


# ── THE RULE ─────────────────────────────────────────────────────────────────────────────────────────────────────

def faults(kind, L, off):
    return kind in ALIGNED and off % (L // 8) != 0


def rule(kind, L, d, y2, y3, mem, off):
    """-> (faulted, YMM3, mem)."""
    n = L // 8
    if faults(kind, L, off):
        return True, y3, mem
    if d == "ld":
        return False, (mem >> (8 * off)) & ((1 << (8 * n)) - 1), mem
    mask = ((1 << (8 * n)) - 1) << (8 * off)
    return False, y3, (mem & ~mask & M512) | ((y2 & ((1 << (8 * n)) - 1)) << (8 * off))


# ── THE WRONG RULES D354 NAMES ───────────────────────────────────────────────────────────────────────────────────

def w_keep_upper(kind, L, d, y2, y3, mem, off):
    """(a) a VEX.128 load that PRESERVES YMM3[255:128] (the legacy rule)."""
    f, w3, m = rule(kind, L, d, y2, y3, mem, off)
    return (f, w3 | (y3 >> 128 << 128), m) if (L == 128 and d == "ld" and not f) else (f, w3, m)


def w_hi_from_low(kind, L, d, y2, y3, mem, off):
    """(b) a VEX.256 load whose high lane reads bytes 15:0 again."""
    f, w3, m = rule(kind, L, d, y2, y3, mem, off)
    return (f, (w3 & M128) | ((w3 & M128) << 128), m) if (L == 256 and d == "ld" and not f) else (f, w3, m)


def w_align16(kind, L, d, y2, y3, mem, off):
    """(c) the VEX.256 alignment taken as 16 instead of 32."""
    if kind in ALIGNED and L == 256 and off % 16 == 0:
        return rule("dqu", L, d, y2, y3, mem, off)     # the same transfer with no fault
    return rule(kind, L, d, y2, y3, mem, off)


def w_store16(kind, L, d, y2, y3, mem, off):
    """(d) a VEX.256 store that writes only 16 bytes."""
    if L == 256 and d == "st" and not faults(kind, L, off):
        return rule(kind, 128, d, y2, y3, mem, off)
    return rule(kind, L, d, y2, y3, mem, off)


WRONG = [   # (letter, label, rule, the row `build` must name on refusing it)
    ("a", "a VEX.128 load preserving YMM3's upper half", w_keep_upper, "vmovdqa128_ld_a0_r0"),
    ("b", "a VEX.256 load's high lane read from bytes 15:0", w_hi_from_low, "vmovdqa256_ld_a0_r0"),
    ("c", "the VEX.256 alignment taken as 16", w_align16, "vmovdqa256_ld_f16"),
    ("d", "a VEX.256 store writing 16 bytes", w_store16, "vmovdqa256_st_a0_r0"),
]


def m_never_fault(kind, L, d, y2, y3, mem, off):
    """(reach only) the alignment check deleted."""
    return rule("dqu", L, d, y2, y3, mem, off)


def m_always_fault(kind, L, d, y2, y3, mem, off):
    """(reach only) every aligned-kind access faults."""
    if kind in ALIGNED:
        return True, y3, mem
    return rule(kind, L, d, y2, y3, mem, off)


MUTANTS = [("the alignment check deleted", m_never_fault), ("every aligned-kind access faults", m_always_fault)]


# ── THE TEXTBOOK: byte lists, and alignment from the address's low bits ──────────────────────────────────────────

def textbook(kind, L, d, y2, y3, mem, off):
    n = L // 8
    if kind in ("dqa", "aps", "apd") and (off & (n - 1)):
        return True, y3, mem
    buf = list(mem.to_bytes(64, "little"))
    if d == "ld":
        return False, int.from_bytes(bytes(buf[off:off + n]), "little"), mem
    src = list(y2.to_bytes(32, "little"))[:n]
    buf[off:off + n] = src
    return False, y3, int.from_bytes(bytes(buf), "little")


# ── the rows ────────────────────────────────────────────────────────────────────────────────────────────────────

ROWS = []   # (name, fn, kind, L, d, y1, y2, y3, f, mx, rax, mem, off, fault, w3, wmem)


class Refused(SystemExit):
    def __init__(self, row, msg):
        super().__init__(msg)
        self.row = row


def placements(kind, L):
    """(tag, off) for one function: two value rows at 0; the unaligned kinds at odd offsets (and 16 at VEX.256); the
    aligned kinds at 16 at VEX.128 (it RUNS) and, as FAULT rows, at 1 and 8 (VEX.128) or 1, 8 and 16 (VEX.256)."""
    out = [("a0_r0", 0), ("a0_r1", 0)]
    if kind in ALIGNED:
        if L == 128:
            out += [("a16", 16), ("f1", 1), ("f8", 8)]
        else:
            out += [("f1", 1), ("f8", 8), ("f16", 16)]
    else:
        out += [("u1_r0", 1), ("u13", 13)] + ([("u16", 16), ("u29", 29)] if L == 256 else [("u47", 47)])
    return out


def build(rl=None):
    rl = rl or rule
    ROWS.clear()
    for k, (fn, kind, L, d, _bs) in enumerate(OPS):
        rng = random.Random(354000 + k)
        for tag, off in placements(kind, L):
            y1 = rng.getrandbits(256) | 1 | (1 << 255)
            y2 = rng.getrandbits(256) | 1 | (1 << 128) | (1 << 255)
            y3 = rng.getrandbits(256) | (1 << 128) | (1 << 200) | 1
            rax = rng.getrandbits(64) | (1 << 63)
            mem = rng.getrandbits(512)
            mx = 0x1f80 | ((len(ROWS) % 4) << 13)
            f = ARITH if len(ROWS) % 2 else 0
            name = "%s_%s" % (fn[2:], tag)
            got = rl(kind, L, d, y2, y3, mem, off)
            want = textbook(kind, L, d, y2, y3, mem, off)
            if got != want:
                raise Refused(name, "mk_vexsild_rows: ⛔ row %s: the RULE gives %r, the TEXTBOOK %r" % (
                    name, (got[0], hex(got[1])), (want[0], hex(want[1]))))
            ROWS.append((name, fn, kind, L, d, y1, y2, y3, f, mx, rax, mem, off, got[0], got[1], got[2]))


def q(v, n):
    return ", ".join("0x%016xULL" % ((v >> (64 * i)) & M64) for i in range(n))


def disagreements(rl):
    return {r[0] for r in ROWS if rl(r[2], r[3], r[4], r[6], r[7], r[11], r[12]) != (r[13], r[14], r[15])}


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

    mem = int.from_bytes(bytes(range(64)), "little")
    say(rule("dqu", 256, "ld", 0, 0, mem, 13) == textbook("dqu", 256, "ld", 0, 0, mem, 13)
        == (False, int.from_bytes(bytes(range(13, 45)), "little"), mem),
        "hand: vmovdqu ymm from offset 13 = bytes 13..44, both references")
    say(rule("dqa", 256, "ld", 0, 7, mem, 16) == textbook("dqa", 256, "ld", 0, 7, mem, 16) == (True, 7, mem),
        "hand: vmovdqa ymm at offset 16 (16- but not 32-aligned) FAULTS and writes nothing, both references")
    say(rule("dqa", 128, "ld", 0, 0, mem, 16)[0] is False,
        "hand: vmovdqa xmm at offset 16 RUNS — the 32 is VEX.256's alone")
    y2 = int.from_bytes(bytes([0xa0 + i for i in range(32)]), "little")
    want = bytes(range(1)) + bytes([0xa0 + i for i in range(16)]) + bytes(range(17, 64))
    say(rule("upd", 128, "st", y2, 5, mem, 1) == textbook("upd", 128, "st", y2, 5, mem, 1)
        == (False, 5, int.from_bytes(want, "little")),
        "hand: vmovupd xmm store at offset 1 writes exactly bytes 1..16, both references")
    rng = random.Random(354999)
    nd = 0
    for i in range(3000):
        kind, L, d = KINDS[i % 6], (128, 256)[(i // 6) % 2], ("ld", "st")[(i // 12) % 2]
        off = rng.randrange(0, 64 - L // 8 + 1)
        y2, y3, m = rng.getrandbits(256), rng.getrandbits(256), rng.getrandbits(512)
        nd += rule(kind, L, d, y2, y3, m, off) != textbook(kind, L, d, y2, y3, m, off)
    say(nd == 0, "the rule and the textbook agree on 3,000 swept (kind, length, direction, operands, buffer, offset) cases")
    build()
    nf = sum(1 for r in ROWS if r[13])
    say(len(ROWS) > 0, "%d rows built (%d FAULT rows), every one equal under the rule and the textbook" % (len(ROWS), nf))
    say(refusals(quiet=True) == 0, "each of the %d wrong rules (a)-(d) is REFUSED on its named row" % len(WRONG))
    reach = {m_never_fault: {r[0] for r in ROWS if r[13]},
             m_always_fault: {r[0] for r in ROWS if r[2] in ALIGNED and not r[13]}}
    for label, rl in MUTANTS:
        hit = disagreements(rl)
        say(hit == reach[rl] and hit, "mutant '%s' disagrees on exactly the %d rows it reaches" % (label, len(hit)))
    say(all(r[12] + r[3] // 8 <= 64 for r in ROWS), "every memory operand lies inside the 64-byte buffer")
    say(all(r[13] == (r[2] in ALIGNED and r[12] % (r[3] // 8) != 0) for r in ROWS),
        "a row is a FAULT row exactly when an aligned kind sits off its width's alignment")
    say(any(r[13] and r[3] == 256 and r[12] == 16 for r in ROWS) and
        any(not r[13] and r[2] in ALIGNED and r[3] == 128 and r[12] == 16 for r in ROWS),
        "offset 16 is a FAULT row at VEX.256 and a RUNNING row at VEX.128 for the aligned kinds")
    say(any(not r[13] and r[2] not in ALIGNED and r[3] == 256 and r[12] == 16 for r in ROWS),
        "offset 16 RUNS at VEX.256 for the unaligned kinds")
    say(all(r[14] >> 128 == 0 for r in ROWS if r[3] == 128 and r[4] == "ld" and not r[13]),
        "every running VEX.128 load expects YMM3[255:128] = 0")
    for nm, want_fault in ((PLANT_ROW, False), (PLANT_NF, False), (PLANT_A0, False), (PLANT_F, True)):
        pr = [r for r in ROWS if r[0] == nm]
        say(len(pr) == 1 and pr[0][13] == want_fault, "plant row %s exists once, fault=%s" % (nm, want_fault))
    say({(r[2], r[3], r[4]) for r in ROWS} == {(o[1], o[2], o[3]) for o in OPS}, "the rows cover all %d functions" % len(OPS))
    print("✅ mk_vexsild_rows selftest" if not bad else "⛔ mk_vexsild_rows selftest FAILED")
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
        for fn, *_ in OPS:
            print("%-24s %3d (fault rows %d)" % (fn, sum(1 for r in ROWS if r[1] == fn),
                                                 sum(1 for r in ROWS if r[1] == fn and r[13])))
        print("rows %d fault-rows %d functions %d" % (len(ROWS), sum(1 for r in ROWS if r[13]), len(OPS)))
        return 0
    if "--reach" in sys.argv:
        for label, rl in [(w[1], w[2]) for w in WRONG] + MUTANTS:
            print("%-56s disagrees on %3d rows" % (label, len(disagreements(rl))))
        return 0
    plant = "--plant" in sys.argv
    print("/* GENERATED by hwprobe/mk_vexsild_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    for fn, *_ in OPS:
        print("void %s(struct xio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const struct xrow XROWS[] = {")
    for name, fn, kind, L, d, y1, y2, y3, f, mx, rax, mem, off, fault, w3, wmem in ROWS:
        if plant and name == PLANT_ROW:
            w3 ^= 1 << 128
        if ("--plant-nf" in sys.argv and name == PLANT_NF) or ("--plant-a0" in sys.argv and name == PLANT_A0):
            fault = True
        if "--plant-f" in sys.argv and name == PLANT_F:
            fault = False
        print('  {"%s", %s, {%s}, {%s}, {%s}, 0x%03x, 0x%04x, 0x%016xULL, {%s}, %d, %d, {%s}, {%s}},' % (
            name, fn, q(y1, 4), q(y2, 4), q(y3, 4), f, mx, rax, q(mem, 8), off, 1 if fault else 0, q(w3, 4), q(wmem, 8)))
    print("};")
    print("static const struct xop XOPS[] = {")
    for i, (fn, _k, _L, _d, bs) in enumerate(OPS):
        bb = bytearray.fromhex(bs)
        if "--plant-op" in sys.argv and i == 0:
            bb[-1] ^= 0x01
        print('  {"%s", %s_at, %d, {%s}},' % (fn, fn, len(bb), ", ".join("0x%02x" % x for x in bb)))
    print("};")
    return 0


if __name__ == "__main__":
    sys.exit(main())
