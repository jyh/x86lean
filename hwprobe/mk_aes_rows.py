#!/usr/bin/env python3
"""hwprobe/mk_aes_rows.py — D342 (V4): the AES-NI, PCLMULQDQ and VEX-shuffle rows the x86-64 referee runs, with
expectations DERIVED HERE.

The nine forms `vale-aesgcm` needs that ACL2 x86isa refuses at every pre-state (`scripts/oracle_availability.py`, D342
prediction 1), all register forms:
  legacy SSE   aesenc xmm,xmm · aesenclast xmm,xmm
  VEX.128      vaesenc · vaesenclast · vpclmulqdq imm · vpshufb · vpalignr imm (xmm,xmm,xmm) · vpslldq · vpsrldq imm (xmm,xmm)
A seventh path, beside the SSE soft-float, integer, bit-string, shuffle, packed-integer and SHA-NI ones, sharing nothing
with them: `aes_ops.S` (one function per form), `aes_probe.c`, and this file.

Every expected value comes from a stated rule in this file (SDM Vol. 2A/2B AESENC, AESENCLAST, PCLMULQDQ, PSHUFB,
PALIGNR, PSLLDQ, PSRLDQ; FIPS-197 §5.1 for the round functions), never from ACL2 x86isa and never from x86lean. Byte i
of a 128-bit value is bits 8i+7 : 8i; the AES state is FIPS-197's column-major s[r][c] = byte r + 4c (byte 0 = SRC1[7:0]).

  AESENC        STATE := SRC1; STATE := ShiftRows(STATE); STATE := SubBytes(STATE); STATE := MixColumns(STATE);
                DEST := STATE ⊕ SRC2 (the round key)
  AESENCLAST    the same without MixColumns
  PCLMULQDQ     A := SRC1's quadword imm8[0] (0 low, 1 high); B := SRC2's quadword imm8[4]; DEST := A •clmul• B
                (bit 127 = 0); imm8's other bits ignored
  VPSHUFB       DEST byte i := 0 if SRC2[8i+7] else SRC1 byte SRC2[8i+3:8i]   (V1b's PSHUFB, D336, data = SRC1)
  VPALIGNR      DEST := ((SRC1 << 128) | SRC2) >> 8·imm8, low 128; 0 at imm8 ≥ 32   (V1b's PALIGNR)
  VPSLLDQ/VPSRLDQ  DEST := SRC shifted left/right by imm8 BYTES, 0 at imm8 > 15
  UPPER         VEX.128: DEST's YMM bits 255:128 := 0. Legacy SSE: bits 255:128 of DEST are PRESERVED.
  NO-FLAGS      "Flags Affected: None"; every other vector register (all 256 bits) unchanged.

THE PROBE'S REGISTERS (`aes_ops.S`): YMM1, YMM2, YMM3 are loaded WHOLE (256 bits each, every upper half seeded
non-zero). A legacy form computes DEST = XMM1 from XMM1 (state) and XMM2 (round key). A VEX three-operand form writes
XMM3 from SRC1 = XMM1 (VEX.vvvv) and SRC2 = XMM2 (ModRM.rm); a VEX two-operand shift writes XMM3 from XMM1. After the
instruction all three YMM registers are read back whole, so the zeroing (VEX) and the preservation (legacy) of the
destination's upper half are both COMPARED, and so is every source's.

⭐ THE KNOWN-ANSWER GROUP, AND WHY IT IS COMPUTED ANOTHER WAY. A misread state layout is a consistent mistake: a rule
written with it and rows derived from it agree with each other. So the KAT rows' expectations come from
`textbook_aes128` — FIPS-197's cipher on a 4×4 state matrix with its own key expansion, its S-box DERIVED from the
multiplicative inverse in GF(2^8) and the affine map (never typed) — and from `textbook_clmul`, a shift-and-xor carry-
less product. `--selftest` holds the textbook AES to FIPS-197 Appendix B (the round-1 state and the ciphertext) and
Appendix C.1, and the textbook CLMUL to the five test vectors of Gueron and Kounavis's Intel CLMUL white paper
(rev. 2.02, "PCLMULQDQ test vectors"). The KAT rows:
  aesenc       the nine middle rounds of Appendix B and of Appendix C.1 (18 rows): SRC1 = the state at the start of
               round r, SRC2 = round key r, want the state at the start of round r + 1
  aesenclast   the final round of each (2 rows): want the ciphertext
  vpclmulqdq   the white paper's five vectors (SRC1 = its xmm1, SRC2 = its xmm2)
Every KAT row must ALSO agree with the RULE (`build` refuses otherwise), so the processor checks the rule's reading and
the textbook checks the rule.

THE ROW POPULATION (per form; flags in: all six clear on even rows, all six set on odd ones):
  aes*         8 edge rows (state/key all-0, all-1, one byte set in each column, the alternating pattern) + 8 random +
               the KAT rows
  vpclmulqdq   imm8 ∈ {00 01 10 11 02 20 ee ff} × 2 operand pairs (edge, random) + 4 random + the 5 KAT rows
  vpshufb      8 controls (identity, reversal, all bit-7, alternating bit-7, bits 6:4 junk, broadcast 0, broadcast 15,
               mixed) × 2 data values
  vpalignr     imm8 ∈ {0 1 4 8 15 16 17 24 31 32 33 128 255} × 2 operand pairs
  vpslldq/vpsrldq  imm8 ∈ {0 1 3 7 8 15 16 17 255} × 2
Random words from `random.Random(342000 + k)` (k the form's index), never re-seeded; every YMM upper half is random.

Usage: mk_aes_rows.py [--plant | --plant-op | --plant-hi | --summary | --reach | --refuse-wrong | --selftest]
  --plant         flips bit 64 (the HIGH quadword) of row 0's expectation: exactly that row must disagree (exit 1)
  --plant-op      declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --plant-hi      one VEX row's expectation keeps the destination's upper half instead of zeroing it: exactly that row
                  must disagree — the upper half is compared, not assumed
  --summary       per-form row counts, not C
  --reach         per form, how many rows a named WRONG rule disagrees on (0 would be a vacuous row set)
  --refuse-wrong  builds the rows under each wrong rule D342 names and shows `build` REFUSE it on a KAT row
  --selftest      the textbooks against the published values, every KAT row against the rule, the refusals, the plants
"""
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "scripts"))
import portable as P  # noqa: E402

ARITH = 0x8d5
M64 = (1 << 64) - 1
M128 = (1 << 128) - 1

# (form, function, mnemonic, VEX?, declared bytes hex, imm8 or None). ModRM: legacy ca = %xmm2,%xmm1 (DEST xmm1);
# VEX c5/c4 with vvvv = xmm1 (1110b) and rm = xmm2, reg = xmm3 (ModRM da); the shifts reg-field /7 /3, rm = xmm1, vvvv
# = xmm3 (1100b). Bytes are clang's assembly of the `aes_ops.S` line (`--selftest` does not re-assemble; the probe
# refuses to run if they differ from what the assembler put at the function's `_at` label).
BASE = [
    ("aesenc", False, "660f38dcca"),
    ("aesenclast", False, "660f38ddca"),
    ("vaesenc", True, "c4e271dcda"),
    ("vaesenclast", True, "c4e271ddda"),
    ("vpshufb", True, "c4e27100da"),
]
CLMUL_IMMS = [0x00, 0x01, 0x10, 0x11, 0x02, 0x20, 0xee, 0xff]
ALIGNR_IMMS = [0, 1, 4, 8, 15, 16, 17, 24, 31, 32, 33, 128, 255]
SHIFT_IMMS = [0, 1, 3, 7, 8, 15, 16, 17, 255]

OPS = []   # (fn, mnemonic, vex, declared bytes hex, imm or None)
for _mn, _vex, _bs in BASE:
    OPS.append(("e_%s" % _mn, _mn, _vex, _bs, None))
for _i in CLMUL_IMMS:
    OPS.append(("e_vpclmulqdq_%02x" % _i, "vpclmulqdq", True, "c4e37144da%02x" % _i, _i))
for _i in ALIGNR_IMMS:
    OPS.append(("e_vpalignr_%d" % _i, "vpalignr", True, "c4e3710fda%02x" % _i, _i))
for _i in SHIFT_IMMS:
    OPS.append(("e_vpslldq_%d" % _i, "vpslldq", True, "c5e173f9%02x" % _i, _i))
    OPS.append(("e_vpsrldq_%d" % _i, "vpsrldq", True, "c5e173d9%02x" % _i, _i))

MNEMONICS = ["aesenc", "aesenclast", "vaesenc", "vaesenclast", "vpclmulqdq", "vpshufb", "vpalignr", "vpslldq",
             "vpsrldq"]
PLANT_HI = "vaesenc_edge0"


# ── the RULE: the SDM's operations over a byte-indexed 128-bit integer ─────────────────────────────────────────────

def byte(v, i):
    return (v >> (8 * i)) & 0xff


def of_bytes(bs):
    return sum((b & 0xff) << (8 * i) for i, b in enumerate(bs))


def gf_mul(a, b):
    """a · b in GF(2^8) mod x^8 + x^4 + x^3 + x + 1 (FIPS-197 §4.2)."""
    r = 0
    for _ in range(8):
        if b & 1:
            r ^= a
        a = ((a << 1) ^ (0x11b if a & 0x80 else 0)) & 0x1ff
        b >>= 1
    return r & 0xff


def _sbox():
    """FIPS-197 §5.1.1: the multiplicative inverse in GF(2^8) (0 ↦ 0), then the affine map — derived, never typed."""
    inv = [0] * 256
    for a in range(1, 256):
        for b in range(1, 256):
            if gf_mul(a, b) == 1:
                inv[a] = b
                break
    out = []
    for a in range(256):
        b = inv[a]
        s = b
        for k in range(1, 5):
            s ^= ((b << k) | (b >> (8 - k))) & 0xff
        out.append(s ^ 0x63)
    return out


SBOX = _sbox()


def shift_rows(v):
    """s'[r][c] = s[r][(c + r) mod 4], byte r + 4c."""
    return of_bytes([byte(v, (i % 4) + 4 * (((i // 4) + (i % 4)) % 4)) for i in range(16)])


def sub_bytes(v):
    return of_bytes([SBOX[byte(v, i)] for i in range(16)])


def mix_columns(v):
    out = []
    for c in range(4):
        a = [byte(v, 4 * c + r) for r in range(4)]
        for r in range(4):
            out.append(gf_mul(2, a[r]) ^ gf_mul(3, a[(r + 1) % 4]) ^ a[(r + 2) % 4] ^ a[(r + 3) % 4])
    return of_bytes(out)


def aes_round(state, key, last):
    s = sub_bytes(shift_rows(state))
    return (s if last else mix_columns(s)) ^ key


def clmul(a, b):
    r = 0
    for i in range(64):
        if b >> i & 1:
            r ^= a << i
    return r


def pclmul(a, b, imm):
    return clmul((a >> 64) if imm & 0x01 else a & M64, (b >> 64) if imm & 0x10 else b & M64)


def pshufb(data, ctl):
    return of_bytes([0 if byte(ctl, i) & 0x80 else byte(data, byte(ctl, i) & 0x0f) for i in range(16)])


def palignr(s1, s2, imm):
    return 0 if imm >= 32 else (((s1 << 128) | s2) >> (8 * imm)) & M128


def pslldq(v, imm):
    return 0 if imm > 15 else (v << (8 * imm)) & M128


def psrldq(v, imm):
    return 0 if imm > 15 else v >> (8 * imm)


def rule(mn, a, b, imm):
    """The SDM rule: SRC1 a, SRC2 b (128-bit ints), imm8 -> the low 128 bits of DEST. The two-operand shifts read a."""
    if mn in ("aesenc", "vaesenc"):
        return aes_round(a, b, False)
    if mn in ("aesenclast", "vaesenclast"):
        return aes_round(a, b, True)
    if mn == "vpclmulqdq":
        return pclmul(a, b, imm)
    if mn == "vpshufb":
        return pshufb(a, b)
    if mn == "vpalignr":
        return palignr(a, b, imm)
    if mn == "vpslldq":
        return pslldq(a, imm)
    if mn == "vpsrldq":
        return psrldq(a, imm)
    raise SystemExit("mk_aes_rows: no rule for %s" % mn)


# THE WRONG RULES D342 NAMES, each a whole substitute for `rule`. `--refuse-wrong` builds under each and `build` must
# refuse on a KAT row. ⚠️ D342's first-named one, ShiftRows and SubBytes SWAPPED, is not wrong at all: SubBytes acts
# per byte and ShiftRows only permutes bytes, so the two COMMUTE and no row can tell them apart. `--reach` prints that
# it agrees on every row (the arithmetic, not a gap), and the MixColumns-sensitive wrong rule refused instead is
# MixColumns applied BEFORE ShiftRows — which every aesenc/vaesenc row can see and no aesenclast row can.
def _swap_sr_sb(state, key, last):
    s = shift_rows(sub_bytes(state))
    return (s if last else mix_columns(s)) ^ key


def _mc_before_sr(state, key, last):
    s = sub_bytes(state)
    s = s if last else mix_columns(s)
    return shift_rows(s) ^ key


def _mc_on_last(state, key, _last):
    return mix_columns(sub_bytes(shift_rows(state))) ^ key


def _wrapped_aes(fn):
    def r(mn, a, b, imm):
        if mn in ("aesenc", "vaesenc"):
            return fn(a, b, False)
        if mn in ("aesenclast", "vaesenclast"):
            return fn(a, b, True)
        return rule(mn, a, b, imm)
    return r


def _sel_low_bits(mn, a, b, imm):
    if mn == "vpclmulqdq":
        return clmul((a >> 64) if imm & 0x01 else a & M64, (b >> 64) if imm & 0x02 else b & M64)
    return rule(mn, a, b, imm)


WRONG = [
    ("MixColumns on the last round", _wrapped_aes(_mc_on_last)),
    ("PCLMULQDQ's selectors read as imm8[1:0]", _sel_low_bits),
    ("MixColumns before ShiftRows (caught only where MixColumns runs)", _wrapped_aes(_mc_before_sr)),
]
COMMUTING = ("ShiftRows and SubBytes swapped (they commute: NOT a wrong rule)", _wrapped_aes(_swap_sr_sb))


# ── THE TEXTBOOKS, sharing nothing with `rule` but `gf_mul` ─────────────────────────────────────────────────────────

def _tb_sbox():
    """The S-box again, by its definition over polynomials: b ↦ b^254 in GF(2^8), then the affine map bit by bit."""
    def pw(a, e):
        r = 1
        while e:
            if e & 1:
                r = gf_mul(r, a)
            a = gf_mul(a, a)
            e >>= 1
        return r
    out = []
    for a in range(256):
        b = pw(a, 254)
        s = 0
        for i in range(8):
            bit = (b >> i ^ b >> ((i + 4) % 8) ^ b >> ((i + 5) % 8) ^ b >> ((i + 6) % 8) ^ b >> ((i + 7) % 8)
                   ^ 0x63 >> i) & 1
            s |= bit << i
        out.append(s)
    return out


TB_SBOX = _tb_sbox()


def tb_key_expansion(key):
    """FIPS-197 §5.2, AES-128: 44 words, returned as eleven 16-byte round keys."""
    w = [list(key[4 * i:4 * i + 4]) for i in range(4)]
    rcon = 1
    for i in range(4, 44):
        t = list(w[i - 1])
        if i % 4 == 0:
            t = t[1:] + t[:1]
            t = [TB_SBOX[x] for x in t]
            t[0] ^= rcon
            rcon = gf_mul(rcon, 2)
        w.append([x ^ y for x, y in zip(w[i - 4], t)])
    return [bytes(sum(w[4 * r:4 * r + 4], [])) for r in range(11)]


def tb_cipher(inp, key):
    """FIPS-197 §5.1 on a 4×4 matrix st[r][c]; returns (round keys, [the state at the START of rounds 1..10], output)."""
    ks = tb_key_expansion(key)
    st = [[inp[r + 4 * c] for c in range(4)] for r in range(4)]

    def ark(st, k):
        return [[st[r][c] ^ k[r + 4 * c] for c in range(4)] for r in range(4)]

    def flat(st):
        return bytes(st[r][c] for c in range(4) for r in range(4))

    st = ark(st, ks[0])
    starts = []
    for rnd in range(1, 11):
        starts.append(flat(st))
        st = [[TB_SBOX[st[r][c]] for c in range(4)] for r in range(4)]
        st = [st[r][r:] + st[r][:r] for r in range(4)]
        if rnd < 10:
            nst = [[0] * 4 for _ in range(4)]
            for c in range(4):
                col = [st[r][c] for r in range(4)]
                nst[0][c] = gf_mul(2, col[0]) ^ gf_mul(3, col[1]) ^ col[2] ^ col[3]
                nst[1][c] = col[0] ^ gf_mul(2, col[1]) ^ gf_mul(3, col[2]) ^ col[3]
                nst[2][c] = col[0] ^ col[1] ^ gf_mul(2, col[2]) ^ gf_mul(3, col[3])
                nst[3][c] = gf_mul(3, col[0]) ^ col[1] ^ col[2] ^ gf_mul(2, col[3])
            st = nst
        st = ark(st, ks[rnd])
    return ks, starts, flat(st)


def textbook_clmul(a, b):
    """The carry-less product as a polynomial product over GF(2): coefficient k is the parity of a_i·b_(k−i)."""
    r = 0
    for k in range(127):
        par = 0
        for i in range(max(0, k - 63), min(63, k) + 1):
            par ^= (a >> i) & (b >> (k - i)) & 1
        r |= par << k
    return r


# The published values the textbooks are held to (typed, because they are the record being checked against).
FIPS197 = [   # (tag, input, key, ciphertext, Appendix B's "start of round 2" state or None)
    ("b", "3243f6a8885a308d313198a2e0370734", "2b7e151628aed2a6abf7158809cf4f3c", "3925841d02dc09fbdc118597196a0b32",
     "a49c7ff2689f352b6b5bea43026a5049"),
    ("c1", "00112233445566778899aabbccddeeff", "000102030405060708090a0b0c0d0e0f", "69c4e0d86a7b0430d8cdb78070b4c55a",
     None),
]
# Gueron and Kounavis, "Intel Carry-Less Multiplication Instruction and its Usage for Computing the GCM Mode", rev.
# 2.02, test vectors 1-5: (xmm1, xmm2, imm8, result), xmm1 the instruction's SRC1/destination and xmm2 its SRC2.
CLMUL_WP = [
    (0x7b5b54657374566563746f725d53475d, 0x48692853686179295b477565726f6e5d, 0x00, 0x1d4d84c85c3440c0929633d5d36f0451),
    (0x7b5b54657374566563746f725d53475d, 0x48692853686179295b477565726f6e5d, 0x10, 0x1bd17c8d556ab5a17fa540ac2a281315),
    (0x7b5b54657374566563746f725d53475d, 0x48692853686179295b477565726f6e5d, 0x01, 0x1a2bf6db3a30862fbabf262df4b7d5c9),
    (0x7b5b54657374566563746f725d53475d, 0x48692853686179295b477565726f6e5d, 0x11, 0x1d1e1f2c592e7c45d66ee03e410fd4ed),
    (0x00000000000000008000000000000000, 0x00000000000000008000000000000000, 0x00, 0x40000000000000000000000000000000),
]


def le(bs):
    return int.from_bytes(bs, "little")


def kat_rows():
    """(name, mnemonic, a, b, imm, want) — expectations from the textbooks only."""
    out = []
    for tag, inp, key, _ct, _r2 in FIPS197:
        ks, starts, ct = tb_cipher(bytes.fromhex(inp), bytes.fromhex(key))
        for rnd in range(1, 10):
            for mn in ("aesenc", "vaesenc"):
                out.append(("kat_%s_r%d" % (tag, rnd), mn, le(starts[rnd - 1]), le(ks[rnd]), None, le(starts[rnd])))
        for mn in ("aesenclast", "vaesenclast"):
            out.append(("kat_%s_r10" % tag, mn, le(starts[9]), le(ks[10]), None, le(ct)))
    for i, (x1, x2, imm, _res) in enumerate(CLMUL_WP):
        lo, hi = x1 & M64, x1 >> 64
        a = textbook_clmul(hi if imm & 1 else lo, (x2 >> 64) if imm & 0x10 else x2 & M64)
        out.append(("kat_wp%d" % (i + 1), "vpclmulqdq", x1, x2, imm, a))
    return out


EDGE_AES = [(0, 0), (M128, 0), (0, M128), (0xff, 0x01 << 120), (0xff << 32, 0x5a << 64), (0xff << 72, 0xa5 << 8),
            (0x80 << 120, 0x63 << 40), (0x55555555555555555555555555555555, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa)]
SHUF_CTL = [of_bytes(range(16)), of_bytes(range(15, -1, -1)), of_bytes([0x80] * 16),
            of_bytes([0x80 if i % 2 else i for i in range(16)]), of_bytes([0x70 | (15 - i) for i in range(16)]),
            0, of_bytes([15] * 16), of_bytes([0x03, 0x8f, 0x1e, 0x0c, 0xf0, 0x07, 0x41, 0x0a, 0x99, 0x02, 0x6d, 0x00,
                                              0x0f, 0xc4, 0x05, 0x38])]

ROWS = []   # (name, fn, mnemonic, vex, y1, y2, y3, imm, f, want256)


def ymm(lo, hi):
    return (lo & M128) | ((hi & M128) << 128)


def build(rl=None):
    """Build every row. `rl` substitutes the rule (the wrong-rule refusals); a KAT row that disagrees REFUSES."""
    rl = rl or rule
    ROWS.clear()
    kats = kat_rows()
    for k, (fn, mn, vex, _bs, imm) in enumerate(OPS):
        rng = random.Random(342000 + k)
        cases = []
        if mn in ("aesenc", "aesenclast", "vaesenc", "vaesenclast"):
            cases += [("edge%d" % i, a, b, None) for i, (a, b) in enumerate(EDGE_AES)]
            cases += [("rand%d" % i, rng.getrandbits(128), rng.getrandbits(128), None) for i in range(8)]
        elif mn == "vpclmulqdq":
            cases += [("edge", (M64 << 64) | 0x8000000000000001, 0x00000000000000ff8000000000000003, None),
                      ("rand", rng.getrandbits(128), rng.getrandbits(128), None)]
            if imm == 0x00:
                cases += [("rand%d" % i, rng.getrandbits(128), rng.getrandbits(128), None) for i in range(1, 5)]
        elif mn == "vpshufb":
            for d, data in enumerate((of_bytes(range(0x10, 0x20)), rng.getrandbits(128))):
                cases += [("d%d_c%d" % (d, c), data, ctl, None) for c, ctl in enumerate(SHUF_CTL)]
        else:   # vpalignr, vpslldq, vpsrldq at one imm8
            cases += [("p0", of_bytes(range(0x10, 0x20)), of_bytes(range(0xa0, 0xb0)), None),
                      ("p1", rng.getrandbits(128), rng.getrandbits(128), None)]
        for nm, kmn, a, b, kimm, want in kats:
            if kmn == mn and (kimm is None or kimm == imm):
                got = rl(mn, a, b, imm)
                if got != want:
                    raise SystemExit("mk_aes_rows: ⛔ KAT %s %s: the RULE gives %032x, the textbook %032x — the rule's "
                                     "reading of the SDM is wrong, or the textbook is" % (mn, nm, got, want))
                cases.append((nm, a, b, want))
        for i, (nm, a, b, want) in enumerate(cases):
            hi1, hi2, y3 = rng.getrandbits(128) | 1, rng.getrandbits(128) | 1, rng.getrandbits(256) | (1 << 128)
            low = rl(mn, a, b, imm) if want is None else want
            if vex:
                w = ymm(low, 0)
            else:
                w = ymm(low, hi1)       # legacy SSE: DEST = XMM1, its upper half PRESERVED
            f = ARITH if i % 2 else 0
            ROWS.append(("%s_%s" % (fn[2:], nm), fn, mn, vex, ymm(a, hi1), ymm(b, hi2), y3, imm, f, w))


def q4(v):
    return ", ".join("0x%016xULL" % ((v >> (64 * i)) & M64) for i in range(4))


def wrong_reach(rl):
    """{mnemonic: (disagreeing rows, rows)} for a substitute rule, over the built rows (rule-derived expectations)."""
    out = {}
    for name, _fn, mn, vex, y1, y2, _y3, imm, _f, w in ROWS:
        n, t = out.get(mn, (0, 0))
        out[mn] = (n + (rl(mn, y1 & M128, y2 & M128, imm) != w & M128), t + 1)
    return out


def refusals(quiet=False):
    """Build under each wrong rule; each must be REFUSED by a KAT row. Returns the number that were NOT."""
    missed = 0
    for label, rl in WRONG:
        try:
            build(rl)
        except SystemExit as e:
            if not quiet:
                print("  ✔ refused — %s:\n      %s" % (label, str(e)))
            continue
        missed += 1
        if not quiet:
            print("  ✖ NOT refused — %s" % label)
    build()
    return missed


def selftest():
    bad = 0

    def say(ok, msg):
        nonlocal bad
        print(("  ✔ " if ok else "  ✖ ") + msg)
        bad += not ok

    say(SBOX == TB_SBOX and SBOX[0] == 0x63 and SBOX[0x53] == 0xed, "the rule's S-box equals the textbook's "
        "(two derivations), with FIPS-197's S(00) = 63 and S(53) = ed")
    for tag, inp, key, ct, r2 in FIPS197:
        _ks, starts, got = tb_cipher(bytes.fromhex(inp), bytes.fromhex(key))
        say(got.hex() == ct, "textbook AES-128 (FIPS-197 Appendix %s) = %s" % (tag.upper(), got.hex()))
        if r2:
            say(starts[1].hex() == r2, "  and its start-of-round-2 state = %s (Appendix B)" % starts[1].hex())
    for x1, x2, imm, res in CLMUL_WP:
        lo, hi = x1 & M64, x1 >> 64
        got = textbook_clmul(hi if imm & 1 else lo, (x2 >> 64) if imm & 0x10 else x2 & M64)
        say(got == res, "textbook CLMUL, white paper imm %02x = %032x" % (imm, got))
    build()
    kat = [r for r in ROWS if "_kat_" in r[0]]
    say(len(kat) == 18 * 2 + 2 * 2 + 5, "%d KAT rows, every one equal under the rule and the textbook" % len(kat))
    # the operand order is not symmetric: swapping SRC1 and SRC2 must change every AES and VPSHUFB KAT expectation
    say(all(rule(mn, y2 & M128, y1 & M128, imm) != w & M128 for _n, _fn, mn, _v, y1, y2, _y3, imm, _f, w in kat
            if mn != "vpclmulqdq"), "every AES KAT expectation changes when SRC1 and SRC2 are swapped")
    say(refusals(quiet=True) == 0, "each of the %d wrong rules is REFUSED by a KAT row" % len(WRONG))
    swap = wrong_reach(COMMUTING[1])
    say(all(n == 0 for n, _t in swap.values()), "ShiftRows/SubBytes swapped agrees on EVERY row (they commute)")
    mcsr = wrong_reach(_wrapped_aes(_mc_before_sr))
    say(mcsr["aesenclast"][0] == 0 and mcsr["vaesenclast"][0] == 0 and mcsr["aesenc"][0] > 0,
        "MixColumns-before-ShiftRows is invisible to every aesenclast row and seen by aesenc rows")
    pk = [r for r in ROWS if r[0] == PLANT_HI]
    say(len(pk) == 1 and pk[0][3] and (pk[0][6] >> 128) != 0, "--plant-hi's row exists once, is VEX, and its "
        "destination's upper half is seeded non-zero")
    say(all((r[4] >> 128) and (r[5] >> 128) and (r[6] >> 128) for r in ROWS), "every row seeds all three YMM upper "
        "halves non-zero")
    say({r[2] for r in ROWS} == set(MNEMONICS), "the rows cover exactly the nine mnemonics")
    print("✅ mk_aes_rows selftest" if not bad else "⛔ mk_aes_rows selftest FAILED")
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
        for mn in MNEMONICS:
            print("%-12s %d" % (mn, sum(1 for r in ROWS if r[2] == mn)))
        print("rows %d functions %d" % (len(ROWS), len(OPS)))
        return 0
    if "--reach" in sys.argv:
        bad = 0
        for label, rl in WRONG + [COMMUTING]:
            print(label)
            for mn, (n, t) in sorted(wrong_reach(rl).items()):
                if n:
                    print("  %-12s disagrees on %3d of %3d rows" % (mn, n, t))
            if rl is not COMMUTING[1]:
                bad += sum(n for n, _t in wrong_reach(rl).values()) == 0
        return 1 if bad else 0
    plant, plant_hi = "--plant" in sys.argv, "--plant-hi" in sys.argv
    print("/* GENERATED by hwprobe/mk_aes_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    for fn, _mn, _v, _b, _i in OPS:
        print("void %s(struct eio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const struct erow EROWS[] = {")
    for i, (name, fn, _mn, vex, y1, y2, y3, _imm, f, w) in enumerate(ROWS):
        if plant and i == 0:
            w ^= 1 << 64          # the control: one expectation made wrong on purpose, in the HIGH quadword
        if plant_hi and name == PLANT_HI:
            w |= y3 >> 128 << 128  # the control: the VEX destination's upper half NOT zeroed
        print('  {"%s", %s, %d, {%s}, {%s}, {%s}, 0x%03x, {%s}},' % (name, fn, 3 if vex else 1, q4(y1), q4(y2),
                                                                     q4(y3), f, q4(w)))
    print("};")
    print("static const struct eop EOPS[] = {")
    for i, (fn, _mn, _v, bs, _imm) in enumerate(OPS):
        bb = bytearray.fromhex(bs)
        if "--plant-op" in sys.argv and i == 0:
            bb[-1] ^= 0x01         # the control: the declared instruction is not the one in aes_ops.S
        print('  {"%s", %s_at, %d, {%s}},' % (fn, fn, len(bb), ", ".join("0x%02x" % x for x in bb)))
    print("};")
    return 0


if __name__ == "__main__":
    sys.exit(main())
