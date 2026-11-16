#!/usr/bin/env python3
"""hwprobe/mk_sha_rows.py — D338 (V2): the SHA-NI rows the x86-64 referee runs (SHA256MSG1, SHA256MSG2, SHA256RNDS2,
legacy SSE, each at xmm,xmm and m128,xmm), with expectations DERIVED HERE.

A sixth path, beside the SSE soft-float (`mk_rows.py`), integer (`mk_int_rows.py`), bit-string (`mk_bitstr_rows.py`),
shuffle (`mk_shuf_rows.py`) and packed-integer (`mk_simda_rows.py`) ones, sharing nothing with any of them:
`sha_ops.S` (one function per form: DEST %xmm1, SRC2 %xmm2 or the 16-byte-aligned m128 at [RBX], the implicit %xmm0),
`sha_probe.c`, and this file.

Every expected value comes from a stated rule in this file (SDM Vol. 2B SHA256MSG1 / SHA256MSG2 / SHA256RNDS2; FIPS
180-4 §4.1.2 for σ and Σ), never from ACL2 x86isa — which refuses all three mnemonics at every pre-state
(`scripts/oracle_availability.py`, D338 prediction 1) — and never from x86lean. Dword i of a 128-bit value is bits
32i+31 : 32i. All arithmetic is mod 2^32.

  σ0(W) = ROR(W,7) ⊕ ROR(W,18) ⊕ SHR(W,3)      σ1(W) = ROR(W,17) ⊕ ROR(W,19) ⊕ SHR(W,10)
  Σ0(A) = ROR(A,2) ⊕ ROR(A,13) ⊕ ROR(A,22)     Σ1(E) = ROR(E,6) ⊕ ROR(E,11) ⊕ ROR(E,25)
  Ch(E,F,G) = (E ∧ F) ⊕ (¬E ∧ G)               Maj(A,B,C) = (A ∧ B) ⊕ (A ∧ C) ⊕ (B ∧ C)
  MSG1-RULE   W4 := SRC2.d0; W3..W0 := SRC1.d3..d0; DEST.d3 := W3 + σ0(W4), DEST.d2 := W2 + σ0(W3),
              DEST.d1 := W1 + σ0(W2), DEST.d0 := W0 + σ0(W1). Only SRC2's LOW dword is read.
  MSG2-RULE   W14 := SRC2.d2; W15 := SRC2.d3; W16 := SRC1.d0 + σ1(W14); W17 := SRC1.d1 + σ1(W15);
              W18 := SRC1.d2 + σ1(W16); W19 := SRC1.d3 + σ1(W17); DEST := W19:W18:W17:W16. SRC2's low two dwords are
              not read, and W18/W19 depend on W16/W17 (the serial chain the SDM's Operation states).
  RNDS2-RULE  A := SRC2.d3, B := SRC2.d2, C := SRC1.d3, D := SRC1.d2, E := SRC2.d1, F := SRC2.d0, G := SRC1.d1,
              H := SRC1.d0; WK0 := XMM0.d0, WK1 := XMM0.d1 (XMM0 is an IMPLICIT operand; its high quadword is not read);
              two rounds, i = 0, 1: T1 := H + Σ1(E) + Ch(E,F,G) + WKi; T2 := Σ0(A) + Maj(A,B,C);
              (A..H) := (T1+T2, A, B, C, D+T1, E, F, G). DEST := A2 : B2 : E2 : F2 (A2 in d3, F2 in d0).
  NO-FLAGS    "Flags Affected: None": the six arithmetic flags leave the instruction as they entered.
  SRC-KEPT    SRC2 (the register and the m128) and XMM0 are not written.

⭐ THE KNOWN-ANSWER GROUP, AND WHY IT IS COMPUTED ANOTHER WAY. A misread operand order (SRC1/SRC2 swapped, dwords read
high-to-low, A and B exchanged) is a consistent mistake: a rule written with it and rows derived from that rule agree
with each other. So the KAT rows' expectations come from `textbook_sha256` — a straightforward FIPS 180-4 SHA-256 (a
message schedule W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16] and 64 rounds over a..h from H0, its K and H0
DERIVED from the cube and square roots of the first primes, never typed) — whose digests of FIPS 180-4's "abc" and
448-bit examples `--selftest` checks against the published values. From each message's FIRST block:
  MSG1 KAT    SRC1 = W0..W3, SRC2 = W4..W7; want dword i = W[16+i] − σ1(W[14+i]) − W[9+i] (the schedule's own words)
  MSG2 KAT    SRC1 dword i = W[i] + σ0(W[i+1]) + W[i+9], SRC2 = W12..W15; want W16..W19 (the schedule's words)
  RNDS2 KAT   rounds 0–1 from H0, then rounds 2–3 from the textbook's state after round 1, each packed in the
              instruction's ABEF / CDGH layout, XMM0 = K[t]+W[t] : K[t+1]+W[t+1] in its LOW quadword and seeded garbage
              in its high one; want the textbook's (a,b,e,f) after the second round.
Every KAT row must ALSO agree with the RULE above (`build` refuses otherwise), so the processor checks the rule's reading
and the textbook checks the rule.

THE ROW POPULATION, per form (the same operands at both shapes, `xx` and `xm`):
  EDGE    16 rows: the dwords of SRC1, SRC2 and XMM0's low quadword drawn from a 16-value edge set — 0, FFFFFFFF,
          7FFFFFFF, AAAAAAAA and single bits on each side of every rotate/shift boundary of σ0, σ1, Σ0 and Σ1 — so every
          edge value sits in every dword position once; XMM0's HIGH quadword (unread by every form) is seeded garbage.
  RANDOM  6 rows, every bit from `random.Random(338000 + k)` (k the mnemonic's index in MNEMONICS), never re-seeded.
  KAT     the known-answer rows above (MSG1 2, MSG2 2, RNDS2 4 per shape).
Flags in: all six clear on even-numbered rows of a form, all six set on odd-numbered ones.

Usage: mk_sha_rows.py [--plant | --plant-op | --plant-wk | --summary | --reach | --selftest]   writes C rows on stdout.
  --plant     flips bit 64 (the HIGH quadword) of ONE expectation: exactly that row must disagree (exit 1)
  --plant-op  declares ONE instruction byte wrong: the probe must refuse to run (exit 2)
  --plant-wk  computes ONE SHA256RNDS2 row's expectation (PLANT_WK) with WK taken from XMM0's HIGH quadword: exactly that
              row must disagree — the implicit operand's half is compared, not assumed
  --summary   prints the per-form row counts, not C
  --reach     prints, per mnemonic, how many of its rows a named WRONG rule disagrees on (0 would be a vacuous row set)
  --selftest  the textbook SHA-256 against FIPS 180-4's two digests, every KAT row against the rule, and the plants
"""
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "scripts"))
import portable as P  # noqa: E402

ARITH = 0x8d5
M32 = (1 << 32) - 1
M128 = (1 << 128) - 1

# (mnemonic, declared opcode bytes) — NP 0F 38 CC/CD/CB; ModRM ca = %xmm2,%xmm1; 0b = (%rbx),%xmm1.
MNEMONICS = [
    ("sha256msg1", "0f38cc"),
    ("sha256msg2", "0f38cd"),
    ("sha256rnds2", "0f38cb"),
]

OPS = []   # (form, function, declared bytes hex, mnemonic, shape)
for _mn, _op in MNEMONICS:
    OPS.append((_mn + "_xx", "h_" + _mn + "_xx", _op + "ca", _mn, "xx"))
    OPS.append((_mn + "_xm", "h_" + _mn + "_xm", _op + "0b", _mn, "xm"))

# Single bits on each side of the boundaries: σ0 (SHR 3 · ROR 7 · ROR 18), σ1 (SHR 10 · ROR 17 · ROR 19),
# Σ0 (2 · 13 · 22), Σ1 (6 · 11 · 25) — bits 2/3, 6/7, 9/10, 17/18/19, 25 and the two ends — plus the all-0, all-1,
# all-but-sign and alternating words.
EDGES = [0x00000000, 0xFFFFFFFF, 0x7FFFFFFF, 0xAAAAAAAA,
         1 << 0, 1 << 2, 1 << 3, 1 << 6, 1 << 7, 1 << 9, 1 << 10, 1 << 17, 1 << 18, 1 << 19, 1 << 25, 1 << 31]
N_RANDOM = 6
PLANT_WK = "sha256rnds2_xx_kat_abc_r01"


def ror(x, n):
    return ((x >> n) | (x << (32 - n))) & M32


def s0(w):
    return ror(w, 7) ^ ror(w, 18) ^ (w >> 3)


def s1(w):
    return ror(w, 17) ^ ror(w, 19) ^ (w >> 10)


def S0(a):
    return ror(a, 2) ^ ror(a, 13) ^ ror(a, 22)


def S1(e):
    return ror(e, 6) ^ ror(e, 11) ^ ror(e, 25)


def ch(e, f, g):
    return (e & f) ^ (~e & M32 & g)


def maj(a, b, c):
    return (a & b) ^ (a & c) ^ (b & c)


def d(v, i):
    return (v >> (32 * i)) & M32


def pack(d0, d1, d2, d3):
    """dwords LOW to HIGH."""
    return (d0 & M32) | (d1 & M32) << 32 | (d2 & M32) << 64 | (d3 & M32) << 96


def rule(mn, a, b, k):
    """The SDM rule for one mnemonic: SRC1 = DEST a, SRC2 b, XMM0 k (128-bit ints) -> the new DEST."""
    if mn == "sha256msg1":
        w = [d(a, 0), d(a, 1), d(a, 2), d(a, 3), d(b, 0)]
        return pack(*[(w[i] + s0(w[i + 1])) & M32 for i in range(4)])
    if mn == "sha256msg2":
        w14, w15 = d(b, 2), d(b, 3)
        w16 = (d(a, 0) + s1(w14)) & M32
        w17 = (d(a, 1) + s1(w15)) & M32
        w18 = (d(a, 2) + s1(w16)) & M32
        w19 = (d(a, 3) + s1(w17)) & M32
        return pack(w16, w17, w18, w19)
    if mn == "sha256rnds2":
        A, B, C, D, E, F, G, H = d(b, 3), d(b, 2), d(a, 3), d(a, 2), d(b, 1), d(b, 0), d(a, 1), d(a, 0)
        for i in range(2):
            t1 = (H + S1(E) + ch(E, F, G) + d(k, i)) & M32
            t2 = (S0(A) + maj(A, B, C)) & M32
            A, B, C, D, E, F, G, H = (t1 + t2) & M32, A, B, C, (D + t1) & M32, E, F, G
        return pack(F, E, B, A)
    raise SystemExit("mk_sha_rows: no rule for %s" % mn)


# --reach: one named WRONG rule per mnemonic — the mistake a reader most plausibly makes. A row set on which it agrees
# with the rule everywhere could not tell the two apart, so the count must be non-zero.
def wrong(mn, a, b, k):
    if mn == "sha256msg1":     # W4 read from SRC2's HIGH dword
        return rule(mn, a, b >> 96, k)
    if mn == "sha256msg2":     # W14 and W15 read from SRC2's LOW two dwords
        return rule(mn, a, b << 64 & M128, k)
    if mn == "sha256rnds2":    # WK read from XMM0's HIGH quadword
        return rule(mn, a, b, k >> 64)
    raise SystemExit("mk_sha_rows: no wrong rule for %s" % mn)


# ── THE TEXTBOOK, written the FIPS 180-4 way and sharing nothing with `rule` but the σ/Σ/Ch/Maj definitions ──────────

def _primes(n):
    ps, c = [], 2
    while len(ps) < n:
        if all(c % p for p in ps):
            ps.append(c)
        c += 1
    return ps


def _iroot(x, e):
    """floor(x ** (1/e)) for an integer x, exactly."""
    r = int(round(x ** (1.0 / e)))
    while r ** e > x:
        r -= 1
    while (r + 1) ** e <= x:
        r += 1
    return r


# FIPS 180-4 §4.2.2 / §5.3.3: the first 32 bits of the fractional parts of the cube roots of the first 64 primes, and
# of the square roots of the first 8 — derived, never typed; the digest checks in `--selftest` hold them to the record.
K = [_iroot(p << 96, 3) & M32 for p in _primes(64)]
H0 = [_iroot(p << 64, 2) & M32 for p in _primes(8)]


def _pad(msg):
    ml = len(msg) * 8
    m = msg + b"\x80"
    m += b"\x00" * ((56 - len(m) % 64) % 64)
    return m + ml.to_bytes(8, "big")


def textbook_schedule(block):
    w = [int.from_bytes(block[4 * t:4 * t + 4], "big") for t in range(16)]
    for t in range(16, 64):
        w.append((s1(w[t - 2]) + w[t - 7] + s0(w[t - 15]) + w[t - 16]) & M32)
    return w


def textbook_states(block, h):
    """The (a..h) working variables before round 0 and after every round t = 0..63."""
    w = textbook_schedule(block)
    a, b, c, dd, e, f, g, hh = h
    out = [(a, b, c, dd, e, f, g, hh)]
    for t in range(64):
        t1 = (hh + S1(e) + ch(e, f, g) + K[t] + w[t]) & M32
        t2 = (S0(a) + maj(a, b, c)) & M32
        hh, g, f, e, dd, c, b, a = g, f, e, (dd + t1) & M32, c, b, a, (t1 + t2) & M32
        out.append((a, b, c, dd, e, f, g, hh))
    return out


def textbook_sha256(msg):
    m, h = _pad(msg), list(H0)
    for i in range(0, len(m), 64):
        st = textbook_states(m[i:i + 64], h)[-1]
        h = [(x + y) & M32 for x, y in zip(h, st)]
    return "".join("%08x" % x for x in h)


# FIPS 180-4's examples (and the NIST example document's digests).
KAT_MSGS = [
    ("abc", b"abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
    ("abcdbcde", b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
     "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
]


def kat_rows(garbage):
    """(name, mnemonic, a, b, k, want) for each message's first block — expectations from the textbook only."""
    out = []
    for tag, msg, _dg in KAT_MSGS:
        blk = _pad(msg)[:64]
        w = textbook_schedule(blk)
        st = textbook_states(blk, H0)
        a = pack(w[0], w[1], w[2], w[3])
        b = pack(w[4], w[5], w[6], w[7])
        want = pack(*[(w[16 + i] - s1(w[14 + i]) - w[9 + i]) & M32 for i in range(4)])
        out.append(("kat_%s" % tag, "sha256msg1", a, b, garbage(), want))
        a = pack(*[(w[i] + s0(w[i + 1]) + w[i + 9]) & M32 for i in range(4)])
        b = pack(w[12], w[13], w[14], w[15])
        out.append(("kat_%s" % tag, "sha256msg2", a, b, garbage(), pack(w[16], w[17], w[18], w[19])))
        for r0 in (0, 2):
            sa, sb, sc, sd, se, sf, sg, sh = st[r0]          # the state BEFORE round r0
            ta, tb, _tc, _td, te, tf, _tg, _th = st[r0 + 2]  # and after round r0 + 1
            kk = pack((K[r0] + w[r0]) & M32, (K[r0 + 1] + w[r0 + 1]) & M32, 0, 0) | (garbage() >> 64 << 64)
            out.append(("kat_%s_r%d%d" % (tag, r0, r0 + 1), "sha256rnds2",
                        pack(sh, sg, sd, sc), pack(sf, se, sb, sa), kk, pack(tf, te, tb, ta)))
    return out


ROWS = []   # (name, fn, mnemonic, a, b, k, f, want)


def build():
    ROWS.clear()
    for km, (mn, _op) in enumerate(MNEMONICS):
        rng = random.Random(338000 + km)
        ops = []
        for r in range(16):
            e = [EDGES[(r + j) % 16] for j in range(10)]
            hi = rng.getrandbits(64) << 64
            ops.append(("edge%d" % r, pack(*e[0:4]), pack(*e[4:8]), pack(e[8], e[9], 0, 0) | hi, None))
        for r in range(N_RANDOM):
            ops.append(("rand%d" % r, rng.getrandbits(128), rng.getrandbits(128), rng.getrandbits(128), None))
        for nm, kmn, a, b, k, want in kat_rows(lambda: rng.getrandbits(128)):
            if kmn != mn:
                continue
            if rule(mn, a, b, k) != want:
                raise SystemExit("mk_sha_rows: ⛔ KAT %s %s: the RULE gives %032x, the textbook %032x — the rule's "
                                 "reading of the SDM is wrong, or the textbook is" % (mn, nm, rule(mn, a, b, k), want))
            ops.append((nm, a, b, k, want))
        for _form, fn, _bs, omn, _shape in OPS:
            if omn != mn:
                continue
            for i, (nm, a, b, k, want) in enumerate(ops):
                f = ARITH if i % 2 else 0
                ROWS.append(("%s_%s" % (fn[2:], nm), fn, mn, a, b, k, f,
                             (rule(mn, a, b, k) if want is None else want) & M128))


def q2(v):
    return "0x%016xULL, 0x%016xULL" % (v & ((1 << 64) - 1), v >> 64)


def selftest():
    bad = 0
    for tag, msg, dg in KAT_MSGS:
        got = textbook_sha256(msg)
        ok = got == dg
        print(("  ✔ " if ok else "  ✖ ") + "textbook SHA-256(%s) = %s%s" % (tag, got, "" if ok else "  WANT " + dg))
        bad += not ok
    ok = K[0] == 0x428a2f98 and K[63] == 0xc67178f2 and H0[0] == 0x6a09e667 and H0[7] == 0x5be0cd19
    print(("  ✔ " if ok else "  ✖ ") + "the derived K and H0 have FIPS 180-4's first and last words")
    bad += not ok
    build()   # refuses unless every KAT row agrees with the rule
    kat = [r for r in ROWS if "_kat_" in r[0]]
    ok = len(kat) == 16
    print(("  ✔ " if ok else "  ✖ ") + "%d KAT rows, every one equal under the rule and the textbook" % len(kat))
    bad += not ok
    # the KAT rows must not be symmetric in the operand order: swapping SRC1 and SRC2 must change every expectation
    ok = all(rule(mn, b, a, k) != w for _n, _fn, mn, a, b, k, _f, w in kat)
    print(("  ✔ " if ok else "  ✖ ") + "every KAT row's expectation changes when SRC1 and SRC2 are swapped")
    bad += not ok
    pk = [r for r in ROWS if r[0] == PLANT_WK]
    ok = len(pk) == 1 and rule("sha256rnds2", pk[0][3], pk[0][4], pk[0][5] >> 64) != pk[0][7]
    print(("  ✔ " if ok else "  ✖ ") + "--plant-wk's row exists once and its WK-from-high expectation differs")
    bad += not ok
    print("✅ mk_sha_rows selftest" if not bad else "⛔ mk_sha_rows selftest FAILED")
    return 1 if bad else 0


def main():
    P.strict_flags(__file__)
    if "--selftest" in sys.argv:
        return selftest()
    build()
    if "--summary" in sys.argv:
        for _form, fn, _bs, _mn, _sh in OPS:
            print("%-22s %d" % (fn, sum(1 for r in ROWS if r[1] == fn)))
        print("rows %d forms %d" % (len(ROWS), len(OPS)))
        return 0
    if "--reach" in sys.argv:
        bad = 0
        for mn, _op in MNEMONICS:
            rs = [r for r in ROWS if r[2] == mn]
            n = sum(1 for r in rs if wrong(mn, r[3], r[4], r[5]) & M128 != r[7])
            print("%-12s wrong rule disagrees on %3d of %3d rows" % (mn, n, len(rs)))
            bad += n == 0
        return 1 if bad else 0
    plant = "--plant" in sys.argv
    plant_wk = "--plant-wk" in sys.argv
    print("/* GENERATED by hwprobe/mk_sha_rows.py %s. Do not edit. */" % " ".join(sys.argv[1:]))
    for _form, fn, _b, _mn, _sh in OPS:
        print("void %s(struct hio *);" % fn)
        print("extern const unsigned char %s_at[];" % fn)
    print("static const struct hrow HROWS[] = {")
    for i, (name, fn, mn, a, b, k, f, want) in enumerate(ROWS):
        if plant and i == 0:
            want ^= 1 << 64        # the control: one expectation made wrong on purpose, in the HIGH quadword
        if plant_wk and name == PLANT_WK:
            want = rule(mn, a, b, k >> 64)   # the control: WK from XMM0's HIGH quadword, which no form reads
        print('  {"%s", %s, {%s}, {%s}, {%s}, 0x%03x, {%s}},' % (name, fn, q2(a), q2(b), q2(k), f, q2(want)))
    print("};")
    print("static const struct hop HOPS[] = {")
    for i, (_form, fn, bs, _mn, _sh) in enumerate(OPS):
        bb = bytearray.fromhex(bs)
        if "--plant-op" in sys.argv and i == 0:
            bb[-1] ^= 0x01         # the control: the declared instruction is not the one in sha_ops.S
        print('  {"%s", %s_at, %d, {%s}},' % (fn, fn, len(bb), ", ".join("0x%02x" % x for x in bb)))
    print("};")
    return 0


if __name__ == "__main__":
    sys.exit(main())
