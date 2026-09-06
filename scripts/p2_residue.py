#!/usr/bin/env python3
"""THE BUILDABLE RESIDUE — of the pairs the oracle EXECUTES and the model does
not claim, which need a ROUNDING rule and which need nothing at all.

WHY THIS EXISTS.  `docs/QUEUE.md`'s P2 item 2 says *"land the buildable groups
the census has surfaced"* and never named one, and the P2 roster's ranked table
shows only its top forty rows — where every unclaimed row that EXECUTES is either
VEX (a new capability) or scalar FP (the soft-float commission).  Read there, the
residue looks like it is blocked on one of two large additions.  It is not:

    64 unclaimed SSE-legacy (xmm) pairs EXECUTE on the oracle
  − 40 of them are the soft-float commission's
  = 24 pairs / 11,040 instructions that need NO rounding rule at all

⇒ 🔑 A CATEGORY NAMED FOR WHAT IT CONTAINS SAYS NOTHING ABOUT ITS COMPLEMENT.
The commission partitioned the FLOATING-POINT mnemonics correctly and completely;
what nothing named was the set it left behind, and its members read as "FP" in a
ranked table because their mnemonics end in `ps`/`pd`.  Being FP-TYPED is not the
same as being FP-VALUED: `xorps` reads no exponent and rounds nothing.
[[feedback-a-declared-list-inherits-its-default]]
[[feedback-a-category-is-a-hypothesis-about-its-members]]

WHAT IS DERIVED AND WHAT IS DECLARED.  The claimed set, the available set and the
demand are all READ from their sources — the Lean roster in `X86/Syntax.lean`,
`oracle_availability.measured_availability()`, and the census.  Only the
ROUNDING/NO-ROUNDING split is declared, one entry per mnemonic with its
sub-group, and it is gated three ways below.

⛔⛔ WHAT GATE 3 DOES AND DOES NOT PROVE.  It re-derives the commission's three
published sub-group totals from the live census and requires them to reproduce.
That proves the DOC AND THE CENSUS STILL AGREE — it does not prove either is
right ([[feedback-a-derivation-gate-wraps-a-false-sentence]]).  Its value is
precisely the defect the commission's own §2 records: the commission's price grew
44% while it sat docketed, because that price was a sentence in a bank rather than
a derived number, and nothing said so.  This gate is what says so.
"""
import argparse, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))

SSE = "SSE-legacy (xmm)"
COMMISSION = os.path.join(ROOT, "docs", "SOFT-FLOAT-COMMISSION.md")

# ⛔ DECLARED, WITH A REASON PER ENTRY — never a default.  Gate 2 refuses if any
# unclaimed executing pair is missing from this map, so a mnemonic that appears
# in a later census cannot be silently swept into either half.
#
# The sub-group letters are the commission's own (docs/SOFT-FLOAT-COMMISSION.md
# §2): A = no rounding at all, A' = a fixed mode independent of MXCSR.RC,
# B = MXCSR.RC-dependent.
ROUNDING = {
    # --- sub-group A: compare / min / max, and the two EXACT widenings.
    "comisd": "A", "comiss": "A", "minsd": "A", "maxss": "A", "minss": "A",
    "maxsd": "A", "ucomiss": "A", "ucomisd": "A", "maxps": "A", "minps": "A",
    "cvtss2sd": "A", "cvtsi2sdl": "A",
    # --- sub-group A': truncation toward zero is not a mode choice.
    "cvttsd2si": "A'", "cvttss2si": "A'",
    # --- sub-group B: arithmetic and the inexact conversions.
    "mulss": "B", "mulsd": "B", "addss": "B", "addsd": "B", "subss": "B",
    "subsd": "B", "divsd": "B", "divss": "B", "cvtsd2ss": "B", "mulps": "B",
    "addps": "B", "cvtsi2ssl": "B", "cvtsi2sdq": "B", "cvtss2si": "B",
    "subps": "B", "sqrtss": "B", "cvtsd2si": "B", "sqrtsd": "B", "mulpd": "B",
    "addpd": "B", "subpd": "B", "cvtsi2ssq": "B", "divps": "B", "divpd": "B",
    "sqrtps": "B", "cvtpd2ps": "B",
}

# ⭐ THE COMPLEMENT, CLASSIFIED BY WHAT ITS RULE NEEDS.  `bitwise` and `move` are
# both rounding-free; the split is kept because it is what decides a BATCH's
# shape, not because the gate reads it.
NO_ROUNDING = {
    "pandn": "bitwise", "andnps": "bitwise", "andnpd": "bitwise",
    "andps": "bitwise", "andpd": "bitwise", "orps": "bitwise",
    "orpd": "bitwise", "xorps": "bitwise", "xorpd": "bitwise",
    "movapd": "move", "movupd": "move", "movlps": "move", "movlpd": "move",
    "movhpd": "move", "movhlps": "move", "movlhps": "move", "movddup": "move",
    "unpcklps": "move", "unpcklpd": "move", "unpckhps": "move",
    "unpckhpd": "move", "shufps": "move", "shufpd": "move",
    "movmskps": "move",
}


def lean_roster(src=None):
    """The mnemonics `X86/Syntax.lean`'s `rosterP0` names.

    ⚠️ COMMENTS ARE STRIPPED FIRST.  The list is interleaved with `--` comment
    lines that name mnemonics; they use backticks today, but a parser that
    depended on that would be reading a typographic convention as a grammar.
    """
    if src is None:
        src = open(os.path.join(ROOT, "X86", "Syntax.lean")).read()
    m = re.search(r"def rosterP0 : List String :=", src)
    if not m:
        raise SystemExit("⛔ p2_residue: `rosterP0` not found in X86/Syntax.lean. "
                         "A roster this script cannot read is a REFUSAL, never an "
                         "empty set — an empty claimed set would report the whole "
                         "roster as unclaimed work.")
    # ⚠️ THE LIST OPENS AT DEPTH 1 AND CLOSES AT 0 — it never goes negative, so
    # `depth < 0` is a terminator that never fires and the scan runs to the end
    # of the file.  Break when the depth has been positive and returns to zero.
    body, depth, opened = [], 0, False
    for line in src[m.end():].splitlines():
        line = re.sub(r"--.*$", "", line)
        body.append(line)
        depth += line.count("[") - line.count("]")
        if depth > 0:
            opened = True
        if opened and depth <= 0:
            break
    else:
        raise SystemExit("⛔ p2_residue: `rosterP0` has no closing `]`.")
    names = re.findall(r'"([^"]+)"', "\n".join(body))
    if not names:
        raise SystemExit("⛔ p2_residue: `rosterP0` parsed to ZERO names.")
    return set(names)


def universe():
    """Every SSE-legacy pair the oracle EXECUTES, claimed or not, with its demand.

    ⛔ THE DECLARED SPLIT IS ABOUT THE RULE, NOT ABOUT THE MODEL'S PROGRESS.
    Whether `xorps` needs a rounding decision does not change when the model
    starts claiming it, so the gates below are keyed to THIS set and not to the
    residue.  Keying them to the residue instead made the whole batch's own nine
    mnemonics read as orphan declarations the moment they were claimed — caught
    by this file's control on its first run, which is what a control is for.
    """
    import oracle_availability as oa, p2_roster as pr
    av = oa.measured_availability()
    d = pr.census()
    per = pr.per_ext_map(d)
    return {mn: (pr.bucket_demand(per, mn, bk) or 0)
            for (mn, bk), verdict in av.items()
            if bk == SSE and verdict == "executes"}


def residue(roster=None, uni=None):
    """The unclaimed part of that universe — what is still buildable work."""
    if roster is None:
        roster = lean_roster()
    if uni is None:
        uni = universe()
    return {m: o for m, o in uni.items() if m not in roster}


def published_totals():
    """The commission's own three sub-group totals, PARSED from its §2 block.

    ⛔ Parsed, not retyped: a literal copied into this file would be a second
    source for one fact, and the copy is what goes stale.
    """
    txt = open(COMMISSION).read()
    want = {"A": r"SUB-GROUP A — NO ROUNDING AT ALL\s*\n\s*(\d+) pairs,\s*([\d,]+) instructions",
            "A'": r"SUB-GROUP A′[^\n]*\n\s*(\d+) pairs,\s*([\d,]+) instructions",
            "B": r"SUB-GROUP B[^\n]*\n\s*(\d+) pairs,\s*([\d,]+) instructions"}
    got = {}
    for key, pat in want.items():
        m = re.search(pat, txt)
        if not m:
            raise SystemExit(f"⛔ p2_residue: sub-group {key}'s published total is not "
                             f"parseable in {os.path.relpath(COMMISSION, ROOT)}. An "
                             f"unparseable gate file reports FAILURE, not absence.")
        got[key] = (int(m.group(1)), int(m.group(2).replace(",", "")))
    return got


def check(uni, res=None, verbose=True):
    """The three gates. Returns a list of failure strings; empty means clean.

    ⚠️ THE TWO GATES HAVE DIFFERENT SUBJECTS, AND THAT IS THE POINT.  Gate 1 asks
    whether a DECLARATION still names a real executing pair — true whether or not
    the model has claimed it.  Gate 2 asks whether every pair still to be BUILT is
    classified.  Keying both to one set was wrong in both directions: to the
    residue, every mnemonic this batch claimed became an orphan; to the universe,
    every mnemonic ever claimed became unclassified.  Both were caught by the
    control before any plant ran.
    """
    if res is None:
        res = residue(uni=uni)
    bad = []

    # GATE 1 — every declared mnemonic is a pair the oracle really EXECUTES at
    # this bucket.  A declaration naming nothing is a rule about a world that
    # has moved.
    declared = set(ROUNDING) | set(NO_ROUNDING)
    orphans = sorted(declared - set(uni))
    if orphans:
        bad.append(f"declared but not an executing {SSE} pair: "
                   f"{', '.join(orphans)}")

    # GATE 2 — every executing pair is declared.  ⛔ THIS IS THE ONE THAT
    # MATTERS: without it a new census pair falls to whichever half the reader
    # assumes, and the assumption is invisible.
    missing = sorted(set(res) - declared)
    if missing:
        bad.append(f"unclassified — neither ROUNDING nor NO_ROUNDING names them: "
                   f"{', '.join(missing)}")

    # GATE 3 — the commission's published sub-group totals still reproduce.
    if not orphans and not missing:
        pub = published_totals()
        for key, (n_pub, occ_pub) in sorted(pub.items()):
            members = [m for m, g in ROUNDING.items() if g == key]
            n, occ = len(members), sum(uni[m] for m in members)
            if (n, occ) != (n_pub, occ_pub):
                bad.append(f"sub-group {key}: census says {n} pairs / {occ:,}, "
                           f"the commission publishes {n_pub} / {occ_pub:,}")
            elif verbose:
                print(f"  ✔ sub-group {key:<2} {n:>2} pairs {occ:>7,}  "
                      f"reproduces the commission's published total")
    return bad


def report():
    uni = universe()
    res = residue(uni=uni)
    print(f"EXECUTING {SSE} pairs: {len(uni)}, {sum(uni.values()):,} instructions")
    print(f"THE BUILDABLE RESIDUE — {len(res)} still UNCLAIMED, "
          f"{sum(res.values()):,} instructions\n")
    bad = check(uni, res)
    if bad:
        for b in bad:
            print(f"  ⛔ {b}")
        return 1
    free = {m: o for m, o in res.items() if m in NO_ROUNDING}
    rnd = {m: o for m, o in res.items() if m in ROUNDING}
    print(f"\n  needs a ROUNDING rule (the commission)  {len(rnd):>2} pairs "
          f"{sum(rnd.values()):>7,}")
    print(f"  needs NO rounding at all                {len(free):>2} pairs "
          f"{sum(free.values()):>7,}   ⭐ BUILDABLE TODAY")
    for kind in ("bitwise", "move"):
        rows = sorted(((o, m) for m, o in free.items() if NO_ROUNDING[m] == kind),
                      reverse=True)
        print(f"\n    {kind}: {len(rows)} pairs, {sum(o for o, _ in rows):,}")
        print("      " + "  ".join(f"{m}:{o}" for o, m in rows))
    return 0


def selftest():
    """⛔ THE CONTROL RUNS FIRST. A harness that reds every plant is a harness
    that has stopped measuring, and it looks exactly like a strict gate."""
    uni = universe()
    res = residue(uni=uni)
    fired = 0

    bad = check(uni, res, verbose=False)
    if bad:
        print("⛔ CONTROL FAILED — the shipped tables do not pass their own gates:")
        for b in bad:
            print(f"     {b}")
        return 1
    print("  ✔ control: the shipped tables pass all three gates")

    # PLANT 1 — an orphan declaration (gate 1).  ⭐ DERIVED FROM THE SHIPPED
    # ARTIFACT rather than invented: a real member, renamed, so the plant cannot
    # drift out of the space the gate polices.
    victim = max(uni, key=uni.get)
    saved = dict(ROUNDING)
    try:
        ROUNDING[victim + "_ZZ"] = "B"
        if any("declared but not" in b for b in check(uni, res, verbose=False)):
            fired += 1
            print("  ✔ plant 1 caught: an orphan declaration")
        else:
            print("  ⛔ plant 1 NOT caught: an orphan declaration passed")
    finally:
        ROUNDING.clear(); ROUNDING.update(saved)

    # PLANT 2 — an unclassified pair (gate 2), the default-inheriting defect.
    saved_n = dict(NO_ROUNDING)
    try:
        drop = next(m for m in NO_ROUNDING if m in res)
        del NO_ROUNDING[drop]
        if any("unclassified" in b for b in check(uni, res, verbose=False)):
            fired += 1
            print("  ✔ plant 2 caught: a residue pair no list names")
        else:
            print("  ⛔ plant 2 NOT caught: an unclassified pair passed")
    finally:
        NO_ROUNDING.clear(); NO_ROUNDING.update(saved_n)

    # PLANT 3 — a pair moved between sub-groups (gate 3).  It keeps the pair
    # count of neither group right, so it must move a published total.
    saved = dict(ROUNDING)
    try:
        mover = next(m for m, g in ROUNDING.items() if g == "B")
        ROUNDING[mover] = "A"
        if any("sub-group" in b for b in check(uni, res, verbose=False)):
            fired += 1
            print("  ✔ plant 3 caught: a pair moved from B to A")
        else:
            print("  ⛔ plant 3 NOT caught: the totals did not move")
    finally:
        ROUNDING.clear(); ROUNDING.update(saved)

    # PLANT 4 — an unreadable roster (the refusal path).  ⛔ A roster that parses
    # to nothing must REFUSE, not report the whole model as unclaimed: silence
    # here would print the largest buildable group this script can imagine.
    try:
        lean_roster("-- no roster here\n")
        print("  ⛔ plant 4 NOT caught: a missing roster did not refuse")
    except SystemExit:
        fired += 1
        print("  ✔ plant 4 caught: a missing roster REFUSES rather than reporting 0 claimed")

    print(f"\n{'✔' if fired == 4 else '⛔'} selftest: {fired} of 4 distinct arms fired, "
          f"control first")
    return 0 if fired == 4 else 1


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true",
                    help="gate only: refuse if the declared split has drifted")
    ap.add_argument("--selftest", action="store_true",
                    help="drive each gate RED before believing it green")
    a = ap.parse_args()
    if a.selftest:
        sys.exit(selftest())
    if a.check:
        u = universe()
        bad = check(u, residue(uni=u))
        for b in bad:
            print(f"⛔ {b}")
        sys.exit(1 if bad else 0)
    sys.exit(report())
