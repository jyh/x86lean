#!/usr/bin/env python3
"""DERIVE x86isa's oracle support for a (mnemonic, bucket) pair STATICALLY, and
check that derivation against every pair the repository has actually MEASURED.

WHY THIS EXISTS.  Asking a pair costs a probe: a spelling chosen, an encoding
assembled, a row added, ACL2 run.  Batches 24-26 chose their predictions from
SIBLING BASE RATES and b26 got five of twenty-three wrong, all in one direction —
four by inferring a VEX-128 verdict from an SSE-legacy sibling, precisely the
inference the census key exists to forbid.  Batch 27 read the answer off x86isa's
own instruction listing instead and scored 23 of 23; this file generalises that
read to every pair, and scores it on all 168 already measured.

⛔⛔⛔ AND THE FIRST THING TO SAY IS THE CORRECTION D132 PAID FOR.  Batch 27's note
called the listing "a SECOND SOURCE" and read 23 of 23 as a model of the oracle
beating naive baselines.  IT IS NOT A SECOND SOURCE.  `machine/dispatch-creator.
lisp` includes `inst-listing` and builds the opcode dispatch FROM it —

    (fn-call (if (equal fn nil) unimplemented-opcode ...))   dispatch-creator.lisp

— so the semantic-function slot this file reads is the very datum that decides
whether the running machine implements the opcode.  ⇒ 🔑 THE CATALOGUE AND THE
MACHINE ARE ONE SOURCE READ TWO WAYS, statically and dynamically.  A high score
here is therefore NOT evidence that a model of the oracle is good; it is evidence
that THIS READER PARSES THE LISTING FAITHFULLY.  A miss would have been the
finding; a hit is the baseline expectation.

WHAT THAT BUYS, WHICH IS MORE THAN A GOOD PREDICTOR.  Oracle support is
DERIVABLE, so the entire unasked remainder can be priced with no ACL2 run at all
— which pairs can become differential vectors, and how much demand sits behind
them.  That is the `--remaining` half of the output.

WHAT IT DOES NOT REPLACE.  `measured_availability` still publishes only what ACL2
EXECUTED, and must.  A static read cannot see the ways a form can fail BEFORE the
dispatch is reached or DESPITE an implemented slot: a byte string that does not
decode to the entry at all, a feature-flag or CR4 gate, an ACL2 guard violation
(`cvtss2sd` at zero operands raises one, which is why it serves as the operand
control).  The 163 of 163 below is a MEASURED statement that none of those bit on
168 pairs — not an assumption that they cannot.

⚠️ THE PREDICTION IS PER FORM, NOT PER PAIR.  One (mnemonic, bucket) can carry
several opcodes — `psrlw` at ymm is both `0F71 /2` and `0FD1` — and x86isa may
implement one and not the other.  Those pairs are reported AMBIGUOUS rather than
guessed, because which verdict a probe gets then depends on the spelling the head
picks, and a coin flip recorded as a prediction is worse than an admitted gap.
"""
import collections, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LISTING = os.path.join(ROOT, "vendor", "acl2", "books", "projects", "x86isa",
                       "machine", "inst-listing.lisp")

# ⚠️ THE BUCKET OF A CATALOGUE ENTRY IS READ OFF ITS ENCODING, not its mnemonic —
# the same mnemonic appears at MMX, SSE, VEX-128, VEX-256 and EVEX widths, which
# is the whole reason the census key is (mnemonic, BUCKET).
def entry_bucket(vex, evex, pfx, feat, args):
    if evex:
        return "AVX-512 (zmm/k)" if ":512" in evex else None   # EVEX.128/256: not a census bucket here
    if vex:
        if ":256" in vex:
            return "AVX2/AVX (ymm)"
        if ":128" in vex:
            return "VEX-128 (v… xmm)"
        return None
    # ⛔⛔ A LEGACY ENTRY'S REGISTER FILE IS IN ITS OPERAND LETTERS, NOT IN ITS
    # FEATURE FLAG.  The first version of this function read the feature, and it
    # was wrong in BOTH directions on real entries:
    #   `PSHUFW`  :FEAT (:SSE)   but ARG (P Q)(Q Q) — an MMX instruction
    #   `PSHUFB`  :FEAT (:SSSE3) but ARG (P Q)(Q Q) — an MMX instruction, and
    #                            `:SSSE3` does not even contain the substring
    #                            `:SSE`, so it fell through to no bucket at all
    # The SDM's operand notation is the datum that cannot go stale: P/Q/N name
    # MMX registers, V/W/H/U name XMM ones.  ⇒ 🔑 read the register file off the
    # OPERANDS — the same rule `probe_bucket` already follows, and for the same
    # reason: the mnemonic and the feature flag are both labels, the operands are
    # the thing.
    if re.search(r"'\((?:P|Q|N)\s", args):
        return "MMX (mm)"
    if re.search(r"'\((?:V|W|H|U)\s", args):
        return "SSE-legacy (xmm)"
    return None


def entries():
    """(name, bucket, implemented) for every INST entry the listing declares."""
    txt = open(LISTING).read()
    out = []
    for part in re.split(r'\n\s*\(INST\s+"', txt)[1:]:
        name = part.split('"')[0].lower()
        body = part[:part.find("(INST ")] if part.find("(INST ") > 0 else part
        vex = re.search(r":VEX\s+'\(([^)]*)\)", body)
        evex = re.search(r":EVEX\s+'\(([^)]*)\)", body)
        pfx = re.search(r":PFX\s+(\S+)", body)
        feat = re.search(r":FEAT\s+'\(([^)]*)\)", body)
        args = re.search(r"\(ARG\s(.*?)\)\s*\n", body, re.S)
        bucket = entry_bucket(vex.group(1) if vex else "",
                              evex.group(1) if evex else "",
                              pfx.group(1) if pfx else "",
                              feat.group(1) if feat else "",
                              args.group(1) if args else "")
        if bucket is None:
            continue
        # ⛔ CASE-INSENSITIVE, AND THAT IS NOT COSMETIC.  x86isa writes some
        # semantic-function names lowercase (`x86-vpsubb/vpsubw/...-vex`) and
        # some uppercase.  An uppercase-only match read a lowercase slot as
        # ABSENT and would have predicted `refuses` for an implemented form —
        # the failure direction that looks like modesty.  It was found on
        # `vpsubw` while the batch-27 predictions were being made, before the
        # run, and it is why this pattern carries re.I.
        fn = re.search(r"\n\s+'\((x86-[a-z0-9/?\-\.]+)[\s)]", body, re.I)
        out.append((name, bucket, bool(fn)))
    return out


def predict():
    """{(mnemonic, bucket): "executes" | "refuses" | "ambiguous"}"""
    by_key = collections.defaultdict(set)
    for name, bucket, impl in entries():
        by_key[(name, bucket)].add(impl)
    out = {}
    for key, impls in by_key.items():
        out[key] = ("ambiguous" if len(impls) > 1
                    else ("executes" if True in impls else "refuses"))
    return out


def main():
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "oa", os.path.join(ROOT, "scripts", "oracle_availability.py"))
    oa = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(oa)

    pred, meas = predict(), oa.measured_availability()
    print("x86isa catalogue: %d (mnemonic, bucket) keys carry a bucket this "
          "census names" % len(pred))

    # ══════════════════════════════════════════════════════════════════════
    # ⭐⭐ THE SCORE, on every pair the repository has actually MEASURED.
    # This is the honest price of the route: 168 pairs, both verdicts well
    # represented, and the catalogue never saw any of them.
    hit = miss = amb = absent = 0
    wrong = []
    for key, got in sorted(meas.items()):
        p = pred.get(key)
        if p is None:
            absent += 1
        elif p == "ambiguous":
            amb += 1
        elif p == got:
            hit += 1
        else:
            miss += 1
            wrong.append((key, p, got))
    scored = hit + miss
    print("\nSCORED AGAINST THE MEASURED TABLE — %d pairs measured" % len(meas))
    print("  predicted and scorable : %d" % scored)
    print("  correct                : %d  (%.1f%% of scorable)"
          % (hit, 100.0 * hit / scored if scored else 0.0))
    print("  wrong                  : %d" % miss)
    print("  ambiguous (not scored) : %d   — the pair carries opcodes x86isa "
          "splits on" % amb)
    print("  absent from catalogue  : %d" % absent)
    if wrong:
        print("\n⛔ WHERE THE CATALOGUE DISAGREES WITH THE MACHINE — each of these "
              "is a finding about the ORACLE'S OWN RECORD, not a bad guess:")
        for (mn, b), p, got in wrong:
            print("    %-16s %-18s catalogue says %-9s ACL2 does %s"
                  % (mn, b, p, got))

    # ══════════════════════════════════════════════════════════════════════
    # ⭐⭐ THE DELIVERABLE: the UNASKED remainder, priced with no ACL2 run.
    sys.path.insert(0, os.path.join(ROOT, "scripts"))
    import p2_roster as R
    d = R.census(); b = R.build(d); per_ext = R.per_ext_map(d)
    rows, unknown = [], []
    for mn, occ, _shapes in b["joined"]:
        bucket = R.dominant_bucket(per_ext, mn)
        if meas.get((mn, bucket)) is not None:
            continue
        p = pred.get((mn, bucket))
        if p in (None, "ambiguous"):
            unknown.append((occ, mn, bucket, p))
        else:
            rows.append((occ, mn, bucket, p))
    tot = sum(o for o, _m, _b, _p in rows) + sum(o for o, _m, _b, _p in unknown)
    ex = sum(o for o, _m, _b, p in rows if p == "executes")
    rf = sum(o for o, _m, _b, p in rows if p == "refuses")
    uk = sum(o for o, _m, _b, _p in unknown)
    print("\nTHE UNASKED REMAINDER, PRICED STATICALLY — %d pairs, %s instructions"
          % (len(rows) + len(unknown), format(tot, ",")))
    print("  x86isa IMPLEMENTS   %3d pairs / %8s / %5.1f%% of the remainder"
          % (sum(1 for r in rows if r[3] == "executes"), format(ex, ","),
             100.0 * ex / tot if tot else 0))
    print("  x86isa DOES NOT     %3d pairs / %8s / %5.1f%%"
          % (sum(1 for r in rows if r[3] == "refuses"), format(rf, ","),
             100.0 * rf / tot if tot else 0))
    print("  NOT RESOLVED HERE   %3d pairs / %8s / %5.1f%%   (absent or split "
          "in the listing under this name)"
          % (len(unknown), format(uk, ","), 100.0 * uk / tot if tot else 0))
    print("\n  the pairs x86isa IMPLEMENTS, by demand — these are the ones that "
          "can become differential vectors:")
    for occ, mn, bucket, _p in sorted(rows, reverse=True):
        if _p == "executes":
            print("    %8s  %-16s %s" % (format(occ, ","), mn, bucket))
    if unknown:
        print("\n  ⚠️ NOT RESOLVED — each needs a look, and a wrong name here is a "
              "lossy key, so none is guessed:")
        for occ, mn, bucket, p in sorted(unknown, reverse=True)[:20]:
            print("    %8s  %-16s %-18s %s" % (format(occ, ","), mn, bucket,
                                               p or "absent under this name"))

    # ⚠️ THE BASELINES, because a score means nothing without something to beat.
    for name, rule in (("always refuses", lambda k: "refuses"),
                       ("always executes", lambda k: "executes"),
                       ("refuse iff v-prefixed/zmm",
                        lambda k: "refuses" if k[0].startswith("v") else "executes")):
        b = sum(1 for k, g in meas.items()
                if pred.get(k) not in (None, "ambiguous") and rule(k) == g)
        print("  baseline %-26s %d / %d" % (name + ":", b, scored))
    return 0


if __name__ == "__main__":
    sys.exit(main())
