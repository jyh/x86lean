#!/usr/bin/env python3
"""DERIVE x86isa's oracle support for a (mnemonic, bucket) pair STATICALLY, and
check that derivation against every pair the repository has actually MEASURED.

WHY THIS EXISTS.  Asking a pair costs a probe: a spelling chosen, an encoding
assembled, a row added, ACL2 run.  Batches 24-26 chose their predictions from
SIBLING BASE RATES and b26 got five of twenty-three wrong, all in one direction —
four by inferring a VEX-128 verdict from an SSE-legacy sibling, precisely the
inference the census key exists to forbid.  Batch 27 read the answer off x86isa's
own instruction listing instead and scored 23 of 23; this file generalises that
read to every pair, and scores it on every pair already measured.

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
every pair measured so far — not an assumption that they cannot.  The count is
printed by the run; it is deliberately not written here, because a literal in a
comment goes stale silently and this table grows every batch.

⚠️ THE PREDICTION IS PER FORM, NOT PER PAIR.  One (mnemonic, bucket) can carry
several opcodes — `psrlw` at ymm is both `0F71 /2` and `0FD1` — and x86isa may
implement one and not the other.  Those pairs are reported AMBIGUOUS rather than
guessed, because which verdict a probe gets then depends on the spelling the head
picks, and a coin flip recorded as a prediction is worse than an admitted gap.
"""
import collections, os, re, sys

# ⛔ REFUSE AN UNKNOWN FLAG BEFORE ANY WORK HAPPENS — see portable.strict_flags.
# A script that declares no flags is the SHARPEST case: it ignores anything and
# runs its main path, so a mistyped flag produced a confident green about a
# subject nobody asked about (measured: check_encodings.py --self-test -> rc 0,
# "synonym collapse: CLEAN", having never run its self-test).
if __name__ == "__main__":
    import os as _os, sys as _sys
    _sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
    from portable import strict_flags as _strict_flags
    _strict_flags(__file__)

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
        # ⛔⛔ THE WIDTH IS NOT ALWAYS SPELLED `:128`/`:256` — D138.  x86isa marks
        # a VEX entry's lane width with SIX different tokens, and reading only
        # two of them dropped 161 of the listing's 3,184 entries on the floor:
        #     :128 306 · :256 277 · :LIG 70 · :L0 36 · :LZ 28 · :L1 27
        # `:LIG` (L ignored), `:L0` and `:LZ` (L must be zero) are the SCALAR
        # VEX forms — vaddss, vmovsd, vcomiss, vcvttss2si and their kin — every
        # one of which an assembler encodes with VEX.L = 0 and the census
        # therefore keys at VEX-128.  `:L1` is 256.
        # ⚠️ AND THE OLD CODE `return None`d, which `entries()` silently
        # `continue`s — so a whole class left no trace, and the remainder tool
        # reported the survivors as "absent under this name" when the name was
        # in the listing all along ([[feedback-a-sentence-missing-case-reads-as-empty]]).
        if ":256" in vex or ":L1" in vex:
            return "AVX2/AVX (ymm)"
        if (":128" in vex or ":LIG" in vex or ":LZ" in vex or ":L0" in vex):
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


def _arg_list(body):
    r"""The WHOLE `(ARG …)` list, by balanced parentheses — never a regex.

    ⛔⛔ THE REGEX THIS REPLACES READ ONLY THE FIRST OPERAND — D138.  It was
    `\(ARG\s(.*?)\)\s*\n`: non-greedy up to the first `)` at end of line.  An
    ARG list is written one operand per line, so on

        (ARG :OP1 '(G D)
             :OP2 '(U DQ)
             :OP3 '(I B))

    it captured `":OP1 '(G D"` — OP1 alone, and with its closing paren eaten.
    `entry_bucket` then looked for the register file in that fragment, found a
    GPR, and returned None; `entries()` dropped the row without a word.

    ⇒ 🔑 EVERY INSTRUCTION WHOSE VECTOR OPERAND IS NOT FIRST WAS INVISIBLE —
    `pextrw`, `pextrd/q`, `pinsrd/q`, `extractps`: the extract-and-insert family,
    which is precisely the family whose destination is a GPR or memory.  They
    are also, not by coincidence, four of the sixteen the tool called "absent
    under this name" ([[feedback-a-column-parser-is-tested-by-its-widest-datum]]).

    Returns "" when the entry has no ARG list at all, which is a real case
    (`vzeroupper` takes no operands) and must not be confused with a parse
    failure — the caller's bucket rule handles a widthless entry by its VEX
    fields instead."""
    i = body.find("(ARG")
    if i < 0:
        return ""
    depth, j = 0, i
    while j < len(body):
        if body[j] == "(":
            depth += 1
        elif body[j] == ")":
            depth -= 1
            if depth == 0:
                return body[i + 4:j]
        j += 1
    return body[i + 4:]      # unterminated: hand back what there is


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
        args = _arg_list(body)
        bucket = entry_bucket(vex.group(1) if vex else "",
                              evex.group(1) if evex else "",
                              pfx.group(1) if pfx else "",
                              feat.group(1) if feat else "",
                              args)
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
    # ⭐ THE PAIRS THE CENSUS AND THE LISTING SPELL DIFFERENTLY, joined BY
    # ENCODING (`resolve_names.py`) rather than by editing the string.  Without
    # this the join misses and the pair is reported "absent under this name" —
    # which was true of six pairs and 1,452 instructions, two of them
    # IMPLEMENTED and therefore askable (D138).
    # ⛔ A DIRECT HIT ALWAYS WINS.  The alias may only FILL a gap, never
    # override a key the listing carries under the census's own name; a resolver
    # that can overwrite a measured-agreeing key can quietly move a verdict.
    sys.path.insert(0, os.path.join(ROOT, "scripts"))
    import resolve_names as RN
    for key, r in RN.resolve().items():
        if key not in out and r["verdict"]:
            out[key] = r["verdict"]
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
    # This is the honest price of the read: every measured pair, both verdicts
    # well represented.  The count is computed, never written down here.
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
    # ⚠️ "ABSENT FROM CATALOGUE" MEANS ABSENT FROM THE *COMPARABLE* KEY SPACE, NOT
    # ABSENT FROM x86isa.  Measured 2026-09-09, after QUEUE 1b took this count from
    # 5 to 10: all five new keys (`endbr64`, `emms`, `prefetcht0`, `prefetchnta`,
    # `movl`) ARE present in `inst-listing.lisp`.  They fall out of `predict()`
    # because `entry_bucket` buckets an entry by its ENCODING and returns None for
    # anything that is not one of the SIMD/vector buckets this census names — so a
    # scalar or CET or PREFETCH form is outside the comparison set by construction.
    # ⇒ 🔑 THE LABEL READ AS "x86isa DOES NOT HAVE IT" AND MEANS "ITS ENTRY BUCKETS
    # SOMEWHERE THIS JOIN CANNOT REACH" — two very different facts, and the first
    # one would be a finding about the ORACLE while the second is a property of the
    # KEY SPACE ([[feedback-a-join-on-a-lossy-key]]).
    print("  absent from the comparable key space : %d   (in the listing, but "
          "their encoding buckets outside the SIMD/vector set this join names — "
          "NOT missing from x86isa)" % absent)
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
    # ⛔⛔ PRICED AT THE BUCKET, NOT AT THE MNEMONIC (D137).  This loop used to
    # carry `occ` — the mnemonic's WHOLE demand — into a row labelled with ONE
    # bucket, which is precisely the defect D134 repaired in the published
    # coverage table and did not sweep for here.  Measured on P2 batch 30's own
    # 38 pairs: this file said 1,317 instructions where the roster credited
    # 1,261, the 56 decomposing exactly across the seven mnemonics whose demand
    # straddles two buckets.  The error is an OVER-claim, so inflated pairs sort
    # upward and the queue spends its next batch on them first.
    # ⚠️ `occ` is still carried, and the difference is PRINTED below, because a
    # number silently swapped for a better one is how the next drift hides.
    rows, unknown = [], []
    for mn, occ, _shapes in b["joined"]:
        bucket = R.dominant_bucket(per_ext, mn)
        if meas.get((mn, bucket)) is not None:
            continue
        bd = R.bucket_demand(per_ext, mn, bucket)
        p = pred.get((mn, bucket))
        if p in (None, "ambiguous"):
            unknown.append((bd, mn, bucket, p, occ))
        else:
            rows.append((bd, mn, bucket, p, occ))
    tot = sum(o for o, _m, _b, _p, _q in rows) + sum(o for o, _m, _b, _p, _q in unknown)
    ex = sum(o for o, _m, _b, p, _q in rows if p == "executes")
    rf = sum(o for o, _m, _b, p, _q in rows if p == "refuses")
    uk = sum(o for o, _m, _b, _p, _q in unknown)
    tot_mn = (sum(q for _o, _m, _b, _p, q in rows)
              + sum(q for _o, _m, _b, _p, q in unknown))
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
    print("  ⚠️ priced at each pair's own BUCKET.  The same remainder priced at "
          "the MNEMONIC's whole\n     demand is %s instructions — %s of it sits "
          "at those mnemonics' OTHER buckets,\n     which is demand asking this "
          "pair cannot resolve (D137)."
          % (format(tot_mn, ","), format(tot_mn - tot, ",")))
    print("\n  the pairs x86isa IMPLEMENTS, by demand — these are the ones that "
          "can become differential vectors:")
    for occ, mn, bucket, _p, _occ_mn in sorted(rows, reverse=True):
        if _p == "executes":
            print("    %8s  %-16s %s" % (format(occ, ","), mn, bucket))
    if unknown:
        print("\n  ⚠️ NOT RESOLVED — each needs a look, and a wrong name here is a "
              "lossy key, so none is guessed:")
        for occ, mn, bucket, p, _occ_mn in sorted(unknown, reverse=True)[:20]:
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
