#!/usr/bin/env python3
"""THE DRIFT GATE — the SECOND kernel-time gate, over a WINDOW of landed batches.

⚖️ **THE ANSWER TO QUEUE ITEM 4f (D153, priced), BUILT AS D154.** The per-batch
delta gate (`kernel_delta.py`) stays the merge gate and is not touched. This runs
BESIDE it, over the last k batches instead of the last one.

## WHY A SECOND GATE AND NOT A REPLACEMENT

D152's finding, in one number: `R = band / allowance`. `R < 1` means the
instrument can see a change the size of the change the gate is willing to permit.
Measured over 23 gated units on two nights: **R = 0.21 (quiet) and 0.29 (loaded)**,
and on the loaded night **18% of units could not resolve their own allowance at
all**. The per-batch gate spends those cases on `UNMEASURABLE` — a refusal, not a
verdict.

Widening the window fixes the RATIO and nothing else. Over k=1→11 on two
independent walks the accumulated allowance grows **11.4x / 11.2x** while the band
moves only **1.01x / 1.43x**, so R falls to **0.11x / 0.23x**. It costs ZERO extra
profiling: this gate reads two trees exactly as the per-batch gate does, they are
just further apart.

⛔⛔ **AND IT CANNOT CONVICT WHERE THE PER-BATCH GATE PASSES.** With the allowance
summed per step, a window that spent under budget every batch is under the summed
budget by construction. Its whole power is over what the per-batch gate REFUSED
(17% of cases on the loaded night). That is why it is a SECOND gate: as a
replacement it would be strictly weaker, and as a tighter gate wearing a repair's
name it would convict by arithmetic. What it BUYS is latency and attribution —
a regression is caught k batches late and attributed to a window, not a commit.

## THE ALLOWANCE — THE SUM OF THE PER-STEP BUDGETS, NEVER k x ONE BUDGET

Every budget in `kernel_delta_budget.txt` is a PERCENTAGE (22 of 22; the only
absolute line is `@floor`), so a step's allowance depends on the tree that step
started from. A k-batch window is entitled to the sum of the k budgets each batch
was entitled to, each computed against ITS OWN base.

⛔ `k * effective(budget, base_at_anchor)` is NOT that sum. MEASURED over the
1,518 (window, unit) cases of the 09/04 walk, the ratio (true sum) / (k x anchor)
runs **p90 1.033, max 1.185**, and per-k it rises with the window to **p90
1.09-1.10 and max 1.18-1.20** by k=10. Shipping the flat spelling would under-allow
the top decile by a fifth and call the shortfall a regression — convictions
manufactured by the design's own arithmetic.
[[feedback-widening-a-gate-needs-a-second-source]]

⛔⛔ **AND THE DIFFERENCE IS NOT ONE-DIRECTIONAL — this file said it was, and the
cross-check refuted it in the same sitting.** The stated reason was *"the tree
grows across the window, so every later step is entitled to more than the anchor
was."* The trees do not only grow: of the 1,518 cases, **468 (30.8%) have sum >
flat, 187 (12.3%) have sum < flat**, and 863 are exactly equal. So the flat
spelling is not merely a conservative gate that can only over-convict — in an
eighth of cases it is too GENEROUS and lets accumulated drift through. That
strengthens the case for the sum and destroys the reason first given for it.
🔑 An "it can only err in the safe direction" premise is the one to measure.
[[feedback-conservative-is-a-direction-not-a-margin]]

⚠️ The median ratio is 1.0000, and that is not evidence the difference is small:
**~48% of gated cases are FLOOR-BOUND** (their percentage falls under `@floor 6`,
so `effective` returns the constant 6 and the sum IS exactly k x 6). Half the
corpus agrees by construction and cannot report on the other half. The selftest
therefore plants BOTH cases — a growing unit where the two spellings differ, and a
floor-bound unit where they must agree exactly.

## WHERE THE PER-STEP BUDGETS COME FROM — THE LEDGER

This gate profiles two trees. It does not profile the k-1 trees in between, so it
cannot measure their bases. It does not need to: **the per-batch gate already
computed each step's allowance when that step merged**, against exactly that
step's own base. The ledger is that number, written down.

`docs/delta-allowance-ledger.jsonl`, one row per landed step:

    {"base": <sha>, "head": <sha>, "t": ..., "box": ..., "source": ...,
     "budget_digest": <sha256/16 of the registry that produced these>,
     "allowance": {unit: ms},     <- the verdict input
     "base_ms":   {unit: ms}}     <- AUDIT ONLY, never read for a verdict

⛔⛔ **THE ANCHOR IS RE-PROFILED EVERY RUN AND NEVER CACHED.** The refuted cheap
spelling of this design reads the anchor's TIMING from a previous session instead
of profiling it: it halves the work and **manufactures 9 convictions that the
same-session comparison calls `ok`** (OVER 0 → 9, UNMEASURABLE 43 → 71) —
regressions made out of the difference between two nights, judged by a band that
does not know the nights differ. The ledger holds ALLOWANCES, which are policy
numbers, never the readings the delta is computed from. `base_ms` is carried so
the allowance can be audited and re-derived, and it is dead to every verdict path;
the selftest perturbs it 10x and requires nothing to move, with a positive control
that perturbing `allowance` DOES move the verdict, so that silence is informative.

⛔ **A GAP IN THE WINDOW IS A REFUSAL, NOT A ZERO.** A step with no ledger row
cannot be priced, and a window missing a step's allowance is not a cheaper window.
Likewise a row whose `budget_digest` differs: summing allowances derived from two
different registries prices one thing with another's rule.
[[feedback-a-join-on-a-lossy-key]]

## WHAT IT DOES NOT DO

* It does not measure DETECTION on this repository's history. Both recorded walks
  return **zero OVER at every k** — the twelve commits landed, so they are all in
  budget, and a statistic computed over history is computed over things that
  PASSED. The lever is demonstrated where it can be: on a plant sized to the band
  in closed form, whose flip point is stated BEFORE the run.
  [[feedback-a-landed-corpus-cannot-measure-detection]]
* It does not buy repeats for resolution. The spread SATURATES at n≈3-4
  (585.9 → 326.7 → 104.4 → 104.1 → 109.5 where 1/sqrt(n) predicts 338 at n=3), so
  the projection that names a finite N names it for a question no N answers (D153).
* Its allowances for the backfilled steps are RETROSPECTIVE — computed from a
  recorded walk, not by the gate that let those batches merge, because this gate
  did not exist then. Every row says which, and the report counts them.

usage:
  kernel_drift.py --anchor <rev> [--head HEAD] [--repeats N]   the gate
  kernel_drift.py --record --readings <kernel_delta --out json> [--ledger P]
  kernel_drift.py --backfill <walk.jsonl> [--ledger P]
  kernel_drift.py --gap [--ratchet P] [--write-ratchet]        the landing ritual's gate
  kernel_drift.py --selftest
exit: 0 CLEAN · 1 OVER · 2 REFUSED · 3 UNMEASURABLE
"""
import hashlib
import json
import math
import os
import statistics
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import kernel_delta as kd                              # noqa: E402  the gate itself

ROOT = os.path.dirname(HERE)
LEDGER = os.path.join(ROOT, "docs", "delta-allowance-ledger.jsonl")
RATCHET = os.path.join(ROOT, "docs", "drift-gap-ratchet.txt")
RATCHET_HEADER = """# DRIFT GAP RATCHET — GENERATED by `kernel_drift.py --gap --write-ratchet`.
# ⛔ DO NOT EDIT. The number below is the count of first-parent steps on master
# that change a `.lean` file and have NO row in the drift allowance ledger.
# It is gated in BOTH directions: landing a batch without recording its row
# raises it (red), and a backfill that lowers it must lower this line in the
# same commit (also red until it does).
# ⚠️ It is NOT a kernel-time judgement. It says only whether the ledger is
# still being kept — which is the precondition every drift verdict rests on.
"""


def refuse(msg, rc=2):
    print(msg)
    sys.exit(rc)


# ── the registry digest ──────────────────────────────────────────────────────
# ⛔ DERIVED FROM THE SHIPPED FILE, never a literal. A gate is not exempt from
# the defect it polices, and a pinned digest written by hand is a stale literal
# in an anti-staleness check. [[feedback-a-gate-is-not-exempt-from-its-own-defect]]
def budget_digest(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()[:16]


# ══════════════════════════════════════════════════════════════════════════════
# THE LEDGER
# ══════════════════════════════════════════════════════════════════════════════
def load_ledger(path):
    """{base: row}. Refuses on a step recorded twice with different allowances —
    the second recording is not a confirmation, it is a fork, and picking one
    silently prices the window with whichever night was read last.

    ⭐⭐ KEYED ON `base` ALONE, WHICH IS WHAT BREAKS THE FIXED POINT (D161). The
    ledger is TRACKED, so writing step N's row is itself a commit and therefore a
    first-parent step needing a row — while the key named the sha the step
    PRODUCES. It does not have to: every budget is a percentage and `allowance`
    is `f(base tree, budget registry)`, both of which exist BEFORE the child is
    made, so a row can ride in its own step's commit once the key stops naming
    the child. `--first-parent` makes `base → head` a function on the walked
    chain, so `base` identifies the step.

    ⛔ AND NO NEW REFUSAL IS NEEDED FOR A RE-CUT BRANCH, though one was proposed.
    Two children of one base are priced from the SAME tree, so their allowances
    are IDENTICAL and either row sums the window correctly. What genuinely
    differs between two rows for one base is the NIGHT `base_ms` was measured on
    — which is what the fork check below has always caught. A blanket refusal on
    a duplicate `base` would have been strictly worse: it would reject the benign
    same-night case this rule deliberately permits."""
    if not os.path.exists(path):
        return {}
    by = {}
    for ln, line in enumerate(open(path), 1):
        line = line.strip()
        if not line:
            continue
        r = json.loads(line)
        key = r["base"]
        prev = by.get(key)
        if prev is not None and prev["allowance"] != r["allowance"]:
            refuse(_fork_msg(key, prev, r, ln))
        by[key] = r
    return by


def _fork_msg(key, prev, new, ln=None):
    def who(r):
        return (f"{r.get('source', '?')}  t={r.get('t', '?')}  "
                f"{str(r.get('box', ''))[:60]}")
    return (f"⛔ the step out of {str(key)[:9]} is priced TWICE with different "
            f"allowances:\n"
            f"   {who(prev)}\n"
            f"   {who(new)}{f' (line {ln})' if ln else ''}\n"
            f"   A step has ONE allowance — the one it was entitled to when it "
            f"merged. Two readings of the same step are two nights, not two "
            f"witnesses; keep the row that gated it and delete the other.")


# ⛔ CHECKED BEFORE ANYTHING IS WRITTEN. The first spelling appended the rows and
# then re-read the file, so a conflicting `--record` left the bad row ON DISK and
# every later run refused until someone hand-edited the ledger — a gate that
# corrupts its own data store and then declines to work. Found by probing the
# record path rather than by reading it. [[feedback-probe-gates-both-ways]]
def append_rows(path, rows, existing):
    seen = dict(existing)
    for r in rows:
        key = r["base"]
        prev = seen.get(key)
        if prev is not None and prev["allowance"] != r["allowance"]:
            refuse(_fork_msg(key, prev, r))
        seen[key] = r
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "a") as f:
        for r in rows:
            f.write(json.dumps(r, sort_keys=True) + "\n")


# ⛔⛔ EXTRACTED FROM `main()` 2026-09-06, AND THE EXTRACTION IS THE REPAIR.
# This ran as an inline block inside `--verify-ledger`, which is precisely why it
# had NO SELFTEST ARM: a selftest calls functions, and there was no function to
# call. D161 re-keyed `load_ledger` from `(base, head)` to `base` and this block
# kept building its `want` on TUPLES, so every `have.get(key)` missed, all 11
# steps read ABSENT, and the surplus loop rendered a STRING key as `3→2` — the
# first two characters of a sha. Master shipped it RED for four hours.
# ⇒ 🔑 **A GATE WITH NO CALLABLE SURFACE CANNOT BE ARMED**, and the selftest
# beside it (18 arms, 10 plants) was green throughout — its greenness was about
# the arithmetic, and read as though it were about the file.
# ⚠️ `head` IS COMPARED HERE even though D161 demoted it to audit-only. That is
# deliberate and it is the widening: the derivation produces `head`, so a
# derivation gate that ignores it leaves the one field D161 stopped reading
# unpoliced, which is exactly where the next rot lands.
# [[feedback-a-gate-is-not-exempt-from-its-own-defect]]
# [[feedback-an-implied-assertion-is-not-a-second-gate]]
# ⛔ A CALLABLE SURFACE, because the single-walk check next door spent four hours
# RED on master for being an inline block in `main()` with nothing able to call
# it (D162). Writing its successor the same way would be that defect surviving the
# record that names it. [[feedback-a-gate-with-no-callable-surface]]
def verify_ledger_all(ledger, decl_map, default_ms, budgets, floor, digest,
                      docs_dir=None):
    """(bad, checked, live, tags, n_rows) — every backfilled row, by its OWN tag."""
    import delta_repair_price as drp
    docs = docs_dir or os.path.join(ROOT, "docs")
    tags = {}
    for k, r in ledger.items():
        tags.setdefault(str(r.get("source", "")), []).append(k)
    bad, checked, n_rows = [], [], 0
    for tag in sorted(t for t in tags if t.startswith("backfill:")):
        path = os.path.join(docs, tag.split(":", 1)[1])
        if not os.path.exists(path):
            bad.append(f"   {len(tags[tag])} row(s) cite `{tag}` and that walk is "
                       f"NOT in docs/ — the evidence for a committed row is gone, "
                       f"so those allowances can never be re-derived")
            continue
        w = drp.load_walk(path)
        ur = drp.unit_readings(w, decl_map)
        order = w["order"]
        want = {}
        for i in range(len(order) - 1):
            med = {u: statistics.median(v) for u, v in ur[order[i]].items()}
            want[order[i]] = (order[i + 1],
                              allowances_for(med, default_ms, budgets, floor))
        bad += verify_ledger(want, ledger, tag, digest)
        checked.append((tag, len(want)))
        n_rows += len(want)
    # ⛔ NAMED, NOT SKIPPED. A live `source=gate` row is not derivable from a walk
    # — it came from the merge gate's own readings — so it is returned for the
    # caller to PRINT, rather than quietly excluded from a green sentence.
    live = [t for t in tags if not t.startswith("backfill:")]
    return bad, checked, live, tags, n_rows


def verify_ledger(want, ledger, tag, digest):
    """[discrepancy, ...] — empty iff the tagged rows ARE their own derivation.

    `want` is {base: (head, {unit: allowance})}, keyed the way `load_ledger`
    keys, because the two dicts are joined. ⛔ A caller that builds `want` with
    its own key shape is a duplicate born in agreement — it matches on the day
    it is written and misses silently on the next re-key.
    [[feedback-a-duplicate-born-in-agreement]]"""
    have = {k: r for k, r in ledger.items() if r.get("source") == tag}
    bad = []
    for base, (head, alw) in sorted(want.items()):
        got = have.get(base)
        if got is None:
            bad.append(f"   {base[:9]}→{head[:9]}  ABSENT from the ledger")
            continue
        if got.get("budget_digest") != digest:
            bad.append(f"   {base[:9]}→{head[:9]}  priced against registry "
                       f"{got.get('budget_digest')}, this run reads {digest}")
        if got.get("head") != head:
            bad.append(f"   {base[:9]}→{head[:9]}  head: ledger "
                       f"{str(got.get('head'))[:9]} vs derived {head[:9]}")
        for u in sorted(set(alw) | set(got["allowance"])):
            a, b = alw.get(u), got["allowance"].get(u)
            if a is None or b is None or abs(a - b) > 1e-9:
                bad.append(f"   {base[:9]}→{head[:9]}  {u}: ledger {b} vs "
                           f"derived {a}")
    for base in sorted(set(have) - set(want)):
        bad.append(f"   {base[:9]}→{str(have[base].get('head'))[:9]}  in the "
                   f"ledger under {tag} but not a step of that walk")
    return bad


def allowances_for(base_units, default_ms, budgets, floor):
    """{unit: allowance ms} for ONE step, at that step's OWN base reading."""
    return {u: kd.effective(budgets.get(u, default_ms), ms, floor)
            for u, ms in base_units.items()}


# ══════════════════════════════════════════════════════════════════════════════
# THE WINDOW
# ══════════════════════════════════════════════════════════════════════════════
def window_steps(anchor, head):
    """[(base, head), ...] — the first-parent steps from anchor to head."""
    out = kd.git("rev-list", "--first-parent", "--reverse", f"{anchor}..{head}")
    revs = [r for r in out.splitlines() if r.strip()]
    if not revs:
        refuse(f"⛔ no commits between {anchor[:9]} and {head[:9]}. A window of zero "
               f"batches has nothing to accumulate; this gate is not the per-batch "
               f"gate and must not stand in for it.")
    chain = [kd.git("rev-parse", anchor)] + revs
    return [(chain[i], chain[i + 1]) for i in range(len(chain) - 1)]


# ══════════════════════════════════════════════════════════════════════════════
# THE GAP — WHAT THE LEDGER DOES NOT COVER, AND WHY IT IS NOT ONE NUMBER
# ══════════════════════════════════════════════════════════════════════════════
# ⛔⛔ BUILT 2026-09-06 (D164) BECAUSE THE `--no-ff` LANDING RITUAL IS A
# DISCIPLINE, AND A GATE WHOSE PRECONDITION IS A DISCIPLINE IS SWITCHED OFF BY
# THE FIRST HEAD WHO FORGETS. Fast-forwarding a batch costs nothing visible: the
# tests pass, the merge gate passes, the bank reads clean, and the ONLY thing
# that would report the new hole is the drift gate — which the hole disables.
# batch 36 was fast-forwarded by a head that had just written the fix down.
# [[feedback-a-gate-whose-precondition-is-a-discipline]]
#
# ⭐⭐ AND THE SPLIT IS THE POINT, NOT THE TOTAL. "The gap is 51 commits" was the
# inherited framing and it prices a backfill at 51 profiling runs — hours. It is
# THREE populations (measured 09/06 at `79bb658`, anchor `144e9a3`):
#
#     51 steps have no row.  Of those:
#        5  change a `.lean` file          ⇐ batches 23, 34, 35, 36a, 36b.
#                                            These need a REAL measurement.
#        5  change no `.lean` but DO change `kernel_cost.py` or the budget
#           registry                       ⇐ they move the READING or the
#                                            ALLOWANCE without moving the code,
#                                            so "nothing to price" is false here.
#       41  change none of the above       ⇐ the exemption candidate, and it is
#                                            a candidate, not a conclusion.
#
# ⇒ 🔑 **A TOTAL CANNOT SEE ITS PARTS**: the backfill is 5 profiling runs and a
# stated argument, not 51 profiling runs. [[feedback-a-total-cannot-see-its-parts]]
# ⛔ THE THIRD BUCKET IS NOT EXEMPTED HERE. This function REPORTS it; nothing in
# this file treats it as zero, because "a docs commit cannot change kernel time"
# is an argument someone still has to write and gate.
# [[feedback-the-burden-is-on-the-departure]]
# ⛔⛔ `lean-toolchain` AND `lake-manifest.json` WERE ADDED 09/06 (D171) AND THEY
# WERE THE HOLE. A toolchain bump changes EVERY unit's reading and touches no
# `.lean` file, so under the two-name list it fell to the exemption bucket — the
# one direction nobody polices. No step in the current window touches either, so
# this corrects a LATENT hole rather than a live miscount, and the bucket counts
# below are unchanged by it. That is the point: it was exempt by DEFAULT, and a
# default is not an argument. [[feedback-a-declared-list-inherits-its-default]]
PROFILER_PATHS = ["scripts/kernel_cost.py", "scripts/kernel_delta_budget.txt",
                  "lean-toolchain", "lake-manifest.json"]

# ══════════════════════════════════════════════════════════════════════════════
# THE EXEMPTION ARGUMENT — AN ALLOWLIST, BECAUSE THE OTHER SHAPE IS A DEFAULT
# ══════════════════════════════════════════════════════════════════════════════
# ⛔⛔ THE BUCKET USED TO BE `else:` — "changes no `.lean` and none of the two
# profiler paths" — and an `else` is not an argument, it is whatever is left. Its
# gaps ALL fall to "exempt", which is the direction that reports no work. A path
# nobody had thought of (a toolchain pin, a vendored input, a new generated
# artifact) was exempt the moment it existed, silently, and the only instrument
# that would have said so was this one.
#
# ⇒ THE DEFAULT IS INVERTED. A step is exempt only when EVERY path it touches is
# matched by a rule below WITH A REASON. Anything unmatched lands in
# `unclassified`, which is NOT exempt and which REFUSES — once, until a human
# writes the rule. The ceiling for it is zero and there is no ratchet, because
# the correct number of un-argued exemptions is none.
#
# ⭐ AND THE CLASSIFIER'S ORDER DOES HALF THE WORK. `*.lean` is tested FIRST, so
# no rule here can ever see a `.lean` file — including a GENERATED one. That is
# what makes the `scripts/*.py` rule sound: a gate or an analyser can only reach
# a kernel-time reading by regenerating a `.lean`, and the regeneration is itself
# a `.lean` diff this classifier has already bucketed. The rule below states that
# rather than assuming it.
EXEMPT_RULES = [
    ("docs/", "a record or a document. `lake` reads nothing under docs/, and a "
              "`.lean` under it would have been bucketed as `.lean` first."),
    (".github/", "chooses WHICH gates run. A workflow file is not an input to "
                 "`lake` and cannot move an elaboration reading."),
    (".githooks/", "a commit-message scrub. Never read by `lake`."),
    ("scripts/", "a gate or an analyser (the profiler and the budget registry are "
                 "bucketed ABOVE this rule). Such a script can reach a reading "
                 "only by REGENERATING a `.lean` file, and that regeneration is "
                 "itself a `.lean` diff, bucketed first."),
    ("README.md", "prose."),
    ("PROVENANCE.md", "prose."),
    ("TRUSTBASE.md", "prose."),
    (".gitignore", "inert."),
]


def _touches_list_has(path):
    """PROFILER_PATHS membership, as a function so an arm can assert it without
    re-typing the list — a second copy of a roster is a duplicate born in
    agreement. [[feedback-a-duplicate-born-in-agreement]]"""
    return path in PROFILER_PATHS


def exempt_reason(path):
    """The stated reason this path cannot move a kernel-time reading, or None."""
    for prefix, why in EXEMPT_RULES:
        if path == prefix or (prefix.endswith("/") and path.startswith(prefix)):
            return why
    return None


def _changed_paths(base, head):
    return [p for p in kd.git("diff", "--name-only", base, head).split("\n") if p.strip()]


def _touches(base, head, paths):
    return bool(kd.git("diff", "--name-only", base, head, "--", *paths).strip())


# ⛔⛔ THE JOIN WAS ON `base` ALONE, AND `head` WAS WRITTEN AND NEVER READ (D171).
# `gap()` said `if b in ledger: continue`, so ANY row whose base sat on the chain
# closed that base's step no matter what span it had actually priced. The path
# that produces a wrong one is the path this file's own usage line recommends:
# `--backfill` rows the CONSECUTIVE pairs of a walk's `order`, and the five-step
# backfill it reports is FOUR DISJOINT SPANS, so a single walk over all nine
# commits would write four correct rows and three bogus ones — whose bases are
# real chain commits, so the gap would have read CLOSED.
# [[feedback-a-join-on-a-lossy-key]]
#
# ⭐⭐ AND THE FIRST VERSION OF THIS CHECK WAS WRONG, WHICH IS HOW THE RULE BELOW
# GOT ITS SHAPE. Requiring `rec["head"] == h` refused TWO rows already in the
# committed ledger — and the object refuted the check, not the rows. The `--no-ff`
# landing ritual measures the BRANCH TIP and then writes the row INSIDE the merge
# commit, so the row's head is the merge's SECOND parent and the chain's child is
# the merge itself. Their trees are not equal either: they differ by exactly the
# ledger row the ritual just wrote.
# ⇒ 🔑 THE INVARIANT IS NOT THE COMMIT AND NOT THE TREE, IT IS THE READING. A
# reading is a function of the `.lean` sources and of the profiler; a row prices
# this step if what separates its head from the chain's child cannot move either.
# Measured on the real ledger: 11 rows name the child exactly, 2 are the ritual's
# shape, and the diff in both is `docs/delta-allowance-ledger.jsonl` alone.
# [[feedback-the-burden-is-on-the-departure]] [[feedback-inherited-diagnosis-is-a-hypothesis]]
def records_step(rec, base, head):
    """Does this ledger row price the step `base` → `head`?"""
    rh = rec.get("head")
    if not isinstance(rh, str) or not rh:
        return False
    if rh == head:
        return True
    # the ritual's shape, and NOT a general licence: the row's head must be
    # REACHABLE from the chain's child (so it is the merged branch, not some
    # other commit that happens to be cheap to diff against) ...
    if subprocess.run(["git", "merge-base", "--is-ancestor", rh, head],
                      cwd=ROOT, capture_output=True).returncode != 0:
        return False
    # ... and nothing between them may move a reading.
    return not _touches(rh, head, ["*.lean"] + PROFILER_PATHS)


def gap_anchor(ledger, head="HEAD"):
    """The EARLIEST ledger base that is on head's first-parent chain, or None.

    ⛔ Derived from the chain, never named by hand: an anchor written as a
    literal is a stale literal in the one check that measures staleness."""
    chain = kd.git("rev-list", "--first-parent", head).split()
    idx = [i for i, r in enumerate(chain) if r in ledger]
    return chain[max(idx)] if idx else None


def gap(ledger, head="HEAD"):
    """(anchor, steps, {bucket: [(base, head)]}) — the unrecorded first-parent
    steps, split by what a missing row actually costs."""
    anchor = gap_anchor(ledger, head)
    if anchor is None:
        refuse(f"⛔ no ledger row's `base` is on {head}'s first-parent chain, so "
               f"there is no anchor to measure a gap from. A ledger disjoint from "
               f"the branch it prices is not an empty gap — it is a wrong ledger.")
    steps = window_steps(anchor, head)
    out = {"lean": [], "profiler": [], "neither": [], "unclassified": []}
    for b, h in steps:
        # ⛔⛔ THE JOIN IS ON `base` AND `head`, NOT ON `base` ALONE (D171). This
        # read `if b in ledger: continue`, so a row whose `base` sits on the chain
        # marked its step recorded NO MATTER WHAT ITS `head` SAID — the `head`
        # field was written, stored, and never read. That is a join on a lossy
        # key: it prices one step with another's allowance and reads as an
        # ordinary row.
        # ⛔ AND THE PATH THAT PRODUCES IT IS THE ONE THIS FILE ASKS A HEAD TO
        # WALK. `--backfill` rows the CONSECUTIVE pairs of a walk's `order`, so a
        # walk covering four disjoint spans of the chain (which is exactly the
        # shape of the five-step backfill this gate reports) writes a correct row
        # for each span AND a bogus row across each gap between them. The bogus
        # rows' bases are real chain commits, so under the old join they closed
        # steps nobody measured — and the gap gate would have reported the
        # backfill complete. [[feedback-a-join-on-a-lossy-key]]
        rec = ledger.get(b)
        if rec is not None:
            if records_step(rec, b, h):
                continue
            refuse(f"⛔ ledger row for base {b[:9]} names head "
                   f"{str(rec.get('head'))[:9]}, which is neither this base's "
                   f"first-parent child {h[:9]} nor a commit reachable from it "
                   f"that differs only in the record. The row prices a span that "
                   f"is not this step — a WRONG row, not a recorded one. A "
                   f"`--backfill` walk whose `order` jumps between disjoint spans "
                   f"writes exactly this; backfill ONE CONTIGUOUS SPAN PER WALK.")
        if _touches(b, h, ["*.lean"]):
            out["lean"].append((b, h))
        elif _touches(b, h, PROFILER_PATHS):
            out["profiler"].append((b, h))
        else:
            # ⛔ EVERY path must be argued, not merely the step. One unrecognised
            # file in an otherwise-documentary commit is exactly the shape the
            # `else` used to swallow.
            unknown = [p for p in _changed_paths(b, h) if exempt_reason(p) is None]
            (out["neither"] if not unknown else out["unclassified"]).append((b, h))
    return anchor, steps, out


# ⛔ A CALLABLE SURFACE, DELIBERATELY. D162 (this same session) found a gate that
# shipped RED for four hours because it was an inline block in `main()` and a
# selftest has nothing to call. Writing the next gate the same way would be the
# defect surviving the sitting that named it.
# [[feedback-a-gate-is-not-exempt-from-its-own-defect]]
def read_ratchet(path):
    """The recorded ceiling, or None if the file is absent/unparseable — and the
    caller must tell those two apart, because an unparseable gate file reports
    FAILURE, not absence. [[feedback-an-unparseable-gate-file-reports-failure-not-absence]]"""
    if not os.path.exists(path):
        return None
    for line in open(path):
        if line.startswith("lean_missing_max"):
            parts = line.split()
            if len(parts) >= 2 and parts[1].lstrip("-").isdigit():
                return int(parts[1])
    return None


def judge_ratchet(nl, want, ledger_rel="docs/delta-allowance-ledger.jsonl"):
    """None when the gap is exactly the ceiling; the refusal text otherwise."""
    if nl > want:
        return (f"⛔ {nl} unrecorded `.lean` step(s) against a ceiling of {want}. "
                f"A batch landed WITHOUT its ledger row — the fix is the landing "
                f"ritual, not the ceiling:\n"
                f"     git merge --no-ff --no-commit <branch>\n"
                f"     python3 scripts/kernel_drift.py --record --readings <merge-gate json>\n"
                f"     git add {ledger_rel} && git commit\n"
                f"   so the row rides INSIDE the merge commit and needs no commit "
                f"of its own.")
    if nl < want:
        return (f"⛔ {nl} unrecorded `.lean` step(s) against a ceiling of {want} — "
                f"the gap SHRANK and the ratchet still claims the old slack, which "
                f"is where the next unrecorded landing would hide. Lower it: "
                f"`--gap --write-ratchet`, in the commit that earned it.")
    return None


def accumulated_allowance(steps, ledger, digest):
    """({unit: ms}, unpriced, rows) — the SUM of the per-step budgets.

    ⛔ Never k x one budget: each term is the allowance that step was entitled to
    against its own base, read from the row written when it merged."""
    missing = [s for s in steps if s[0] not in ledger]
    if missing:
        refuse(f"⛔ the ledger is missing {len(missing)} of {len(steps)} steps in this "
               f"window, so its allowance cannot be summed:\n" +
               "".join(f"   {b[:9]} → {h[:9]}\n" for b, h in missing) +
               f"   A missing step is not a cheaper window. Record it with --record "
               f"at merge, or --backfill it from a committed walk.")
    rows = [ledger[s[0]] for s in steps]
    for s, r in zip(steps, rows):
        if r.get("budget_digest") != digest:
            refuse(f"⛔ step {s[0][:9]}→{s[1][:9]} was priced against budget registry "
                   f"{r.get('budget_digest')} and this run reads {digest}. Summing "
                   f"allowances from two registries prices the window with a rule it "
                   f"was never judged by; re-record the window's steps.")
    # a unit must be priced at EVERY step or it is not priced for the window: the
    # gaps of a declared list all fall the way its default points, and here that
    # direction is a larger allowance nobody registered.
    per_step = [r["allowance"] for r in rows]
    everywhere = set(per_step[0]).intersection(*per_step[1:]) if per_step else set()
    anywhere = set().union(*per_step) if per_step else set()
    alloc = {u: sum(a[u] for a in per_step) for u in everywhere}
    unpriced = {u: sum(1 for a in per_step if u in a) for u in anywhere - everywhere}
    return alloc, unpriced, rows


# ══════════════════════════════════════════════════════════════════════════════
# THE VERDICT
# ══════════════════════════════════════════════════════════════════════════════
def unit_series(readings, decl_map):
    """{unit: [ms, ...]} over one side's readings, by the GATE's own flattening."""
    out = {}
    for r in readings:
        for u, v in kd.units_of(r, decl_map).items():
            out.setdefault(u, []).append(v)
    return out


def judge_window(series_base, series_head, alloc):
    rows = []
    for u in sorted(set(series_base) & set(series_head) & set(alloc)):
        j = kd.judge_delta(series_base[u], series_head[u], alloc[u])
        if j:
            j["unit"] = u
            rows.append(j)
    return rows


def report(rows, unpriced, steps, ledger_rows, alloc, series_base,
           default_ms, budgets, floor, quiet=False):
    """(rc, lines). Prints the flat allowance beside the summed one, because the
    difference between them is what this design turns on and a number no output
    carries is a claim no reader can check."""
    lines, k = [], len(steps)
    out = lines.append
    backfilled = sum(1 for r in ledger_rows
                     if str(r.get("source", "")).startswith("backfill"))
    out(f"── DRIFT over {k} batches  {steps[0][0][:9]} → {steps[-1][1][:9]}")
    out(f"   allowance = the SUM of {k} per-step budgets"
        f"{f' ({backfilled} backfilled, retrospective)' if backfilled else ''}")
    over = [r for r in rows if r["verdict"] == "OVER"]
    unmeas = [r for r in rows if r["verdict"] == "UNMEASURABLE"]
    # ⛔ THE `flat` COLUMN IS A CROSS-NIGHT COMPARISON AND MUST SAY SO. It is
    # k x the budget computed from THIS run's anchor profile, while `allow` sums
    # allowances priced on the nights those steps merged. The ratio therefore
    # carries the difference between those nights as well as the trees' growth,
    # and a reader who takes it for the growth alone is reading a join on a lossy
    # key. The clean measurement of the two spellings is D154 §2, computed inside
    # ONE walk. Only `allow` reaches the verdict; `flat` is a diagnostic.
    # [[feedback-two-readings-are-not-two-witnesses]] [[feedback-a-join-on-a-lossy-key]]
    out(f"   ⚠️  `flat` = k x the budget from THIS run's anchor; `allow` was priced "
        f"on the steps' own nights — their ratio is not growth alone.")
    out(f"   {'unit':<46} {'delta':>10} {'band':>9} {'allow':>10} {'flat':>10} "
        f"{'sum/flat':>8}  verdict")
    for r in sorted(rows, key=lambda r: -(r["margin"])):
        base_med = statistics.median(series_base[r["unit"]])
        flat = k * kd.effective(budgets.get(r["unit"], default_ms), base_med, floor)
        ratio = (r["budget"] / flat) if flat > 0 else float("nan")
        mark = {"OVER": "⛔ OVER", "UNMEASURABLE": "⚠️  UNMEASURABLE",
                "ok": "   ok"}[r["verdict"]]
        if quiet and r["verdict"] == "ok":
            continue
        out(f"   {r['unit']:<46} {r['d']:>10.1f} {r['band']:>9.1f} "
            f"{r['budget']:>10.1f} {flat:>10.1f} {ratio:>8.3f}  {mark}")
    if unpriced:
        out(f"   ⚠️  {len(unpriced)} unit(s) UNPRICED over this window and therefore "
            f"NOT judged here — each is priced by the per-batch gate:")
        for u, n in sorted(unpriced.items()):
            out(f"      {u:<46} present at {n}/{k} steps")
    out(f"   {len(rows)} judged · {len(over)} OVER · {len(unmeas)} UNMEASURABLE · "
        f"{len(unpriced)} unpriced")
    out(f"   {kd.box_stamp()}")
    if over:
        out("⛔ DRIFT FAILED — accumulated kernel time over the window exceeds the sum "
            "of the budgets those batches were entitled to. The per-batch gate passed "
            "each of them; this is what it could not see.")
        rc = 1
    elif unmeas:
        out("⚠️  DRIFT UNMEASURABLE on some units — the band straddles the accumulated "
            "allowance. That is a statement about this run, not about the window.")
        rc = 3
    else:
        out("✅ DRIFT CLEAN over the window.")
        rc = 0
    return rc, lines


# ══════════════════════════════════════════════════════════════════════════════
# SELFTEST — the control runs FIRST, and every plant is sized in closed form
# ══════════════════════════════════════════════════════════════════════════════
DIG = "0123456789abcdef"


# ⭐⭐ WHAT A WALK'S LOAD MEANS, PRICED FROM COMMITTED EVIDENCE RATHER THAN FELT.
# A backfilled allowance is a PERCENTAGE OF THE MEASURED base_ms, so a loud box
# inflates the allowance with the reading, and the inflation is in the direction
# that makes the drift window convict LESS. "load1 was 20" is a number a reader
# cannot act on; the factor is.
# ⛔ THE REFERENCE IS DERIVED FROM COMMITTED WALKS, NOT A LITERAL — two walks over
# the SAME twelve commits at different loads are already in `docs/`, which is the
# second source the factor needs. Measured 09/06: quiet (load1 median 4.51) → 12.27
# is x1.14 median (p90 1.35), → 13.72 is x1.18 (p90 1.55), and EVERY unit's ratio
# exceeds 1 — load makes nothing faster.
# ⛔ AND IT IS PRINTED, NEVER GATED. A threshold on load average is the heuristic
# D141 took out of this family of gates; this is a reading beside a reading.
# [[feedback-a-measurement-without-its-conditions]] [[feedback-conservative-is-a-direction-not-a-margin]]
LOAD_REFERENCE = [("docs/kernel-delta-history-2026-09-04.jsonl", "the quiet walk"),
                  ("docs/kernel-delta-history-USER-CONTENDED-2026-09-05.jsonl",
                   "the contended walk")]


def load_context(walk_rows):
    """Lines describing this walk's load beside the committed reference walks."""
    loads = [r.get("load1") for r in walk_rows if r.get("load1") is not None]
    if not loads:
        return ["⚠️  this walk's readings carry no `load1`, so its conditions "
                "cannot be stated — not 'it was quiet'."]
    out = [f"walk load1: median {statistics.median(loads):.2f}, "
           f"max {max(loads):.2f}, over {len(loads)} reading(s)"]
    for path, what in LOAD_REFERENCE:
        full = os.path.join(ROOT, path)
        if not os.path.exists(full):
            out.append(f"   ⚠️  {path} is absent, so {what} cannot be quoted — "
                       f"the comparison is MISSING, not favourable.")
            continue
        rl = [json.loads(l).get("load1") for l in open(full) if l.strip()]
        rl = [x for x in rl if x is not None]
        if rl:
            out.append(f"   vs {what}: load1 median {statistics.median(rl):.2f} "
                       f"({os.path.basename(path)})")
    out.append("   ⇒ a backfilled allowance is a PERCENTAGE OF THE MEASURED "
               "base_ms, so a louder box buys a LARGER allowance. Measured "
               "across these committed walks the shift is x1.14-x1.18 median "
               "(p90 1.35-1.55) and no unit gets faster, so a window priced on "
               "a loud box convicts LESS than one priced quiet.")
    return out


def _row(base, head, alloc, base_ms=None, digest=DIG, source="synthetic",
         conditions=None):
    # ⭐ `conditions` (D171): the per-pass (load1, secs) of the run that produced
    # this row, plus its drift. A row keeps MEDIANS, and medians cannot show that
    # a run drifted — which is exactly the defect this session found in the arm
    # that reads them. Absent rather than empty when the readings predate the pass
    # stamp: an invented order would print a drift figure that looks measured.
    r = {"base": base, "head": head, "allowance": dict(alloc),
         "base_ms": dict(base_ms or alloc), "budget_digest": digest,
         "source": source, "t": 0, "box": "synthetic"}
    if conditions is not None:
        r["conditions"] = conditions
    return r


def _steps(n):
    # ⛔ DISTINGUISHABLE IN THE FIRST NINE CHARACTERS, because every refusal in
    # this file names a step by `sha[:9]`. Sequential integers rendered as 40 hex
    # digits are all `000000000` there, and an arm asserting that a refusal names
    # the missing step would pass while it named the wrong one.
    shas = [hashlib.sha1(str(i).encode()).hexdigest() for i in range(n + 1)]
    return [(shas[i], shas[i + 1]) for i in range(n)]


def _series(level, spread, n, drift=0.0):
    """n readings around `level`, spread fixed so the band is reproducible."""
    return [level + drift + (spread if i % 2 else -spread) for i in range(n)]


def selftest():
    fails, caught, arms = [], [], []

    # `plant` is the arm's SHORT NAME, appended when it fires. The summary joins
    # them, so the list of what this selftest catches is derived from the arms
    # that ran and cannot go stale against a hand-written sentence.
    def ok(cond, what, plant=None):
        print(f"  {'✔' if cond else '✘'} {what}")
        arms.append(what)
        if not cond:
            fails.append(what)
        elif plant:
            caught.append(plant)

    # ── THE CONTROL, FIRST. A harness that reds everything reds every plant too,
    # and a plant probe whose control was never run has told you nothing.
    # [[feedback-a-plant-probes-control-comes-first]]
    print("CONTROL — an unplanted window must be CLEAN and must fire no arm:")
    st = _steps(4)
    led = {s[0]: _row(*s, {"M": 100.0}) for s in st}
    alloc, unpriced, rows_l = accumulated_allowance(st, led, DIG)
    sb = {"M": _series(1000.0, 5.0, 4)}
    sh = {"M": _series(1000.0, 5.0, 4, drift=10.0)}
    rows = judge_window(sb, sh, alloc)
    ok(alloc == {"M": 400.0}, "the accumulated allowance is the SUM of 4 steps (400)")
    ok(rows and rows[0]["verdict"] == "ok" and not unpriced,
       "a clean window is `ok`, with nothing unpriced")

    # ── A. THE ALLOWANCE ARITHMETIC ────────────────────────────────────────────
    print("\nA. THE ALLOWANCE — the sum of the per-step budgets, never k x one:")
    # A GROWING tree: each step is entitled to 10% of a base that rises 100→800.
    # sum = 10+20+40+80 = 150 ; k x anchor = 4 x 10 = 40.  The delta is placed
    # BETWEEN them, so the two spellings give OPPOSITE verdicts on one reading.
    bases = [100.0, 200.0, 400.0, 800.0]
    grow = {s[0]: _row(*s, {"G": 0.10 * b}, base_ms={"G": b})
            for s, b in zip(st, bases)}
    a_sum, _, _ = accumulated_allowance(st, grow, DIG)
    flat = 4 * 0.10 * bases[0]
    ok(abs(a_sum["G"] - 150.0) < 1e-9 and abs(flat - 40.0) < 1e-9,
       f"a growing window sums to {a_sum['G']:.0f} where k x anchor is {flat:.0f} "
       f"({a_sum['G'] / flat:.2f}x)")
    gb = {"G": _series(1000.0, 2.0, 4)}
    gh = {"G": _series(1000.0, 2.0, 4, drift=90.0)}     # 40 < 90 < 150
    v_sum = judge_window(gb, gh, a_sum)[0]["verdict"]
    v_flat = judge_window(gb, gh, {"G": flat})[0]["verdict"]
    ok(v_sum == "ok" and v_flat == "OVER",
       f"a delta of 90 is `{v_sum}` against the summed allowance and `{v_flat}` "
       f"against k x one budget — the flat spelling CONVICTS what the window was "
       f"entitled to spend", plant="flat-allowance conviction")

    # ⛔ THE OTHER DIRECTION, AND IT IS 12.3% OF THE REAL CORPUS. A window whose
    # trees SHRINK is entitled to LESS than k x the anchor's budget, so there the
    # flat spelling is too GENEROUS and lets accumulated drift through. Planting
    # only the growing case would have left the arm above reading as "the sum is
    # the larger number", which is false in an eighth of cases.
    # [[feedback-naming-a-defect-is-not-finding-its-siblings]]
    shrink = {s[0]: _row(*s, {"S": 0.10 * b}, base_ms={"S": b})
              for s, b in zip(st, reversed(bases))}
    a_shr, _, _ = accumulated_allowance(st, shrink, DIG)
    flat_s = 4 * 0.10 * bases[-1]
    sb_s = {"S": _series(1000.0, 2.0, 4)}
    sh_s = {"S": _series(1000.0, 2.0, 4, drift=200.0)}     # 150 < 200 < 320
    v_shr = judge_window(sb_s, sh_s, a_shr)[0]["verdict"]
    v_flt = judge_window(sb_s, sh_s, {"S": flat_s})[0]["verdict"]
    ok(a_shr["S"] < flat_s and v_shr == "OVER" and v_flt == "ok",
       f"a SHRINKING window sums to {a_shr['S']:.0f} where k x anchor is "
       f"{flat_s:.0f}: a delta of 200 is `{v_shr}` on the sum and `{v_flt}` on the "
       f"flat spelling — the flat gate is too GENEROUS here, not too tight",
       plant="flat-allowance acquittal")

    # THE POSITIVE CONTROL FOR THAT ARM: where the budget is FLOOR-BOUND the two
    # spellings must agree EXACTLY. Without this, the arm above is satisfied by a
    # gate that simply always takes the larger number.
    # [[feedback-a-control-can-share-the-blind-spot]]
    floorb = {s[0]: _row(*s, {"F": 6.0}, base_ms={"F": b}) for s, b in zip(st, bases)}
    a_fl, _, _ = accumulated_allowance(st, floorb, DIG)
    ok(a_fl["F"] == 4 * 6.0,
       "a FLOOR-BOUND unit sums to exactly k x the floor (24) — the two spellings "
       "agree where they must, so the arm above is not 'always take the larger'")

    # ── B. THE LEDGER REFUSES RATHER THAN INVENTING ────────────────────────────
    print("\nB. THE LEDGER — a gap is a refusal, not a zero:")
    for tag, what, mutate in (
        ("missing step", "a MISSING step refuses and names it",
         lambda d: d.pop(st[2][0])),
        ("foreign registry", "a step priced against a DIFFERENT budget registry refuses",
         lambda d: d.__setitem__(st[1][0], _row(*st[1], {"M": 100.0}, digest="beef"))),
    ):
        d = dict(led)
        mutate(d)
        try:
            accumulated_allowance(st, d, DIG)
            ok(False, what, plant=tag)
        except SystemExit as e:
            ok(e.code == 2, what, plant=tag)
    # ...and the positive control: the UNMUTATED ledger must NOT refuse, or every
    # refusal above is the harness refusing and not the rule.
    try:
        accumulated_allowance(st, led, DIG)
        ok(True, "...and the complete, consistent ledger does NOT refuse")
    except SystemExit:
        ok(False, "...and the complete, consistent ledger does NOT refuse")

    # a unit absent from SOME steps is UNPRICED and REPORTED — never silently
    # dropped, and never given the whole window's allowance from a partial sum.
    part = dict(led)
    part[st[1][0]] = _row(*st[1], {"M": 100.0, "P": 50.0})
    a_p, unp, _ = accumulated_allowance(st, part, DIG)
    ok("P" not in a_p and unp.get("P") == 1,
       "a unit present at 1 of 4 steps is UNPRICED and counted, not summed to a "
       "partial allowance", plant="partial pricing")

    # ⛔ THE REFUSAL MUST LAND BEFORE THE WRITE. The first spelling of --record
    # appended the rows and THEN re-read the file to check them, so a conflicting
    # record left the bad row on disk and every later run refused until a human
    # edited the ledger. A gate that corrupts its own store and then declines to
    # work is worse than one that simply declines.
    with tempfile.TemporaryDirectory() as td:
        lp = os.path.join(td, "led.jsonl")
        append_rows(lp, [_row(*st[0], {"M": 100.0}, source="first")], {})
        before = open(lp).read()
        try:
            append_rows(lp, [_row(*st[0], {"M": 999.0}, source="second")],
                        load_ledger(lp))
            ok(False, "a conflicting record REFUSES BEFORE writing",
               plant="write-before-check")
        except SystemExit as e:
            ok(e.code == 2 and open(lp).read() == before,
               "a conflicting record REFUSES and leaves the ledger BYTE-UNCHANGED",
               plant="write-before-check")
        append_rows(lp, [_row(*st[1], {"M": 100.0})], load_ledger(lp))
        ok(len(load_ledger(lp)) == 2,
           "...and a NON-conflicting step still appends, so the arm above is the "
           "conflict and not a store that never writes")

    # ── B2. THE DERIVATION GATE — THE ONE THAT HAD NO ARM UNTIL TODAY ─────────
    # ⛔⛔ `--verify-ledger` shipped RED on master for four hours (found 09/06) and
    # NOTHING said so: it was an inline block in `main()`, so there was no
    # function for an arm to call, and the 18 green arms above were about the
    # ARITHMETIC while reading as though they were about the FILE.
    # ⭐ EVERY LEDGER BELOW IS WRITTEN WITH `append_rows` AND READ WITH
    # `load_ledger` — the shipped producer and consumer — so the key shape under
    # test comes from the artifact and never from this test's own hand. Had this
    # section built its dict directly, it would have adopted whatever key D161
    # chose and agreed with the bug.
    # [[feedback-a-gate-is-not-exempt-from-its-own-defect]]
    # [[feedback-a-duplicate-born-in-agreement]]
    print("\nB2. THE DERIVATION GATE — a written ledger, read back by the shipped "
          "reader:")
    TAG = "backfill:walk.jsonl"
    vst = _steps(3)
    vwant = {b: (h, {"M": 100.0, "N": 40.0}) for b, h in vst}

    def _written(rows):
        """rows → a ledger dict, THROUGH the file and the shipped reader."""
        d = tempfile.mkdtemp()
        lp = os.path.join(d, "led.jsonl")
        append_rows(lp, rows, {})
        return load_ledger(lp)

    good = [_row(b, h, {"M": 100.0, "N": 40.0}, source=TAG) for b, h in vst]
    ok(verify_ledger(vwant, _written(good), TAG, DIG) == [],
       "CONTROL FIRST — a ledger that IS its derivation reports NO discrepancy "
       "(this is the arm master was failing)")

    def red(rows, want, needle, what, plant):
        bad = verify_ledger(want, _written(rows), TAG, DIG)
        ok(bool(bad) and any(needle in b for b in bad),
           f"{what} — refused naming `{needle}`" if bad else what, plant=plant)

    red([_row(b, h, {"M": 100.0 + (11.0 if i == 1 else 0.0), "N": 40.0},
              source=TAG) for i, (b, h) in enumerate(vst)],
        vwant, "M: ledger 111.0 vs derived 100.0",
        "a hand-edited ALLOWANCE is caught, and the message names the unit and "
        "both numbers", "edited allowance")
    red(good[:2], vwant, "ABSENT from the ledger",
        "a step the walk derives but the ledger lacks is ABSENT, not a cheaper "
        "window", "missing step")
    red(good + [_row(_steps(9)[8][0], _steps(9)[8][1], {"M": 100.0, "N": 40.0},
                     source=TAG)],
        vwant, "not a step of that walk",
        "a surplus row UNDER THE SAME TAG is caught — a ledger may not carry a "
        "backfilled step the walk does not contain", "surplus row")
    red([_row(b, h, {"M": 100.0, "N": 40.0}, digest="deadbeefdeadbeef",
              source=TAG) for b, h in vst],
        vwant, "priced against registry",
        "a row priced against a FOREIGN budget registry is caught", "foreign registry")
    # ⭐ THE FIELD D161 DEMOTED. `head` is audit-only to the verdict, which is
    # exactly why nothing else would report it rotting.
    red([_row(b, "0" * 40, {"M": 100.0, "N": 40.0}, source=TAG) for b, h in vst],
        vwant, "head: ledger 000000000",
        "a row whose audit-only `head` disagrees with the walk is caught",
        "rotted head")
    # ⛔ AND THE ARM THAT DECIDES WHETHER A LIVE ROW CAN EVER BE RECORDED. The
    # first `--record` at a merge writes `source="gate"`; if this gate counted it
    # as a surplus row, the ledger could hold backfill OR live rows but never
    # both, and the 48-commit backfill would be unable to coexist with the
    # landing ritual that ends it. NEGATIVE CONTROL, and it is load-bearing.
    live = _row(_steps(9)[7][0], _steps(9)[7][1], {"M": 1.0}, source="gate")
    ok(verify_ledger(vwant, _written(good + [live]), TAG, DIG) == [],
       "a LIVE `source=gate` row beside the backfill is INVISIBLE to this gate, "
       "so the two kinds of row coexist")
    # ...and its positive control, or the arm above only proves the tag filter
    # rejects everything. [[feedback-a-probe-must-create-its-condition]]
    ok(bool(verify_ledger(vwant, _written(good + [dict(live, source=TAG)]),
                          TAG, DIG)),
       "...while THE SAME ROW re-tagged as backfill IS caught, so the arm above "
       "is the tag and not a filter that matches nothing", plant="tag filter")

    # ── B3. THE GAP AND ITS RATCHET (D164) ────────────────────────────────────
    # ⛔ The ratchet is what makes `--no-ff` survive a head who forgets, so it is
    # the one gate here whose FAILURE MODE IS SILENCE — it must be driven in both
    # directions or its green means only that nobody landed anything.
    print("\nB3. THE GAP — measured on the REAL first-parent chain, and its "
          "ratchet driven BOTH ways:")
    real = load_ledger(LEDGER)
    g_anchor, g_steps, g_buckets = gap(real, "HEAD")
    n_missing = sum(len(v) for v in g_buckets.values())
    n_recorded = len(g_steps) - n_missing
    ok(g_anchor in {b for b, _ in g_steps} | {g_steps[0][0]},
       "CONTROL — the anchor is a step boundary on the walked chain, not a name "
       "written down somewhere")
    # ⛔ AN INVARIANT, NOT A LITERAL. The chain grows with every commit, so an arm
    # asserting `51` would be red by tomorrow and would be *edited* rather than
    # read. [[feedback-a-gate-is-not-exempt-from-its-own-defect]]
    ok(n_recorded + n_missing == len(g_steps) and n_recorded == len(real),
       f"the {len(g_buckets)} buckets PARTITION the unrecorded steps — "
       f"{n_recorded} recorded + {n_missing} missing = {len(g_steps)} steps, and "
       f"every ledger row is used exactly once")
    # a ledger disjoint from the branch is a WRONG ledger, not an empty gap.
    try:
        gap({("f" * 40): _row("f" * 40, "e" * 40, {"M": 1.0})}, "HEAD")
        ok(False, "a ledger with no base on the chain REFUSES", plant="no anchor")
    except SystemExit as e:
        ok(e.code == 2, "a ledger with no base on the chain REFUSES rather than "
                        "reporting a gap of zero", plant="no anchor")
    # ⭐ THE POSITIVE CONTROL FOR THE BUCKETS: a ledger recording EVERY step must
    # empty them, or "5 in the lean bucket" might be a classifier that always says
    # 5. [[feedback-a-probe-must-create-its-condition]]
    full = {b: _row(b, h, {"M": 1.0}) for b, h in g_steps}
    _, _, empt = gap(full, "HEAD")
    ok(all(not v for v in empt.values()),
       f"...and a ledger recording EVERY step empties all {len(empt)} buckets, so the "
       "counts are about the ledger and not a constant", plant="full ledger")
    # ...and removing ONE known `.lean` step must put exactly one back.
    # ⛔⛔ THIS ARM AND THE ONE BELOW USED TO READ `g_buckets["lean"]` — the
    # UNRECORDED `.lean` steps — and on 09/06 the five-step backfill emptied that
    # bucket and BOTH ARMS SILENTLY STOPPED RUNNING. The suite stayed green and
    # its arm count went UP; the only thing that said so was the DISTINCT-PLANT
    # list losing two entries. An arm whose precondition is "the repository is
    # currently in arrears" is an arm that switches off exactly when the work it
    # guards has been done.
    # ⇒ the subject is now every `.lean`-changing step ON THE CHAIN, recorded or
    # not, which is a property of the history and cannot be discharged.
    # [[feedback-a-gate-whose-precondition-is-a-discipline]]
    # [[feedback-probe-silence-has-two-causes]]
    lean_steps = [(b, h) for b, h in g_steps if _touches(b, h, ["*.lean"])]
    ok(bool(lean_steps),
       f"CONTROL — the chain carries {len(lean_steps)} `.lean`-changing step(s) "
       f"for the two arms below to use, independently of what the ledger records")
    # ⛔ AND IT MUST NOT BE THE ANCHOR'S OWN STEP. `gap_anchor` takes the EARLIEST
    # ledger base on the chain, so deleting that row does not open a gap — it moves
    # the window forward and EVERY bucket reads zero. The re-armed form of this arm
    # picked the first `.lean` step, which IS the anchor, and went red for that
    # reason rather than for a defect.
    lean_pick = next((p for p in reversed(lean_steps) if p[0] != g_anchor), None)
    ok(lean_pick is not None,
       "CONTROL — a `.lean` step exists that is NOT the anchor's own, so the arm "
       "below tests a GAP rather than a moved window")
    if lean_pick:
        one = dict(full)
        del one[lean_pick[0]]
        _, _, b1 = gap(one, "HEAD")
        ok(len(b1["lean"]) == 1 and not b1["profiler"] and not b1["neither"]
           and not b1["unclassified"],
           "...and deleting ONE row for a `.lean`-changing step puts exactly that "
           "step, in that bucket, back", plant="one lean step")

    # ⚠️ THE BEHAVIOUR THE ARM ABOVE TRIPPED OVER, RECORDED SO IT IS KNOWN RATHER
    # THAN REDISCOVERED: losing the EARLIEST row does not report a gap. The window
    # simply starts later and every bucket reads zero — a narrowed observation does
    # not say "unknown", it says "nothing unrecorded".
    # [[feedback-unobserved-regions-report-agreement]]
    _noanchor = dict(full)
    del _noanchor[g_anchor]
    _a2, _s2, _b2 = gap(_noanchor, "HEAD")
    ok(_a2 != g_anchor and not any(_b2.values()) and len(_s2) < len(g_steps),
       f"KNOWN BEHAVIOUR — deleting the ANCHOR's row moves the window "
       f"({g_anchor[:9]} → {_a2[:9]}, {len(g_steps)} → {len(_s2)} steps) and every "
       f"bucket reads zero: a coverage LOSS that looks like a clean gap. `--gap` "
       f"prints the anchor and the commits before it for that reason",
       plant="anchor row deleted")

    # ── THE JOIN: `base` AND `head`, DRIVEN BOTH WAYS (D171) ──────────────────
    # ⛔ Every commit below is DERIVED from the live chain, never typed: an arm
    # naming a sha is an arm that stops being about this branch.
    ritual = [(b, h, real[b]) for b, h in g_steps
              if b in real and real[b].get("head") != h]
    ok(all(records_step(r, b, h) for b, h, r in ritual),
       f"CONTROL — the {len(ritual)} row(s) written by the `--no-ff` landing "
       f"ritual ARE accepted: their head is the merge's second parent, reachable "
       f"from the chain's child and separated from it by no `.lean` and no "
       f"profiler path")
    ok(all(_touches(r["head"], h, ["*.lean"] + PROFILER_PATHS) is False
           for b, h, r in ritual),
       "...and accepted FOR THAT REASON — the separating diff moves no reading — "
       "rather than by a sha comparison that happened to hold")
    if lean_pick:
        lb, lh = lean_pick
        ok(not records_step({"head": lb}, lb, lh),
           "RED-FIRST — a row whose head is separated from the chain's child by a "
           "`.lean` diff does NOT record the step, even though it is reachable",
           plant="head short of a .lean step")
    if len(g_steps) > 2:
        b0, h0 = g_steps[0]
        ok(not records_step({"head": g_steps[-1][1]}, b0, h0),
           "RED-FIRST — a row whose head is NOT reachable from the chain's child "
           "does not record the step, however small the diff",
           plant="head off the span")
    ok(not records_step({}, "x", "y") and not records_step({"head": None}, "x", "y")
       and not records_step({"head": ""}, "x", "y"),
       "RED-FIRST — a row with a missing, null or empty head records NOTHING; an "
       "absent field must not read as a match", plant="headless row")

    # ── THE CONDITIONS A ROW CARRIES (D171, queue item 3) ─────────────────────
    _fake = {"decl_map": {}, "readings": {
        "base": [{"modules": {"M": 100.0 + 10 * i}, "decls": {}, "load1": 1.0,
                  "secs": 9, "pass": p, "side": "base"}
                 for i, p in enumerate((1, 4, 5, 8))],
        "head": [{"modules": {"M": 105.0 + 10 * i}, "decls": {}, "load1": 2.0,
                  "secs": 9, "pass": p, "side": "head"}
                 for i, p in enumerate((2, 3, 6, 7))]}}
    c = kd.pass_conditions(_fake)
    ok(c.get("passes") and [p["pass"] for p in c["passes"]] == [1, 2, 3, 4, 5, 6, 7, 8],
       "CONTROL — the conditions summary orders passes by their STAMPED global "
       "index, across both sides, not by the order they sit in the readings dict")
    # ⛔ THE EXPECTED SLOPE IS THE EXACT ONE, NOT A TOLERANCE AROUND A GUESS. The
    # first form of this arm asserted `|slope - 10*4/7| < 2.0`; the true least
    # squares slope of the planted series is 200/42 = 4.762, and 10*4/7 = 5.714 —
    # so the arm PASSED on a wrong prediction that its own tolerance was wide
    # enough to hide. Computed from the plant instead, and asserted to 1e-9.
    # [[feedback-a-confirmed-prediction-is-not-a-checked-statistic]]
    _pts = sorted([(r["pass"], r["modules"]["M"])
                   for side in ("base", "head") for r in _fake["readings"][side]])
    _mx = statistics.mean([p for p, _ in _pts])
    _my = statistics.mean([v for _, v in _pts])
    _want = (sum((p - _mx) * (v - _my) for p, v in _pts)
             / sum((p - _mx) ** 2 for p, _ in _pts))
    ok(c.get("drift", {}).get("ms_per_pass") is not None
       and abs(c["drift"]["ms_per_pass"] - round(_want, 3)) < 1e-9,
       f"...and it recovers the planted drift EXACTLY: "
       f"{c.get('drift', {}).get('ms_per_pass')} ms/pass on "
       f"`{c.get('drift', {}).get('worst_unit')}`, against {_want:.6f} computed "
       f"from the plant and stored at 3 dp", plant="planted drift")
    _stripped = {"decl_map": {}, "readings": {
        "base": [{k: v for k, v in r.items() if k != "pass"}
                 for r in _fake["readings"]["base"]],
        "head": [{k: v for k, v in r.items() if k != "pass"}
                 for r in _fake["readings"]["head"]]}}
    c2 = kd.pass_conditions(_stripped)
    ok(c2.get("passes") is None and "pre-D171" in c2.get("why", ""),
       "RED-FIRST — readings with NO pass stamp report ABSENT with a reason, not "
       "an invented order and a drift figure that would look measured",
       plant="unstamped readings")
    ok("conditions" not in _row("a", "b", {"M": 1.0})
       and _row("a", "b", {"M": 1.0}, conditions=c)["conditions"] is c,
       "...and a row written without conditions OMITS the key rather than "
       "carrying an empty one that reads as 'measured, and quiet'")

    # ── EVERY BACKFILLED ROW IS DERIVED, NOT JUST THE NAMED WALK'S (D174) ─────
    # ⛔ READ FROM THE SHIPPED REGISTRY, not from a synthetic one: this arm's
    # subject is the COMMITTED ledger, so its digest and budgets must be the ones
    # the committed rows were priced against, or every row would read "priced
    # against another registry" and the arm would be about the fixture.
    _bf = kd.BUDGET_FILE
    _default_ms, _budgets, _floor = kd.read_budgets(_bf)
    _digest = budget_digest(_bf)
    _dm = kd.gated_declarations()
    _bad, _checked, _live, _tags, _nrows = verify_ledger_all(
        real, _dm, _default_ms, _budgets, _floor, _digest)
    _bfill = sum(len(v) for t, v in _tags.items() if t.startswith("backfill:"))
    ok(not _bad and _nrows == _bfill and _bfill > 0,
       f"CONTROL — every one of the {_bfill} backfilled ledger row(s), across "
       f"{len(_checked)} walk(s), re-derives from the walk IT names "
       f"({_nrows} checked)")
    ok(len(_checked) >= 2,
       f"...and it followed {len(_checked)} distinct walks, so the arm is not one "
       f"filename wearing a plural — a single-walk ledger could not tell them apart")
    ok(sum(len(_tags[t]) for t in _live) + _bfill == len(real),
       f"...and the {sum(len(_tags[t]) for t in _live)} non-backfill row(s) are "
       f"NAMED rather than dropped: named + derived = {len(real)}, the whole ledger")
    # ⛔ THE ROW WHOSE EVIDENCE IS GONE. A committed allowance whose walk has been
    # deleted can never be re-derived, and under a gate told ONE filename it would
    # simply never be looked at.
    _bad2, _, _, _, _ = verify_ledger_all(real, _dm, _default_ms, _budgets, _floor,
                                          _digest, docs_dir="/nonexistent-docs-dir")
    ok(_bad2 and all("evidence for a committed row is gone" in b for b in _bad2),
       "RED-FIRST — a backfilled row whose walk is MISSING refuses and says the "
       "evidence is gone, rather than passing unexamined", plant="walk deleted")

    # ── THE LOAD CONTEXT (D174) — including the branch a missing file takes ───
    lc = load_context([{"load1": 10.0}, {"load1": 20.0}])
    ok(lc and "median 15.00" in lc[0] and "max 20.00" in lc[0],
       "CONTROL — the load context reports this walk's own median and max")
    ok(sum(1 for l in lc if " vs " in l) == len(LOAD_REFERENCE),
       f"CONTROL — it quotes all {len(LOAD_REFERENCE)} committed reference walk(s), "
       f"so the factor has a second source and not a remembered number")
    lc2 = load_context([{"secs": 9}, {"secs": 9}])
    ok(len(lc2) == 1 and "cannot be stated" in lc2[0] and "not 'it was quiet'" in lc2[0],
       "RED-FIRST — readings with NO load1 say the conditions cannot be stated, "
       "rather than printing nothing (which reads as quiet)", plant="no load1")
    _real = LOAD_REFERENCE[:]
    try:
        globals()["LOAD_REFERENCE"] = [("docs/does-not-exist.jsonl", "a gone walk")]
        lc3 = load_context([{"load1": 1.0}])
    finally:
        globals()["LOAD_REFERENCE"] = _real
    ok(any("MISSING, not favourable" in l for l in lc3),
       "RED-FIRST — an ABSENT reference walk is reported as a missing comparison, "
       "not silently dropped so the walk looks unremarkable",
       plant="absent reference")

    # ── THE EXEMPTION ARGUMENT, DRIVEN BOTH WAYS (D171) ───────────────────────
    # ⛔ The bucket these arms guard used to be an `else`, so there was nothing to
    # drive: every path was exempt and the arm would have been "does the default
    # still default". The rules are an allowlist now, so each direction is real.
    ok(all(w.strip() for _, w in EXEMPT_RULES) and len(EXEMPT_RULES) >= 4,
       f"CONTROL — every one of the {len(EXEMPT_RULES)} exemption rules carries a "
       f"stated reason (a rule with no reason is an `else` wearing a name)")
    ok(exempt_reason("docs/DECISIONS.md") is not None
       and exempt_reason("scripts/ci_local.py") is not None
       and exempt_reason(".github/workflows/ci.yml") is not None,
       "CONTROL — the three path shapes the real window is made of ARE argued, so "
       "the arms below cannot pass by the rules matching nothing")
    # ⛔ THE FALSIFIERS. Each of these moves EVERY unit's reading and touches no
    # `.lean` file, which is exactly the combination the old `else` sent to
    # "exempt". They must not be exempt.
    falsifiers = ["lean-toolchain", "lake-manifest.json", "vendor/blas.c",
                  "Tests/generated.txt", "toolchain/leanc"]
    unargued = [p for p in falsifiers if exempt_reason(p) is None]
    ok(len(unargued) == len(falsifiers),
       "RED-FIRST — a toolchain pin, a manifest, a vendored source and an "
       "unrecognised artifact are ALL unargued: " + ", ".join(unargued),
       plant="falsifier paths")
    ok(exempt_reason("lean-toolchain") is None
       and _touches_list_has("lean-toolchain"),
       "...and `lean-toolchain` is ALSO named in PROFILER_PATHS, so it is priced "
       "as moving the reading rather than merely refused as unknown",
       plant="toolchain in PROFILER_PATHS")
    # ⛔ AND THE COMPOSITION, not only the predicate: a step whose diff carries one
    # unargued path must leave the exempt bucket even when every other path in it
    # is argued. One unrecognised file in a documentary commit is the shape.
    if g_buckets["neither"]:
        victim = g_buckets["neither"][0]
        real_paths = _changed_paths
        try:
            globals()["_changed_paths"] = (
                lambda b, h: (real_paths(b, h) + ["vendor/sneaky.c"])
                if (b, h) == victim else real_paths(b, h))
            _, _, planted = gap(real, "HEAD")
        finally:
            globals()["_changed_paths"] = real_paths
        ok(victim in planted["unclassified"] and victim not in planted["neither"]
           and len(planted["unclassified"]) == 1,
           "RED-FIRST — ONE unargued path in an otherwise fully-argued step moves "
           "that step, and only that step, out of EXEMPT and into UNCLASSIFIED",
           plant="one unargued path")
    _, _, live = gap(real, "HEAD")
    ok(not live["unclassified"],
       f"...and with nothing planted the real window has 0 unclassified steps, so "
       f"the arm above measured the plant and not a standing red")
    # ── the ratchet, both directions, and its unparseable case ────────────────
    ok(judge_ratchet(5, 5) is None, "CONTROL — gap == ceiling is silent")
    ok("landed WITHOUT its ledger row" in (judge_ratchet(6, 5) or ""),
       "a gap ABOVE the ceiling refuses and names the landing ritual, not a wider "
       "ceiling", plant="ratchet up")
    ok("gap SHRANK" in (judge_ratchet(4, 5) or ""),
       "a gap BELOW the ceiling ALSO refuses — slack is where the next unrecorded "
       "landing hides, so the rot is policed in both directions",
       plant="ratchet down")
    with tempfile.TemporaryDirectory() as td:
        rp = os.path.join(td, "r.txt")
        ok(read_ratchet(rp) is None, "an ABSENT ratchet reads None")
        open(rp, "w").write(RATCHET_HEADER + "lean_missing_max 7\n")
        ok(read_ratchet(rp) == 7, "...and a written one reads back its number, so "
                                  "the arm above is absence and not a reader that "
                                  "always returns None", plant="ratchet roundtrip")
        open(rp, "w").write(RATCHET_HEADER + "lean_missing_max\n")
        ok(read_ratchet(rp) is None, "a ratchet whose line has NO number reads as "
                                     "unparseable — which the caller must refuse "
                                     "on, never treat as absent", plant="ratchet unparseable")

    # ── C. THE ANCHOR IS PROFILED, NEVER READ FROM THE LEDGER ──────────────────
    print("\nC. THE ANCHOR — re-profiled every run, and the ledger's readings are "
          "dead to the verdict:")
    # ONE pair of readings, judged against three ledgers that differ ONLY in the
    # fields under test. `gb`/`gh` are used because their delta (90) is resolvable
    # against their band (~4): a delta the band swallows can never be convicted by
    # ANY allowance, so it cannot witness that the allowance was read.
    big = {s[0]: _row(*s, {"G": 100.0}) for s in st}                      # sum 400
    pois = {s[0]: _row(*s, {"G": 100.0}, base_ms={"G": 10_000.0}) for s in st}
    small = {s[0]: _row(*s, {"G": 10.0}) for s in st}                     # sum  40
    a_big, _, _ = accumulated_allowance(st, big, DIG)
    a_pois, _, _ = accumulated_allowance(st, pois, DIG)
    a_small, _, _ = accumulated_allowance(st, small, DIG)
    v_big = judge_window(gb, gh, a_big)[0]["verdict"]
    v_pois = judge_window(gb, gh, a_pois)[0]["verdict"]
    v_small = judge_window(gb, gh, a_small)[0]["verdict"]
    ok(a_pois == a_big and v_pois == v_big,
       f"the ledger's `base_ms` perturbed 10x moves NOTHING (`{v_pois}`) — the "
       f"delta comes from this run's profile, never from a recorded reading",
       plant="dead base_ms")
    # ⛔ and its positive control, or the silence above proves only that nothing
    # reads the ledger at all. [[feedback-a-probe-must-create-its-condition]]
    ok(v_big == "ok" and v_small == "OVER",
       f"...while perturbing `allowance` alone moves the SAME readings from "
       f"`{v_big}` to `{v_small}`, so the arm above is a fact about the field and "
       f"not about a ledger nobody reads")

    # ── D. DETECTION, ON A PLANT, WITH THE FLIP POINT STATED FIRST ─────────────
    # ⛔ The corpus cannot supply this: every commit in it landed, so it is over
    # budget nowhere and the k-curve measures REFUSAL, never DETECTION.
    print("\nD. DETECTION — a plant over budget every batch, flip point predicted "
          "BEFORE the run:")
    # ⛔ SIZED SO THE FLIP IS NOT AT k=2. With a surplus that clears the band in
    # one step there is exactly ONE sub-flip observation, and 'not convicted
    # below k' rests on a single cell. The surplus here is a fraction of the
    # band, so three windows sit below the flip and each is checked.
    per_step_alloc, over_per_step, spread, n = 10.0, 15.0, 8.0, 4
    band = kd.K_SIGMA * kd.resolution(_series(1000.0, spread, n),
                                      _series(1000.0, spread, n))
    # OVER needs  d - band > alloc, with d = k*over and alloc = k*per_step:
    #   k*(over - per_step) > band  =>  k > band / (over - per_step)
    predicted = int(math.floor(band / (over_per_step - per_step_alloc))) + 1
    print(f"     band={band:.2f}  surplus/batch={over_per_step - per_step_alloc:.1f}"
          f"  ⇒ PREDICTED first conviction at k={predicted}")
    seen = {}
    for k in range(1, predicted + 2):
        stk = _steps(k)
        ledk = {s[0]: _row(*s, {"D": per_step_alloc}) for s in stk}
        ak, _, _ = accumulated_allowance(stk, ledk, DIG)
        db = {"D": _series(1000.0, spread, n)}
        dh = {"D": _series(1000.0, spread, n, drift=k * over_per_step)}
        seen[k] = judge_window(db, dh, ak)[0]["verdict"]
    ok(all(seen[k] != "OVER" for k in range(1, predicted)),
       f"below the predicted k the plant is NOT convicted "
       f"({', '.join(f'k={k}:{seen[k]}' for k in range(1, predicted))})", plant="sub-flip silence")
    ok(seen[predicted] == "OVER",
       f"...and it IS convicted at exactly the predicted k={predicted}", plant="at-flip conviction")
    # the null arm: the same window with NO drift must stay `ok` at that k, or
    # "convicted at k" is just "everything converts once the window is long".
    stk = _steps(predicted)
    ledk = {s[0]: _row(*s, {"D": per_step_alloc}) for s in stk}
    ak, _, _ = accumulated_allowance(stk, ledk, DIG)
    v_null = judge_window({"D": _series(1000.0, spread, n)},
                          {"D": _series(1000.0, spread, n)}, ak)[0]["verdict"]
    ok(v_null == "ok",
       f"...while a NULL window of the same length is `{v_null}` — the conviction "
       f"is the drift, not the window")

    # ── E. THE BAND ────────────────────────────────────────────────────────────
    print("\nE. THE BAND — one reading a side cannot estimate its own noise:")
    v1 = judge_window({"M": [1000.0]}, {"M": [1500.0]}, alloc)[0]
    ok(v1["verdict"] == "UNMEASURABLE" and v1["band"] == float("inf"),
       "a single reading a side is UNMEASURABLE (infinite band), never silently "
       "decided — a 500 ms delta against a 400 ms allowance included", plant="single-reading refusal")

    print()
    if fails:
        print(f"⛔ drift-gate selftest: {len(fails)} FAILED")
        for f in fails:
            print(f"   ✘ {f}")
        return 1
    print(f"  {len(arms)} arms, {len(arms) - len(fails)} green; {len(caught)} "
          f"DISTINCT arms caught a plant: {', '.join(caught)}")
    print(f"drift-gate selftest: CLEAN — the ARITHMETIC and the LEDGER only, with "
          f"NO measurement in any arm. A green here says nothing about whether the "
          f"profiler can see a code change; that is the per-batch gate's "
          f"--selftest-measure.")
    return 0


# ══════════════════════════════════════════════════════════════════════════════
def main():
    if "--selftest" in sys.argv:
        return selftest()
    budget_file = kd.arg("--budget", kd.BUDGET_FILE)
    default_ms, budgets, floor = kd.read_budgets(budget_file)
    decl_map = kd.gated_declarations()
    digest = budget_digest(budget_file)
    ledger_path = kd.arg("--ledger", LEDGER)

    # ⭐ THE LEDGER IS DERIVED, AND THIS IS WHAT SAYS SO. Same discipline as the
    # budget file: re-derive every backfilled allowance from the committed walk
    # and require equality, so a hand-edited allowance cannot ride in under a
    # generated header. It compares the NUMBERS, not the bytes, because `t` and
    # `box` are provenance and legitimately differ per append.
    # ⚠️ WHAT IT PROVES AND WHAT IT DOES NOT: that the file matches its
    # derivation, never that the derivation is right. The rule is one line —
    # `effective(budget, that step's own base, floor)` — and it is stated here so
    # it can be corrected rather than only recomputed.
    # [[feedback-a-derivation-gate-wraps-a-false-sentence]]
    # ⛔⛔ `--verify-ledger <ONE FILE>` VERIFIED A SUBSET AND PRINTED A COMPLETE
    # SENTENCE (D174). It filters the ledger by `source == backfill:<that file>`,
    # so rows written from any OTHER walk are not examined — and it says
    # "✅ ledger DERIVED: 11 steps ... equal to the committed ledger", which reads
    # as a statement about the ledger. It is a statement about 11 of its rows.
    # Adding five rows from four new walks left them derivable by nothing, and the
    # CI step names the ONE walk file by literal, so it would never have grown.
    # ⇒ 🔑 THE LEDGER'S OWN ROWS NAME THEIR EVIDENCE in `source`. The gate follows
    # that pointer instead of being told a filename, so a walk added tomorrow is
    # covered without editing the workflow, and a row whose walk is GONE refuses
    # rather than passing unexamined.
    # [[feedback-a-complete-count-of-a-subset]]
    # [[feedback-a-gate-named-by-a-literal-stops-seeing-renamed-work]]
    if "--verify-ledger-all" in sys.argv:
        ledger = load_ledger(ledger_path)
        bad, checked, live, tags, n_rows = verify_ledger_all(
            ledger, decl_map, default_ms, budgets, floor, digest)
        if bad:
            refuse(f"⛔ the ledger is not what its own derivation produces "
                   f"({len(bad)} discrepancies):\n" + "\n".join(bad[:40]) +
                   f"\n   Regenerate with --backfill; do not edit it.")
        print(f"✅ ledger DERIVED, EVERY BACKFILLED ROW: {n_rows} row(s) across "
              f"{len(checked)} walk(s) re-derived and equal to the committed "
              f"ledger, against registry {digest}.")
        for tag, n in checked:
            print(f"     {n:2d} row(s)  {tag}")
        for t in sorted(live):
            print(f"     {len(tags[t]):2d} row(s)  source={t!r} — NOT derivable "
                  f"from a walk (the merge gate's own readings); named here "
                  f"rather than excluded from the sentence above")
        return 0

    walk_v = kd.arg("--verify-ledger")
    if walk_v:
        import delta_repair_price as drp
        w = drp.load_walk(walk_v)
        ur = drp.unit_readings(w, decl_map)
        order = w["order"]
        ledger = load_ledger(ledger_path)
        tag = f"backfill:{os.path.basename(walk_v)}"
        want = {}
        for i in range(len(order) - 1):
            med = {u: statistics.median(v) for u, v in ur[order[i]].items()}
            want[order[i]] = (order[i + 1],
                              allowances_for(med, default_ms, budgets, floor))
        bad = verify_ledger(want, ledger, tag, digest)
        if bad:
            refuse(f"⛔ the ledger is not what its own derivation produces "
                   f"({len(bad)} discrepancies):\n" + "\n".join(bad[:40]) +
                   f"\n   Regenerate it with --backfill; do not edit it.")
        n_u = sum(len(a) for _, a in want.values())
        # ⛔ THE SCOPE IS IN THE SENTENCE NOW. This verifies the rows tagged with
        # THIS walk and no others; without the count of what it left alone, an
        # 11-of-18 check reads as a whole-ledger receipt (D174).
        others = sum(1 for r in load_ledger(ledger_path).values()
                     if r.get("source") != tag)
        print(f"✅ ledger DERIVED: {len(want)} steps x {n_u // max(len(want), 1)} units "
              f"= {n_u} allowances re-derived from {os.path.basename(walk_v)} and "
              f"equal to the committed ledger, against registry {digest}.")
        print(f"⚠️  SCOPE: {others} further ledger row(s) carry a DIFFERENT source "
              f"and were not examined here. Use --verify-ledger-all, which "
              f"follows each row's own `source` and covers all of them.")
        return 0

    # ⭐⭐ THE LANDING RITUAL'S GATE (D164). It does NOT judge kernel time; it
    # judges whether the ledger is still being kept. Gated on ONE bucket — the
    # steps that change `.lean` — because that is the quantity ORDINARY WORK
    # DOES NOT MOVE: a docs commit grows the chain and this number stays put, so
    # the gate is not a chore, and a batch landed without a row moves it by one
    # and goes red. [[feedback-match-the-gate-units-to-the-growth-law]]
    # ⛔ BOTH DIRECTIONS REFUSE. A ceiling that only complains upward rots
    # upward: a backfill that removes four holes leaves a ratchet claiming four
    # holes that are gone, and the next unrecorded landing hides inside the
    # slack. Lowering it is one line, in the commit that earned it.
    # [[feedback-under-claims-are-unpoliced]]
    if "--gap" in sys.argv:
        ledger = load_ledger(ledger_path)
        anchor, steps, buckets = gap(ledger, kd.arg("--head", "HEAD"))
        nl, npr, nn = (len(buckets["lean"]), len(buckets["profiler"]),
                       len(buckets["neither"]))
        nu = len(buckets["unclassified"])
        print(f"── DRIFT GAP from anchor {anchor[:9]} over {len(steps)} "
              # ⛔ `nu` WAS MISSING FROM THIS SUBTRACTION when the fourth bucket
              # was added, so `recorded` counted the unclassified steps as
              # recorded. Invisible while nu == 0, which is every day until the
              # one it matters. [[feedback-a-ratio-survives-a-doubling]]
              f"first-parent step(s); {len(steps) - nl - npr - nn - nu} recorded, "
              f"{nl + npr + nn + nu} not"
              # ⛔ AND THE COMMITS BEFORE THE ANCHOR ARE OUTSIDE THIS AUDIT.
              # Losing the earliest row does not open a gap, it SHRINKS the
              # window; a coverage loss nobody prints looks exactly like a pass.
              + (f"\n   ⚠️  {len(kd.git('rev-list', '--first-parent', anchor).splitlines()) - 1}"
                 f" commit(s) precede the anchor and are OUTSIDE this audit"))
        print(f"   {nl:3d}  change a `.lean` file          ⇐ GATED: each needs a real "
              f"measurement")
        for b, h in buckets["lean"]:
            print(f"        {b[:9]} → {h[:9]}  {kd.git('log', '--format=%s', '-1', h)[:66]}")
        print(f"   {npr:3d}  change no `.lean` but DO change {' or '.join(PROFILER_PATHS)}")
        print(f"        ⚠️  these move the READING or the ALLOWANCE without moving "
              f"the code, so 'nothing to price' is FALSE for them")
        print(f"   {nn:3d}  EXEMPT — every path argued by a rule in EXEMPT_RULES")
        seen = {}
        for b, h in buckets["neither"]:
            for p in _changed_paths(b, h):
                why = exempt_reason(p)
                seen.setdefault(why, set()).add(p)
        for why, ps in sorted(seen.items(), key=lambda kv: -len(kv[1])):
            print(f"        · {len(ps):2d} path(s) — {why}")
            print(f"          {', '.join(sorted(ps)[:6])}"
                  + (f", … (+{len(ps)-6})" if len(ps) > 6 else ""))
        print(f"   {nu:3d}  UNCLASSIFIED                   "
              + ("⛔ NOT exempt — see below" if nu else
                 "✅ nothing unargued; the exemption is an allowlist, not an `else`"))
        for b, h in buckets["unclassified"]:
            unknown = [p for p in _changed_paths(b, h) if exempt_reason(p) is None]
            print(f"        ⛔ {b[:9]} → {h[:9]}  unargued: {', '.join(unknown[:5])}")
        # ⛔ NO RATCHET HERE, DELIBERATELY. A ratchet exists so a gate on a
        # quantity the WORK consumes is not a chore; the correct number of
        # un-argued exemptions is ZERO and stays zero, so a ceiling would only
        # be somewhere for one to hide. [[feedback-match-the-gate-units-to-the-growth-law]]
        if nu:
            refuse(f"⛔ {nu} step(s) touch a path no rule in EXEMPT_RULES argues "
                   f"about. They are NOT exempt: an unrecognised path is where a "
                   f"toolchain pin, a vendored input or a new generated artifact "
                   f"would arrive, and each of those moves every reading. Add a "
                   f"rule WITH ITS REASON to EXEMPT_RULES, or price the step.")
        ratchet_p = kd.arg("--ratchet", RATCHET)
        if "--write-ratchet" in sys.argv:
            with open(ratchet_p, "w") as f:
                f.write(RATCHET_HEADER + f"lean_missing_max {nl}\n")
            print(f"\n✅ ratchet ← {nl} → {ratchet_p}")
            return 0
        if not os.path.exists(ratchet_p):
            refuse(f"⛔ no ratchet at {ratchet_p}. A gap with no recorded ceiling "
                   f"is not a passing gate, it is an unarmed one; write it with "
                   f"--write-ratchet in the commit that earns the number.")
        want = read_ratchet(ratchet_p)
        if want is None:
            refuse(f"⛔ {ratchet_p} carries no parseable `lean_missing_max` line. "
                   f"An unparseable gate file reports FAILURE, never absence.")
        msg = judge_ratchet(nl, want, os.path.relpath(ledger_path, ROOT))
        if msg:
            refuse(msg)
        print(f"\n✅ drift gap: {nl} unrecorded `.lean` step(s), exactly the "
              f"ceiling in {os.path.basename(ratchet_p)}.")
        return 0

    if "--record" in sys.argv or "--backfill" in sys.argv:
        rows = []
        saved = kd.arg("--readings")
        if saved:
            data = json.load(open(saved))
            base_units = {}
            for r in data["readings"]["base"]:
                for u, v in kd.units_of(r, data.get("decl_map", decl_map)).items():
                    base_units.setdefault(u, []).append(v)
            med = {u: statistics.median(v) for u, v in base_units.items()}
            rows.append(_row(data["base_rev"], data["head_rev"],
                             allowances_for(med, default_ms, budgets, floor),
                             base_ms=med, digest=digest, source="gate",
                             conditions=kd.pass_conditions(data)))
        walk = kd.arg("--backfill")
        if walk:
            import delta_repair_price as drp
            w = drp.load_walk(walk)
            ur = drp.unit_readings(w, decl_map)
            order = w["order"]
            for i in range(len(order) - 1):
                med = {u: statistics.median(v) for u, v in ur[order[i]].items()}
                # ⛔ THE BACKFILL'S CONDITIONS HAVE A DIFFERENT SHAPE AND SAY SO.
                # A walk visits each commit once per SWEEP, so its readings are
                # not the gate's alternating passes; and two sweeps give two
                # points per commit, from which a slope is not a drift
                # measurement. The `why` field states that instead of leaving the
                # key absent, because an absent key reads as "not applicable" and
                # a blank one reads as "measured, and quiet".
                # [[feedback-a-tool-has-no-concept-of-not-applicable]]
                rows.append(_row(order[i], order[i + 1],
                                 allowances_for(med, default_ms, budgets, floor),
                                 base_ms=med, digest=digest,
                                 source=f"backfill:{os.path.basename(walk)}",
                                 conditions={
                                     "passes": [{"sweep": r.get("sweep"),
                                                 "load1": round(r.get("load1", 0.0), 2),
                                                 "secs": r.get("secs")}
                                                for r in w["by"][order[i]]],
                                     "why": "walk sweeps, not gate passes; too "
                                            "few points per commit for a drift "
                                            "slope"}))
        if walk:
            for l in load_context(w["rows"]):
                print("   " + l)
        for r in rows:
            r["t"] = int(time.time())
            r["box"] = kd.box_stamp()
        append_rows(ledger_path, rows, load_ledger(ledger_path))
        print(f"ledger ← {len(rows)} step(s) → {ledger_path}")
        return 0

    anchor = kd.arg("--anchor")
    if not anchor:
        print(__doc__)
        return 2
    head = kd.arg("--head", "HEAD")
    steps = window_steps(anchor, head)
    ledger = load_ledger(ledger_path)
    alloc, unpriced, ledger_rows = accumulated_allowance(steps, ledger, digest)
    print(f"── DRIFT: re-profiling the anchor {steps[0][0][:9]} and the head "
          f"{steps[-1][1][:9]} in ONE session ({len(steps)} batches)")
    data = kd.measure(steps[0][0], head, int(kd.arg("--repeats", "3")))
    sb = unit_series(data["readings"]["base"], data["decl_map"])
    sh = unit_series(data["readings"]["head"], data["decl_map"])
    rows = judge_window(sb, sh, alloc)
    rc, lines = report(rows, unpriced, steps, ledger_rows, alloc, sb,
                       default_ms, budgets, floor)
    print("\n".join(lines))
    return rc


if __name__ == "__main__":
    sys.exit(main())
