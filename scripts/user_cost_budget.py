#!/usr/bin/env python3
"""QUEUE ITEM 4d — CAN THE CHILD'S `user` CPU CARRY THE MERGE GATE?  (D151)

⭐⭐ WHY THIS EXISTS.  The kernel-delta gate reads the profiler's cumulative
`type checking` time.  D141/D142/D150 measured what that instrument can resolve:
the SAME COMMIT on both sides invented a −2,150 ms delta against a 1,980 ms
budget and returned `ok`, and five profiles of ONE unchanged tree spanned 22,500
ms against a 1,764 ms budget.  D150 then found a quantity that was in every pass
already — `kernel_cost.py` runs one `lean` process per module, so
`getrusage(RUSAGE_CHILDREN)` is a PER-UNIT CPU time at zero extra cost — and
measured it 14.6x tighter on ONE tree.

⛔ THIS SCRIPT DOES NOT GATE ANYTHING, AND THAT RESTRAINT IS THE ITEM.  `user`
charges ELABORATION AND KERNEL where the gated number charges the kernel alone,
so it is a DIFFERENT QUANTITY and not a better reading of the same one.  Before
it can carry a budget it owes: a SECOND SOURCE for that budget (never the runs
that recommended it), and a second machine for the portability claim.
[[feedback-widening-a-gate-needs-a-second-source]]

## THE SECOND SOURCE, AND WHY IT IS THIS CORPUS

The budgets in `scripts/kernel_delta_budget.txt` were derived by
`kernel_delta_history.py --register-budget` from a twelve-commit walk of the
project's OWN history (`docs/kernel-delta-history-2026-09-04.jsonl`).  This
script reads a re-run of THAT SAME WALK over THOSE SAME TWELVE COMMITS with the
CPU fields recorded (`docs/kernel-delta-history-USER-CONTENDED-2026-09-05.jsonl`).

⛔ THAT PATH READ `…-USER-2026-09-05.jsonl` UNTIL 2026-09-09, AND NO SUCH FILE HAS
EVER EXISTED IN THIS REPOSITORY (`git log --all --diff-filter=A` over
`docs/kernel-delta-history-USER*` adds exactly two: `USER2` and `USER-CONTENDED`).
D151's own conditions paragraph records the rename that stranded it — "the corpus
is named `…-CONTENDED-…` rather than labelled by hand" — and this docstring kept
the pre-rename name.  ⇒ WHICH corpus it means was decided by SCORING, not by
reading the label: D151 publishes "contended corpus, 14 readings", and this tool
reports 14 readings on `USER-CONTENDED` and 24 on `USER2`.  Found by
`scripts/check_corpus_claims.py`, the gate written for exactly this class after
`b5d1522`.  [[feedback-only-the-contract-says-which-file]]

⚠️ AND THE NEAR-MISS BESIDE IT, because it is the same defect one step further on.
Reading this tool's own "2 tree(s) with repeated readings" line for CONTENDED, I
was about to file a SECOND defect — that "THOSE SAME TWELVE COMMITS" is false of
it too.  Counted directly, CONTENDED carries **12 distinct commits**: sweep 0 is
complete at 12 and sweep 1 was interrupted at 2, which is why only two trees have
a repeated reading.  "Trees with REPEATED readings" is not "distinct commits", so
the sentence is TRUE.  A right-shaped measurement about the wrong object, caught
by counting rather than by re-reading.
[[feedback-a-partial-corpus-carries-its-interruption]]

So the candidate's budgets come from batch history, exactly as the shipped ones did,
and NOT from `docs/threads-ab-2026-09-05.jsonl` — the readings that nominated
`user` in the first place.

## ⛔ THE RULE IS IMPORTED, NOT RE-IMPLEMENTED

`budget_info()` lives in `kernel_delta_history.py` and is called here with a
different quantity extractor.  D148 §2 recorded what happens otherwise: a
referee invented beside a shipped rule was LOOSER than the gate it refereed and
disagreed in the flattering direction.  One rule, two quantities, so a
difference in the answers is a difference in the QUANTITIES.
[[feedback-widening-a-gate-needs-a-second-source]]
[[feedback-a-derivation-gate-wraps-a-false-sentence]]

## ⭐ THE THIRD ARM IS A CONTROL, NOT A CANDIDATE

`real_s` — the same child's wall-clock — is scored beside `user_s` because the
two answer different questions about WHERE any improvement comes from:

    if `real_s` is as tight as `user_s`  ⇒ the gain is measuring the WHOLE
        PROCESS instead of trusting the profiler's internal attribution, and it
        would survive on any machine.
    if `real_s` is much noisier          ⇒ the gain is CPU ACCOUNTING being
        robust to contention, which is a claim about this box's load and is
        exactly what a second machine would have to confirm.

Without it, "user is tighter" is a fact with two incompatible mechanisms and no
way to tell which one a second machine would reproduce.
[[feedback-score-the-null-model]] [[feedback-a-single-reading-is-about-its-run]]

usage: user_cost_budget.py --readings FILE [--baseline FILE] [--decl-names a,b,c]
       --baseline is an EARLIER walk over the same commits; it re-measures the
       SHIPPED quantity only, so the two corpora are a matched pair for that arm
       and their difference is a difference between two DAYS on one box.
"""
import os, sys, json, statistics

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import kernel_delta_history as kdh

DECL_DEFAULT = "memDestSweep,pre_states_have_a_returnable_frame,vectorCoverage"


def arg(name, default=None):
    for i, a in enumerate(sys.argv):
        if a == name and i + 1 < len(sys.argv):
            return sys.argv[i + 1]
    return default


# ⚠️ THE CANDIDATE CANNOT EXPRESS EVERY GATED UNIT, AND THAT IS A STRUCTURAL
# FACT ABOUT THE INSTRUMENT, NOT A GAP IN THIS CORPUS.  `getrusage` accounts per
# PROCESS; `kernel_cost.py` runs one process per MODULE; so there is no
# per-DECLARATION CPU time to be had.  Four of the twenty-three gated units are
# sub-module (`Tests.Coverage @decl x3` and `@residue`) and no re-run of any walk
# will ever supply them.  A table that silently omitted those rows would report
# agreement about units nobody measured.
# [[feedback-unobserved-regions-report-agreement]]
def ms_units(reading, decl_names):
    """The SHIPPED quantity: profiler `type checking`, modules AND declarations."""
    return kdh.units(reading, decl_names)


def cpu_units(field):
    """A candidate quantity from the `cpu` block, in ms, MODULES ONLY."""
    def f(reading, decl_names):
        cpu = reading.get("cpu")
        if not cpu:
            return {}
        return {m: v[field] * 1000.0 for m, v in cpu.items() if v.get(field) is not None}
    return f


# ⛔⛔ THE RELATIVE SPREAD ALONE WOULD FLATTER THE CANDIDATE, AND THE MECHANISM
# IS ARITHMETIC.  `user` charges elaboration AND kernel, so on `Tests.Coverage`
# it is a ~57,000 ms number where the gated one is ~25,000 ms.  If the two
# carried the SAME absolute noise, the candidate's relative spread would be 2.3x
# smaller for free — an improvement wholly manufactured by a larger denominator,
# and one that no percentage can reveal.  So both spreads are computed and both
# are printed: the ABSOLUTE column is what says whether the instrument is
# genuinely steadier, and the RELATIVE column is what the budgets are written
# in.  A candidate that wins only on the relative column has not won.
# [[feedback-a-ratio-survives-a-doubling]]
# [[feedback-a-normalisation-needs-its-denominator-to-vary-the-same-way]]
def spread_table(rows, extract, decl_names, absolute=False):
    """Per unit: the within-commit spread, relative (%) or absolute (ms).

    ⭐ THIS IS THE HEAD-TO-HEAD THE CORPUS EXISTS FOR.  The two sweeps read the
    SAME TREE about twenty minutes apart, so the difference between them is the
    instrument's own repeatability over the interval that actually separates two
    sides of a delta — measured on TWELVE trees, where D150 had one."""
    order, per = [], {}
    for r in rows:
        per.setdefault(r["commit"], []).append(r)
        if r["commit"] not in order:
            order.append(r["commit"])
    out = {}
    for c in order:
        us = [extract(r, decl_names) for r in per[c]]
        for k in set().union(*[set(u) for u in us]) if us else []:
            vals = [u[k] for u in us if k in u]
            if len(vals) > 1 and statistics.median(vals) > 0:
                rng = max(vals) - min(vals)
                out.setdefault(k, []).append(
                    rng if absolute else 100.0 * rng / statistics.median(vals))
    return out


def level_table(rows, extract, decl_names):
    """Per unit: the median LEVEL, so an absolute spread can be read in scale."""
    per = {}
    for r in rows:
        for k, v in extract(r, decl_names).items():
            per.setdefault(k, []).append(v)
    return {k: statistics.median(v) for k, v in per.items()}


# ⭐⭐⭐ THE TRANSFER RATIO, AND WHY IT IS NOT A DIAGNOSTIC BUT AN INPUT.
#
# MDR (below) prices each arm as `budget% x level` and compares the answers in
# milliseconds.  That comparison carries an ASSUMPTION, stated in the code when
# it was written: that X ms of extra kernel work adds about X ms to the child's
# CPU time, so the two arms' millisecond scales are the same scale.
#
# ⛔ THE FIRST RUN THAT PRINTED BOTH REFUTED IT.  Measured over the pairs whose
# ms move clears the noise floor, `Δuser / Δms` came out at **9.23**, not 1.0 —
# a real change moves the child's CPU by several times the milliseconds it moves
# the profiler's `type checking`, because it moves ELABORATION too.  A candidate
# whose budget is 3x larger but which hears the signal 9x louder is MORE
# sensitive, not less, and the uncorrected table said the opposite.
#
# ⇒ the deciding column is `MDR / transfer` — the smallest change measured in the
# SHIPPED arm's own units that each arm would notice.  The raw column is kept
# beside it because the correction is an estimate with real spread and the reader
# must see both.  [[feedback-audit-the-premise-of-a-right-decision]]
# [[feedback-the-burden-is-on-the-departure]]
def transfer_ratios(metas, shipped, cand, units_, noise_abs):
    """({unit: Δcand/Δms}, used, dropped, skipped, flipped) over LIVE pairs.

    ⛔ A UNIT WITH NO MEASURED NOISE IS SKIPPED, NOT GIVEN A FLOOR OF ZERO.  The
    first version wrote `noise_abs.get(u, [0.0])`, so a unit with only one
    reading per commit — no repeatability data at all — got a floor of 0 and
    every pair, including pure noise, was accepted as signal.  A default fills a
    gap in the direction nobody polices, and here it manufactured transfer ratios
    out of noise for exactly the units the corpus knows least about.
    [[feedback-a-declared-list-inherits-its-default]]

    ⛔ AND A NEGATIVE RATIO IS A FINDING, NOT SOMETHING TO `abs()` AWAY.  It means
    the two instruments disagree about the DIRECTION of a real change — the
    candidate went down where the gated number went up.  Dividing an MDR by its
    magnitude would turn that into a confident correction.  Such units are
    reported as flipped and left without a ratio."""
    ms, cd = metas.get(shipped), metas.get(cand)
    if not ms or not cd:
        return {}, 0, 0, 0, []
    out, used, dropped, skipped, flipped = {}, 0, 0, 0, []
    for u in units_:
        floor = noise_abs.get(u)
        if not floor:
            skipped += 1
            continue
        rs = []
        for a, b in zip(ms["seq"], ms["seq"][1:]):
            if b in ms["zero_lean"]:
                continue
            aa, ba = ms["med"][a].get(u), ms["med"][b].get(u)
            ab, bb = cd["med"][a].get(u), cd["med"][b].get(u)
            if None in (aa, ba, ab, bb):
                continue
            d_ms, d_c = ba - aa, bb - ab
            if abs(d_ms) <= max(floor):
                dropped += 1
                continue
            rs.append(d_c / d_ms)
            used += 1
        if rs:
            m = statistics.median(rs)
            if m <= 0:
                flipped.append(u)
            else:
                out[u] = m
    return out, used, dropped, skipped, flipped


# ⭐⭐ THE SELFTEST, AND THE TWO ARMS THAT MAKE THE ABSOLUTE COLUMN REAL.
#
# The report above claims two things a reader cannot check by reading it: that
# the budgets come from the SHIPPED rule (not a copy), and that a candidate which
# is tighter only because its numbers are BIGGER will be visibly so.  Both are
# planted.  The synthetic corpora use the repository's REAL commit ids, because
# `budget_info` asks `git diff` which pairs changed no `.lean` file, and against
# invented shas that question returns empty and every pair reads as a no-op —
# a corpus whose control column is silently fabricated.
# [[feedback-a-probe-must-create-its-condition]]
REAL_COMMITS = ["144e9a3", "4f6766b", "76cb51b", "3769ea0", "0f929e3", "320cb45"]


# ⛔⛔ THE FIXTURES CARRY A **SPIKE**, NOT A UNIFORM RAMP, AND THE REASON IS
# STRUCTURAL — I found it by failing to write them without one.
#
# The corrected MDR needs two things of a corpus AT ONCE: a budget dominated by
# NOISE (otherwise `cand%` is just the median step, and MDR/transfer cancels to
# `2 x step_ms` for BOTH arms — every unit reads "no difference" and the table
# decides nothing), and at least one pair whose ms move CLEARS the noise floor
# (otherwise no transfer ratio exists to correct by).  With a UNIFORM step those
# two demands contradict each other: noise-dominated means noise > step, and the
# floor needs step > noise.
#
# Real batch history is not uniform — most commits barely move a unit and a few
# move it a lot — so the fixture is shaped the same way: flat, with ONE spike.
# The flat part sets the budget from noise; the spike measures the transfer.
# A fixture that could not reproduce that shape would have been testing an
# instrument no real corpus can drive.
# [[feedback-a-control-can-share-the-blind-spot]]
def _fake_rows(level_ms, noise_ms, level_user, noise_user,
               step_ms=1.0, step_user=None, spike_at=None,
               spike_ms=0.0, spike_user=0.0, lonely_unit=False,
               reexport_unit=False):
    """Two sweeps over six real commits, with the noise AND the signal placed by
    hand.  `step_*` is the per-commit increment — the SIGNAL — so a fixture can
    make the candidate carry the whole change (`step_user == step_ms`) or be
    partly deaf to it."""
    if step_user is None:
        step_user = step_ms
    import subprocess as sp
    shas = [sp.run(["git", "rev-parse", c], cwd=ROOT, capture_output=True,
                   text=True).stdout.strip() for c in REAL_COMMITS]
    rows = []
    for sweep in (0, 1):
        for i, sha in enumerate(shas):
            # the same tree reads level ± noise/2 between the two sweeps
            sgn = 1 if sweep == 0 else -1
            rows.append({
                "commit": sha, "sweep": sweep, "load1": 1.0, "load5": 1.0,
                "modules": {"M": level_ms + sgn * noise_ms / 2.0 + i * step_ms
                                 + (spike_ms if (spike_at is not None and i >= spike_at) else 0.0)},
                "decls": {}, "missing": [],
                "cpu": {"M": {"user_s": (level_user + sgn * noise_user / 2.0 + i * step_user
                                         + (spike_user if (spike_at is not None and i >= spike_at) else 0.0)) / 1000.0,
                              "sys_s": 0.0,
                              "real_s": (level_user + sgn * noise_user / 2.0 + i * step_user
                                         + (spike_user if (spike_at is not None and i >= spike_at) else 0.0)) / 1000.0}},
            })
            if reexport_unit:
                # ⛔ a pure re-export module: it type-checks NOTHING, so the
                # SHIPPED arm reads 0.0 ms, while the candidate still records the
                # CPU the `lean` process burned importing. Without this unit no
                # fixture can tell "the candidate cannot express it" apart from
                # "the shipped arm has no base", which is the pair that gave two
                # different inexpressible counts in one report.
                rows[-1]["modules"]["R"] = 0.0
                rows[-1]["cpu"]["R"] = {"user_s": 0.2, "sys_s": 0.0, "real_s": 0.2}
            if lonely_unit and sweep == 0:
                # ⛔ a unit present in ONE sweep only: it has a LEVEL but no
                # measurable noise, which is the gap the floor default used to
                # fill with zero.
                rows[-1]["modules"]["Z"] = 5000.0 + i * 500.0
                rows[-1]["cpu"]["Z"] = {"user_s": (5000.0 + i * 500.0) / 1000.0,
                                        "sys_s": 0.0,
                                        "real_s": (5000.0 + i * 500.0) / 1000.0}
    return rows


def _run_on(rows, extra=()):
    import tempfile, subprocess as sp
    fd, p = tempfile.mkstemp(prefix="x86lean-ucb-", suffix=".jsonl")
    with os.fdopen(fd, "w") as fh:
        for r in rows:
            fh.write(json.dumps(r) + "\n")
    try:
        r = sp.run([sys.executable, os.path.abspath(__file__), "--readings", p, *extra],
                   capture_output=True, text=True)
        return r.returncode, r.stdout + r.stderr
    finally:
        os.unlink(p)


def selftest():
    bad = []

    def arm(ok, name):
        print(("  ✔ " if ok else "  ⛔ ") + name)
        if not ok:
            bad.append(name)

    # ⛔ ARM 1 — THE DENOMINATOR ARTIFACT IS VISIBLE.  Same absolute noise
    # (100 ms), candidate level 2x the shipped one.  A report that showed only
    # percentages would announce a 2x tightening where the instrument is exactly
    # as steady.  The absolute ratio must read ~1.00x and the relative ~2.00x.
    rc, out = _run_on(_fake_rows(1000.0, 100.0, 2000.0, 100.0))
    m = [l for l in out.splitlines() if "child user CPU" in l and "abs" in l]
    ok = rc == 0 and m and "abs  1.0" in m[0] and "rel  2.0" in m[0]
    arm(ok, "a candidate with the SAME absolute noise and a 2x level reads "
            "abs 1.00x / rel 2.00x (the denominator artifact is not hidden)")
    if not ok and m:
        print("     got: " + m[0].strip())

    # ⭐ ARM 2 — AND A GENUINELY STEADIER CANDIDATE WINS ON BOTH COLUMNS.  The
    # held-out arm: without it, arm 1 is satisfied by a report that always prints
    # abs 1.00x.  [[feedback-probe-gates-both-ways]]
    rc, out = _run_on(_fake_rows(1000.0, 100.0, 1000.0, 10.0))
    m = [l for l in out.splitlines() if "child user CPU" in l and "abs" in l]
    ok = rc == 0 and m and "abs 10.0" in m[0] and "rel 10.0" in m[0]
    arm(ok, "a genuinely steadier candidate reads tighter on BOTH columns")
    if not ok and m:
        print("     got: " + m[0].strip())

    # ⛔ ARM 3 — A PARTIAL CORPUS IS REFUSED, not quietly scored over a smaller
    # set of commits than the shipped arm.
    rows = _fake_rows(1000.0, 100.0, 1000.0, 10.0)
    rows[3].pop("cpu")
    rc, out = _run_on(rows)
    arm(rc == 2 and "carry no `cpu` block" in out,
        "a corpus where some readings lack `cpu` is REFUSED, not scored")

    # ⛔ ARM 4 — A UNIT THE CANDIDATE CANNOT EXPRESS IS NAMED.  The real corpus's
    # `@decl` units have no per-process CPU and never will; a silent omission
    # would report agreement about units nobody measured.
    rows = _fake_rows(1000.0, 100.0, 1000.0, 10.0, reexport_unit=True)
    for r in rows:
        r["decls"] = {"M": {"memDestSweep": 400.0}}
    rc, out = _run_on(rows)
    # ⚠️ AND THE TWO PLACES THAT COUNT THEM MUST AGREE.  COVERAGE said 4 and the
    # MDR table said 6 on the real corpus, because "the candidate cannot express
    # this" and "the SHIPPED arm reads 0 ms here" were wearing one label. Two
    # numbers for one fact in one report is a defect even when both are printed.
    arm(rc == 0 and "NOT EXPRESSIBLE: M @decl memDestSweep" in out
        and "NOT EXPRESSIBLE: M @residue" in out
        and "INTERNAL DISAGREEMENT" not in out,
        "a gated unit the candidate cannot express is NAMED, not omitted — and "
        "COVERAGE's count agrees with the MDR table's")

    # ⛔ ARM 5 — THE RULE IS THE SHIPPED ONE.  Stub `kdh.budget_info` and require
    # the DERIVED BUDGETS table to move.  A docstring naming a delegate reads AS
    # the delegation.  [[feedback-a-citation-is-an-ungated-claim]]
    rows = _fake_rows(1000.0, 100.0, 1000.0, 10.0)
    real = kdh.budget_info
    try:
        kdh.budget_info = lambda *a, **k: ({"M": {"cand": 424242.0, "med": 0.0,
                                                  "ctrl": 0.0, "noise": 0.0,
                                                  "worst": 0.0, "base": 1.0}}, {})
        import io, contextlib
        buf = io.StringIO()
        sys.argv = ["x", "--readings", "/dev/null"]
        moved = False
        fd, p = __import__("tempfile").mkstemp(suffix=".jsonl")
        with os.fdopen(fd, "w") as fh:
            for r in rows:
                fh.write(json.dumps(r) + "\n")
        sys.argv = ["x", "--readings", p]
        with contextlib.redirect_stdout(buf):
            main()
        moved = "424242.0%" in buf.getvalue()
        os.unlink(p)
    finally:
        kdh.budget_info = real
    arm(moved, "the budgets really come from kernel_delta_history.budget_info "
               "(delegate stubbed; the table must move)")

    # ⭐⭐⭐ ARM 6 — THE DECIDING TABLE DECIDES CORRECTLY IN ALL THREE DIRECTIONS.
    # MDR exists to neutralise the denominator artifact that arm 1 plants, so it
    # is driven on the SAME three fixtures and must reach a different verdict on
    # each. Without the third case an MDR that simply never says WORSE would pass.
    # [[feedback-probe-gates-both-ways]] [[feedback-under-claims-are-unpoliced]]
    # flat + one spike; the budget comes from the NOISE, the transfer from the
    # SPIKE. See the note on `_fake_rows` for why a uniform ramp cannot do both.
    # ⛔ `spike_at=4` IS NOT ARBITRARY: it places the jump on pair 3->4, which
    # among these six real commits actually CHANGES `.lean` files. At `spike_at=3`
    # the jump landed on 76cb51b..3769ea0, a pair git reports as touching NO
    # `.lean` file — so `budget_info` scored the whole spike as CONTROL noise and
    # the transfer step discarded it as a no-op. The fixture then read
    # "UNDECIDED" for a reason that had nothing to do with the code under test.
    # ⇒ a fixture built on real commits inherits their real diff structure, and
    # a planted signal has to be planted where the corpus says work happened.
    def spiked(noise_ms, noise_user, spike_ms, spike_user):
        return _fake_rows(100000.0, noise_ms, 100000.0, noise_user, step_ms=0.0,
                          step_user=0.0, spike_at=4,
                          spike_ms=spike_ms, spike_user=spike_user)
    def spiked_lonely():
        return _fake_rows(100000.0, 1000.0, 100000.0, 1000.0, step_ms=0.0,
                          step_user=0.0, spike_at=4, spike_ms=5000.0,
                          spike_user=5000.0, lonely_unit=True)
    mdr_cases = [
        # twice the noise but the candidate hears the change TWICE as loudly:
        # 2 x 2000 / 2.0 == 2 x 1000, so sensitivity is EQUAL and the percentage
        # table's flattering "2x tighter" must not survive the correction.
        (spiked(1000.0, 2000.0, 5000.0, 10000.0), "no difference",
         "twice the noise but twice the signal is NO change in sensitivity"),
        # genuinely steadier at equal transfer: the candidate wins.
        (spiked(1000.0, 200.0, 5000.0, 5000.0), "candidate better",
         "a genuinely steadier candidate at equal transfer wins on MDR"),
        # five times the noise at equal transfer: it must be called WORSE.
        (spiked(200.0, 1000.0, 5000.0, 5000.0), "candidate WORSE",
         "five times the noise at equal transfer is WORSE on MDR"),
    ]
    for rows_, want, label in mdr_cases:
        rc, out = _run_on(rows_)
        line = [l for l in out.splitlines()
                if l.strip().startswith("M ") and "ms" in l]
        ok = rc == 0 and line and want in line[0]
        arm(ok, label)
        if not ok:
            print("     got: " + (line[0].strip() if line else "(no M row)"))

    # ⭐⭐ ARM 7 — SIGNAL TRANSFER DECIDES BOTH WAYS.  The statistic that could
    # kill the candidate outright must be shown able to say both "carries it all"
    # and "is deaf to most of it", or a median near 1.0 on the real corpus means
    # nothing.  [[feedback-probe-gates-both-ways]] [[feedback-an-implied-assertion-is-not-a-second-gate]]
    for step_u, want, label in [
        (1000.0, "median  1.00", "a candidate carrying the WHOLE change reads Δuser/Δms 1.00"),
        (300.0, "median  0.30", "a candidate DEAF to two thirds of it reads 0.30"),
    ]:
        rc, out = _run_on(_fake_rows(1000.0, 10.0, 1000.0, 10.0,
                                     step_ms=1000.0, step_user=step_u))
        line = [l for l in out.splitlines() if "Δuser / Δms" in l]
        ok = rc == 0 and line and want in line[0]
        arm(ok, label)
        if not ok:
            print("     got: " + (line[0].strip() if line else "(no transfer line)"))

    # ⚠️ ARM 8 — AND A CHANGE BELOW THE NOISE FLOOR IS DROPPED, NOT DIVIDED.
    # A ratio whose denominator is noise is a ratio about noise, and it would
    # arrive looking like a measurement.
    rc, out = _run_on(_fake_rows(1000.0, 100.0, 1000.0, 100.0, step_ms=1.0))
    ok = rc == 0 and "cannot measure signal transfer" in out
    arm(ok, "a corpus whose changes are all below the noise floor REFUSES to "
            "report a transfer ratio")

    # ⛔⛔ ARM 9 — THE EXACT-ZERO COUNT IS ITSELF GATED, and it was NOT until a
    # plant probe found it silent.  That count exists to detect a bias that
    # flatters the SHIPPED arm — two sweeps printing the identical 3-significant-
    # figure string, spread exactly 0 — and therefore flatters the conclusion I
    # had already sealed on the bus.  An unpoliced diagnostic that guards against
    # my own predicted answer is the last thing that should have been left
    # ungated.  [[feedback-an-implied-assertion-is-not-a-second-gate]]
    # [[feedback-ungated-prose-overclaims]]
    rc, out = _run_on(_fake_rows(1000.0, 0.0, 1000.0, 10.0))
    line = [l for l in out.splitlines() if "type checking ms" in l and " of " in l]
    ok = rc == 0 and line and "biases this arm" in line[0] and " 0 of " not in line[0]
    arm(ok, "ties in the SHIPPED arm are COUNTED and flagged as a bias")
    if not ok:
        print("     got: " + (line[0].strip() if line else "(no zero-count row)"))
    # ⚠️ and the held-out arm: with real noise the count must be zero, or the
    # flag fires on every run and stops being read.
    rc, out = _run_on(_fake_rows(1000.0, 100.0, 1000.0, 10.0))
    line = [l for l in out.splitlines() if "type checking ms" in l and " of " in l]
    ok = rc == 0 and line and "biases this arm" not in line[0]
    arm(ok, "with real noise the tie-count is silent (it does not cry wolf)")
    if not ok:
        print("     got: " + (line[0].strip() if line else "(no zero-count row)"))

    # ⛔ ARM 10 — THE LIVE / NO-OP SPLIT IS REAL.  `budget_info`'s `worst` runs
    # over ALL pairs, no-ops included, so printing it beside `ctrl` as "worst
    # REAL move" produced three rows reading `no-op == real, ratio 1.00x` —
    # identical numbers in adjacent fields, which is what one arm wearing two
    # names looks like.  A plant probe found the repaired split UNGATED, so:
    # the spiked fixture puts its whole signal on a pair that changes `.lean`,
    # and the no-op column must therefore stay far BELOW the live one.
    # [[feedback-two-arms-that-agree-to-the-case]]
    # ⛔ THE FIXTURE PUTS THE BIGGEST MOVE ON A **NO-OP** PAIR, and the first
    # version of this arm did the opposite and was SILENT.  Collapsing the split
    # makes the LIVE column absorb the no-op pairs; when the biggest move is
    # already on a live pair the maximum does not change and the arm sees
    # nothing.  The defect is only visible when the no-op pair is the one
    # carrying the outlier — which is also the real corpus's situation, where
    # the shipped instrument's worst apparent move IS on a commit that changed
    # no `.lean` file.  [[feedback-a-probe-must-create-its-condition]]
    rc, out = _run_on(_fake_rows(100000.0, 200.0, 100000.0, 200.0,
                                 step_ms=1000.0, step_user=1000.0,
                                 spike_at=3, spike_ms=20000.0, spike_user=20000.0))
    line = [l for l in out.splitlines() if "type checking ms" in l and "NO-OP" in l]
    ok = False
    if rc == 0 and line:
        import re as _re
        nums = _re.findall(r"([\d.]+)%", line[0])
        ok = len(nums) >= 2 and float(nums[0]) > 5.0 * float(nums[1])
    arm(ok, "the worst NO-OP move and the worst LIVE move are scored over "
            "DIFFERENT pairs (an outlier planted on a NO-OP pair must not leak "
            "into the live column)")
    if not ok:
        print("     got: " + (line[0].strip() if line else "(no error-rate row)"))

    # ⛔ ARM 11 — A UNIT WITH NO MEASURED NOISE GETS NO TRANSFER RATIO.  The
    # floor used to default to 0 for such a unit, so pure noise was accepted as
    # signal for exactly the units the corpus knows least about.
    # [[feedback-a-declared-list-inherits-its-default]]
    rc, out = _run_on(spiked_lonely())
    ok = rc == 0 and "skipped for having no measured noise" in out
    arm(ok, "a unit with no repeatability data is SKIPPED, not given a noise "
            "floor of zero")

    # ⛔ ARM 12 — THE TWO ARMS MOVING IN OPPOSITE DIRECTIONS IS A FINDING.  A
    # negative ratio must not be abs()'d into a confident correction.
    rc, out = _run_on(_fake_rows(100000.0, 1000.0, 100000.0, 1000.0, step_ms=0.0,
                                 step_user=0.0, spike_at=4,
                                 spike_ms=5000.0, spike_user=-5000.0))
    ok = rc == 0 and "OPPOSITE directions" in out and "UNDECIDED" in out
    arm(ok, "a unit where the candidate moves OPPOSITE to the shipped arm is "
            "reported flipped and left UNDECIDED, not corrected by |ratio|")

    n = 5 + len(mdr_cases) + 3 + 2 + 1 + 2
    if bad:
        print(f"user-cost-budget selftest: FAIL ({len(bad)} of {n} arms)")
        return 1
    print(f"user-cost-budget selftest: PASS ({n} arms — the denominator artifact, "
          "its held-out control, the partial corpus, the inexpressible unit, "
          "the shared rule, MDR deciding in all three directions, and signal "
          "transfer deciding in both plus its noise-floor refusal, and the tie-count that guards the comparison's own bias, the live/no-op split, the unit with no measured noise, and the arms moving in opposite directions)")
    return 0


def main():
    if "--selftest" in sys.argv:
        return selftest()
    path = arg("--readings")
    if not path or not os.path.exists(path):
        print(__doc__)
        return 2
    decl_names = [x for x in (arg("--decl-names") or DECL_DEFAULT).split(",") if x]
    rows = [json.loads(l) for l in open(path) if l.strip().startswith("{")]
    if not rows:
        print(f"⛔ {path} holds no readings.")
        return 2
    have_cpu = sum(1 for r in rows if r.get("cpu"))
    print(f"readings: {len(rows)}   carrying a `cpu` block: {have_cpu}")
    if have_cpu != len(rows):
        # ⛔ A PARTIAL CORPUS IS NOT A SMALLER CORPUS.  Mixing readings that
        # carry the candidate with readings that do not would score the
        # candidate over a different set of commits from the shipped quantity,
        # which is the borrowed-denominator defect D148 §3 recorded.
        # [[feedback-a-borrowed-denominator-invents-its-own-gap]]
        print(f"⛔ {len(rows) - have_cpu} readings carry no `cpu` block. Both arms "
              f"must be scored over the SAME readings; re-run the walk with the "
              f"instrumented `kernel_cost.py`.")
        return 2

    arms = [("type checking ms  (SHIPPED)", ms_units),
            ("child user CPU    (CANDIDATE)", cpu_units("user_s")),
            ("child real  clock (CONTROL)", cpu_units("real_s"))]

    # ── 1. COVERAGE ────────────────────────────────────────────────────────
    # ⛔ COVERAGE IS COMPUTED FROM THE LEVELS, NOT FROM THE SPREADS.  The first
    # version read the unit sets off `spread_table`, which needs TWO sweeps per
    # commit — so on a corpus still being written it announced "the candidate
    # expresses 0 of 0 gated units", which is a PASS-shaped sentence about a
    # question nobody asked.  A coverage claim must not depend on having repeats.
    # [[feedback-a-route-cannot-see-its-subject]]
    shipped_units = set(level_table(rows, ms_units, decl_names))
    cand_units = set(level_table(rows, cpu_units("user_s"), decl_names))
    missing = sorted(shipped_units - cand_units)
    print(f"\n── COVERAGE ── the candidate expresses "
          f"{len(shipped_units & cand_units)} of {len(shipped_units)} gated units")
    for u in missing:
        print(f"   ⛔ NOT EXPRESSIBLE: {u}")
    if missing:
        print("   (getrusage accounts per PROCESS and kernel_cost runs one per "
              "MODULE, so no walk can ever supply these — a hybrid gate would "
              "leave them on the noisy instrument.)")

    # ── 2. REPEATABILITY, head to head ─────────────────────────────────────
    tables = {name: spread_table(rows, ex, decl_names) for name, ex in arms}
    abstab = {name: spread_table(rows, ex, decl_names, absolute=True) for name, ex in arms}
    levels = {name: level_table(rows, ex, decl_names) for name, ex in arms}
    # ⛔ THE COUNT IS COUNTED, NOT TYPED.  This header said "the median over the
    # twelve trees" on a corpus that had TWO trees with repeats — a number
    # written when the walk was designed and still standing when the walk was
    # cut short at 14 readings.  A printed count that no one computes is a claim
    # the output makes on the tool's behalf.
    # [[feedback-a-citation-is-an-ungated-claim]] [[feedback-ungated-prose-overclaims]]
    n_trees = max((len(v) for v in tables[arms[0][0]].values()), default=0)
    print(f"\n── REPEATABILITY ── same tree, {n_trees} tree(s) with repeated "
          f"readings ~20 min apart; the median over them")
    print(f"   {'unit':<44} " + " ".join(f"{n.split('(')[0].strip():>26}" for n, _ in arms))
    print(f"   {'':<44} " + " ".join(f"{'level    abs      rel':>26}" for _ in arms))
    for u in sorted(shipped_units):
        cells = []
        for name, _ in arms:
            v, a, lv = tables[name].get(u), abstab[name].get(u), levels[name].get(u)
            cells.append(f"{lv:>9.0f}{statistics.median(a):>8.0f}{statistics.median(v):>8.1f}%"
                         if v else f"{'—':>26}")
        print(f"   {u:<44} " + " ".join(cells))
    print("   level/abs in ms (user and real are CPU/clock seconds x1000)")
    if not any(tables[n] for n, _ in arms):
        # ⛔ AN EMPTY TABLE IS NOT AN AGREEING TABLE.  Repeatability needs at
        # least two sweeps per commit; say so rather than printing headers over
        # nothing.  [[feedback-unobserved-regions-report-agreement]]
        print("   ⛔ NO REPEATABILITY DATA: this corpus carries fewer than two "
              "readings per commit, so the head-to-head above is EMPTY, not equal. "
              "Re-run the walk with --sweeps 2.")
    # ⛔⛔ A TWO-SAMPLE RANGE CAN REACH EXACTLY ZERO BY ROUNDING, AND THAT WOULD
    # BIAS THIS COMPARISON IN THE DIRECTION I PREDICTED.  Lean's profiler prints
    # THREE SIGNIFICANT FIGURES, so at ~25,000 ms its quantum is 100 ms and two
    # sweeps of one tree can print the identical string; `getrusage` reports
    # microseconds and essentially never ties.  Spurious zeros in the SHIPPED arm
    # make the shipped instrument look steadier than it is — i.e. they
    # manufacture the "candidate is worse" verdict — so the count is printed for
    # every arm rather than left to be trusted.  D148 §2 is the same mechanism
    # one level up: a noise estimate that CAN reach zero will reach it.
    # [[feedback-a-noise-estimate-that-can-reach-zero]]
    # [[feedback-conservative-is-a-direction-not-a-margin]]
    print(f"\n   {'arm':<32} {'exact-zero spreads':>22}")
    for name, _ in arms:
        alla = [x for v in abstab[name].values() for x in v]
        if alla:
            z = sum(1 for x in alla if x == 0.0)
            flag = "  ⚠️ biases this arm to look steadier" if z else ""
            print(f"   {name:<32} {z:>10} of {len(alla):<8}{flag}")

    print(f"\n   {'arm':<32} {'median abs':>12} {'median rel':>12}   "
          f"{'tightening vs SHIPPED':>24}")
    base_abs = base_rel = None
    for name, _ in arms:
        allv = [x for v in tables[name].values() for x in v]
        alla = [x for v in abstab[name].values() for x in v]
        if not allv:
            continue
        ma, mr = statistics.median(alla), statistics.median(allv)
        if base_abs is None:
            base_abs, base_rel = ma, mr
            tail = "   (the reference)"
        else:
            # ⛔ BOTH ratios, because they can disagree: a candidate can be
            # tighter in % while carrying the same milliseconds of noise.
            tail = f"   abs {base_abs / ma:5.2f}x   rel {base_rel / mr:5.2f}x"
        print(f"   {name:<32} {ma:>10.0f}ms {mr:>11.2f}%{tail}")

    # ── 3. BUDGETS, by the SHIPPED rule ────────────────────────────────────
    print(f"\n── DERIVED BUDGETS ── one rule (kernel_delta_history.budget_info), "
          f"three quantities")
    infos, metas = {}, {}
    for name, ex in arms:
        try:
            infos[name], metas[name] = kdh.budget_info(rows, ex, decl_names)
        except Exception as e:
            print(f"   ⛔ {name}: {type(e).__name__}: {e}")
    print(f"   {'unit':<46} " + " ".join(f"{n.split('(')[0].strip():>14}" for n, _ in arms))
    for u in sorted(shipped_units):
        cells = []
        for name, _ in arms:
            i = infos.get(name, {}).get(u)
            cells.append(f"{i['cand']:>13.1f}%" if i else f"{'—':>14}")
        print(f"   {u:<46} " + " ".join(cells))

    # ── 4. SAFETY / LIVENESS on the same corpus ────────────────────────────
    # ⭐ A safety bound is free to a gate that never speaks, so BOTH are printed.
    # [[feedback-measure-a-gates-error-rates]]
    print(f"\n── ERROR RATES ── on the corpus's own no-op pairs (truth = 0) and "
          f"live pairs")
    # ⛔⛔ `worst` FROM `budget_info` IS OVER **ALL** PAIRS, NO-OPS INCLUDED, so
    # printing it as "worst REAL move" beside `ctrl` produced three rows reading
    # `worst no-op == worst real, ratio 1.00x` — identical numbers in adjacent
    # fields, which is what one arm wearing two names looks like. The live-only
    # worst is computed here from the same meta rather than by widening
    # `budget_info`, whose output the SHIPPED budgets are derived from.
    # [[feedback-two-arms-that-agree-to-the-case]]
    for name, ex in arms:
        i, meta = infos.get(name), metas.get(name)
        if not i or not meta:
            continue
        noop = [v["ctrl"] for v in i.values()]
        live = []
        for u in i:
            for a, b in zip(meta["seq"], meta["seq"][1:]):
                if b in meta["zero_lean"]:
                    continue
                ba, bb = meta["med"][a].get(u), meta["med"][b].get(u)
                if ba and bb and ba > 0:
                    live.append(abs(100.0 * (bb - ba) / ba))
        if not live:
            print(f"   {name:<32} ⛔ no LIVE pairs in this corpus")
            continue
        wn, wl = max(noop) if noop else 0.0, max(live)
        r = f"   ratio {wl / wn:5.2f}x" if wn > 0 else "   (no-op moves all exactly 0)"
        print(f"   {name:<32} worst on a NO-OP commit {wn:7.2f}%   "
              f"worst on a LIVE commit {wl:7.2f}%{r}")

    # ── 5. THE SHIPPED QUANTITY, MEASURED TWICE ────────────────────────────
    # ⭐⭐ THIS WALK RE-MEASURES THE SAME `type checking` MS THE 09/04 WALK DID,
    # over the SAME twelve commits, with the SAME tool — so the two corpora are a
    # matched pair for the SHIPPED arm, and the difference between them is a
    # difference between two DAYS on one box.  That matters for the decision and
    # not only for the candidate: the budgets this repository merges on were
    # derived from the 09/04 corpus, so if that day's within-commit spread was
    # much smaller than this one's, the shipped budgets were calibrated on an
    # unrepresentatively quiet afternoon and are tighter than the instrument can
    # actually support — which is a finding about the GATE, arrived at with no
    # reference to the candidate at all.
    # ⛔ It is one extra pair of days, not a distribution over days.
    # [[feedback-a-single-reading-is-about-its-run]]
    # [[feedback-two-readings-are-not-two-witnesses]]
    base_path = arg("--baseline")
    if base_path and os.path.exists(base_path):
        brows = [json.loads(l) for l in open(base_path) if l.strip().startswith("{")]
        bt = spread_table(brows, ms_units, decl_names)
        ba = spread_table(brows, ms_units, decl_names, absolute=True)
        mine_r = [x for v in tables["type checking ms  (SHIPPED)"].values() for x in v]
        mine_a = [x for v in abstab["type checking ms  (SHIPPED)"].values() for x in v]
        theirs_r = [x for v in bt.values() for x in v]
        theirs_a = [x for v in ba.values() for x in v]
        if mine_r and theirs_r:
            print(f"\n── THE SHIPPED QUANTITY ON TWO DAYS ── same 12 commits, same "
                  f"tool, same box")
            print(f"   {'corpus':<44} {'median abs':>12} {'median rel':>12}  n")
            print(f"   {os.path.basename(base_path):<44} "
                  f"{statistics.median(theirs_a):>10.0f}ms "
                  f"{statistics.median(theirs_r):>11.2f}%  {len(theirs_r)}")
            print(f"   {os.path.basename(path):<44} "
                  f"{statistics.median(mine_a):>10.0f}ms "
                  f"{statistics.median(mine_r):>11.2f}%  {len(mine_r)}")
            f_r = statistics.median(mine_r) / statistics.median(theirs_r)
            print(f"   ⇒ this walk's within-commit spread is {f_r:.2f}x the one the "
                  f"SHIPPED BUDGETS were calibrated against.")
            if f_r > 1.5:
                print(f"   ⛔ the budgets in `kernel_delta_budget.txt` therefore rest "
                      f"on a quieter day than this one. That is a finding about the "
                      f"GATE, independent of any candidate.")

    # ── 6. THE DECIDING TABLE: MINIMUM DETECTABLE REGRESSION ───────────────
    # ⭐⭐⭐ A PERCENTAGE OF `user` IS NOT A PERCENTAGE OF KERNEL TIME, so the
    # budget columns above cannot be compared to each other as they stand — and
    # comparing them anyway is how a candidate that is quieter gets adopted while
    # being DEAFER.
    #
    # `user` charges Lean's startup, import loading and elaboration as well as
    # the kernel.  On `Tests.Coverage` that makes it a ~57,000 ms number where
    # the gated one is ~25,000 ms, and on a small module it is almost ALL
    # constant.  A constant addend shrinks the relative noise and shrinks the
    # relative SIGNAL by the very same factor, so a candidate can look 2x tighter
    # and catch nothing extra.  [[feedback-a-ratio-survives-a-doubling]]
    #
    # ⇒ THE COMMON CURRENCY IS MILLISECONDS OF REAL EXTRA WORK:
    #
    #       MDR(unit) = budget% x level(unit) / 100
    #
    # — the smallest regression that would clear that arm's own budget.  The
    # assumption is stated because it is doing work: X ms of extra KERNEL
    # reduction adds about X ms to the child's CPU time as well, since kernel
    # work is CPU work in that same process.  It is the levels, not the
    # percentages, that make the two arms commensurable.
    # ⛔ LOWER IS BETTER HERE. An arm with a smaller MDR catches smaller
    # regressions; an arm with a larger MDR has bought its quiet by going deaf.
    # ⛔⛔ ONE FIXED MULTIPLE, SHARED BY BOTH ARMS — and the alternative was tried
    # and REFUTED in the same sitting.  Using each arm's OWN registered multiple
    # (`kernel_delta_history.registered_mult(need)`, the shipped rule) makes the
    # comparison VACUOUS: that multiple is calibrated so the gate never rejects a
    # batch that actually landed, i.e. `mult ~ need = worst/cand`, so
    # `MDR = cand x mult x level` collapses to the WORST HISTORICAL MOVE and is
    # the same for any arm measuring the same history.  Driven on the fixtures it
    # read 5,025 ms against 5,005 ms — both just the planted 5,000 ms spike — and
    # two arms designed to differ by 5x reported "no difference".
    # ⇒ comparing INSTRUMENTS needs a multiple that does not absorb each
    # instrument's own worst case.  2.0 is the shipped floor and is applied
    # identically to both arms, so it cancels out of every ratio in the verdict
    # column and none of the conclusions depend on its value.
    # [[feedback-a-normalisation-needs-its-denominator-to-vary-the-same-way]]
    MULT = 2.0
    SHIP = "type checking ms  (SHIPPED)"
    CAND = "child user CPU    (CANDIDATE)"
    tr, tr_used, tr_dropped, tr_skipped, tr_flipped = transfer_ratios(
        metas, SHIP, CAND, sorted(shipped_units & cand_units),
        abstab[SHIP])
    print(f"\n── MINIMUM DETECTABLE REGRESSION ── budget% x level, in ms.  "
          f"LOWER IS BETTER.")
    # ⛔ THE PROVENANCE LINE PRINTS UNCONDITIONALLY.  The first version reported
    # `skipped` and `flipped` only inside the branch where SOME unit still had a
    # ratio — so a corpus in which EVERY unit's two arms moved in opposite
    # directions fell through to "no transfer ratio could be measured" and the
    # flip, the most interesting thing in the run, was never mentioned.
    # A diagnostic that only prints when the news is good is not a diagnostic.
    # [[feedback-a-sentence-missing-case-reads-as-empty]]
    bits = [f"{tr_used} pair(s) used", f"{tr_dropped} below the ms noise floor"]
    if tr_skipped:
        bits.append(f"{tr_skipped} unit(s) skipped for having no measured noise")
    if tr_flipped:
        bits.append(f"⛔ {len(tr_flipped)} unit(s) whose two arms moved in "
                    f"OPPOSITE directions ({', '.join(tr_flipped)}) — left "
                    f"UNDECIDED rather than corrected by |ratio|")
    print("   transfer: " + "; ".join(bits) + ".")

    # ⛔⛔⛔ THE FLOOR CHOICE DECIDES THE ANSWER, SO THE ANSWER MUST SHOW ITS
    # SENSITIVITY TO IT.  This report uses the WORST same-tree spread as each
    # unit's noise floor, which is the conservative choice and the one D148 §2's
    # scar argues for (a referee looser than the gate it refereed produced a
    # measured false positive).  But on the real corpus that choice alone moves
    # the count of usable pairs from 0 to 99:
    #
    #     floor = MAX same-tree spread      0 of 102 pairs clear
    #     floor = MEDIAN                   49 of 102
    #     floor = MIN                      99 of 102
    #
    # ⇒ 🔑 THE SIGNAL AND THE NOISE IN THIS CORPUS ARE THE SAME SIZE.
    # `Tests.Coverage`'s largest real batch delta is 1,700 ms against a same-tree
    # spread of 600 ms (median) to 2,600 ms (worst). Whether a batch is
    # "resolvable" is therefore decided by which noise statistic is chosen, not
    # by the readings — and a verdict printed without that is my choice wearing
    # a measurement's clothes.
    # ⛔ THE FLOOR IS NOT LOOSENED TO PRODUCE AN ANSWER. UNDECIDED is the honest
    # output; the sensitivity is printed so the reader can see what it rests on.
    # [[feedback-widening-a-gate-needs-a-second-source]]
    # [[feedback-a-single-reading-is-about-its-run]]
    alts = []
    for label, f in (("MAX (used)", max), ("MEDIAN", statistics.median),
                     ("MIN", min)):
        used_a = tot_a = 0
        for u_ in sorted(shipped_units & cand_units):
            sp = abstab[SHIP].get(u_)
            if not sp:
                continue
            fl = f(sp)
            m0 = metas.get(SHIP)
            if not m0:
                continue
            for a_, b_ in zip(m0["seq"], m0["seq"][1:]):
                if b_ in m0["zero_lean"]:
                    continue
                x, y = m0["med"][a_].get(u_), m0["med"][b_].get(u_)
                if x is None or y is None:
                    continue
                tot_a += 1
                if abs(y - x) > fl:
                    used_a += 1
        alts.append(f"{label} {used_a}/{tot_a}")
    print(f"   ⚠️ SENSITIVITY TO THE FLOOR — pairs clearing it: " + ";  ".join(alts))
    if alts and alts[0].startswith("MAX (used) 0/"):
        print(f"      ⇒ NOT ONE pair in this project's history clears the WORST "
              f"same-tree spread, while most clear the best. The signal a batch "
              f"produces and the noise one tree produces are THE SAME SIZE, which "
              f"is the finding — and it is about the SHIPPED instrument, not "
              f"about the candidate.")
    if tr:
        allr = sorted(tr.values())
        print(f"   ⚠️ the RAW columns assume a change moves each arm by the same "
              f"milliseconds. Measured, it does not: Δuser/Δms has median "
              f"{statistics.median(allr):.2f} over {len(tr)} unit(s). The "
              f"CORRECTED column divides by each unit's own ratio and is the one "
              f"the verdict reads.")
    else:
        print(f"   ⛔ NO USABLE TRANSFER RATIO. Every verdict below is therefore "
              f"UNDECIDED rather than resting on the untested assumption that "
              f"both arms move by the same milliseconds.")
    print(f"   {'unit':<40} {'SHIPPED':>11} {'cand RAW':>11} {'Δu/Δms':>8} "
          f"{'cand CORR':>11}   verdict")
    wins = {"SHIPPED": 0, "CANDIDATE": 0, "tie": 0, "n/a": 0, "unknown": 0,
            "no-base": 0}
    for u in sorted(shipped_units):
        mdr = {}
        for name in (SHIP, CAND):
            i, lv = infos.get(name, {}).get(u), levels[name].get(u)
            mdr[name] = i["cand"] * MULT * lv / 100.0 if (i and lv) else None
        a, b = mdr[SHIP], mdr[CAND]
        ratio = tr.get(u)
        corr = (b / abs(ratio)) if (b is not None and ratio) else None
        # ⛔ TWO DIFFERENT FACTS WERE WEARING ONE LABEL, and the tell was that
        # this table said "cannot express 6" while COVERAGE above said 4.  The
        # other two are `Tests` and `X86`: pure re-export modules that type-check
        # NOTHING, so the SHIPPED arm's level is 0.0 and a percentage budget on it
        # is meaningless — the CANDIDATE expresses them perfectly well (a `lean`
        # process still burns CPU importing).  Reporting that as a failure of the
        # candidate is an under-claim against the candidate, and an under-claim
        # looks like modesty.  [[feedback-under-claims-are-unpoliced]]
        if b is None:
            v, key = "candidate CANNOT express this unit", "n/a"
        elif a is None:
            v, key = ("the SHIPPED arm reads 0 ms here (a re-export module) — "
                      "no percentage budget exists to compare against"), "no-base"
        elif corr is None:
            v, key = "⚠️ no transfer ratio — UNDECIDED", "unknown"
        elif corr < a * 0.95:
            v, key = f"candidate better ({a / corr:.2f}x)", "CANDIDATE"
        elif a < corr * 0.95:
            v, key = f"⛔ candidate WORSE ({corr / a:.2f}x)", "SHIPPED"
        else:
            v, key = "no difference", "tie"
        wins[key] += 1
        print(f"   {u:<40} "
              f"{(f'{a:.0f}ms' if a is not None else '—'):>11} "
              f"{(f'{b:.0f}ms' if b is not None else '—'):>11} "
              f"{(f'{ratio:.2f}' if ratio else '—'):>8} "
              f"{(f'{corr:.0f}ms' if corr is not None else '—'):>11}   {v}")
    print(f"\n   ⇒ over {len(shipped_units)} gated units: candidate better on "
          f"{wins['CANDIDATE']}, WORSE on {wins['SHIPPED']}, tied on {wins['tie']}, "
          f"UNDECIDED for want of a transfer ratio {wins['unknown']}, "
          f"cannot express {wins['n/a']}, shipped arm has no base "
          f"{wins['no-base']}.")
    # ⚠️ the two counts must agree, and they did not until the row above split.
    if wins["n/a"] != len(missing):
        print(f"   ⛔ INTERNAL DISAGREEMENT: COVERAGE named {len(missing)} "
              f"inexpressible unit(s), this table counted {wins['n/a']}. One of "
              f"the two is wrong.")

    # ── 6b. SIGNAL TRANSFER: DOES THE CANDIDATE HEAR A REAL CHANGE? ────────
    # ⭐⭐⭐ MDR PRICES SENSITIVITY FROM THE BUDGET.  This measures it directly,
    # and it is the arm that could kill the candidate outright: if a commit that
    # adds X ms of kernel work moves the child's CPU by much LESS than X ms, then
    # `user` is not a quieter reading of the signal — it is partly deaf to it, and
    # every quietness figure above is the quietness of an instrument that is not
    # listening.  [[feedback-a-dimension-with-no-parameter-is-frozen]]
    #
    # Paired, per (live adjacent commit pair, expressible unit): the same change
    # measured by both arms in the SAME two readings, so nothing here depends on
    # a budget, a rule, or a percentage.
    # ⛔ Pairs whose ms move is below the unit's own measured noise are DROPPED
    # and counted: a ratio whose denominator is noise is a ratio about noise.
    print(f"\n── SIGNAL TRANSFER ── for the same real change, ms moved by each arm")
    med_ms = {}
    for name, ex in arms:
        order, per = [], {}
        for r in rows:
            per.setdefault(r["commit"], []).append(r)
            if r["commit"] not in order:
                order.append(r["commit"])
        med_ms[name] = {c: {k: statistics.median([u[k] for u in
                            [ex(r, decl_names) for r in per[c]] if k in u])
                            for k in set().union(*[set(ex(r, decl_names)) for r in per[c]])}
                        for c in order}
        seq = order
    zl = infos and kdh.budget_info(rows, ms_units, decl_names)[1].get("zero_lean", set())
    noise_ms = abstab["type checking ms  (SHIPPED)"]
    ratios, dropped, big = [], 0, 0
    for a, b in zip(seq, seq[1:]):
        if b in (zl or set()):
            continue
        for u in sorted(shipped_units & cand_units):
            da = med_ms["type checking ms  (SHIPPED)"].get(b, {}).get(u)
            aa = med_ms["type checking ms  (SHIPPED)"].get(a, {}).get(u)
            db = med_ms["child user CPU    (CANDIDATE)"].get(b, {}).get(u)
            ab = med_ms["child user CPU    (CANDIDATE)"].get(a, {}).get(u)
            if None in (da, aa, db, ab):
                continue
            d_ms, d_user = da - aa, db - ab
            floor = max(noise_ms.get(u, [0.0]))
            if abs(d_ms) <= floor:
                dropped += 1
                continue
            big += 1
            ratios.append(d_user / d_ms)
    if ratios:
        ratios.sort()
        print(f"   pairs x units above the ms noise floor: {big}   "
              f"(dropped as indistinguishable from noise: {dropped})")
        print(f"   Δuser / Δms   median {statistics.median(ratios):5.2f}   "
              f"quartiles {ratios[len(ratios)//4]:5.2f} .. {ratios[3*len(ratios)//4]:5.2f}")
        agree = sum(1 for r in ratios if r > 0)
        print(f"   same SIGN as the shipped arm: {agree} of {len(ratios)}")
        print("   ⇒ a median near 1.0 means the candidate carries the whole change; "
              "well under 1.0 means it is DEAF to part of it and its quiet is "
              "partly the quiet of not listening.")
    else:
        print(f"   ⛔ no pair x unit cleared the ms noise floor "
              f"({dropped} dropped) — this corpus cannot measure signal transfer.")

    # ── 7. THE MECHANISM, STRATIFIED BY HOW BUSY THE BOX WAS ───────────────
    # ⭐⭐ THIS IS NOT A SECOND MACHINE AND IS NOT OFFERED AS ONE.  But "user CPU
    # is steadier" has TWO possible mechanisms with different portability, and
    # this box's own load varies enough (idle 0%-64% within one walk) to tell
    # them apart:
    #
    #   (a) CPU accounting is robust to CONTENTION.  Then the shipped
    #       instrument's noise should grow as the box gets busier and the
    #       candidate's should not — and on a quiet second machine the
    #       advantage would SHRINK, because there is less contention to be
    #       robust to.
    #   (b) The gain is measuring the WHOLE PROCESS rather than trusting the
    #       profiler's internal attribution.  Then the advantage is roughly
    #       flat in load and would travel.
    #
    # ⛔ Whichever way it reads, this is a fact about ONE box across two of its
    # own states, with the n printed beside it.  It makes the second-machine
    # prediction FALSIFIABLE; it does not discharge it.
    # [[feedback-a-ratio-travels-where-a-ceiling-cannot]]
    # [[feedback-a-single-reading-is-about-its-run]]
    def idle_of(r):
        for k in ("conditions_before", "conditions_after"):
            v = (r.get(k) or {}).get("idle_pct")
            if v is not None:
                return v
        return None

    per_commit = {}
    for r in rows:
        per_commit.setdefault(r["commit"], []).append(r)
    idles = {c: [i for i in (idle_of(r) for r in rs) if i is not None]
             for c, rs in per_commit.items()}
    usable = {c: statistics.mean(v) for c, v in idles.items() if v}
    if len(usable) >= 4:
        cut = statistics.median(usable.values())
        busy = {c for c, v in usable.items() if v <= cut}
        quiet = {c for c, v in usable.items() if v > cut}
        print(f"\n── MECHANISM ── the same {len(usable)} trees split by how idle "
              f"the box was (cut at {cut:.1f}% idle)")
        print(f"   {'arm':<32} {'busier half':>18} {'quieter half':>18}   n={len(busy)}/{len(quiet)}")
        for name, ex in arms:
            halves = []
            for grp in (busy, quiet):
                sub = [r for r in rows if r["commit"] in grp]
                t = spread_table(sub, ex, decl_names, absolute=True)
                allv = [x for v in t.values() for x in v]
                halves.append(statistics.median(allv) if allv else None)
            cells = " ".join(f"{h:>16.0f}ms" if h is not None else f"{'—':>18}"
                             for h in halves)
            print(f"   {name:<32} {cells}")
        print("   (median absolute within-tree spread, ms. If the SHIPPED row "
              "grows on the busier half and the CANDIDATE row does not, the gain "
              "is contention-robustness — mechanism (a) — and a quiet second "
              "machine would show LESS of it, not more.)")
    else:
        print(f"\n── MECHANISM ── not computed: only {len(usable)} trees carry an "
              f"idle reading. (A conditions field that is absent is reported as "
              f"absent, never as a default.)")

    print(f"\n⛔ PORTABILITY IS UNMEASURED for every arm above. Each number here "
          f"is from ONE box ({os.uname().machine}), and a second machine is the "
          f"outstanding debt of every candidate this queue item has considered. "
          f"The budgets are PERCENTAGES because a percentage travels where an "
          f"absolute allowance does not — but that a percentage travels is "
          f"itself the prediction, and `.github/workflows/ci.yml` records the "
          f"same tree reading 1.7x-3.1x slower on a runner DEPENDING ON THE "
          f"MODULE, which is exactly the shape that would break it.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
