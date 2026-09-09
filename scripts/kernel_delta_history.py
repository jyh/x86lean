#!/usr/bin/env python3
"""THE DELTA HISTORY — the second source a delta budget has to come from.

⭐⭐ WHY THIS EXISTS AT ALL.  `scripts/kernel_delta.py` gates the CHANGE in kernel
time a commit introduces, and a gate needs an allowance.  Deriving that allowance
from the commit under test is the defect this repository has recorded three times
(D62, D111, D122): the number then drifts with its subject and the gate stops
being one.  The helm's ruling of 09/04 21:42 names the second source — *"a
per-batch delta budget paris sets from its own batch history (print the last ten
batches' deltas; budget = a stated multiple of their median, with the reason)"* —
and this script is how that history is MEASURED rather than remembered.

⛔⛔ AND THE ESTIMATE IT REPLACED WAS WRONG BY TWO ORDERS OF MAGNITUDE.  The bank
that ordered this work priced the walk at *"a checkout plus a full `lake` rebuild
(hours, not minutes)"* and recorded the history as unmeasurable in a batch.  A
full clean build of this project in a fresh worktree is **33 seconds** and a full
profile pass is **57 seconds** — measured, both, before any of this was written.
⇒ 🔑 AN INHERITED COST ESTIMATE IS A HYPOTHESIS, AND THE CHEAPEST WAY TO TEST IT
IS TO RUN ONE INSTANCE.  A whole ruling had been shaped around a number nobody
had timed.

## THE MEASUREMENT, AND WHY IT IS SHAPED THIS WAY

A delta is only meaningful between two trees profiled in ONE session on ONE
machine (D111): the across-session shift at a single commit was measured at 11%,
which is larger than any batch's own cost.  So this walks a SINGLE detached
worktree through the commits in order, profiling each, and differences ADJACENT
readings — every delta is therefore a matched pair taken minutes apart.

⚠️ A single reading per commit carries that commit's run-to-run noise, and the
adjacent difference carries two of them.  So the walk runs SWEEPS: forward, then
reverse, then forward again if asked.  A commit's reading is the MEDIAN of its
sweeps, which cancels monotone drift in machine load — the reverse sweep visits
the commits in the opposite order, so a load that rises through the afternoon
biases the two sweeps in OPPOSITE directions rather than in the same one.

⭐ THE NEGATIVE CONTROL IS ALREADY IN THE HISTORY AND IS NOT SYNTHETIC.  `e57c99f`
(D122) changes `docs/DECISIONS.md` and nothing else — zero `.lean` files.  Its
measured delta is what this instrument reports for a commit that CANNOT have
changed any kernel time, and it is therefore this walk's noise floor, measured on
the same box in the same session as every other point.  A budget quoted without
it would be a number with no scale.  ⇒ A PROBE THAT CANNOT SHOW ITS ZERO HAS NOT
SHOWN ITS ONE.

## MECHANICS

- The worktree lives under `TMPDIR`, never under the repository.  A probe that
  writes the tree makes `git add -A` a race, and that race shipped a planted
  defect to both remotes once already (D75).
- The profiler that runs is always the CURRENT tree's `kernel_cost.py`, pointed
  at the worktree with `--root`.  A delta measured by two different measuring
  programs is not a delta.
- Readings are appended to the output file AS THEY ARE TAKEN, one JSON object per
  line, so a walk interrupted at sweep 2 still leaves sweep 1 usable.

usage: kernel_delta_history.py --commits c1,c2,...  [--sweeps 2] [--interleave] [--out FILE]
       kernel_delta_history.py --analyse FILE   (no measurement; prints the table)
"""
import os, sys, json, math, time, subprocess, tempfile, shutil, statistics
import os as _os
import sys as _sys

# ⛔ REFUSE AN UNKNOWN FLAG BEFORE ANY WORK HAPPENS. This script dispatched on
# `"--x" in sys.argv` and otherwise fell through to its main path, so a mistyped
# flag did not fail — it RAN. Measured 2026-09-09: `threads_ab.py` given a bogus
# flag started `lake env lean -D profiler=true`, saturated a core for 300+ s on a
# shared machine, and orphaned past its caller. See portable.strict_flags.
if __name__ == "__main__":
    import os as _os, sys as _sys
    _sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
    from portable import strict_flags as _strict_flags
    _strict_flags(__file__)
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
from portable import utf8_stdio, loadavg, fmt_load  # noqa: E402
# ⛔ CALLED AT IMPORT, and that is deliberate where `os.chdir` at import is not:
# it changes no state a caller depends on -- only the ENCODING of streams any
# caller would also want as utf-8 -- and it must be in effect before the first
# print, which in this module can happen from an imported helper. Three separate
# Windows crashes were reached one line apart before this existed; see portable.py.
utf8_stdio()

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
KCOST = os.path.join(ROOT, "scripts", "kernel_cost.py")
DECL_MODULES = "Tests.Coverage"


def arg(name, default=None):
    for i, a in enumerate(sys.argv):
        if a == name and i + 1 < len(sys.argv):
            return sys.argv[i + 1]
    return default


def git(*a, cwd=ROOT):
    r = subprocess.run(["git"] + list(a), cwd=cwd, capture_output=True, text=True)
    if r.returncode != 0:
        print(f"⛔ git {' '.join(a)} failed in {cwd}:\n{r.stdout}\n{r.stderr}")
        sys.exit(2)
    return r.stdout.strip()


def profile(worktree):
    """One reading of one tree, by the CURRENT tree's profiler."""
    r = subprocess.run([sys.executable, KCOST, "--emit-json", "--root", worktree,
                        "--decl-modules", DECL_MODULES],
                       capture_output=True, text=True)
    if r.returncode != 0:
        # ⛔ A GATE THAT REFUSES MUST SAY WHAT IT SAW.  Discarding the child's
        # output turns a failed reading into a local re-run that measures a
        # different machine (D94).
        print(f"⛔ the profiler failed on {worktree}:\n{r.stdout}\n{r.stderr}")
        sys.exit(2)
    for line in reversed(r.stdout.splitlines()):
        if line.startswith("{"):
            return json.loads(line)
    print(f"⛔ the profiler produced no JSON for {worktree}:\n{r.stdout}\n{r.stderr}")
    sys.exit(2)


def units(reading, decl_names):
    """The gateable quantities of ONE reading, as a flat {unit: ms} dict.

    ⚠️ THE RESIDUE IS COMPUTED OVER A DECLARATION SET THE CALLER FIXES, not over
    whichever declarations each tree happens to gate.  A residue whose subtrahend
    changes between the two sides of a delta is not a residue, it is two
    different quantities that subtract without complaining."""
    out = dict(reading["modules"])
    for mod, decls in reading["decls"].items():
        total = reading["modules"].get(mod)
        named = 0.0
        for n in decl_names:
            if n in decls:
                out[f"{mod} @decl {n}"] = decls[n]
                named += decls[n]
        if total is not None:
            out[f"{mod} @residue"] = total - named
    return out


def analyse(path, decl_names):
    rows = [json.loads(l) for l in open(path, encoding="utf-8") if l.strip().startswith("{")]
    if not rows:
        print(f"⛔ {path} holds no readings.")
        return 2
    order = []
    per = {}
    for r in rows:
        c = r["commit"]
        if c not in per:
            per[c] = []
            order.append(c)
        per[c].append(r)
    # The walk's canonical order is the order of the FIRST sweep.
    seq = [c for c in order]
    print(f"readings: {len(rows)} over {len(seq)} commits "
          f"({len(rows)//max(len(seq),1)} sweeps)")
    print(f"loads seen: " + " ".join(fmt_load(r['load1']) for r in rows))
    med = {}
    for c in seq:
        us = [units(r, decl_names) for r in per[c]]
        keys = set().union(*[set(u) for u in us])
        med[c] = {k: statistics.median([u[k] for u in us if k in u]) for k in keys}
    subjects = ["X86.Syntax", "X86.Theorems", "Tests.Anchors", "Tests.Coverage",
                "Tests.Coverage @residue", "Tests.Coverage @decl memDestSweep",
                "Tests.Coverage @decl vectorCoverage",
                "Tests.Coverage @decl pre_states_have_a_returnable_frame"]
    subj = [s for s in subjects if any(s in med[c] for c in seq)]
    print()
    print("PER-COMMIT MEDIAN READINGS (ms)")
    print(f"{'commit':<10}" + "".join(f"{s.replace('Tests.Coverage','T.Cov').replace('@decl ','')[-13:]:>15}" for s in subj))
    for c in seq:
        print(f"{c[:9]:<10}" + "".join(f"{med[c].get(s, float('nan')):>15.1f}" for s in subj))
    print()
    print("ADJACENT DELTAS (ms) — each pair profiled minutes apart in one session")
    print(f"{'commit':<10}" + "".join(f"{s.replace('Tests.Coverage','T.Cov').replace('@decl ','')[-13:]:>15}" for s in subj))
    deltas = {}
    for a, b in zip(seq, seq[1:]):
        allk = set(med[a]) | set(med[b])
        d = {s: med[b].get(s, float('nan')) - med[a].get(s, float('nan')) for s in allk}
        deltas[b] = d
        print(f"{b[:9]:<10}" + "".join(f"{d[s]:>+15.1f}" for s in subj))
    print()
    print("MEDIAN and MAX of the deltas above, per unit")
    for s in subj:
        vs = [deltas[b][s] for b in deltas if deltas[b][s] == deltas[b][s]]
        if not vs:
            continue
        print(f"  {s:<52}median {statistics.median(vs):>+9.1f}   "
              f"max {max(vs):>+9.1f}   min {min(vs):>+9.1f}   n={len(vs)}")
    # ⭐⭐⭐ THE BUDGET DERIVATION, PRINTED RATHER THAN REMEMBERED.
    #
    # ⛔ THE UNIT OF A PORTABLE BUDGET IS A RATIO, NOT A MILLISECOND. The same
    # tree profiled on a GitHub runner reads 1.7x-3.1x slower DEPENDING ON THE
    # MODULE (`.github/workflows/ci.yml`), so an absolute allowance is a fact
    # about this box. A ratio of two readings of the SAME unit on the SAME
    # machine divides that factor out exactly.
    #
    # ⛔ AND A GATE CANNOT BE TIGHTER THAN ITS INSTRUMENT. `noise` below is the
    # within-commit spread this walk MEASURED — the same commit, profiled in two
    # sweeps — so it is the resolution of the reading, not a guess from `uptime`.
    # A budget under it would report the machine.
    # ⭐⭐⭐ WHICH ESTIMATOR, DECIDED BY A GROUND TRUTH RATHER THAN BY TASTE.
    #
    # Contention noise is ONE-SIDED: another process can only make a measurement
    # slower, never faster.  That is an argument for the MINIMUM of the repeats
    # rather than their median — but an argument is not a measurement, and this
    # repository has a standing record of cost models that were right about the
    # existence of an effect and wrong about its size (D62, D105, D111).
    #
    # ⭐ SO IT IS SCORED AGAINST SOMETHING THE CODE ITSELF GUARANTEES.  Across the
    # commits in this window the coverage table only GROWS — every batch adds rows
    # and none of them removed any — so `Tests.Coverage`'s true cost is
    # non-decreasing, and every NEGATIVE delta an estimator reports on it is a
    # measurement error the estimator produced. Counting them ranks the
    # estimators without appealing to which one sounds better.
    #
    # ⚠️ THE ASSUMPTION IS NAMED SO IT CAN BE REFUTED: if some commit in the
    # window did make the module cheaper, that commit's negative delta is real and
    # this score is unfair to whichever estimator reports it. `git log --stat`
    # over the window is where that would show, and the window was chosen after
    # checking it.
    print()
    print("ESTIMATOR SCORE — negative deltas on a quantity the code only grows")
    ground = "Tests.Coverage"
    for label, f in (("median", statistics.median), ("min", min), ("max", max)):
        est = {}
        for c in seq:
            vs = [units(r, decl_names)[ground] for r in per[c]
                  if ground in units(r, decl_names)]
            if vs:
                est[c] = f(vs)
        ds = [est[b] - est[a] for a, b in zip(seq, seq[1:]) if a in est and b in est]
        neg = [d for d in ds if d < 0]
        print(f"  {label:<8} {len(neg)} of {len(ds)} deltas negative; "
              f"worst {min(ds):+.0f} ms; spread of the series "
              f"{max(ds)-min(ds):.0f} ms")
    # ⭐⭐ AND THE TWO COMMITS THAT CHANGED NO LEAN AT ALL, which is the noise
    # floor stated in the only way that cannot be argued with: whatever this
    # instrument reports for them, it reported about nothing.
    print()
    print("THE ZERO-LEAN CONTROLS — commits whose diff touches no .lean file")
    for c in seq[1:]:
        a = seq[seq.index(c) - 1]
        changed = subprocess.run(["git", "diff", "--name-only", a, c],
                                 cwd=ROOT, capture_output=True, text=True).stdout
        if any(x.endswith(".lean") for x in changed.split()):
            continue
        print(f"  {c[:9]} (no .lean changed) apparent deltas: " +
              ", ".join(f"{s.split('@')[-1].strip()[:18]} "
                        f"{deltas[c][s]:+.1f}" for s in subj if s in deltas[c]))
    print()
    print("RELATIVE deltas (delta / the PARENT's reading) — the portable unit")
    print(f"{'UNIT':<52}{'base':>10}{'noise%':>9}{'med%':>9}{'max%':>9}{'maxms':>9}")
    # ⛔ THE BUDGET DERIVATION RUNS OVER **EVERY** UNIT, not over the eight the
    # table above prints. The readable table is a summary; a budget derived from
    # a summary would leave every unit it omits to the default, and a declared
    # list's gaps all fall the way its default points.
    all_subj = sorted(set().union(*[set(med[c]) for c in seq]))
    rel_rows = []
    for s in all_subj:
        rels, noises, bases = [], [], []
        for a, b in zip(seq, seq[1:]):
            ba, bb = med[a].get(s), med[b].get(s)
            if ba is None or bb is None or ba <= 0:
                continue
            rels.append(100.0 * (bb - ba) / ba)
            bases.append(ba)
        for c in seq:
            us = [units(r, decl_names) for r in per[c]]
            vs = [u[s] for u in us if s in u]
            if len(vs) > 1 and statistics.median(vs) > 0:
                noises.append(100.0 * (max(vs) - min(vs)) / statistics.median(vs))
        if not rels:
            continue
        base = statistics.median(bases)
        noise = statistics.median(noises) if noises else 0.0
        rel_rows.append((s, base, noise, statistics.median(rels), max(rels),
                         max(deltas[b][s] for b in deltas
                             if deltas[b][s] == deltas[b][s])))
        print(f"{s:<52}{base:>10.1f}{noise:>9.2f}{statistics.median(rels):>9.2f}"
              f"{max(rels):>9.2f}{rel_rows[-1][5]:>+9.1f}")
    if rel_rows:
        print()
        print("THE MULTIPLE THAT WOULD HAVE PASSED ALL TEN, per unit")
        print("  budget = MULT x max(median relative delta, measured noise); the "
              "smallest MULT\n  that clears this unit's WORST historical batch is:")
        worst = 0.0
        for s, base, noise, medr, maxr, maxms in rel_rows:
            cand = max(medr, noise, 0.01)
            m0 = maxr / cand if cand > 0 else float("inf")
            worst = max(worst, m0)
            print(f"  {s:<52}cand {cand:>6.2f}%   worst batch {maxr:>6.2f}%   "
                  f"MULT >= {m0:>5.2f}")
        print(f"\n  ⇒ ONE multiple covering every unit's worst of ten: "
              f"MULT >= {worst:.2f}")
        print("  ⚠️ Registering AT that number leaves zero headroom for the "
              "eleventh batch, which\n     is how a gate becomes a chore. Round "
              "up, and print the margin the round-up buys.")
    json.dump({"commits": seq, "median": med,
               "deltas": {k: v for k, v in deltas.items()}},
              open(path + ".analysis.json", "w", encoding="utf-8"), indent=1)
    print(f"\nwrote {path}.analysis.json")
    return 0


# ⭐⭐⭐ THE BUDGET FILE, GENERATED FROM THE WALK WITH ITS DERIVATION INSIDE IT.
#
# ⛔ A HAND-ACCUMULATED NUMBER WITH NO PER-STEP RULE CAN ONLY BE RECOMPUTED, NEVER
# CORRECTED — this repository carried a coverage total that was ELEVEN LOW for
# eighteen batches for exactly that reason (D56). So the budget is not typed: it
# is written by this function, from this walk's readings, with every input that
# produced each line printed beside it.
#
# THE RULE, stated once and applied to every unit:
#
#     candidate_u = max( median of the historical RELATIVE deltas for u,
#                        the worst relative delta on a ZERO-LEAN control commit,
#                        the measured within-commit relative spread )
#     budget_u    = MULT x candidate_u,  floored at @floor absolute milliseconds
#
# The three terms are three different things and the max is deliberate: the first
# says what a batch costs, the second says what a commit that changed NOTHING
# appeared to cost, and the third says what the instrument can resolve. A gate
# under any of them is not a gate — under the first it fires on ordinary work,
# under the second and third it reports the machine.
#
# MULT is then the smallest multiple at which EVERY batch in the window passes,
# rounded up: a gate registered at a multiple that would have failed a batch
# which actually landed is a gate calibrated to reject its own history.
# ⭐⭐⭐ THE RULE, EXTRACTED SO THERE IS EXACTLY ONE OF IT (D151, QUEUE item 4d).
#
# `register_budget` used to BE this computation.  Item 4d needs the same rule
# applied to a DIFFERENT QUANTITY — the child's `user` CPU instead of the
# profiler's `type checking` ms — and the tempting way to get that is a second
# copy with the extractor swapped.  D148 §2 is exactly what that costs: a
# referee invented beside a shipped rule turned out to be LOOSER than the gate it
# refereed, and it disagreed in the flattering direction.
#
# ⇒ ONE RULE, PARAMETERISED BY THE QUANTITY.  `extract(reading, decl_names) ->
# {unit: value}` is the only thing that varies, so any difference between the
# shipped budgets and a candidate's is a difference between the QUANTITIES and
# cannot be a difference between two implementations of the rule.
# [[feedback-duplicate-born-in-agreement]] [[feedback-widening-a-gate-needs-a-second-source]]
# ⭐ THE REGISTERED MULTIPLE, AS A FUNCTION, for the same reason `budget_info`
# is one: item 4d's report prices each arm's MDR as `budget% x level`, and a `2.0`
# typed there is a copy of this rule that agrees until someone re-registers at a
# different multiple. One rule, every caller.
# [[feedback-duplicate-born-in-agreement]]
def registered_mult(need):
    """The smallest multiple at which every batch in the window passes, floored
    at 2.0 so the unit that BINDS the gate keeps headroom (see the note below)."""
    return max(2.0, math.ceil(need * 10) / 10.0)


def budget_info(rows, extract, decl_names):
    """(info, meta) for one quantity.  No file is written and nothing is gated."""
    order, per = [], {}
    for r in rows:
        per.setdefault(r["commit"], []).append(r)
        if r["commit"] not in order:
            order.append(r["commit"])
    seq = order
    med, spread = {}, {}
    for c in seq:
        us = [extract(r, decl_names) for r in per[c]]
        keys = set().union(*[set(u) for u in us]) if us else set()
        med[c] = {k: statistics.median([u[k] for u in us if k in u]) for k in keys}
        spread[c] = {k: (max(v) - min(v)) if len(v := [u[k] for u in us if k in u]) > 1
                     else 0.0 for k in keys}
    zero_lean = set()
    for a, b in zip(seq, seq[1:]):
        ch = subprocess.run(["git", "diff", "--name-only", a, b],
                            cwd=ROOT, capture_output=True, text=True).stdout.split()
        if not any(x.endswith(".lean") for x in ch):
            zero_lean.add(b)
    all_u = sorted(set().union(*[set(med[c]) for c in seq])) if seq else []
    info = _unit_info(seq, med, spread, all_u, zero_lean)
    meta = {"seq": seq, "med": med, "spread": spread, "zero_lean": zero_lean,
            "all_u": all_u, "rows": len(rows)}
    if info:
        meta["need"] = max(i["worst"] / i["cand"] for i in info.values())
        meta["binding"] = max(info, key=lambda u: info[u]["worst"] / info[u]["cand"])
        # the @floor candidate: the worst within-commit spread among SMALL units
        SMALL_MS = 50.0
        worst_spread = 0.0
        for c in seq:
            for u in all_u:
                if u in med[c] and med[c][u] <= SMALL_MS:
                    worst_spread = max(worst_spread, spread[c].get(u, 0.0))
        meta["floor_candidate"] = max(math.ceil(worst_spread), 1.0)
    return info, meta


def _unit_info(seq, med, spread, all_u, zero_lean):
    info = {}
    for u in all_u:
        rels, ctrl, noise = [], [], []
        for a, b in zip(seq, seq[1:]):
            ba, bb = med[a].get(u), med[b].get(u)
            if ba is None or bb is None or ba <= 0:
                continue
            r = 100.0 * (bb - ba) / ba
            rels.append((r, b))
            if b in zero_lean:
                ctrl.append(abs(r))
        for c in seq:
            if med[c].get(u, 0) > 0:
                noise.append(100.0 * spread[c].get(u, 0.0) / med[c][u])
        if not rels:
            continue
        cand = max(statistics.median([r for r, _ in rels]),
                   max(ctrl) if ctrl else 0.0,
                   max(noise) if noise else 0.0, 0.01)
        worst, worst_c = max(rels, key=lambda t: t[0])
        info[u] = {"cand": cand, "med": statistics.median([r for r, _ in rels]),
                   "ctrl": max(ctrl) if ctrl else 0.0,
                   "noise": max(noise) if noise else 0.0,
                   "worst": worst, "worst_commit": worst_c[:9],
                   "base": statistics.median([med[c][u] for c in seq if u in med[c]])}
    return info


def register_budget(path, out, decl_names, mult=None, floor=None):
    rows = [json.loads(l) for l in open(path, encoding="utf-8") if l.strip().startswith("{")]
    info, meta = budget_info(rows, units, decl_names)
    seq, med, spread = meta["seq"], meta["med"], meta["spread"]
    all_u, zero_lean = meta["all_u"], meta["zero_lean"]
    need, binding = meta["need"], meta["binding"]
    # ⛔⛔ THE FIRST GENERATION OF THIS FILE REGISTERED `MULT = ceil(need)` — 1.4
    # against a needed 1.40 — AND THAT IS A GATE WITH ZERO HEADROOM ON THE UNIT
    # THAT BINDS IT. `vectorCoverage`'s worst batch in the window would have sat
    # exactly ON its budget, so the next batch costing what that one cost fires
    # the gate, and a gate that fires on ordinary work is the chore this
    # repository has recorded three times. The registered multiple is therefore
    # STATED and larger, and the file prints both numbers and the margin between
    # them rather than describing a rule its own value does not follow.
    if mult is None:
        mult = registered_mult(need)
    if floor is None:
        # ⛔⛔ THE FIRST VERSION OF THIS RULE TOOK THE WORST ABSOLUTE CONTROL DELTA
        # OVER **ALL** UNITS AND IT GENERATED A FLOOR OF 800 ms — `Tests.Coverage`'s
        # noise, in milliseconds, handed to `X86.Syntax`, whose whole reading is
        # 200 ms. That is a borrowed denominator wearing a floor's name: one unit's
        # scale lent to another, and it would have made the gate toothless on
        # exactly the unit whose real margin was two milliseconds
        # ([[feedback-a-borrowed-denominator-invents-its-own-gap]]).
        #
        # ⭐ THE FLOOR EXISTS FOR SMALL UNITS AND IS THEREFORE MEASURED ON SMALL
        # UNITS. Every unit above `SMALL_MS` already has a relative budget far
        # larger than any floor; the floor binds only where a percentage of a
        # two-millisecond module would be a rounding error, so it is the worst
        # absolute apparent delta a zero-Lean commit produced THERE.
        # ⛔⛔ AND THE SECOND VERSION WAS WRONG TOO, IN A THIRD WAY: it took the
        # worst DELTA on a zero-Lean commit (2 ms) while the gate's refusal
        # THEN compared a budget against the run's own SPREAD (it no longer does
        # — D141; this paragraph is the history of the number). Those are different
        # statistics of the same readings, and the spread is systematically the
        # larger — measured, 5.30 ms on `X86Native` against a 2 ms delta-derived
        # floor. A gate registered on the first would REFUSE on small modules
        # whenever an ordinary run was as noisy as this walk already was.
        #
        # ⇒ 🔑 A THRESHOLD MUST BE DERIVED FROM THE STATISTIC IT WILL BE COMPARED
        # AGAINST — which is why this line is now on notice. When it was written
        # the refusal read `budget < spread`; since D141 it reads as a band around
        # the DELTA, and the floor is no longer constrained to clear any spread.
        # ⛔ IT IS LEFT AS IT WAS ON PURPOSE. Re-deriving it would move an
        # ALLOWANCE in the same commit that moved a RULE, and the two would not be
        # separable afterwards. A floor is a minimum allowance, so the direction of
        # the staleness is known: this one can only be too generous, never too
        # tight, and re-deriving it against the band is an open item.
        # ⚠️ Anything reading this to justify the number should read D141 first.
        #
        # ⚠️ AND NO EXTRA MULTIPLE IS APPLIED TO IT, deliberately. A run noisier
        # than the worst this walk saw SHOULD refuse rather than pass; padding the
        # floor to prevent that would buy silence with the one verdict that says
        # the instrument could not see.
        floor = meta["floor_candidate"]
    with open(out, "w", encoding="utf-8") as fh:
        fh.write(f"""# KERNEL-TIME DELTA BUDGETS — GENERATED by
# `scripts/kernel_delta_history.py --register-budget`, from a measured walk over
# {len(seq)} commits x {len(rows)//max(len(seq),1)} sweeps, whose RAW READINGS are committed beside it at
# `{os.path.relpath(path, ROOT)}` — a timing walk cannot be re-derived on
# another day, so the readings ARE the evidence and are kept rather than cited.
# Re-analyse them with `--analyse`; re-register with `--register-budget`.
# DO NOT EDIT BY HAND: every number below
# is derived, and the derivation is printed beside it so that it can be
# CORRECTED rather than only recomputed.
#
# THE RULE (one rule, every unit):
#   candidate = max(median historical relative delta,
#                   worst relative delta on a commit that changed NO .lean file,
#                   worst measured within-commit relative spread)
#   budget    = MULT x candidate, floored at @floor absolute milliseconds
#
# MULT = {mult:g}, REGISTERED. The smallest multiple at which every batch in the
# window passes is {need:.2f} — set by `{binding}`, whose worst batch in the window
# cost exactly {need:.2f}x its candidate. Registering AT that number would leave
# ZERO headroom on the unit that binds it, so the next batch costing what that one
# cost fires the gate; the registered multiple buys {mult/need:.2f}x margin over the worst
# batch in the window, and that margin is the number to argue with.
# ⛔ A gate registered below {need:.2f} would reject a batch that actually landed. A gate
# registered far above it is a tripwire with headroom nobody polices. Both numbers
# are printed so neither can hide.
#
# @floor = {floor:g} ms — the worst WITHIN-COMMIT SPREAD this walk measured among the
# units under 50 ms, i.e. the resolution this box has on a module a percentage
# cannot express.
# ⛔ TWO EARLIER RULES FOR THIS NUMBER WERE GENERATED, READ AND REFUSED. Taken as
# the worst apparent delta over EVERY unit it read 800 ms — `Tests.Coverage`'s
# noise lent to a module whose entire reading is 200 ms. Taken as the worst
# apparent DELTA among small units it read 2 ms — against a within-commit spread
# on those same units of 5.30 ms.
# ⚠️⚠️ AND THE REASON THAT SETTLED IT HAS SINCE EXPIRED (D141, 2026-09-05). It read:
# *"the gate's refusal compares a budget against the run's SPREAD, not against a
# delta, so a threshold must be derived from the statistic it will be compared
# against."* The refusal no longer reads `budget < spread` — it asks whether a band
# of K standard errors around the DELTA straddles the budget — so the floor is no
# longer constrained to clear a spread at all.
# ⛔ THE NUMBER IS DELIBERATELY UNCHANGED, AND THE DIRECTION IS STATED. A floor is a
# MINIMUM ALLOWANCE, so 6 ms is now slightly LOOSER on tiny modules than a
# band-derived floor would be; re-deriving it in the same commit as the rule change
# would make a rule repair and an allowance change indistinguishable, which is the
# one thing this file's own history says not to do. The re-derivation is an OPEN
# ITEM and it can only tighten. ⇒ 🔑 A JUSTIFICATION OUTLIVES THE CONDITION THAT
# MADE IT TRUE, and it outlives it INSIDE A GENERATED FILE, where byte-for-byte
# re-derivation proves the file matches the script and never that the script is
# still right.
#
# ⛔ THE UNITS ARE PERCENTAGES BECAUSE A PERCENTAGE TRAVELS.  The same tree reads
# 1.7x-3.1x slower on a GitHub runner DEPENDING ON THE MODULE, so an absolute
# allowance is a fact about this box; a ratio of two readings of the same unit on
# the same machine divides that factor out. See `.github/workflows/ci.yml`.
#
# derivation, per unit (all figures are percentages of the unit's own base):
#   {'UNIT':<50}{'base(ms)':>10}{'med%':>8}{'ctrl%':>8}{'noise%':>8}{'cand%':>8}{'worst%':>8}  worst at
""")
        for u in sorted(info):
            i = info[u]
            fh.write(f"#   {u:<50}{i['base']:>10.1f}{i['med']:>8.2f}{i['ctrl']:>8.2f}"
                     f"{i['noise']:>8.2f}{i['cand']:>8.2f}{i['worst']:>8.2f}  "
                     f"{i['worst_commit']}\n")
        fh.write(f"\n@floor {floor:g}\n")
        # ⛔ AND A @default, because a unit this walk never saw must not be
        # ungated: a declared list's gaps all fall the way its default points.
        # ⛔ THE DEFAULT IS THE MEDIAN CANDIDATE, NOT THE LARGEST.
        # A default taken from the loosest unit (58% here, `Tests.VectorRuns`, a
        # 0.3 ms file) would hand every future module an allowance nobody chose
        # for it, and that is the direction nobody polices. A unit that falls to
        # the default is LISTED by the gate on every run, so a module landing here
        # by accident is visible rather than silently free.
        fh.write(f"@default "
                 f"{mult * statistics.median([i['cand'] for i in info.values()]):.1f}%\n")
        for u in sorted(info):
            fh.write(f"{u} {mult * info[u]['cand']:.1f}%\n")
    print(f"wrote {out}: MULT {mult:g} (needed {need:.2f}), @floor {floor:g} ms, "
          f"{len(info)} units")
    return 0


# ── THE WALK ORDER ───────────────────────────────────────────────────────────
def visit_order(commits, sweeps, interleave):
    """[(sweep, commit)] in the order they are visited.

    "sweeps"      forward over all N, then REVERSE, then forward…  (the default)
    "interleaved" every repeat of a commit back to back, in forward order.

    ⚖️ WHY BOTH EXIST, AND WHY THE COST OF THE SECOND WAS MEASURED BEFORE IT WAS
    BUILT (2026-09-09).  The default's reversal is justified in this file's
    docstring as cancelling "monotone drift in machine load" — a mechanism that
    had never been scored.  Scored over the three committed 24-reading corpora,
    against ELAPSED time, with each key normalised by its own night-median:

        corpus    r(visit, level)   drift %/hour      r(visit, load1)
        QUIET          -0.186          -3.75              +0.062
        USER2          +0.243          +3.63              +0.236
        NIGHT3         +0.088          +1.94              +0.279
        n = 24 each; the 5% critical |r| at df=22 is ~0.404 and NOTHING reaches it,
        and the three SIGNS DISAGREE.

    ⇒ **No monotone drift is detectable, so the reversal is cancelling something
    that has not been shown to exist.**  And taking the slopes at face value
    anyway — which the correlations do not license — the bias interleaving would
    put on an adjacent-commit delta is `slope x 2 x (seconds per reading)`:
    **0.08% to 0.19% of level.**  ⭐ That bound does NOT grow with the number of
    commits or the length of the night: under interleaving a commit's two
    readings are always ~one reading apart, whatever N is.  Against per-commit
    p95 spreads measured at 6%-83% on the same corpora, it is two to three orders
    of magnitude below the noise it would sit in.

    ⛔ SO A COUNTERBALANCED INTERLEAVE (`c1 c2 c2 c1 | c3 c4 c4 c3`) WAS DESIGNED
    AND DROPPED.  It would cancel the drift exactly within each block at the cost
    of making the gate speak after FOUR readings instead of two — and a safeguard
    is not evidence that its absence would cost anything.  Here the absence was
    measured and costs 0.2%.  [[feedback-a-state-added-for-a-defect]]

    ⚠️ WHAT THIS DOES NOT SAY: that the two orders give the same answer on any
    particular night.  It says the systematic term separating them is bounded and
    small.  Every row records `walk_order`, so a corpus states which order
    produced it instead of leaving a reader to infer it from the timestamps.
    """
    if sweeps < 1:
        raise ValueError("a walk needs at least one sweep")
    if interleave:
        return [(s, c) for c in commits for s in range(sweeps)]
    out = []
    for s in range(sweeps):
        seq = commits if s % 2 == 0 else list(reversed(commits))
        out += [(s, c) for c in seq]
    return out


# ── THE ORDER'S OWN ARMS ─────────────────────────────────────────────────────
def selftest():
    """Pure: no worktree, no profile, no box.  `visit_order` is the whole subject."""
    bad = []

    def ok(cond, what, plant=None):
        print(f"   {'ok  ' if cond else '⛔ FAIL'} [{'RED ' if plant else 'CTRL'}] {what}")
        if not cond:
            bad.append(what)

    C = [f"c{i}" for i in range(5)]
    sw = visit_order(C, 2, False)
    il = visit_order(C, 2, True)

    ok(sorted(sw) == sorted(il),
       "CONTROL — the two orders are the SAME MULTISET of (sweep, commit): the "
       "order changes WHEN a reading is taken, never WHICH readings are taken")
    ok([c for _s, c in sw] == C + list(reversed(C)),
       "CONTROL — the default is forward then REVERSE, unchanged")
    ok([c for _s, c in il] == [c for c in C for _ in range(2)],
       "the interleaved order takes a commit's repeats BACK TO BACK", plant="interleaved")
    ok(len(visit_order(C, 3, True)) == 15 and
       [c for _s, c in visit_order(C, 3, True)][:3] == ["c0"] * 3,
       "interleaving generalises to --sweeps 3", plant="three-sweeps")
    try:
        visit_order(C, 0, False); fired = False
    except ValueError:
        fired = True
    ok(fired, "a walk with ZERO sweeps is REFUSED, not silently empty "
              "[[feedback-an-unparseable-gate-file-reports-failure-not-absence]]",
       plant="zero-sweeps")

    # ⭐ THE PROPERTY THE HELM ASKED FOR, DRIVEN: when can a per-commit gate first speak?
    def first_pair(seq):
        seen = {}
        for k, (_s, c) in enumerate(seq, 1):
            seen[c] = seen.get(c, 0) + 1
            if seen[c] == 2:
                return k
        return None
    N = len(C)
    ok(first_pair(il) == 2,
       "under --interleave the FIRST commit has both readings at reading 2, so a "
       "per-commit gate is evaluable from the second reading", plant="early-2")
    ok(first_pair(sw) == N + 1,
       f"under the default NO commit has a pair until reading {N + 1} of {2 * N} — "
       f"the gate cannot speak in the first half of the run at all", plant="early-late")
    ok(first_pair(il) < first_pair(sw),
       "CONTROL — the two arms above are compared in the same run, so the claim is "
       "a DIFFERENCE and not two remembered numbers")

    print("SELFTEST " + ("⛔ FAILED" if bad else "ok"))
    return 1 if bad else 0


def main():
    decl_names = [x for x in (arg("--decl-names") or
                              "memDestSweep,pre_states_have_a_returnable_frame,"
                              "vectorCoverage").split(",") if x]
    if "--register-budget" in sys.argv:
        m = arg("--mult")
        f = arg("--floor")
        return register_budget(arg("--readings") or arg("--out")
                               or os.path.join(tempfile.gettempdir(),
                                               "kernel-delta-history.jsonl"),
                               arg("--register-budget"), decl_names,
                               float(m) if m else None, float(f) if f else None)
    if "--analyse" in sys.argv:
        return analyse(arg("--analyse"), decl_names)
    if "--selftest" in sys.argv:
        return selftest()
    commits = [c for c in (arg("--commits") or "").split(",") if c]
    if not commits:
        print(__doc__)
        return 2
    sweeps = int(arg("--sweeps", "2"))
    interleave = "--interleave" in sys.argv
    out = arg("--out", os.path.join(tempfile.gettempdir(), "kernel-delta-history.jsonl"))
    # ⛔ THE WORKTREE IS UNDER TMPDIR AND IS REMOVED AT THE END, PASS OR FAIL.
    wt = tempfile.mkdtemp(prefix="x86lean-history-")
    shutil.rmtree(wt)
    git("worktree", "add", "--detach", wt, commits[0])
    fh = open(out, "a", encoding="utf-8")
    try:
        for s, c in visit_order(commits, sweeps, interleave):
            git("checkout", "--detach", c, cwd=wt)
            t0 = time.time()
            r = profile(wt)
            r["commit"] = git("rev-parse", c)
            r["sweep"] = s
            r["walk_order"] = "interleaved" if interleave else "sweeps"
            r["secs"] = round(time.time() - t0, 1)
            fh.write(json.dumps(r) + "\n")
            fh.flush()
            print(f"sweep {s}  {c[:9]}  load1={fmt_load(r['load1'])}  "
                  f"{r['secs']:.0f}s  Tests.Coverage={r['modules'].get('Tests.Coverage',0):.0f}  "
                  f"X86.Syntax={r['modules'].get('X86.Syntax',0):.1f}", flush=True)
    finally:
        fh.close()
        subprocess.run(["git", "worktree", "remove", "--force", wt],
                       cwd=ROOT, capture_output=True, text=True)
    print(f"\nreadings → {out}")
    return analyse(out, decl_names)



# ⛔ GUARDED (D151's sweep).  An unguarded `sys.exit(main())` means `import <this
# module>` RUNS the tool and then exits the importer — `kernel_cost.py` cost a
# two-minute profiling pass and a killed probe before this was noticed, and
# `kernel_delta.py` had already been given the same guard by D148.  Two prior
# namings and the siblings were never swept for.
# [[feedback-naming-a-defect-is-not-finding-its-siblings]]
if __name__ == "__main__":
    sys.exit(main())
