#!/usr/bin/env python3
"""THE DELTA GATE — the only kernel-time verdict this box can honestly reach.

⚖️ **RULED BY THE HELM, 2026-09-04 21:42**, on the evidence of D111, D121 and
D122: *"the absolute ceilings are retired as a MERGE GATE and kept as READINGS
printed beside every merge (the two numbers, box-stamped); D111's delta method is
the gate — you set the per-batch delta budget from your own batch history, print
the last ten batches' deltas, budget = a stated multiple of their median with the
reason, register it in the repo's CI as the check that runs, red-first driven (a
planted constructor that doubles the delta must fail)."*

## WHY THE ABSOLUTE CEILINGS COULD NOT STAY THE GATE

`scripts/kernel_ceilings.txt` holds absolute millisecond ceilings, and on this
machine the UNCHANGED PARENT of the batch under test was already over two of them
(D122): `Tests.Coverage`'s residue on master, in band, and `X86.Syntax` at 198 of
200 — a **two-millisecond margin**, which the next AST constructor of any kind
crosses. A gate no commit can pass reports the same red for a good batch and a
bad one, and the across-session shift at ONE commit was measured at 11% while the
margin was 6% (D111).

⇒ 🔑 **A CEILING WHOSE MARGIN IS UNDER THE MACHINE'S OWN SPREAD REPORTS THE
MACHINE, NOT THE CODE.** The absolutes are still printed here, box-stamped, as
readings — a reading is not a verdict, and this file is careful never to let one
read as the other.

## WHAT THIS GATE MEASURES

The CHANGE in kernel (type-checking) time that a commit introduces, between two
trees profiled in ONE session on ONE box, with the passes ALTERNATED
(base, head, base, head, …) so that a load that drifts through the run biases
both sides equally instead of one of them.

The gated units are every module's kernel total, plus — for a module that gates
declarations in `kernel_ceilings.txt` — each of those declarations and the
RESIDUE (module total minus them). Every unit is gated: a unit named in
`scripts/kernel_delta_budget.txt` gets its own budget, and a unit that is not
named falls to the file's `@default`. ⛔ There is no third case — a unit with
neither is an ERROR, because a declared list's gaps all fall the way its default
points and that direction is the one nobody polices.

## THE THREE VERDICTS, AND WHY THE MIDDLE ONE EXISTS

* **CLEAN** — every unit's delta is within its budget.
* **FAILED** (rc 1) — some unit's delta exceeds its budget. The code got more
  expensive to check by more than the batch history says a batch costs.
* **UNMEASURABLE** (rc 3) — some unit's budget is SMALLER THAN THE SPREAD THIS
  RUN ITSELF MEASURED between repeats of the SAME tree. That is not a verdict
  about the commit and must not be reported as one: the instrument could not
  resolve the quantity being gated.

⭐ The third verdict is what replaces `kernel_cost.py`'s load-average band, and it
is strictly better evidence: the band is a HEURISTIC about the machine calibrated
on four readings months of batches ago, while this is the machine's spread
MEASURED IN THE SAME RUN, on the same trees, by the same profiler. A gate that
can measure its own noise does not need to guess at it from `uptime`.

## WHAT IT DOES NOT DO

⛔ It does not touch the working tree. Both sides are detached worktrees under
`TMPDIR`, removed at the end. A probe that writes the repository makes
`git add -A` a race, and that race pushed a planted defect to both remotes once
already (D75).

⛔ It does not derive any budget from the commit under test. The budget comes
from `scripts/kernel_delta_budget.txt`, whose numbers are the measured deltas of
the TEN PRECEDING BATCHES (`scripts/kernel_delta_history.py`), and the commit
under test contributes nothing to its own allowance.

usage:
  kernel_delta.py [--base REV] [--head REV] [--repeats N] [--budget FILE]
  kernel_delta.py --readings FILE            re-run the VERDICT over saved readings
  kernel_delta.py --selftest                 the comparison arms (seconds)
  kernel_delta.py --selftest-measure         the two arms that need real trees
"""
import os, re, sys, json, time, shutil, socket, platform, statistics, subprocess, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
KCOST = os.path.join(ROOT, "scripts", "kernel_cost.py")
BUDGET_FILE = os.environ.get("X86LEAN_DELTA_BUDGET",
                             os.path.join(ROOT, "scripts", "kernel_delta_budget.txt"))
CEIL_FILE = os.path.join(ROOT, "scripts", "kernel_ceilings.txt")
DEFAULT_TAG = "@default"
FLOOR_TAG   = "@floor"


def arg(name, default=None):
    for i, a in enumerate(sys.argv):
        if a == name and i + 1 < len(sys.argv):
            return sys.argv[i + 1]
    return default


def git(*a, cwd=ROOT, check=True):
    r = subprocess.run(["git"] + list(a), cwd=cwd, capture_output=True, text=True)
    if check and r.returncode != 0:
        print(f"⛔ git {' '.join(a)} failed in {cwd}:\n{r.stdout}\n{r.stderr}")
        sys.exit(2)
    return r.stdout.strip()


# ⭐ THE GATED DECLARATIONS COME FROM THE CEILING FILE, so the delta gate and the
# reading gate are talking about the SAME declarations. Two lists that agree
# today diverge on the next ordinary append to one of them, and the divergence is
# silent in whichever direction nobody is looking.
def gated_declarations():
    """{module: [decl, …]} exactly as `kernel_ceilings.txt` gates them."""
    out = {}
    if os.path.exists(CEIL_FILE):
        for line in open(CEIL_FILE):
            p = line.split("#")[0].strip().split()
            if len(p) == 4 and p[1] == "@decl":
                out.setdefault(p[0], []).append(p[2])
    return out


# ⭐⭐⭐ A BUDGET MAY BE ABSOLUTE OR RELATIVE, AND THE RELATIVE ONE IS THE PORTABLE
# HALF.  This is the whole reason the delta method can be registered on a runner
# when the absolute ceilings could not.
#
# `.github/workflows/ci.yml` records why the ceilings cannot travel: the same
# tree profiled on a GitHub runner and locally differs by a factor that VARIES
# PER MODULE — 1.7x on `memDestSweep`, 3.1x on `vectorCoverage`, 2.1x overall —
# so no single calibration constant exists and raising the ceilings to fit would
# leave them ~2x slack where batches are developed.
#
# ⇒ 🔑 THE VERY FACT THAT REFUTES A PORTABLE CEILING IS WHAT MAKES A PORTABLE
# RATIO WORK.  That factor is a property of (machine, unit); a RATIO of two
# readings of the SAME unit on the SAME machine divides it out exactly, whatever
# its value, because it appears in the numerator and the denominator.
#
# ⚠️ AND THAT IS A PREDICTION, NOT A MEASUREMENT.  It follows from the factor
# being multiplicative and stable within one session, which the CI table supports
# for ABSOLUTE readings but which nothing has yet tested for a matched DELTA on
# two machines — this account has no runner (GitHub Actions refuses every job for
# billing, desk FH). The first delta this gate prints on a runner is that test,
# and it is the reading to compare with the local one, not to trust.
#
# ⛔ A RATIO IS MEANINGLESS ON A UNIT TOO SMALL TO MEASURE.  `X86.Flags` reads
# 2.4 ms; 8% of it is 0.2 ms, well under the run-to-run spread of anything. So a
# relative budget is floored by `@floor`, an absolute number, and a unit whose
# floor still cannot beat the measured spread REFUSES rather than passing.
def read_budgets(path):
    """(default, {unit: budget}, floor_ms) where a budget is ("abs"|"rel", value).

    ⛔ THE BUDGET IS THE LAST FIELD AND THE UNIT IS EVERYTHING BEFORE IT, because
    a unit name legitimately contains spaces (`Tests.Coverage @decl memDestSweep`)
    and a positional split would bet that it never grows another word."""
    if not os.path.exists(path):
        print(f"⛔ no budget file at {path}. A delta gate with no allowance is not "
              f"a gate; run scripts/kernel_delta_history.py and register one.")
        sys.exit(2)
    default, per, floor = None, {}, None
    for line in open(path):
        line = line.split("#")[0].strip()
        if not line:
            continue
        parts = line.rsplit(None, 1)
        if len(parts) != 2:
            print(f"⛔ unparseable budget line: {line!r}")
            sys.exit(2)
        unit, val = parts[0].strip(), parts[1]
        kind = "rel" if val.endswith("%") else "abs"
        try:
            v = float(val[:-1] if kind == "rel" else val)
        except ValueError:
            print(f"⛔ budget line does not end in a number or a percentage: {line!r}")
            sys.exit(2)
        if unit == FLOOR_TAG:
            if kind != "abs":
                print(f"⛔ {FLOOR_TAG} must be absolute milliseconds: {line!r}")
                sys.exit(2)
            floor = v
        elif unit == DEFAULT_TAG:
            default = (kind, v)
        else:
            per[unit] = (kind, v)
    if floor is None and (default and default[0] == "rel"
                          or any(k == "rel" for k, _ in per.values())):
        print(f"⛔ a relative budget is registered but no {FLOOR_TAG}. A percentage "
              f"of a two-millisecond module is not an allowance, it is a rounding "
              f"error, and a gate whose budget is under its own noise reports the "
              f"machine.")
        sys.exit(2)
    return default, per, floor


def effective(budget, base, floor):
    """A budget's value in milliseconds for one unit's base reading."""
    kind, v = budget
    return v if kind == "abs" else max(v / 100.0 * base, floor or 0.0)


def units_of(reading, decl_map):
    """The gateable quantities of ONE reading, flattened to {unit: ms}."""
    out = dict(reading["modules"])
    for mod, names in decl_map.items():
        total = reading["modules"].get(mod)
        if total is None:
            continue
        got = reading.get("decls", {}).get(mod, {})
        named = 0.0
        for n in names:
            if n in got:
                out[f"{mod} @decl {n}"] = got[n]
                named += got[n]
        out[f"{mod} @residue"] = total - named
    return out


def profile(worktree, decl_mods):
    r = subprocess.run([sys.executable, KCOST, "--emit-json", "--root", worktree,
                        "--decl-modules", ",".join(decl_mods)],
                       capture_output=True, text=True)
    if r.returncode != 0:
        # ⛔ A GATE THAT REFUSES MUST SAY WHAT IT SAW (D94): a refusal with no
        # reading attached turns a remote failure into a local re-run, and for a
        # TIMING gate the local re-run answers a different question.
        print(f"⛔ the profiler failed on {worktree}:\n{r.stdout}\n{r.stderr}")
        sys.exit(2)
    for line in reversed(r.stdout.splitlines()):
        if line.startswith("{"):
            return json.loads(line)
    print(f"⛔ the profiler produced no JSON for {worktree}:\n{r.stdout}\n{r.stderr}")
    sys.exit(2)


# ⭐ THE BASE IS "THE TREE THIS CHANGE IS A CHANGE TO", and which commit that is
# depends on where the head sits: a branch's base is where it left the trunk, a
# trunk commit's base is its parent.
#
# ⛔ AND THE TRUNK MAY NOT BE A LOCAL BRANCH.  `actions/checkout` leaves a runner
# with a detached HEAD and no local `master`, so a gate that only knows the name
# `master` reports a git error on the machine it was registered for.  The
# candidates are tried in order and the one that RESOLVES is used; if none does,
# the gate refuses rather than inventing a base.
def resolve_base(head):
    trunk = None
    for cand in ("master", "origin/master", "refs/remotes/origin/master"):
        if subprocess.run(["git", "rev-parse", "--verify", "--quiet", cand],
                          cwd=ROOT, capture_output=True).returncode == 0:
            trunk = cand
            break
    if trunk is None:
        print("⛔ no `master` or `origin/master` in this clone, so the base of "
              "this change cannot be resolved. Pass --base explicitly; a gate "
              "that guessed one would be comparing against a tree nobody chose.")
        sys.exit(2)
    on_trunk = subprocess.run(["git", "merge-base", "--is-ancestor", head, trunk],
                              cwd=ROOT, capture_output=True).returncode == 0
    return git("rev-parse", f"{head}^") if on_trunk else git("merge-base", trunk, head)


def box_stamp():
    try:
        la1, la5, la15 = os.getloadavg()
        load = f"{la1:.2f}/{la5:.2f}/{la15:.2f}"
    except OSError:
        load = "unavailable"
    return (f"BOX {socket.gethostname()} · {platform.platform()} · "
            f"{os.cpu_count()} cpus · load(1/5/15) {load} · "
            f"{time.strftime('%Y-%m-%d %H:%M:%S %Z')}")


def measure(base_rev, head_rev, repeats, keep=None, plant=None):
    """Alternating passes over two detached worktrees. Returns a readings dict.

    ⚠️ THE ALTERNATION IS THE METHOD AND NOT A FLOURISH. Profiling one tree three
    times and then the other three times measures the difference between the
    first half of the run and the second half as surely as it measures the
    difference between the trees; interleaving makes a monotone drift cancel."""
    decl_map = gated_declarations()
    decl_mods = sorted(decl_map)
    tmp = keep or tempfile.mkdtemp(prefix="x86lean-delta-")
    base_wt, head_wt = os.path.join(tmp, "base"), os.path.join(tmp, "head")
    made = []
    try:
        for wt, rev in ((base_wt, base_rev), (head_wt, head_rev)):
            if not os.path.exists(wt):
                git("worktree", "add", "--detach", wt, rev)
                made.append(wt)
        if plant:
            plant(head_wt)
        readings = {"base": [], "head": []}
        for _ in range(repeats):
            for side, wt in (("base", base_wt), ("head", head_wt)):
                t0 = time.time()
                r = profile(wt, decl_mods)
                r["secs"] = round(time.time() - t0, 1)
                readings[side].append(r)
                print(f"  pass {side:<4} load1={r['load1']:.2f}  {r['secs']:>4.0f}s  "
                      f"Tests.Coverage={r['modules'].get('Tests.Coverage', 0):.0f}  "
                      f"X86.Syntax={r['modules'].get('X86.Syntax', 0):.1f}", flush=True)
        return {"base_rev": git("rev-parse", base_rev),
                "head_rev": git("rev-parse", head_rev),
                "planted": bool(plant), "box": box_stamp(),
                "decl_map": decl_map, "readings": readings}
    finally:
        if keep is None:
            for wt in made:
                subprocess.run(["git", "worktree", "remove", "--force", wt],
                               cwd=ROOT, capture_output=True, text=True)
            shutil.rmtree(tmp, ignore_errors=True)


def verdict(data, default_ms, budgets, floor=None, quiet=False):
    """(rc, lines) — the whole comparison, over readings that are already taken.

    Split out from `measure` so that every failure mode of the COMPARISON can be
    driven red in seconds against saved readings, instead of only after a
    seven-minute measurement that would make the probe too expensive to run."""
    L = []
    def p(s=""):
        L.append(s)
        if not quiet:
            print(s)
    decl_map = data["decl_map"]
    sides = {s: [units_of(r, decl_map) for r in data["readings"][s]] for s in ("base", "head")}
    p(data["box"])
    p(f"base {data['base_rev'][:9]}   head {data['head_rev'][:9]}"
      + ("   ⚠️ PLANTED HEAD — this run is a PROBE" if data.get("planted") else ""))
    p(f"repeats per side: {len(sides['base'])} (passes alternated base/head)")
    p(f"loads: " + " ".join(f"{r['load1']:.2f}" for s in ("base", "head")
                            for r in data["readings"][s]))
    all_units = sorted(set().union(*[set(u) for u in sides["base"] + sides["head"]]))
    p()
    p(f"{'UNIT':<56}{'base':>10}{'head':>10}{'delta':>10}{'spread':>9}{'budget':>9}  VERDICT")
    fail, refuse, defaulted, flags = False, False, [], []
    for u in all_units:
        bs = [x[u] for x in sides["base"] if u in x]
        hs = [x[u] for x in sides["head"] if u in x]
        if not bs:
            flags.append(f"NEW unit in head: {u}")
        if not hs:
            flags.append(f"unit GONE from head: {u} "
                         f"(renamed, deleted, or below the profiler threshold)")
        b = statistics.median(bs) if bs else 0.0
        h = statistics.median(hs) if hs else 0.0
        d = h - b
        # ⚠️ THE SPREAD IS THE INSTRUMENT'S OWN NOISE, measured on the SAME trees
        # in the SAME run: the worst within-side range of the two sides. It is
        # what makes the refusal below a measurement rather than a guess.
        spread = max((max(bs) - min(bs)) if len(bs) > 1 else 0.0,
                     (max(hs) - min(hs)) if len(hs) > 1 else 0.0)
        if u in budgets:
            bud = effective(budgets[u], b, floor)
        elif default_ms is not None:
            bud = effective(default_ms, b, floor)
            defaulted.append(u)
        else:
            p(f"{u:<56}{b:>10.1f}{h:>10.1f}{d:>+10.1f}{spread:>9.1f}{'-':>9}  NO BUDGET ⛔")
            fail = True
            continue
        if bud < spread:
            v = "UNMEASURABLE ⛔"
            refuse = True
        elif d > bud:
            v = "OVER BUDGET ⛔"
            fail = True
        else:
            v = "ok"
        p(f"{u:<56}{b:>10.1f}{h:>10.1f}{d:>+10.1f}{spread:>9.1f}{bud:>9.1f}  {v}")
    p()
    if defaulted:
        # ⛔ A DEFAULT THAT IS NOT LISTED IS A LIST WITH INVISIBLE GAPS. Every
        # unit that fell to it is named, so that a unit quietly inheriting an
        # allowance nobody chose for it is visible in the gate's own output.
        p(f"⚠️  {len(defaulted)} unit(s) fell to {DEFAULT_TAG} "
          f"{default_ms[1]:g}{'%' if default_ms[0] == 'rel' else ' ms'}"
          + (f" (floor {floor:g} ms)" if default_ms[0] == "rel" else "") + ": "
          + ", ".join(defaulted))
    for f in flags:
        p(f"⚠️  {f}")
    if refuse:
        p(f"⛔ delta gate UNMEASURABLE — a budget below the spread this run itself "
          f"measured between repeats of the SAME tree. The readings above are "
          f"printed and are NOT a verdict about this commit: the instrument could "
          f"not resolve the quantity being gated. Re-run with more --repeats or on "
          f"a quieter box; do NOT widen the budget, which would derive the "
          f"allowance from the noise it is supposed to see through.")
        return 3, L
    if fail:
        p("⛔ delta gate FAILED (a unit's delta is over its budget, or has none).")
        return 1, L
    p("delta gate: CLEAN")
    return 0, L


# ⭐⭐ THE READINGS THE HELM ORDERED TO RIDE BESIDE EVERY MERGE.  The absolute
# ceilings are retired as a gate and kept as READINGS, box-stamped — printed
# here so that a merge's record carries both numbers without either of them
# being able to read as a verdict.
def absolute_readings(data):
    ceil = {}
    for line in open(CEIL_FILE):
        p = line.split("#")[0].strip().split()
        if len(p) == 4 and p[1] == "@decl":
            ceil[f"{p[0]} @decl {p[2]}"] = float(p[3])
        elif len(p) == 3 and p[1] == "@tail":
            ceil[f"{p[0]} @residue"] = float(p[2])
        elif len(p) == 2:
            ceil[p[0]] = float(p[1])
    print("\n--- ABSOLUTE READINGS (RETIRED AS A GATE, 09/04 21:42; box-stamped)")
    print(f"{'UNIT':<56}{'base':>10}{'head':>10}{'ceiling':>10}   base/head")
    # ⛔ THE CLOSING SENTENCE USED TO SAY "the unchanged parent was already over
    # TWO of them" — a literal, in a tool that is reading the very numbers that
    # would say so. Prose in a gate's own output is prose, and a count in it goes
    # stale exactly like a count in a comment (D41, D65, D94). It is DERIVED now,
    # and it names the units rather than counting them.
    over_base, over_head = [], []
    ub = [units_of(r, data["decl_map"]) for r in data["readings"]["base"]]
    uh = [units_of(r, data["decl_map"]) for r in data["readings"]["head"]]
    for u in sorted(set().union(*[set(x) for x in ub + uh])):
        if u not in ceil:
            continue
        b = statistics.median([x[u] for x in ub if u in x]) if any(u in x for x in ub) else float("nan")
        h = statistics.median([x[u] for x in uh if u in x]) if any(u in x for x in uh) else float("nan")
        if b > ceil[u]:
            over_base.append(u)
        if h > ceil[u]:
            over_head.append(u)
        print(f"{u:<56}{b:>10.1f}{h:>10.1f}{ceil[u]:>10.1f}   "
              f"{'over' if b > ceil[u] else 'under'}/"
              f"{'over' if h > ceil[u] else 'under'}")
    print(f"⚠️ These are READINGS, not a verdict. The BASE — the tree this change "
          f"is a change to, with none of it applied — is over "
          f"{len(over_base)} of these ceilings"
          + (": " + ", ".join(over_base) if over_base else "") + "; the head is over "
          f"{len(over_head)}" + (": " + ", ".join(over_head) if over_head else "")
          + ". A ceiling the parent already exceeds is an instrument scoped to the "
          "box, not to the commit (D111, D122).")


# ───────────────────────────── the probes ──────────────────────────────────

def _synthetic(base_vals, head_vals, repeats=2, jitter=0.0):
    """Readings with no measurement in them, for driving the COMPARISON red."""
    def side(vals, k):
        return [{"modules": {m: v + (jitter if i else 0.0) for m, v in vals.items()},
                 "decls": {}, "load1": 1.0, "load5": 1.0}
                for i in range(k)]
    return {"base_rev": "0" * 40, "head_rev": "1" * 40, "planted": False,
            "box": "BOX synthetic — no measurement in this run",
            "decl_map": {}, "readings": {"base": side(base_vals, repeats),
                                         "head": side(head_vals, repeats)}}


def selftest():
    """⛔ EVERY WAY THE COMPARISON COULD STOP LOOKING, DRIVEN SEPARATELY.

    These arms carry NO measurement: they feed the verdict function readings it
    cannot tell from real ones. That is deliberate and it is also the limit of
    what they prove — a green here says the comparison is sound and says NOTHING
    about whether the profiler can see a code change. `--selftest-measure` is the
    arm that creates that condition, and it is the one the helm asked for."""
    arms, bad = [], []

    def run(name, data, default_ms, budgets, want_rc, want_text=None, floor=None):
        rc, lines = verdict(data, default_ms, budgets, floor, quiet=True)
        out = "\n".join(lines)
        ok = rc == want_rc and (want_text is None or want_text in out)
        arms.append(name)
        print(("  ✔ " if ok else "  ⛔ ") + name +
              ("" if ok else f"   (rc={rc}, wanted {want_rc} / {want_text!r})"))
        if not ok:
            bad.append(name)
            for l in lines:
                print("      " + l)

    # ⭐ THE CONTROL COMES FIRST: four reds prove the comparison can fail; only
    # this proves it can pass, and an arm suite with no green arm is a suite that
    # would also pass if the gate refused everything.
    run("control: a delta inside its budget is CLEAN",
        _synthetic({"M": 100.0}, {"M": 110.0}), None, {"M": ("abs", 50.0)}, 0, "ok")
    run("a delta OVER its budget FAILS",
        _synthetic({"M": 100.0}, {"M": 200.0}), None, {"M": ("abs", 50.0)}, 1, "OVER BUDGET")
    run("a unit with NO budget and no @default FAILS",
        _synthetic({"M": 100.0}, {"M": 101.0}), None, {}, 1, "NO BUDGET")
    run("a unit with no budget but a @default is gated AND LISTED",
        _synthetic({"M": 100.0}, {"M": 101.0}), ("abs", 50.0), {}, 0, "fell to @default")
    run("a @default that does not cover the delta still FAILS",
        _synthetic({"M": 100.0}, {"M": 400.0}), ("abs", 50.0), {}, 1, "OVER BUDGET")
    # ⛔ THE ARM THAT MATTERS MOST FOR HONESTY: a budget under the run's own
    # measured spread is not a verdict about the commit, and must not be reported
    # as one — in EITHER direction.
    run("a budget under the measured spread REFUSES, not passes",
        _synthetic({"M": 100.0}, {"M": 105.0}, jitter=80.0), None, {"M": ("abs", 50.0)},
        3, "UNMEASURABLE")
    run("a REFUSAL outranks an over-budget red (it is not a verdict at all)",
        _synthetic({"M": 100.0}, {"M": 900.0}, jitter=80.0), None, {"M": ("abs", 50.0)},
        3, "UNMEASURABLE")
    # ⛔ a unit present on one side only: silence here would report "no change"
    # about the one direction that is certainly a change.
    run("a unit NEW in head is flagged",
        {"base_rev": "0"*40, "head_rev": "1"*40, "planted": False, "box": "BOX synthetic",
         "decl_map": {}, "readings": {"base": [{"modules": {}, "decls": {}, "load1": 1.0}],
                                      "head": [{"modules": {"N": 10.0}, "decls": {}, "load1": 1.0}]}},
        ("abs", 1000.0), {}, 0, "NEW unit in head")
    run("a unit GONE from head is flagged",
        {"base_rev": "0"*40, "head_rev": "1"*40, "planted": False, "box": "BOX synthetic",
         "decl_map": {}, "readings": {"base": [{"modules": {"N": 10.0}, "decls": {}, "load1": 1.0}],
                                      "head": [{"modules": {}, "decls": {}, "load1": 1.0}]}},
        ("abs", 1000.0), {}, 0, "GONE from head")

    # ⭐⭐ THE RELATIVE FORM, DRIVEN IN BOTH DIRECTIONS.  A percentage budget is
    # the half of this file that is supposed to survive a change of machine, and
    # an untested portable claim is the kind this repository keeps paying for.
    run("a RELATIVE budget scales with the base reading (small base ⇒ tight)",
        _synthetic({"M": 100.0}, {"M": 120.0}), None, {"M": ("rel", 10.0)}, 1,
        "OVER BUDGET", floor=1.0)
    run("the same 10% on a ten-times-larger base PASSES the same delta",
        _synthetic({"M": 1000.0}, {"M": 1020.0}), None, {"M": ("rel", 10.0)}, 0,
        "ok", floor=1.0)
    # ⛔ AND THE FLOOR, WHICH IS WHAT STOPS A PERCENTAGE OF A TINY MODULE FROM
    # BEING A ROUNDING ERROR WEARING A GATE'S NAME.
    run("@floor lifts a percentage that is smaller than it",
        _synthetic({"M": 2.4}, {"M": 20.0}), None, {"M": ("rel", 10.0)}, 0,
        "ok", floor=50.0)
    run("@floor does NOT lift a delta above the floor",
        _synthetic({"M": 2.4}, {"M": 80.0}), None, {"M": ("rel", 10.0)}, 1,
        "OVER BUDGET", floor=50.0)
    # ⛔⛔ AND THE BUDGET FILE'S OWN FAILURE MODES, WHICH THE ARMS ABOVE CANNOT
    # REACH.  Everything above hands `verdict` budgets that were already parsed;
    # the parser's refusals are `sys.exit` and can only be observed in a CHILD.
    # A gate whose configuration file is unparseable must REFUSE — an
    # unparseable gate file that read as "no budgets" would report a clean run
    # about a file it could not read.
    probe = tempfile.mkdtemp(prefix="x86lean-budgetprobe-")
    saved = os.path.join(probe, "readings.json")
    json.dump(_synthetic({"M": 100.0}, {"M": 110.0}), open(saved, "w"))
    file_arms = [
        ("control: a well-formed budget file gives a verdict",
         "@floor 5\nM 50\n", 0, "delta gate: CLEAN"),
        ("a RELATIVE budget with no @floor REFUSES",
         "M 10%\n", 2, "no @floor"),
        ("a line whose last field is not a number REFUSES",
         "@floor 5\nM plenty\n", 2, "does not end in a number"),
        ("a one-word line REFUSES rather than being skipped",
         "@floor 5\nM\n", 2, "unparseable budget line"),
    ]
    for name, text, want_rc, want in file_arms:
        bf = os.path.join(probe, "budget.txt")
        open(bf, "w").write(text)
        r = subprocess.run([sys.executable, os.path.abspath(__file__),
                            "--readings", saved],
                           capture_output=True, text=True,
                           env=dict(os.environ, X86LEAN_DELTA_BUDGET=bf))
        out = r.stdout + r.stderr
        ok = r.returncode == want_rc and want in out
        arms.append(name)
        print(("  ✔ " if ok else "  ⛔ ") + name +
              ("" if ok else f"   (rc={r.returncode}, wanted {want_rc} / {want!r})"))
        if not ok:
            bad.append(name)
            for l in out.splitlines():
                print("      " + l)
    # ⛔ AND A MISSING FILE, WHICH IS THE ONE THAT LOOKS LIKE ABSENCE RATHER THAN
    # FAILURE: 0 budgets read as "nothing to gate" unless the gate refuses.
    r = subprocess.run([sys.executable, os.path.abspath(__file__), "--readings", saved],
                       capture_output=True, text=True,
                       env=dict(os.environ,
                                X86LEAN_DELTA_BUDGET=os.path.join(probe, "absent.txt")))
    ok = r.returncode == 2 and "no budget file" in (r.stdout + r.stderr)
    arms.append("a MISSING budget file REFUSES, it does not read as 'nothing to gate'")
    print(("  ✔ " if ok else "  ⛔ ") + arms[-1] +
          ("" if ok else f"   (rc={r.returncode})"))
    if not ok:
        bad.append(arms[-1])
    shutil.rmtree(probe, ignore_errors=True)

    if bad:
        print(f"delta-gate selftest: FAIL ({len(bad)} of {len(arms)} arms)")
        return 1
    print(f"delta-gate selftest: PASS ({len(arms)} arms — the COMPARISON and the "
          f"BUDGET FILE only, with NO measurement in any of them. That is stated "
          f"rather than implied: a green here says nothing about whether the "
          f"profiler can see a code change. --selftest-measure is that arm.)")
    return 0


# ⭐⭐⭐ THE PLANT.  The helm asked for *"a planted constructor that doubles the
# delta"*, and this is literally that, with one constraint stated rather than
# quietly worked around.
#
# ⛔ A CONSTRUCTOR CANNOT BE PLANTED IN `Op`.  Adding one there leaves
# `opOperands`, `Op.anyLocked` and `Op.mnemonic` non-exhaustive in
# `X86/Syntax.lean` and breaks a further ~30 match sites in five other files —
# the tree would not compile, and a probe whose subject does not build measures
# nothing.
#
# ⭐ `PrefetchHint` IS THE ONE INDUCTIVE THAT CAN CARRY IT.  It is matched in
# exactly one place in the whole repository (`PrefetchHint.mnemonic`, and grep
# says so), so N constructors plus their N arms compile, change no other module,
# and put their entire cost in `X86.Syntax` — the unit whose real margin was two
# milliseconds. The plant is a REAL constructor addition to a REAL inductive,
# which is why it is preferred to a synthetic block of `decide` theorems.
def plant_constructors(n):
    def go(worktree):
        p = os.path.join(worktree, "X86", "Syntax.lean")
        s = open(p).read()
        ctors = "".join(f"  | plant{i}\n" for i in range(n))
        arms = "".join(f'  | .plant{i} => "prefetchplant{i}"\n' for i in range(n))
        s2 = s.replace("  | t0\n", "  | t0\n" + ctors, 1)
        s2 = s2.replace('  | .nta => "prefetchnta" | .t0 => "prefetcht0"\n',
                        '  | .nta => "prefetchnta" | .t0 => "prefetcht0"\n' + arms, 1)
        if s2 == s or ctors not in s2 or arms not in s2:
            print("⛔ the plant did not apply — X86/Syntax.lean's `PrefetchHint` no "
                  "longer has the shape this probe edits. A probe that silently "
                  "fails to create its condition reports the gate as sound.")
            sys.exit(2)
        open(p, "w").write(s2)
    return go


def selftest_measure():
    """⛔ THE TWO ARMS THAT NEED REAL TREES, AND THEY ARE THE POINT.

    Arm 1 is the NEGATIVE control and it is the one that could quietly invalidate
    everything: base and head at the SAME commit. Whatever this gate reports
    there is pure instrument — if it is not CLEAN with a delta near zero, every
    green it has ever printed was a green about the machine.

    Arm 2 is the helm's: a planted constructor. It is sized from arm 1's own
    measured spread rather than from a number I liked, so the arm cannot pass by
    being large enough to beat a budget that was never resolvable."""
    repeats = int(arg("--repeats", "2"))
    default_ms, budgets, floor = read_budgets(arg("--budget", BUDGET_FILE))
    head = arg("--head", "HEAD")
    bad = []

    # ⭐ THE ARMS' RAW READINGS ARE SAVED WHEN ASKED, because a measurement that
    # took eleven minutes should be re-judgeable against a changed budget in
    # seconds. `--readings` replays the VERDICT over them without re-measuring —
    # which is also the only honest way to re-judge, since a second measurement
    # would be a different afternoon.
    save = arg("--save-readings")
    print("── arm 1 (NEGATIVE CONTROL): base and head are the SAME commit")
    d0 = measure(head, head, repeats)
    if save:
        json.dump(d0, open(os.path.join(save, "arm1-identical.json"), "w"))
    rc0, lines0 = verdict(d0, default_ms, budgets, floor, quiet=True)
    us = {s: [units_of(r, d0["decl_map"]) for r in d0["readings"][s]] for s in ("base", "head")}
    keys = set(us["base"][0]) & set(us["head"][0])
    # ⛔ NAME THE UNIT, DO NOT ONLY SIZE IT. "worst unit delta 350 ms" is a number
    # a reader cannot act on; the unit is what says whether the instrument's noise
    # lands where the gate is tight or where it is loose.
    per_unit = {k: statistics.median([x[k] for x in us["head"]]) -
                   statistics.median([x[k] for x in us["base"]]) for k in keys}
    worst_unit = max(per_unit, key=lambda k: abs(per_unit[k]))
    worst = abs(per_unit[worst_unit])
    ok0 = rc0 == 0
    print(("  ✔ " if ok0 else "  ⛔ ") +
          f"identical trees ⇒ rc {rc0} (wanted 0); worst unit delta {worst:.1f} ms "
          f"on `{worst_unit}` — that is what this box invents between two copies "
          f"of one commit, and every budget has to clear it")
    if not ok0:
        bad.append("identical-trees control")
        for l in lines0:
            print("      " + l)

    print("── arm 2 (THE HELM'S RED-FIRST): a planted constructor must FAIL")
    # ⚠️ SIZED FROM ARM 1, NOT FROM TASTE. The plant has to exceed the budget of
    # the unit it lands in by a margin larger than the instrument's own noise,
    # and arm 1 is where that noise was just measured on these very trees.
    syn_base = statistics.median([units_of(r, d0["decl_map"])["X86.Syntax"]
                                  for r in d0["readings"]["base"]])
    syn_budget = effective(budgets.get("X86.Syntax", default_ms), syn_base, floor)
    # ⛔⛔ THE PLANT SIZE IS CALIBRATED, AND THE FIRST SIZE WAS TOO SMALL TO CREATE
    # THE CONDITION — MEASURED, and the arm FAILED rather than passing quietly.
    # 48 planted constructors moved `X86.Syntax` **+16.0 ms** (0.33 ms each)
    # against a 27.4 ms budget: rc 0 where 1 was wanted. The arm would otherwise
    # have reported the gate sound while planting something the gate is right to
    # ignore ([[feedback-a-probe-must-create-its-condition]]).
    # ⚠️ AND THE FIRST FIGURE I READ FOR IT WAS +6 ms, off two single passes of a
    # four-pass run before the medians existed. The arm's own summary line is the
    # reading; a pass line is not ([[feedback-read-what-the-instrument-measured]]).
    #
    # ⇒ 🔑 A CONSTRUCTOR ON A FRESH INDUCTIVE COSTS A THIRD OF A MILLISECOND; A
    # REAL `Op` CONSTRUCTOR COSTS EIGHT. The difference is not the constructor —
    # it is three total match functions over a ~200-constructor inductive each
    # growing an arm, and a roster row. Measuring that gap is what the first
    # plant bought, and it is why a plant sized to a real constructor would not
    # have cleared the budget either.
    #
    # The plant must clear the BUDGET, not a real constructor: the budget is ~40 ms
    # because that is what this box can resolve.
    #
    # ⭐⭐ AND THE LINEAR ESTIMATE BEHIND 512 WAS WRONG BY 4.3x, WHICH IS EXACTLY
    # WHY THE ARM PRINTS ITS MEASURED DELTA. At 0.33 ms a constructor the
    # prediction was ~170 ms; measured, 512 constructors cost **+723.0 ms** —
    # 1.41 ms each. 10.7x the constructors bought 45x the cost, so the match
    # compiler is SUPER-LINEAR in the arm count and a plant sized by extrapolation
    # is a plant sized by a model nobody checked. The over-shoot (18x the budget)
    # is the right direction for a probe and it is stated rather than trimmed.
    n = int(arg("--plant", "512"))
    d1 = measure(head, head, repeats, plant=plant_constructors(n))
    if save:
        json.dump(d1, open(os.path.join(save, "arm2-planted.json"), "w"))
    rc1, lines1 = verdict(d1, default_ms, budgets, floor, quiet=True)
    us1 = {s: [units_of(r, d1["decl_map"]) for r in d1["readings"][s]] for s in ("base", "head")}
    dsyn = (statistics.median([x["X86.Syntax"] for x in us1["head"]]) -
            statistics.median([x["X86.Syntax"] for x in us1["base"]]))
    ok1 = rc1 == 1 and "OVER BUDGET" in "\n".join(lines1)
    print(("  ✔ " if ok1 else "  ⛔ ") +
          f"{n} planted constructors ⇒ rc {rc1} (wanted 1); X86.Syntax delta "
          f"{dsyn:+.1f} ms against a {syn_budget:.1f} ms budget and a {worst:.1f} ms "
          f"control spread")
    if not ok1:
        bad.append("planted-constructor arm")
        for l in lines1:
            print("      " + l)

    if bad:
        print(f"delta-gate measured selftest: FAIL ({len(bad)} of 2 arms)")
        return 1
    print("delta-gate measured selftest: PASS (2 arms — the identical-trees "
          "control and the planted constructor)")
    return 0


def main():
    if "--selftest" in sys.argv:
        return selftest()
    if "--selftest-measure" in sys.argv:
        return selftest_measure()
    default_ms, budgets, floor = read_budgets(arg("--budget", BUDGET_FILE))
    saved = arg("--readings")
    if saved:
        data = json.load(open(saved))
        rc, _ = verdict(data, default_ms, budgets, floor)
        absolute_readings(data)
        return rc
    head = arg("--head", "HEAD")
    base = arg("--base") or resolve_base(head)
    print(f"── measuring the delta {base[:9]} → {git('rev-parse', head)[:9]}")
    data = measure(base, head, int(arg("--repeats", "3")))
    out = arg("--out")
    if out:
        json.dump(data, open(out, "w"))
        print(f"readings → {out}")
    rc, _ = verdict(data, default_ms, budgets, floor)
    absolute_readings(data)
    return rc


sys.exit(main())
