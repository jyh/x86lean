#!/usr/bin/env python3
"""RUN THE CI GATES ON THIS BOX, DERIVED FROM `ci.yml` RATHER THAN COPIED FROM IT.

⛔⛔ WHY THIS EXISTS, AND IT IS A MEASURED REASON, NOT A CONVENIENCE.
`scripts/demand_census.py --check` is a CI step. It has been **RED since P2 batch
20** (`a5326fd`) — measured commit by commit: CLEAN at `762da1a`, red at
`a5326fd`, `873a4d9`, `0f7baee`, `5c01599` and on the tree that merged batch 23.
Five batches, each of whose records says "gates green", because:

  * GitHub Actions refuses every job on this account for BILLING (desk FH), so no
    CI run has ever executed it; and
  * the per-batch local discipline runs the gates named in
    `scripts/run_differential.sh`, which is a SUBSET of this workflow.

⇒ 🔑 **A GATE THAT LIVES ONLY IN CI, ON AN ACCOUNT WHERE CI CANNOT RUN, IS A GATE
NOBODY HAS.** The repository already knew the shape of this — *"a gate nobody has
ever seen run is not a gate"* (D104) — and the repair it made then was to fix the
gates. The repair it did not make was to give a head one command that runs the
whole list on the box that exists.

⛔ AND THE LIST IS DERIVED, NOT TYPED. A hand-copied roster of CI steps is a
duplicate born in agreement: it matches on the day it is written and diverges on
the next ordinary append to the workflow, silently, in whichever direction nobody
is looking. This script PARSES `.github/workflows/ci.yml` and runs the `run:`
blocks of the job it is asked for, in order, so a step added to CI is a step this
runs the same afternoon.

⚠️ WHAT IT CANNOT DO, STATED RATHER THAN LEFT TO BE DISCOVERED:
  * `uses:` steps (checkout, the Lean toolchain action) are SKIPPED and NAMED —
    they set up a runner, and this box is already set up.
  * The runner is x86-64 Linux and this box is arm64 macOS. A step that passes
    here can still fail there; that is what the runner is for when it returns.
  * Timing-calibrated gates are deliberately NOT in this workflow
    (`kernel_cost.py`, and see `kernel_delta.py`'s own jobs), so this list is
    exactly the portable half.

usage: ci_local.py [--job build] [--list] [--jobs] [--from N] [--to N]
⚠️ ONE JOB PER INVOCATION, and `--jobs` lists what that leaves out.
"""
import os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WF = os.path.join(ROOT, ".github", "workflows", "ci.yml")


def arg(name, default=None):
    for i, a in enumerate(sys.argv):
        if a == name and i + 1 < len(sys.argv):
            return sys.argv[i + 1]
    return default


# ⚠️ A HAND-ROLLED READER, AND WHY: PyYAML is not a dependency of this repository
# and adding one to run a gate would put the gate behind an install. The shape
# parsed here is narrow and asserted — a step is `- name:`/`- uses:` at six
# spaces, its `run:` is a scalar or a `|` block at eight — and anything this
# cannot parse is REPORTED, never skipped silently.
def steps(job):
    lines = open(WF).read().splitlines()
    out, in_job, cur, block, indent = [], False, None, None, 0
    for i, ln in enumerate(lines):
        if re.match(r"^  [A-Za-z0-9_-]+:\s*$", ln):
            in_job = ln.strip().rstrip(":") == job
            continue
        if not in_job:
            continue
        if block is not None:
            if ln.strip() == "" or ln.startswith(" " * indent):
                block.append(ln[indent:] if len(ln) >= indent else "")
                continue
            cur["run"] = "\n".join(block).strip("\n")
            out.append(cur)
            cur, block = None, None
        m = re.match(r"^      - (name|uses):\s*(.*)$", ln)
        if m:
            if cur is not None:
                out.append(cur)
            cur = {"name": m.group(2).strip().strip('"'), "kind": m.group(1)}
            continue
        m = re.match(r"^        run:\s*\|\s*$", ln)
        if m and cur is not None:
            nxt = next((l for l in lines[i + 1:] if l.strip()), "")
            indent = len(nxt) - len(nxt.lstrip())
            block = []
            continue
        m = re.match(r"^        run:\s*(\S.*)$", ln)
        if m and cur is not None:
            cur["run"] = m.group(1)
            continue
        m = re.match(r"^      - (name|uses):", ln)
    if block is not None:
        cur["run"] = "\n".join(block).strip("\n")
    if cur is not None:
        out.append(cur)
    if not out:
        print(f"⛔ no steps parsed for job {job!r} in {WF}. A runner script that "
              f"finds nothing to run reports success about an empty list.")
        sys.exit(2)
    return out


# ⛔⛔ ADDED 2026-09-06 (D162), AND IT IS A SCOPE REPAIR, NOT A FEATURE.
# `--job build` is 33 of this workflow's 43 runnable steps, and the summary line
# said `CLEAN (33 steps of CI job 'build')` — accurate, and read for two days as
# a whole-workflow receipt, because **a complete count of a subset is
# indistinguishable from a complete count**: `n/n` says the list was finished,
# never what the list was. A drift gate red on master survived three such
# receipts. The denominator now carries its scope and NAMES what did not run.
# ⛔ DERIVED FROM `ci.yml`, like the step list — a hand-typed roster of jobs is
# the same duplicate-born-in-agreement this file exists to avoid.
# [[feedback-a-gate-behind-a-failing-step-is-silent]]
def jobs():
    """[job name, ...] in workflow order — every key at two spaces under `jobs:`."""
    out, in_jobs = [], False
    for ln in open(WF).read().splitlines():
        if re.match(r"^jobs:\s*$", ln):
            in_jobs = True
            continue
        if in_jobs:
            if ln.strip() and not ln.startswith(" "):
                break
            m = re.match(r"^  ([A-Za-z0-9_-]+):\s*$", ln)
            if m:
                out.append(m.group(1))
    if not out:
        print(f"⛔ no jobs parsed from {WF}. A runner that cannot see the "
              f"workflow's jobs cannot say what its receipt leaves out.")
        sys.exit(2)
    return out


# ⛔⛔ AN UNKNOWN FLAG USED TO START THE MOST EXPENSIVE DEFAULT PATH (D173).
# `arg()` scans for a flag it knows and ignores everything else, so `--list-jobs`
# — a plausible spelling of the real `--jobs` — matched nothing, `job` fell to its
# default `"build"`, and the tool began RUNNING all 33 steps of the build job. A
# relit head typed exactly that at 11:0x and the job started under it.
#
# 🔑 THE SHAPE: `--help` and a listing flag are the FIRST things a new or relit
# head types, and they are the two places where "ignore what you do not
# understand" spends the most. A tool that answers an unrecognised request by
# doing its most expensive thing is worse than one that refuses, because the
# refusal is instant and the misfire is not.
# ⛔ POSITIONALS ARE REFUSED TOO, and that is deliberate: this tool takes none, so
# a bare word is a mistyped flag or a shell glob that expanded.
KNOWN_FLAGS = {"--job", "--jobs", "--list", "--from", "--to", "--help",
               "-h", "--selftest"}
VALUED_FLAGS = {"--job", "--from", "--to"}


def check_argv(argv=None):
    av = sys.argv[1:] if argv is None else argv
    bad, dangling, skip = [], None, False
    for a in av:
        if skip:
            skip = False
            continue
        if a in VALUED_FLAGS:
            skip, dangling = True, a
            continue
        dangling = None
        if a in KNOWN_FLAGS:
            continue
        bad.append(a)
    if skip:
        # ⛔ THE HALF THE FIRST FORM MISSED, found by the sibling guard's own
        # red-first arm in `kernel_delta.py`: `--job` with nothing after it fell
        # through and `arg()` returned the DEFAULT job. A flag whose value went
        # missing is the same silent default one level in.
        print(f"⛔ {dangling!r} takes a value and none follows it. `arg()` would "
              f"have returned its DEFAULT, so this would have run a job you did "
              f"not name.")
        return 2
    if bad:
        print(f"⛔ unrecognised argument(s): {', '.join(repr(b) for b in bad)}.\n"
              f"   This tool RUNS CI jobs, so an ignored flag would have started "
              f"the default one (`--job build`, 33 steps) instead of answering "
              f"you. Known: {', '.join(sorted(KNOWN_FLAGS))}.\n"
              f"   Did you mean `--jobs` (list the jobs) or `--list` (list one "
              f"job's steps)?")
        return 2
    return 0


# ⛔ A CALLABLE SURFACE AND AN ARM, because an inline block in `main()` cannot be
# driven and its neighbours lend it their green (D162's finding, in this file).
# [[feedback-a-gate-with-no-callable-surface]]
def selftest():
    cases = [(["--jobs"], 0, "CONTROL — a known flag is accepted"),
             (["--job", "build", "--to", "7"], 0,
              "CONTROL — value-taking flags' VALUES are not read as flags"),
             (["--job", "--list"], 0,
              "...and a value that LOOKS like a flag is consumed as a value"),
             (["--list-jobs"], 2,
              "RED-FIRST — an unknown flag REFUSES instead of running `--job "
              "build`, all 33 steps (this is the call a relit head made on 09/06)"),
             (["--job"], 2,
              "RED-FIRST — a value-taking flag with NO value refuses"),
             (["build"], 2, "RED-FIRST — a bare positional refuses")]
    bad = []
    for av, want, name in cases:
        rc = check_argv(av)
        ok = rc == want
        print(("  ✔ " if ok else "  ⛔ ") + name + ("" if ok else f"  (rc={rc}, wanted {want})"))
        if not ok:
            bad.append(name)
    if bad:
        print(f"ci_local selftest: FAIL ({len(bad)} of {len(cases)} arms)")
        return 1
    print(f"ci_local selftest: CLEAN ({len(cases)} arms — the ARGUMENT READER "
          f"only. No job is run by any of them.)")
    return 0


def main():
    if "--selftest" in sys.argv:
        return selftest()
    rc = check_argv()
    if rc:
        return rc
    if "--help" in sys.argv or "-h" in sys.argv:
        print(__doc__)
        return 0
    all_jobs = jobs()
    if "--jobs" in sys.argv:
        for j in all_jobs:
            print(f"  {j:24s} {len([x for x in steps(j) if 'run' in x])} runnable step(s)")
        return 0
    job = arg("--job", "build")
    if job not in all_jobs:
        print(f"⛔ {job!r} is not a job of {WF}. It has {len(all_jobs)}: "
              + ", ".join(all_jobs))
        return 2
    st = steps(job)
    runnable = [s for s in st if "run" in s]
    skipped = [s for s in st if "run" not in s]
    if "--list" in sys.argv:
        for i, s in enumerate(runnable, 1):
            print(f"{i:3d}  {s['name']}")
        for s in skipped:
            print(f"  -  SKIPPED ({s['kind']}): {s['name']}")
        return 0
    start = int(arg("--from", "1"))
    # ⚠️ `--to` EXISTS BECAUSE A JOB IS NOT UNIFORM IN PRICE. `kernel-delta`'s
    # seven steps are six pure-python gates (seconds) and one full two-tree
    # profiling run (the merge gate, minutes-to-an-hour). Without a way to name
    # the cheap prefix, "run the drift gates before merging" is a command nobody
    # can type, and a discipline expensive to exercise gets exercised less.
    # [[feedback-make-the-probe-cheap]]
    end = int(arg("--to", str(len(runnable))))
    print(f"CI job {job!r}: {len(runnable)} runnable step(s); "
          f"{len(skipped)} skipped as runner setup "
          + ", ".join(f"`{s['name']}`" for s in skipped))
    # ⛔ `--from N` PAST THE END PRINTED `CLEAN (7 steps of CI job ...)` HAVING
    # RUN NONE — found 09/06 while repairing the job-scope defect one line above,
    # and it is the SAME class inside the same file: the number in the receipt was
    # the length of the LIST, not of what executed. A skip is not a pass.
    # [[feedback-read-what-the-instrument-measured]]
    # [[feedback-naming-a-defect-is-not-finding-its-siblings]]
    if start > len(runnable) or end < start:
        print(f"⛔ --from {start} --to {end} selects NONE of job {job!r}'s "
              f"{len(runnable)} step(s). Running nothing is not a clean run.")
        return 2
    bad, ran = [], 0
    for i, s in enumerate(runnable, 1):
        if i < start or i > end:
            continue
        ran += 1
        print(f"── [{i}/{len(runnable)}] {s['name']}", flush=True)
        r = subprocess.run(["bash", "-e", "-c", s["run"]], cwd=ROOT,
                           capture_output=True, text=True)
        if r.returncode == 0:
            print("   ✔", flush=True)
        else:
            # ⛔ A GATE THAT REFUSES MUST SAY WHAT IT SAW (D94): the failing
            # step's own output is the reading a head needs, and re-running it
            # by hand is how a diagnosis cycle gets spent twice.
            print(f"   ⛔ FAILED (rc {r.returncode})", flush=True)
            for l in (r.stdout + r.stderr).splitlines()[-30:]:
                print("      " + l)
            bad.append(s["name"])
    others = [j for j in all_jobs if j != job]
    scope = (f"\n⚠️  SCOPE: this ran CI job {job!r} ONLY. The workflow has "
             f"{len(all_jobs)} jobs; NOT RUN here: "
             + ", ".join(f"{j} ({len([x for x in steps(j) if 'run' in x])} steps)"
                         for j in others)
             + f".\n    Quote this line with the count, or the count reads as the "
               f"whole workflow.")
    # the count in a receipt is what RAN, never what was listed.
    of = (f"{ran} of {len(runnable)} steps" if ran != len(runnable)
          else f"all {len(runnable)} steps")
    if bad:
        print(f"\n⛔ ci_local: {len(bad)} of the {ran} step(s) RUN in job "
              f"{job!r} FAILED: " + "; ".join(bad) + scope)
        return 1
    print(f"\nci_local: CLEAN ({of} of CI job {job!r} RAN"
          + (f", steps {start}-{min(end, len(runnable))} of {len(runnable)} "
             f"selected by --from/--to" if ran != len(runnable) else "")
          + f"; on THIS box — an arm64 macOS run is not a receipt for the "
            f"x86-64 runner)" + scope)
    return 0



# ⛔ GUARDED (D151's sweep).  An unguarded `sys.exit(main())` means `import <this
# module>` RUNS the tool and then exits the importer — `kernel_cost.py` cost a
# two-minute profiling pass and a killed probe before this was noticed, and
# `kernel_delta.py` had already been given the same guard by D148.  Two prior
# namings and the siblings were never swept for.
# [[feedback-naming-a-defect-is-not-finding-its-siblings]]
if __name__ == "__main__":
    sys.exit(main())
