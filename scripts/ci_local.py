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

usage: ci_local.py [--job build] [--list] [--from N]
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


def main():
    job = arg("--job", "build")
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
    print(f"CI job {job!r}: {len(runnable)} runnable step(s); "
          f"{len(skipped)} skipped as runner setup "
          + ", ".join(f"`{s['name']}`" for s in skipped))
    bad = []
    for i, s in enumerate(runnable, 1):
        if i < start:
            continue
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
    if bad:
        print(f"\n⛔ ci_local: {len(bad)} of {len(runnable)} step(s) FAILED: "
              + "; ".join(bad))
        return 1
    print(f"\nci_local: CLEAN ({len(runnable)} steps of CI job {job!r}, on THIS "
          f"box — an arm64 macOS run is not a receipt for the x86-64 runner)")
    return 0


sys.exit(main())
