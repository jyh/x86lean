#!/usr/bin/env python3
"""⭐ SCRATCH DIRECTORIES THAT GET REMOVED — the repair for a 591 MB leak.

⛔ WHY THIS EXISTS, MEASURED 2026-09-09.  `/T` held **584 `x86lean-*` directories,
591 MB**, dating back to 09-03.  Audited across `scripts/`:

    mkdtemp with NO cleanup    check_driver_cr4 · check_encodings · check_readme_lean
                               oracle_undef_probe · threads_ab · resolve_names
    mkdtemp WITH cleanup       claimed_forms · deterministic_cost · kernel_cost
                               kernel_delta · kernel_delta_history · kernel_drift
    partial                    oracle_availability (3 mkdtemp, 1 cleanup)

⇒ 🔑 **HALF THIS REPOSITORY'S TOOLS CLEAN UP AND HALF DO NOT, AND NOTHING SAYS
WHICH** — so the habit was never learned, only re-decided per tool.  368 of the 584
came from ONE gate (`check_readme_lean`), which is a CI step: **a leak in a gate
scales with how often the gate is trusted.**

⚠️ IT IS INVISIBLE IN EVERY DIRECTION THAT NORMALLY REPORTS.  Nothing fails, no gate
reddens, `git status` is clean, and the disk is not this seat's to watch — the same
shape as the fleet's orphaned `wi-test` loops (paris bank, 09/09 §6), where the
lesson was **a leak owned by no seat is a leak nobody reaps.**  These ARE this
seat's, so this time the tools own it ([[feedback-a-leak-filed-as-housekeeping]]).

USAGE.  Replace `tempfile.mkdtemp(prefix="x86lean-foo-")` with
`scratch.mkdtemp("x86lean-foo-")`.  The directory is removed when the process
exits, however it exits.

⚠️ THE ESCAPE HATCH IS AN ENV VAR, NOT A CODE PATH: set `X86LEAN_KEEP_SCRATCH=1`
and every directory survives and its path is printed.  A per-tool "keep on failure"
flag was the first design and was dropped — it needs a correct failure path in each
of six tools, and a cleanup that is conditional on the thing most likely to be wrong
is a cleanup that does not run when it matters
([[feedback-a-gate-whose-precondition-is-a-discipline]]).
"""
import atexit
import os
import shutil
import tempfile

# ⛔ REFUSE AN UNKNOWN FLAG BEFORE ANY WORK HAPPENS — see portable.strict_flags.
if __name__ == "__main__":
    import os as _os, sys as _sys
    _sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
    from portable import strict_flags as _strict_flags
    _strict_flags(__file__)

_DIRS = []
KEEP = os.environ.get("X86LEAN_KEEP_SCRATCH", "") not in ("", "0", "no", "false")


def mkdtemp(prefix="x86lean-"):
    """A scratch directory that is removed at process exit.

    ⚠️ `prefix` IS OPTIONAL BECAUSE ONE CALL SITE DID NOT PASS ONE.  The first
    version of this helper made it required; a mechanical rewrite of seven tools
    then broke five build steps at once, all from `check_encodings.py`'s bare
    `tempfile.mkdtemp()`.  ⇒ 🔑 A MECHANICAL REWRITE IS CORRECT ONLY WHERE THE
    CALL SHAPE IS UNIFORM, AND THE ONE SITE THAT DIFFERS IS THE ONE THE REWRITE
    CANNOT SEE.  Defaulting also gives that dir an `x86lean-` name, so the next
    person auditing /T for this repo's leavings can actually find it."""
    d = tempfile.mkdtemp(prefix=prefix)
    _DIRS.append(d)
    return d


@atexit.register
def _cleanup():
    if KEEP:
        for d in _DIRS:
            print("⚠️  X86LEAN_KEEP_SCRATCH: kept %s" % d)
        return
    for d in _DIRS:
        shutil.rmtree(d, ignore_errors=True)


def selftest():
    """⭐ RED-FIRST: the cleanup must actually remove, and the hatch must keep."""
    import subprocess, sys
    here = os.path.abspath(__file__)
    prog = ("import sys; sys.path.insert(0, %r); import scratch;"
            "d = scratch.mkdtemp('x86lean-selftest-'); print(d)" % os.path.dirname(here))
    arms = 0
    r = subprocess.run([sys.executable, "-c", prog], capture_output=True, text=True)
    d = r.stdout.strip().splitlines()[0]
    if os.path.exists(d):
        print("⛔ arm FAILED: %s survived a normal exit" % d); return 1
    arms += 1
    print("  ✔ a scratch dir is removed when the process exits normally")

    # ⚠️ A CRASH MUST ALSO CLEAN — atexit runs on an uncaught exception, and the
    #   crashing case is exactly when a leak would otherwise be created.
    r = subprocess.run([sys.executable, "-c", prog + "; raise SystemExit(3)"],
                       capture_output=True, text=True)
    d = r.stdout.strip().splitlines()[0]
    if os.path.exists(d):
        print("⛔ arm FAILED: %s survived a nonzero exit" % d); return 1
    arms += 1
    print("  ✔ a scratch dir is removed when the process exits NONZERO")

    env = dict(os.environ, X86LEAN_KEEP_SCRATCH="1")
    r = subprocess.run([sys.executable, "-c", prog], capture_output=True, text=True, env=env)
    d = r.stdout.strip().splitlines()[0]
    if not os.path.exists(d):
        print("⛔ arm FAILED: X86LEAN_KEEP_SCRATCH=1 did not keep %s" % d); return 1
    shutil.rmtree(d, ignore_errors=True)
    arms += 1
    print("  ✔ X86LEAN_KEEP_SCRATCH=1 keeps it (so the hatch is real, not documented)")

    # ⚠️ CONTROL: a plain tempfile.mkdtemp must SURVIVE — otherwise the two arms
    #   above would pass on a machine that cleans /T on its own, and would be
    #   measuring the OS rather than this module.
    prog2 = "import tempfile; print(tempfile.mkdtemp(prefix='x86lean-control-'))"
    r = subprocess.run([sys.executable, "-c", prog2], capture_output=True, text=True)
    d = r.stdout.strip().splitlines()[0]
    if not os.path.exists(d):
        print("⛔ CONTROL FAILED: a plain mkdtemp did not survive — these arms are "
              "measuring the operating system, not this module"); return 1
    shutil.rmtree(d, ignore_errors=True)
    arms += 1
    print("  ✔ control: a plain `tempfile.mkdtemp` SURVIVES, so the arms above are "
          "about this module and not about /T")
    print("\nscratch selftest: PASS (%d arms)" % arms)
    return 0


if __name__ == "__main__":
    import sys
    sys.exit(selftest())
