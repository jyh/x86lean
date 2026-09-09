#!/usr/bin/env python3
"""KERNEL-COST MEASUREMENT AND CEILING (plan v1 §3.3, §3.7).

⚠️ WHAT THIS MEASURES, PRECISELY.  Lean's profiler reports `type checking`
separately from `elaboration` and `tactic execution`.  `type checking` is the
KERNEL: the time the trusted checker spends replaying what the elaborator
produced.  It is the number plan v1 §3.7 asks to be measured and capped, because
it is the one that explodes when a proof leans on defeq across a
composite-routine boundary — and it is NOT the number that dominates the build,
so a wall-clock ceiling would not notice the blow-up until it was enormous.

The §3.3 MEASUREMENT the plan asks for is the per-module kernel time on the
twenty forms.  It measures the cost of the three-axiom route.  It does NOT
choose an axiom base: that was fixed by the helm's ruling (TRUSTBASE.md), and
the measurement is reported, not obeyed.

CEILINGS live in `scripts/kernel_ceilings.txt`.  A module over its ceiling, or
with no ceiling registered, FAILS — that is the "fail on a registered ceiling"
of §3.7.  Raising a ceiling is a decision to record in docs/DECISIONS.md.

Usage:  kernel_cost.py [--register]   (--register rewrites the ceiling file)
"""
import os, re, subprocess, sys, glob, json, time, tempfile

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
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from portable import child_cpu, sub_cpu  # noqa: E402

# ⭐⭐ P2 BATCH 25 (D123) — THE ROOT IS A SEAM, AND IT EXISTS SO THAT ONE
# MEASUREMENT IMPLEMENTATION SERVES BOTH GATES.  `kernel_delta.py` profiles a
# SECOND tree (a detached worktree at the parent commit) and must get its
# numbers from the SAME code that produces the ceiling gate's numbers — two
# copies of a profiler agree until the next ordinary append to one of them, and
# then they disagree silently in whichever direction nobody is looking.  So the
# delta gate runs THIS script, with `--root <the other tree>`, rather than
# carrying its own `lean -D profiler=true` invocation.
#
# ⚠️ The script that runs is always the CURRENT tree's, never the other tree's:
# a delta measured by two different measuring programs is not a delta.
def _root_arg():
    for i, a in enumerate(sys.argv):
        if a == "--root" and i + 1 < len(sys.argv):
            return os.path.abspath(sys.argv[i + 1])
        if a.startswith("--root="):
            return os.path.abspath(a.split("=", 1)[1])
    return None

root = _root_arg() or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(root)
# ⭐⭐ P2 BATCH 1 (D75) — THE CEILINGS PATH IS A SEAM, AND IT IS A SEAM BECAUSE A
# COMMIT SHIPPED A PLANTED DEFECT.  `--selftest` used to mutate this file IN THE
# TREE and restore it afterwards; `afcde4a` was staged inside that window and
# pushed `@decl vectorCoverageXX` — the exact string the third arm plants — to
# both remotes.  ⇒ A PROBE THAT EDITS THE TREE MAKES `git add -A` A RACE, and
# the window is invisible: this script's output says nothing about the tree, and
# the planted line is one character from a legitimate one.  With the seam the
# probe writes only under TMPDIR and the repository is never touched, which is
# the same move the P1 seal made for `scripts/sharing_redprobe.sh` (a467a22).
CEIL_FILE = os.environ.get("X86LEAN_CEIL_FILE", "scripts/kernel_ceilings.txt")
# Headroom over the measured baseline.  Generous enough that ordinary noise on a
# loaded machine does not fail a build, tight enough that a real regression does.
HEADROOM = 3.0
FLOOR_MS = 50   # below this, timing noise dominates and a ratio is meaningless

# ⭐⭐ QUEUE ITEM 7 (D151) — THE CONDITIONS LINE RECORDED A LOAD, AND A LOAD IS
# NOT THE QUANTITY A WALL-CLOCK READING COMPETES WITH.
#
# D149 measured it on this box: a 1-minute load of 282 with `top` reading 0.0%
# idle, 44% user / 55% SYSTEM and exactly one `lean` at 160% CPU — the load was
# dominated by short-lived runnable processes, not by compute.  A reading taken
# at "load 282" and one taken at "load 40" can describe the same machine, which
# is precisely why D142's two afternoons could not be told apart.
#
# ⛔ THE PROBE IS NOT REIMPLEMENTED HERE.  `threads_ab.idle_pct` already exists,
# already returns `None` rather than a default on a failed read, and a second
# copy of it would agree with the first until the next ordinary append to either.
# [[feedback-duplicate-born-in-agreement]]
# ⚠️ The delegation is the direction it is for a reason: importing THIS module
# from elsewhere would run its module-level `os.chdir(root)` and re-parse the
# IMPORTER's argv for `--root`.  The dependency points at the side-effect-free
# module.  (The `type checking` parse is still duplicated in `threads_ab`; the
# two are behaviourally identical today and `--selftest` now holds them to that.)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import threads_ab as _tab


# ⭐⭐ QUEUE ITEM 8 (D151) — A TIMING RUN MUST FIRST LOOK FOR THE SEAT'S OWN
# ORPHANS.  A `ci_local --job build` from a dead session was found running 47
# minutes at ppid 1 (D149), and no instrument this seat owned could see it: it
# contributed to every wall-clock reading taken beside it and to none of their
# recorded conditions.  A relight kills the SESSION, not the processes, and the
# survivors are exactly the long-lived ones.
#
# ⛔ ATTRIBUTE BY CWD, NEVER BY COMMAND NAME.  The orphan found at this seat's
# last exit had a command line identical to the seat's OWN armed bus watch, so a
# `pkill -f` on the pattern would have reaped another seat's live process.  This
# reports; it never kills.  [[feedback-enumerate-is-not-attribute]]
# [[feedback-a-process-filter-matches-its-own-waiter]]
# ⭐⭐⭐ QUEUE ITEM 10 (D156) — WHICH TREES ARE *MINE*, IN ONE PLACE.
#
# ⛔⛔ THE BUG THIS REPLACES, MEASURED RATHER THAN REASONED. `foreign_builds`
# excluded temp trees by the substring `"x86lean-history"` — the prefix of ONE of
# the THIRTEEN `mkdtemp` producers in `scripts/`. The merge gate's and the drift
# gate's own worktrees use `x86lean-delta-`, so a fake `lean` run in one was
# counted as ANOTHER CAMPAIGN'S BUILD (measured: history excluded, delta counted,
# budgetprobe counted, a genuinely foreign tree counted — the last two are the
# probe's controls). Two consequences, and the second is item 10's whole subject:
#   * any reading taken from the repo root while a delta run profiles a worktree
#     is stamped CONTENDED by this seat's own children;
#   * an orphan left in a worktree by a KILLED timing job was invisible to
#     `repo_orphans` (whose test was cwd == the repo root, exactly) while being
#     counted as someone else's build — backwards in both directions at once.
# 🔑 A declared list's gaps all fall the way its default points, and here the
# default was "foreign". [[feedback-a-declared-list-inherits-its-default]]
#
# The primary test is STRUCTURAL and name-free: a detached worktree of this
# repository carries a `.git` FILE whose `gitdir:` points inside this repo's own
# common git directory. The name test is a FALLBACK, and it is here for the case
# that matters after a kill — a worktree whose directory has already been removed,
# where nothing structural survives to be read.
TMP_PREFIX = "x86lean-"

# ⚠️ FIXTURES THAT DELIBERATELY IMPERSONATE ANOTHER CAMPAIGN'S TREE, each with a
# reason — the same shape as `NOT_AN_AVAILABILITY_QUESTION` in the census. The
# convention arm below requires every `mkdtemp` prefix in `scripts/` to start
# with TMP_PREFIX *or* to be declared here, and it also refuses a STALE entry
# that no longer appears in the source, so this list cannot quietly grow.
FOREIGN_FIXTURES = {
    "some-other-campaign-":
        "the positive control that a genuinely foreign tree IS counted; if this "
        "started with TMP_PREFIX the control would test nothing",
}
_COMMON_GITDIR = None


def _common_gitdir():
    global _COMMON_GITDIR
    if _COMMON_GITDIR is None:
        try:
            r = subprocess.run(["git", "rev-parse", "--git-common-dir"],
                               capture_output=True, text=True, timeout=10)
            _COMMON_GITDIR = (os.path.realpath(r.stdout.strip())
                              if r.returncode == 0 and r.stdout.strip() else "")
        except Exception:
            _COMMON_GITDIR = ""
    return _COMMON_GITDIR


def _under_tmp(rp):
    for base in {tempfile.gettempdir(), "/tmp", "/private/tmp", "/var/folders"}:
        try:
            b = os.path.realpath(base)
        except OSError:
            continue
        if rp == b or rp.startswith(b + os.sep):
            return True
    return False


def _own_tree(rp, want):
    """True if `rp` is this repository, a worktree of it, or its scratch space."""
    if rp == want or rp.startswith(want + os.sep):
        return True
    cg = _common_gitdir()
    dotgit = os.path.join(rp, ".git")
    # ⭐ AND THE RELATION IS SYMMETRIC. `want` is the tree being profiled, which
    # during a delta run is a WORKTREE — so without this the MAIN repository
    # counts as another campaign's tree while its own gate profiles a worktree of
    # it. The main tree is the parent of the common git directory.
    try:
        if cg and os.path.realpath(os.path.dirname(cg)) == rp:
            return True
    except OSError:
        pass
    try:
        if cg and os.path.isfile(dotgit):
            line = open(dotgit).read().strip()
            if line.startswith("gitdir:"):
                gd = os.path.realpath(line.split(":", 1)[1].strip())
                if gd == cg or gd.startswith(cg + os.sep):
                    return True
    except OSError:
        pass
    # ⚠️ NAME-BASED, LAST, AND ONLY WHERE NOTHING STRUCTURAL CAN SURVIVE — the
    # directory is GONE. A live tree that is really ours answers test 2; if the
    # directory still exists and carries no `gitdir:` into this repo, it is not
    # ours however it is named.
    # ⛔ THE FIRST SPELLING DROPPED THAT CONDITION and claimed EVERY `x86lean-*`
    # temp directory. It promptly reclassified this selftest's own foreign
    # fixture (`x86lean-fake-lean-`, a scratch dir that deliberately impersonates
    # another campaign) as this seat's, turning a passing arm red — the arm was
    # right and the rule was too broad. A refusal is a design hint before it is
    # an exemption. [[feedback-a-gate-that-refuses-names-a-cheaper-build]]
    if _under_tmp(rp) and not os.path.isdir(rp):
        for part in os.path.normpath(rp).split(os.sep):
            if part.startswith(TMP_PREFIX):
                return True
    return False


def repo_orphans(root=None):
    """Processes whose cwd is this repository and whose session is gone (ppid 1).

    Returns a list of dicts, or None if the probe itself could not run — a
    conditions field that reads "no orphans" because `lsof` was missing is worse
    than an absent one.  [[feedback-probe-silence-has-two-causes]]"""
    want = os.path.realpath(root or os.getcwd())
    try:
        ps = subprocess.run(["ps", "-eo", "pid,ppid,etime,comm"],
                            capture_output=True, text=True, timeout=20)
        if ps.returncode != 0:
            return None
        cand = {}
        me = str(os.getpid())
        for line in ps.stdout.splitlines()[1:]:
            parts = line.split(None, 3)
            # ⛔ NEVER THE CALLER ITSELF. A probe run as a BACKGROUND job is
            # reparented to init like any other, so without this it names its own
            # process as an orphan — and the caller, reading a report it asked
            # for, is exactly the reader least likely to doubt it.
            if (len(parts) == 4 and parts[1] == "1"
                    and parts[0] != "1" and parts[0] != me):
                cand[parts[0]] = {"etime": parts[2], "comm": parts[3].strip()}
        if not cand:
            return []
        lf = subprocess.run(["lsof", "-a", "-d", "cwd", "-p", ",".join(cand)],
                            capture_output=True, text=True, timeout=60)
        # ⚠️ `lsof` exits non-zero when ANY named pid is gone, which is routine
        # over a 1,100-pid list.  Its stdout is still valid, so the exit code is
        # not a refusal here; an empty stdout with no header is.
        if "COMMAND" not in lf.stdout:
            return None
        out = []
        for line in lf.stdout.splitlines()[1:]:
            parts = line.split(None, 8)
            if len(parts) < 9:
                continue
            pid, cwd = parts[1], parts[8].strip()
            if pid in cand and _own_tree(os.path.realpath(cwd), want):
                out.append({"pid": int(pid), "cwd": cwd, **cand[pid]})
        return out
    except Exception:
        return None


# ⭐⭐ THE HELM'S RULE OF 2026-09-05, AS CODE RATHER THAN AS ETIQUETTE.
#
# Ruled after two campaigns collided on this box: *"when two campaigns contend
# for a box, the party whose numbers contention merely SLOWS yields to the party
# whose numbers contention INVALIDATES"*, and — the half this function exists for
# — a reading taken under contention **must be marked CONTENDED in its own
# receipt**, because a number reported without that label is the reassuring
# direction again.
#
# ⛔ A LABEL THAT DEPENDS ON SOMEONE REMEMBERING IS NOT A LABEL.  The seat that
# takes the reading is the seat least able to see the other campaign: my own
# tools recorded load and idle% all evening and could not say that the load WAS
# another seat's salt build in `seats/math/salt`.  "The box was busy" and "the
# box was busy with two other trees" are the difference between a number you can
# compare and a number you can only quote.
#
# ⚠️ THE TWO FILTERS DO DIFFERENT JOBS AND THE DISTINCTION IS THE WHOLE DESIGN.
# The COMMAND NAME answers *what kind of work is this* (a Lean build); the CWD
# answers *whose it is*.  `repo_orphans` above must never filter by command name
# because it feeds a decision about KILLING, and this seat's own tools carry the
# same command lines as the processes it hunts.  This function only COUNTS, and
# it kills nothing.  [[feedback-enumerate-is-not-attribute]]
def foreign_builds(root=None):
    """Lean/lake processes whose cwd is OUTSIDE this repository.

    Returns a list of {pid, cwd}, or None if the probe could not run — never []
    on failure, because "no other builds" and "could not look" must not be the
    same reading.  [[feedback-probe-silence-has-two-causes]]"""
    want = os.path.realpath(root or os.getcwd())
    try:
        ps = subprocess.run(["ps", "-eo", "pid,comm,args"],
                            capture_output=True, text=True, timeout=20)
        if ps.returncode != 0:
            return None
        pids = []
        for line in ps.stdout.splitlines()[1:]:
            parts = line.split(None, 2)
            if len(parts) < 3:
                continue
            pid, args = parts[0], parts[2]
            if re.search(r"(^|/)(lean|lake)( |$)", args) and pid != str(os.getpid()):
                pids.append(pid)
        if not pids:
            return []
        lf = subprocess.run(["lsof", "-a", "-d", "cwd", "-p", ",".join(pids)],
                            capture_output=True, text=True, timeout=60)
        if "COMMAND" not in lf.stdout:
            return None
        out, seen = [], set()
        for line in lf.stdout.splitlines()[1:]:
            parts = line.split(None, 8)
            if len(parts) < 9:
                continue
            pid, cwd = parts[1], parts[8].strip()
            rp = os.path.realpath(cwd)
            # ⚠️ "outside" means outside this repo AND outside every tree of it —
            # the delta gate, the drift gate, the history walk and ten other
            # producers all profile detached worktrees under TMPDIR. `_own_tree`
            # is the single place that decides; naming one producer here is what
            # made this filter wrong for the other twelve.
            if _own_tree(rp, want):
                continue
            if (pid, rp) in seen:
                continue
            seen.add((pid, rp))
            out.append({"pid": int(pid), "cwd": rp})
        return out
    except Exception:
        return None


def _sentinel(v):
    """-1.0 for an unreadable load, for the legacy top-level fields only."""
    return -1.0 if v is None else v


def conditions(root=None):
    """The conditions a reading must be quoted with.  `None` never a default."""
    try:
        la1, la5, _ = os.getloadavg()
    except (AttributeError, OSError):
        # ⛔ AttributeError, NOT JUST OSError: on Windows `os.getloadavg` does not
        # EXIST, so the old clause did not catch the case the second machine
        # actually produces. `None` stays the value, per this function's own rule.
        la1, la5 = None, None
    fb = foreign_builds(root)
    return {"load1": la1, "load5": la5, "idle_pct": _tab.idle_pct(),
            "orphans": repo_orphans(root),
            "foreign_builds": fb,
            # ⭐ the stamp itself. `None` where the probe could not look — an
            # unknown is not a clean bill.
            "contended": None if fb is None else bool(fb)}


# ⛔⛔ THE OTHER HALF OF "WHAT DID I LEAVE BEHIND", ADDED 2026-09-06 (D163).
# `kernel_delta.measure()` adds TWO detached worktrees per run and removes them
# on its way out. A run that is KILLED does not get there — and killing a timing
# run is the ordinary case, not the exotic one, because it is the longest thing
# a seat starts. The registrations then survive in `.git/worktrees` and the
# checkouts survive on disk.
# ⚠️ IT HAS HAPPENED AT LEAST TWICE AND WAS FILED AS HOUSEKEEPING BOTH TIMES.
# `docs/DIFFERENTIAL-P2-BATCH19.md` records `x86lean-delta-9ceaj7ek/{base,head}`
# plus `/private/tmp/x86ci` as *"housekeeping, not a complaint"*; on 09/06 this
# seat found `/private/tmp/x86ci` STILL THERE (149 MB, from the batch-12 era)
# beside four more it had just made — **293 MB across five stale checkouts**.
# ⇒ 🔑 **A LEAK FILED AS HOUSEKEEPING IS A LEAK NOBODY OWNS**, and the instrument
# a head actually runs to ask the question answered an ADJACENT one: `post_flight`
# said `✅ nothing of mine is running detached` — true, and read as "nothing of
# mine is left behind". Its own header says "orphan check".
# ⛔ REPORTS, NEVER REMOVES, for the same reason the process half does not kill:
# a LIVE `kernel_delta` legitimately holds two of these, and this probe cannot
# tell a live one from a stranded one any more than `ppid 1` can. It names the
# ambiguity. [[feedback-enumerate-is-not-attribute]]
# [[feedback-a-tool-has-no-concept-of-not-applicable]]
def stale_worktrees(root=None):
    """[{path, rev, exists}] — checkouts registered to this repo besides the main
    one. None if git could not look (an absence of evidence, not a clean bill)."""
    want = os.path.realpath(root or os.getcwd())
    try:
        r = subprocess.run(["git", "worktree", "list", "--porcelain"], cwd=want,
                           capture_output=True, text=True, timeout=20)
        if r.returncode != 0:
            return None
    except Exception:
        return None
    out, cur, first = [], {}, True
    for line in r.stdout.splitlines() + [""]:
        if not line.strip():
            if cur:
                if first:
                    first = False           # the main working tree is not stale
                else:
                    pth = cur.get("worktree", "")
                    out.append({"path": pth, "rev": cur.get("HEAD", "")[:9],
                                "exists": os.path.isdir(pth)})
            cur = {}
            continue
        k, _, v = line.partition(" ")
        cur[k] = v
    return out


# ⭐⭐⭐ QUEUE ITEM 10, THE HALF THAT WAS MISSING — THE **POST**-FLIGHT PROBE.
#
# The pre-flight half has run since D151: a timing run looks for orphans before
# it believes its own numbers. But orphans are not made before a job, they are
# made when one is KILLED — a relight kills the SESSION, not the processes, and
# the survivors are exactly the long-lived ones (D149 found a `ci_local --job
# build` at ppid 1 after 47 minutes). The probe therefore has to run at the one
# moment nobody was running it.
#
# ⛔⛔ IT REPORTS AND NEVER KILLS, and that is not squeamishness. Every seat on
# this box runs identical command lines from identical paths — the fleet's shared
# bus-watch script (`bus_watch.sh`, run from the kit) is byte-for-byte the same at
# six seats —
# so a name-matched sweep at one seat's exit selects the whole fleet's watches,
# silently, discoverable only at the next boot (math, 2026-09-05 22:45, one
# command away from doing it). The seats are distinguishable ONLY by cwd.
# ⇒ This prints pids and cwds and stops. Anything killed is killed by a human or
# by `TaskStop`, which scopes to its own task.
# [[feedback-enumerate-is-not-attribute]] [[feedback-a-process-filter-matches-its-own-waiter]]
def post_flight(root=None):
    """(rc, lines) — orphans this seat left behind, and other campaigns' builds.

    rc 0 nothing of mine · 1 my orphans survive · 2 a probe could not look."""
    want = os.path.realpath(root or os.getcwd())
    mine, others = repo_orphans(want), foreign_builds(want)
    trees = stale_worktrees(want)
    lines = [f"── POST-FLIGHT orphan check · {want}"]
    if mine is None or others is None or trees is None:
        # ⛔ "could not look" and "nothing there" must never print the same.
        # [[feedback-probe-silence-has-two-causes]]
        lines.append("⛔ the probe could NOT LOOK (ps or lsof unavailable or "
                     "refused), so this is not a clean bill — it is an absence "
                     f"of evidence: repo_orphans={'ok' if mine is not None else 'FAILED'} "
                     f"foreign_builds={'ok' if others is not None else 'FAILED'} "
                     f"stale_worktrees={'ok' if trees is not None else 'FAILED'}")
        return 2, lines
    for o in mine:
        lines.append(f"⚠️  MINE, ppid 1  pid {o['pid']:>7}  up {o['etime']:>12}  "
                     f"{o['comm']}  cwd {o['cwd']}")
    for o in others:
        lines.append(f"   another tree    pid {o['pid']:>7}  cwd {o['cwd']}")
    for t in trees:
        lines.append(f"⚠️  WORKTREE      {t['rev']}  "
                     f"{'' if t['exists'] else '(DIRECTORY GONE) '}{t['path']}")
    lines.append(f"   {len(mine)} ppid-1 process(es) in my trees · {len(others)} "
                 f"build(s) in other trees · {len(trees)} extra worktree(s) "
                 f"registered · NOTHING WAS KILLED OR REMOVED")
    if trees:
        # ⛔ THE SAME AMBIGUITY AS `ppid 1`, NAMED RATHER THAN RESOLVED.
        lines.append("⚠️  A RUNNING `kernel_delta` HOLDS TWO OF THESE legitimately, so "
                     "this list cannot tell a live measurement from a killed one's "
                     "leavings. Check that no timing run is in flight first.")
        lines.append("⛔ Then, per path: `git worktree remove --force <path>`. "
                     "`git worktree prune` alone drops only registrations whose "
                     "DIRECTORY is already gone, and these usually still exist — "
                     "the disk is the larger half (293 MB across five on 09/06).")
    if mine:
        # ⛔⛔ "ppid 1" IS NOT "ORPHANED", AND THIS TOOL LEARNED THAT BY NEARLY
        # COSTING ME A LIVE JOB. Every background job in this harness is launched
        # from a shell that then exits, so a RUNNING, WANTED job is reparented to
        # init exactly like a stranded one. The first version of this report
        # labelled them "MINE, ORPHANED" and said "these survived a job of mine";
        # minutes later it said that about the selftest that was at that moment
        # running, and the reading is indistinguishable from the real orphan it
        # had correctly caught one minute earlier.
        # ⇒ The report names the AMBIGUITY it cannot resolve instead of asserting
        # the reading it happens to have. [[feedback-enumerate-is-not-attribute]]
        lines.append("⚠️  ppid 1 means the launching shell exited — which is TRUE OF "
                     "EVERY DELIBERATELY BACKGROUNDED JOB as well as of every "
                     "orphan. This list cannot tell them apart.")
        lines.append("⛔ Before killing any of these: confirm it is not a job you "
                     "still want, then kill BY PID — never by a name pattern, "
                     "which at this box selects other seats' live processes.")
        return 1, lines
    if trees:
        return 1, lines
    lines.append("✅ nothing of mine is running detached, and no worktree of mine "
                 "is registered beyond the main checkout.")
    return 0, lines


def modules():
    fs = sorted(glob.glob("X86/*.lean")) + ["X86.lean", "X86Native.lean"] \
         + sorted(glob.glob("Tests/*.lean")) + ["Tests.lean"]
    return [f for f in fs if os.path.exists(f)]

def mod_name(f):
    """`X86/Basic.lean` -> `X86.Basic`. A LOGICAL name, not a path.

    ⛔⛔ THIS READ `f[:-5].replace("/", ".")` UNTIL 2026-09-09 AND WAS WRONG ON
    WINDOWS IN THE QUIETEST POSSIBLE WAY. `glob.glob("X86/*.lean")` returns
    `os.sep`-joined paths, so on kenai every module came back as `X86\\Basic`,
    `Tests\\Coverage`. Measured in the smoke test that preceded the fourth
    calibration night:
        {"modules": {"X86\\Basic": 109.0, ..., "Tests\\Anchors": 704.0, ...}}
    ⇒ The keys of a kenai walk would not have matched the keys of a yukon walk,
    and `--decl-modules Tests.Coverage` is matched against THIS function's output
    (line ~846), so the declaration set would have come back EMPTY.
    ⇒ 🔑 **A NAME DERIVED FROM A PATH CARRIES THE PLATFORM'S SEPARATOR INTO A
    NAMESPACE THAT HAS NONE** — and the walk would have completed, written a full
    corpus, and compared as though it had measured nothing.
    [[feedback-a-route-cannot-see-its-subject]]
    """
    return f[:-5].replace("\\", "/").replace("/", ".")

# ⭐⭐⭐ QUEUE ITEM 4d (D151) — THE PER-UNIT CPU TIME WAS IN EVERY PASS ALREADY.
#
# This function runs ONE `lean` process per module, so the CPU that process
# burns is ALREADY a per-unit quantity: `getrusage(RUSAGE_CHILDREN)` differenced
# across the `subprocess.run` costs nothing, needs no second invocation, and
# belongs to exactly the pass whose milliseconds sit beside it.  D150 measured
# it against the number this gate reads, five profiles of ONE unchanged tree:
#
#     profiler `type checking`   51,400 / 42,700 / 28,900 / 31,000 / 42,700 ms
#     child `user` CPU               56.99 / 58.05 / 55.98 / 56.69 / 57.24 s
#
# — a 52.7% range against a 3.6% one, policing a 1,764 ms budget.
#
# ⛔ RECORDING IT IS NOT GATING ON IT, and that difference is the whole of item
# 4d.  `user` charges ELABORATION AND KERNEL where the gated number charges the
# kernel alone, so it is a DIFFERENT QUANTITY, not a better reading of the same
# one: every budget in `kernel_ceilings.txt` and `kernel_delta_budget.txt` would
# have to be re-derived from a SECOND SOURCE before it could carry a gate, and
# deriving one from the runs that recommended it would be deriving the allowance
# from the thing it checks.
# [[feedback-widening-a-gate-needs-a-second-source]]
#
# ⚠️ RUSAGE_CHILDREN IS CUMULATIVE over every descendant this process has
# reaped, so this difference is THIS invocation's only because the profiling
# loop is sequential and reaps nothing else inside the window.  If that loop is
# ever parallelised, the field silently attributes one module's CPU to whichever
# module happened to be differencing — it must then move to a per-child `wait4`
# or be deleted.  A reading whose precondition has quietly lapsed is worse than
# no reading, because it still prints.
def profile_module(f):
    """One profiler pass over one module.

    Returns {"ms", "user_s", "sys_s", "real_s"}.  `kernel_ms` is the thin
    wrapper the ceiling gate and the delta gate both call, so there is exactly
    ONE `lean` invocation per module and exactly one implementation of the
    parse — a second copy of either agrees until the next ordinary append.
    """
    u0, s0, _cpu_src = child_cpu()
    t0 = time.time()
    r = subprocess.run(
        ["lake", "env", "lean", "-D", "profiler=true", "-D", "profiler.threshold=100000", f],
        capture_output=True, text=True)
    real_s = time.time() - t0
    u1, s1, _ = child_cpu()
    # ⛔ ABSENT, NOT ZERO — and `real_s` is unaffected because `time.time()` is
    # everywhere. So off POSIX this reading loses its CPU companions and keeps
    # the wall clock AND the gated `ms`, which is the whole point.
    cpu = {"user_s": sub_cpu(u0, u1), "sys_s": sub_cpu(s0, s1),
           "real_s": real_s, "cpu_source": _cpu_src}
    if r.returncode != 0:
        print(f"⛔ {f} did not compile:\n{r.stdout}\n{r.stderr}")
        sys.exit(2)
    # ⚠️ The profiler writes to STDERR, not stdout.  The first draft of this
    # script searched stdout only, measured 0.0ms for every module, and printed
    # "kernel-cost gate: CLEAN" — a gate that cannot see its subject reports a
    # pass. Both streams are searched now, and a module that yields NO reading
    # is an error rather than a zero.
    blob = r.stdout + "\n" + r.stderr
    m = re.search(r'^\s*type checking\s+([\d.]+)(ms|s)\s*$', blob, re.M)
    if not m:
        # A pure re-export module (X86.lean is nothing but `import` lines)
        # type-checks nothing, so the profiler prints its cumulative block with
        # no `type checking` entry.  That is a real zero.  A run with NO
        # cumulative block at all is a failed measurement and must not be
        # silently read as zero — the distinction is the whole difference
        # between "nothing to check" and "we did not look".
        if "cumulative profiling times" in blob:
            cpu["ms"] = 0.0
            return cpu
        print(f"⛔ {f}: the profiler produced no cumulative block at all. "
              f"A missing reading is not a zero.")
        sys.exit(2)
    v = float(m.group(1))
    cpu["ms"] = v * 1000 if m.group(2) == "s" else v
    return cpu


def kernel_ms(f):
    """The gated quantity, unchanged: the profiler's cumulative `type checking`."""
    return profile_module(f)["ms"]

# ⭐ THE DENOMINATOR FOR A TABLE-DRIVEN MODULE, AND WHY IT CAN BE TRUSTED.
#
# `Tests.Coverage` type-checks `decide` over the coverage TABLE: its kernel cost
# is linear in the number of rows, and the roster grows every batch by
# construction.  An absolute-millisecond ceiling on such a module is a gate that
# must be RAISED EVERY BATCH — and a gate relaxed on schedule is not a gate, it
# is a chore that trains its owner to raise it.  Batches 3 and 14 both raised
# this one; batch 10 recorded 2.4x headroom as "room to do this properly rather
# than under pressure", and by batch 14 the headroom was 1.09x.  So the ceiling
# for such a module is registered PER ROW and multiplied by the live row count.
#
# ⚠️ The row count is not counted by this script.  It is read from the LITERAL
# in `theorem roster_size_is_N : rosterSize = N := by decide` — and that literal
# is kernel-pinned to the table by `table_row_count : tableP0.length =
# rosterSize`, so the denominator this gate divides by is a number Lean PROVES
# is the table's length, not a number this script counted and could get wrong.
# A missing or unparseable literal is an ERROR, never a default: a denominator
# guessed at is a ceiling that means nothing.
PER_ROW_TAG = "@perRow"
DECL_TAG    = "@decl"     # ⭐ an ABSOLUTE ceiling on one named declaration
TAIL_TAG    = "@tail"     # ⭐ an ABSOLUTE ceiling on everything else in the module

# ⭐⭐ THE PER-DECLARATION GATE (P1 seal, D68) — THE UNIT PROBLEM, ENDED.
#
# The helm, 13:37: *"a number measured in the wrong unit and applied with care is
# still the wrong number."*  `Tests.Coverage` was gated PER ROW, and D62 had
# already proved the row is not the unit: after D63 one declaration is half the
# module and is barely row- or vector-driven.  Every refinement since batch 14
# went into the MARGIN (x1.6, worst-of-N, loads recorded) and none into the
# DENOMINATOR.
#
# ⇒ An ABSOLUTE millisecond ceiling on a NAMED DECLARATION has no denominator, so
# it cannot be in the wrong unit.  D62 designed exactly this and recorded it as
# blocked; D63 removed the reason it looked hard.
#
# ⛔ AND THE MEASUREMENT REFUSED THE NAIVE VERSION OF IT, which was to gate every
# declaration.  Four profiles on a quiet machine (one-minute loads 3.25-5.37):
#
#     memDestSweep                       11 800 · 12 100 · 11 900 · 11 900   2.5%
#     pre_states_have_a_returnable_frame  1 800 ·  1 800 ·  1 690 ·  1 820   7.7%
#     vectorCoverage                      1 440 ·  1 410 ·  1 410 ·  1 450   2.8%
#     ---------------------------------------------------------------- gateable
#     table_mnemonics_subset_roster          708 ·   513 ·     …             38%
#     bitcnt_encodable_forms_…               912 ·   809 ·   844 ·    919    13%
#     (and the COUNT of attributed declarations moved 26 / 27 / 28 between runs)
#
# ⇒ 🔑 **A PER-DECLARATION CEILING IS SOUND ONLY FOR DECLARATIONS BIG ENOUGH TO
# MEASURE.**  Below about a second the run-to-run noise is larger than any
# sensible margin, and a gate there would need relaxing on somebody's schedule —
# which is the chore D62 warned about, one layer down.
#
# So: the three declarations above a second are gated INDIVIDUALLY, and
# everything else is gated as ONE ABSOLUTE TAIL (module total minus the gated
# declarations).  Neither number divides by anything.
# ⚠️ A gated declaration MISSING from the profile is an ERROR, never a pass: a
# declaration that has been renamed or deleted takes its ceiling with it, and a
# gate that cannot find its subject reports a pass.

def roster_size():
    src = open("Tests/Coverage.lean").read()
    ms = re.findall(r'rosterSize\s*=\s*(\d+)\s*:=\s*by\s+decide', src)
    if len(ms) != 1:
        print(f"⛔ could not read a unique kernel-pinned `rosterSize = N` from "
              f"Tests/Coverage.lean (found {len(ms)}). A per-row ceiling "
              f"without a trustworthy denominator is not a gate.")
        sys.exit(2)
    return int(ms[0])


# ⭐⭐ P1 BATCH 20 — THE DENOMINATOR BATCH 17 SAID COULD BE PINNED, PINNED.
# `vectorCount` is proved equal to `vectors.length` in Tests/Coverage.lean, so
# this is a number Lean checks and not a number this script counted.  The same
# refusal as `roster_size`: a missing literal is an ERROR, never a default.
def vector_count():
    src = open("Tests/Coverage.lean").read()
    ms = re.findall(r'vectorCount\s*=\s*(\d+)\s*:=\s*by\s+decide', src)
    if len(ms) != 1:
        print(f"⛔ could not read a unique kernel-pinned `vectorCount = N` from "
              f"Tests/Coverage.lean (found {len(ms)}). A per-declaration ceiling "
              f"without a trustworthy denominator is not a gate.")
        sys.exit(2)
    return int(ms[0])


# ⭐⭐⭐ PER-DECLARATION KERNEL TIME — THE MEASUREMENT BATCH 17 RECORDED AS
# BLOCKED, AND THE BLOCK WAS ONE SENTENCE TOO WIDE.
#
# Batch 17 wrote: "A vector count could be pinned the same way; an ASSERTION
# count cannot be, because it is a property of the file's text and not of any
# term in it."  Both halves are TRUE.  What was not noticed for three batches is
# what they rule out: they block gating the module's TOTAL in an
# (assertions x vectors) unit.  They say nothing about gating EACH
# DECLARATION — and a per-declaration gate needs no assertion count at all,
# because dividing by the number of declarations is the only thing the assertion
# count was ever for.
#
# ⇒ 🔑 A BLOCKED REPAIR BLOCKS A DESIGN, NOT A GOAL.
#
# The mechanism: `lean --json -D profiler.threshold=N` emits one
# `type checking took X` message PER DECLARATION, carrying `fileName` and
# `pos.line`, so a failure names the declaration instead of the module.  Plain
# (non-JSON) output carries the same timings with NO position, which is why the
# first attempt at this looked impossible too.
def per_declaration(f, threshold_ms=100):
    """[(line, name, ms)] for one module, kernel time attributed by source line."""
    r = subprocess.run(
        ["lake", "env", "lean", "--json", "-D", "profiler=true",
         "-D", f"profiler.threshold={threshold_ms}", f],
        capture_output=True, text=True)
    if r.returncode != 0:
        print(f"⛔ {f} did not compile under the per-declaration profiler:\n{r.stderr}")
        sys.exit(2)
    src = open(f).read().splitlines()
    # A declaration's header is the nearest `theorem`/`def`/`example` at or
    # before the message's line — the message sits on the declaration's own line
    # for a term-mode proof and on its tactic block for others.
    def name_at(line):
        for k in range(line, 0, -1):
            m = re.match(r'\s*(?:private\s+)?(theorem|def|example|lemma)\s+(\S+)',
                         src[k - 1])
            if m:
                return m.group(2)
        return "?"
    out, seen = [], 0
    for ln in r.stdout.splitlines():
        if not ln.startswith("{"):
            continue
        try:
            m = json.loads(ln)
        except json.JSONDecodeError:
            continue
        g = re.match(r'type checking took ([\d.]+)(ms|s)', m.get("data", ""))
        if not g:
            continue
        seen += 1
        v = float(g.group(1)) * (1000 if g.group(2) == "s" else 1)
        out.append((m["pos"]["line"], name_at(m["pos"]["line"]), v))
    if not out:
        print(f"⛔ {f}: the per-declaration profiler produced no `type checking` "
              f"message at all. A gate that cannot see its subject reports a pass.")
        sys.exit(2)
    return sorted(out, key=lambda t: -t[2])

# ⭐⭐ P1 BATCH 17 — THE GROWTH LAW, MEASURED AND REPORTED RATHER THAN
# REDISCOVERED, AND THE LOAD AVERAGE BESIDE IT.
#
# The per-row ceiling was introduced by batch 14 precisely so that a gate would
# not need raising every batch (D38).  It has not needed raising since — and the
# DENSITY it gates has climbed every batch anyway: 266 -> 339 -> 363 ms/row
# across batches 14 to 16, so the headroom went 1.77x -> 1.39x -> 1.30x.
#
# ⛔ AND THE SERIES CANNOT BE EXTENDED HONESTLY, BECAUSE NONE OF THOSE READINGS
# RECORDS WHETHER THE MACHINE WAS IDLE.  This file's own comment knows that it
# matters — it records "measured on an IDLE machine (81.8 / 81.4 across two
# runs)" for `Tests.Nonvacuity`, and notes that a reading taken during the
# selftest was ~15% high — and the line beside it, the per-row figure handed
# from batch to batch, records nothing.  ⇒ A MEASUREMENT WHOSE CONDITIONS ARE
# NOT RECORDED CANNOT BE COMPARED WITH A LATER ONE; the discipline was written
# down once and not applied to the number that is actually tracked.  So this
# script now prints the one-minute LOAD AVERAGE beside every figure it reports,
# and a head reading a batch record can tell whether the trend is real.
#
# ⛔ SO THE ROW IS NOT THE UNIT EITHER.  `Tests.Coverage`'s cost is linear in
# (ASSERTIONS x VECTORS), and neither factor is the roster size: a batch adds
# theorems and vectors faster than it adds mnemonics.  Batch 16 -> 17 moves
# +2.6% in the flat unit (688.6 -> 706.6 ns) and +8.9% per row (362.7 -> 394.9).
# ⚠️ ONE PAIR IS NOT A SERIES, and it is offered as one pair: batch 17's reading
# records its load (two runs at 2.20 and 4.08, both 31 200 ms) and batch 16's
# records none, so this is the FIRST comparison in the repository that could be
# checked at all.
#
# ⚠️ AND THE SOUND REPAIR IS BLOCKED, WHICH IS WHY THIS PRINTS AND DOES NOT
# GATE.  The per-row ceiling can be trusted because its denominator is
# KERNEL-PINNED — `roster_size_is_N` is proved equal to the table's length, so
# it is a number Lean checks rather than a number this script counted.  A vector
# count could be pinned the same way; an ASSERTION count cannot be, because it
# is a property of the file's text and not of any term in it.  Registering a
# ceiling in a unit whose denominator this script greps for would trade a proven
# denominator for a guessed one — the exact thing the note above says makes a
# ceiling mean nothing.
#
# So the figure is REPORTED on every run, in the unit that is actually flat, so
# that the growth law is observed each batch instead of being reconstructed from
# git by whoever finally hits the ceiling.
#
# ⛔⛔ P1 BATCH 20 MEASURED THAT UNIT AND IT IS NOT FLAT.  "Linear in
# (assertions x vectors)" was inferred from two whole-module totals, and a total
# cannot tell a linear module from a super-linear one.  Profiled PER
# DECLARATION at 700 and again at 775 vectors -- the same code, minutes apart --
# three declarations grow FASTER than their input:
#
#     vectors_cover_the_roster   x1.645        (vectors x1.107)
#     every_row_has_a_vector     x1.324
#     every_vector_has_a_row     x1.321
#
# and the reason is in the source rather than in the timings: `vectorMnemonics`
# is `(vectors.map Vec.mnemonic).eraseDups`, and `List.eraseDups` is QUADRATIC.
# The two theorems above then run `contains` over its result once per row.
#
# ⭐⭐ P1 BATCH 21 PRICED THAT REPAIR BEFORE TAKING IT, AND IT WAS THE SMALLER
# OF THE TWO.  The dedup is real -- `vectorMnemonics.length = 83` costs 935 ms
# against a 69 ms control forcing the same 775 projections with no dedup -- but
# it is 2.8 s of a 37 900 ms module (7%).  What was never measured is that the
# kernel's reduction cache SPANS A DECLARATION AND NOT TWO, so the three
# mem-dest sweeps were paid three times over: 10 600 + 9 720 + 5 250 = 25 570 ms
# apart, 11 200 ms in one declaration.  Stating each group's claims in ONE
# reduction (`memDestSweep`, `vectorCoverage`) and DERIVING the original
# theorems from it, statements byte-for-byte unchanged, took the module
# 37 900 -> 22 400 ms.  ⇒ 🔑 A COST MODEL THAT ONLY KNOWS ABOUT THE ARTIFACT
# CANNOT SEE THE COST OF ASKING TWICE.  See D63.
#
# ⛔ AND THE TECHNIQUE IS NOT GENERAL, WHICH WAS MEASURED RATHER THAN LEFT TO BE
# OVER-APPLIED.  NINETEEN theorems here reduce `preStates 1 8` -- more sharing by
# count than the six that were merged -- and merging four of them saves 7%
# (786 -> 733 ms, back to back).  ⇒ 🔑 SHARING PAYS WHERE THE SHARED SUBJECT'S
# REDUCTION IS EXPENSIVE, NOT WHERE THE SUBJECT IS MERELY SHARED.  A dedup or a
# character sweep costs seconds; 86 records built from simple constructors do
# not, and the per-state PREDICATE, which is where those theorems' time goes,
# is different in each and cannot be shared at all.  D63 §5.
#
# ⚠️ AND THE TWO DECLARATIONS THAT DOMINATE THE MODULE ARE BARELY VECTOR-DRIVEN
# AT ALL -- `mem_dest_rewrite_changed_exactly_the_three_operand_rows` x1.050 and
# `mem_dest_claims_are_backed` x1.077, most of even that being the SHAPES prose
# this batch lengthened rather than the vectors it added.  Together they are 53%
# of the module.
#
# ⇒ A PER-VECTOR DENOMINATOR WOULD HAVE GONE SLACK EXACTLY WHERE THE COST IS,
# and slack is the direction nobody polices.  The gate that was going to replace
# the per-row ceiling is therefore NOT INSTALLED: its own second source refused
# it (D62).  What IS installed is the measurement that refused it, printed on
# every run, because the next design needs this table and not another two
# batches of whole-module totals.
def coverage_growth_denominator():
    """(assertions, vectors) for Tests.Coverage — REPORTED, never gated."""
    thms = len(re.findall(r'^theorem\s', open("Tests/Coverage.lean").read(), re.M))
    vecs = len(re.findall(r'\{\s*id\s*:=\s*"', open("Tests/Vectors.lean").read()))
    return thms, vecs

# ⭐⭐⭐ P2 BATCH 25 (D123) — THE RAW-READING MODE THE DELTA GATE CONSUMES.
#
# `kernel_delta.py` needs the SAME numbers this gate reads, taken in ONE session,
# from TWO trees.  It gets them by running this script twice with `--root`, and
# this mode is the interface: no ceilings, no verdict, no load refusal — the
# readings and the conditions they were taken under, and nothing that pretends
# to be a judgement about a commit.
#
# ⛔ `--decl-modules` IS AN ARGUMENT AND NOT A LOOKUP, ON PURPOSE.  If each tree
# read its OWN ceiling file for the list of per-declaration modules, the two
# sides of a delta could be asked different questions — and the answer would
# still be two numbers that subtract.  The caller passes one list to both.
#
# ⛔ A NAMED MODULE WITH NO SOURCE FILE IS REPORTED, NEVER SKIPPED.  A module
# that exists on one side of the delta and not the other is a real change, and
# the caller has to decide what it means; a skip here would decide it silently
# in the direction of "no difference".
def emit_json():
    want = []
    for i, a in enumerate(sys.argv):
        if a == "--decl-modules" and i + 1 < len(sys.argv):
            want = [x for x in sys.argv[i + 1].split(",") if x]
    b = subprocess.run(["lake", "build", "X86", "Tests", "X86Native"],
                       capture_output=True, text=True)
    if b.returncode != 0:
        sys.stderr.write(f"⛔ {os.getcwd()}: `lake build` failed, so every reading "
                         f"below would be about a tree that does not compile.\n"
                         f"{b.stdout}\n{b.stderr}\n")
        return 2
    # ⭐ The conditions are sampled BEFORE the measurement and again after it,
    # and both are recorded.  D150: a sample taken before a 56-second reading
    # describes a different minute — round 0 began at 40.1% idle, ended with the
    # box at 0.0%, and was the highest of five readings on one tree.  One sample
    # cannot say which minute the number belongs to; two bound it.
    cond_before = conditions()
    mods, cpu, decls, missing = {}, {}, {}, []
    for f in modules():
        r = profile_module(f)
        mods[mod_name(f)] = r["ms"]
        cpu[mod_name(f)] = {k: r[k] for k in ("user_s", "sys_s", "real_s")}
    for m in want:
        f = [x for x in modules() if mod_name(x) == m]
        if not f:
            missing.append(m)
            continue
        decls[m] = {name: ms for _l, name, ms in per_declaration(f[0])}
    cond_after = conditions()
    print(json.dumps({"root": os.getcwd(),
                      # ⚠️ `load1`/`load5` KEEP their place, their meaning (the
                      # load BEFORE the pass) AND their -1.0 sentinel.
                      # `docs/kernel-delta-history-2026-09-04.jsonl` is read by
                      # `--analyse`, and a field that changes place between two
                      # halves of one corpus is a corpus that cannot be analysed
                      # as one.
                      # [[feedback-a-positional-index-bets-the-record-wont-grow]]
                      # ⛔ AND THE SENTINEL IS NOT "TIDIED" TO `None` HERE, even
                      # though D149's rule (`None`, never a default) is the right
                      # one and the new `conditions_*` fields obey it.  Three
                      # analysers format this field with `:.2f`
                      # (`kernel_delta.py:412,444`, `kernel_delta_history.py:136,532`)
                      # and would raise on a `None` — a probe failure would then
                      # surface as a crash in a DIFFERENT tool reading the corpus
                      # months later.  The honest `None` lives in
                      # `conditions_before/after`, which no formatter touches.
                      "load1": _sentinel(cond_before["load1"]),
                      "load5": _sentinel(cond_before["load5"]),
                      "t": time.time(), "modules": mods, "decls": decls,
                      "missing": missing,
                      # ⭐ QUEUE item 4d's candidate quantity, and items 7/8's
                      # conditions.  Additive: nothing above changed meaning.
                      "cpu": cpu,
                      "conditions_before": cond_before,
                      "conditions_after": cond_after}))
    return 0


def read_ceilings():
    """Returns ({module: (kind, value)}, {module: {decl: ms}}, {module: tail_ms})."""
    d, decls, tails = {}, {}, {}
    if os.path.exists(CEIL_FILE):
        for line in open(CEIL_FILE):
            line = line.split("#")[0].strip()
            if not line:
                continue
            parts = line.split()
            if len(parts) == 4 and parts[1] == DECL_TAG:
                decls.setdefault(parts[0], {})[parts[2]] = float(parts[3])
            elif len(parts) == 3 and parts[1] == TAIL_TAG:
                tails[parts[0]] = float(parts[2])
            elif len(parts) == 3 and parts[1] == PER_ROW_TAG:
                d[parts[0]] = ("perRow", float(parts[2]))
            elif len(parts) == 2:
                d[parts[0]] = ("abs", float(parts[1]))
            else:
                print(f"⛔ unparseable ceiling line: {line!r}")
                sys.exit(2)
    return d, decls, tails

# ⭐⭐ THE ARMS FOR THE THREE THINGS ADDED BY QUEUE ITEMS 4d / 7 / 8 (D151).
#
# All four are IN-PROCESS and cost under five seconds together, which is the
# only reason they can live inside a ~6-minute selftest rather than beside it in
# a step nobody runs.  A gate behind a step that is skipped is silent, and
# silence reads as green.  [[feedback-a-gate-behind-a-failing-step-is-silent]]
# [[feedback-make-the-probe-cheap]]
def conditions_selftest():
    """Returns a list of (ok, name).  Each arm creates the condition it tests."""
    out = []

    # ⛔ ARM 1 — THE DELEGATION IS REAL, NOT A COMMENT SAYING SO.  `conditions()`
    # claims to get its idle % from `threads_ab.idle_pct` rather than from a
    # second copy.  A comment naming a delegate reads AS the delegation.  So the
    # delegate is STUBBED and the answer must MOVE.
    # [[feedback-a-citation-is-an-ungated-claim]]
    real = _tab.idle_pct
    try:
        _tab.idle_pct = lambda: 424242.0
        moved = conditions()["idle_pct"] == 424242.0
    finally:
        _tab.idle_pct = real
    out.append((moved, "the idle % is really read through threads_ab.idle_pct "
                       "(delegate stubbed; the answer must move)"))

    # ⭐ ARM 2 — THE ORPHAN PROBE CREATES ITS OWN CONDITION.  A probe that finds
    # nothing on a clean box has told you nothing: it cannot distinguish "no
    # orphans" from "cannot see orphans".  So make a REAL one — a child whose
    # parent exits, leaving it reparented to pid 1 with its cwd in this
    # repository — and require the probe to name it BY PID.
    # [[feedback-a-probe-must-create-its-condition]] [[feedback-probe-silence-has-two-causes]]
    orphan_pid, found = None, False
    try:
        r = subprocess.run(["sh", "-c", "sleep 45 >/dev/null 2>&1 & echo $!"],
                           capture_output=True, text=True, cwd=root, timeout=20)
        orphan_pid = int(r.stdout.strip())
        for _ in range(30):            # reparenting is not instantaneous
            got = repo_orphans()
            if got is not None and any(o["pid"] == orphan_pid for o in got):
                found = True
                break
            time.sleep(0.2)
    except Exception:
        found = False
    finally:
        # ⛔ KILLED BY PID, the pid THIS arm created and no other.  Never
        # `pkill -f` a pattern — the seat's own tools carry the same patterns as
        # the processes it is hunting, which is how a sweep reaps a live seat.
        # [[feedback-a-process-filter-matches-its-own-waiter]]
        if orphan_pid:
            try:
                os.kill(orphan_pid, 9)
            except Exception:
                pass
    out.append((found, "the orphan probe FINDS a real orphan it created "
                       "(ppid 1, cwd = this repo), by pid"))

    # ⚠️ ARM 3 — THE HELD-OUT ARM, and it is the one that keeps the probe usable.
    # A probe that reported every process whose cwd is this repository would
    # name the seat's OWN live tools on every reading, and a conditions field
    # that always fires is one nobody reads.  This process is itself a live,
    # properly-parented process with its cwd in the repo, so it is the control
    # the probe must NOT report.  [[feedback-a-control-can-share-the-blind-spot]]
    got = repo_orphans()
    quiet = got is not None and not any(o["pid"] == os.getpid() for o in got)
    out.append((quiet, "the orphan probe does NOT report this live, parented "
                       "process whose cwd is also this repo"))

    # ⭐⭐ ARM 3b / 3c — THE CONTENTION STAMP, DRIVEN BOTH WAYS BY A REAL PROCESS.
    # A stamp that is never exercised is a field, not a label. These create a
    # process that LOOKS like a Lean build (the command name says WHAT) and put
    # it first outside this repository and then inside it (the cwd says WHOSE),
    # requiring the stamp to flip. Without the second arm a probe that reported
    # every Lean process anywhere would pass — and it would mark this seat's own
    # profiling run CONTENDED on every reading, which is a label nobody reads.
    # [[feedback-a-probe-must-create-its-condition]]
    # [[feedback-a-control-can-share-the-blind-spot]]
    import tempfile, shutil as _sh
    d = tempfile.mkdtemp(prefix="x86lean-fake-lean-")
    fake = os.path.join(d, "lean")
    seen_out = seen_in = None
    try:
        # ⛔ NOT a copy of /bin/sleep: macOS kills a copied PLATFORM BINARY on
        # exec because the copy has lost its code signature, so the first version
        # of this arm launched a process that was dead within milliseconds. Both
        # arms then "passed" the way a probe passes when its subject never
        # existed — and the OUT arm's red is the only reason I looked.
        # [[feedback-a-probe-must-create-its-condition]]
        # ⛔ `exec`, so the shell is REPLACED by the sleep. A plain `sleep`
        # leaves the shell as a parent whose death reparents the sleep to
        # init, so this fixture leaked a ppid-1 process for 40 s on every
        # arm that used it — caught by the post-flight probe D156 added,
        # in the two arms that PREDATE it. Measured: sh 54864 -> child
        # 55138; kill 54864 and 55138 survives with ppid 1.
        open(fake, "w").write("#!/bin/sh\nexec sleep 40\n")
        os.chmod(fake, 0o755)
        for label, cwd_ in (("out", d), ("in", root)):
            pr = subprocess.Popen([fake], cwd=cwd_,
                                  stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            try:
                hit = False
                for _ in range(25):
                    fb = foreign_builds()
                    if fb is not None and any(o["pid"] == pr.pid for o in fb):
                        hit = True
                        break
                    time.sleep(0.2)
                if label == "out":
                    seen_out = hit
                else:
                    seen_in = hit
            finally:
                pr.kill()
                pr.wait()
    except Exception:
        pass
    finally:
        _sh.rmtree(d, ignore_errors=True)
    out.append((seen_out is True,
                "a Lean-looking build OUTSIDE this repo is counted, and the "
                "reading is stamped CONTENDED"))
    out.append((seen_in is False,
                "the same binary run INSIDE this repo is NOT counted (the seat's "
                "own work must not mark its own reading contended)"))

    # ⭐⭐⭐ ARM 3d — EVERY TEMP TREE PRODUCER, NOT THE ONE THAT WAS NAMED (D156).
    # The filter this replaces excluded the literal `"x86lean-history"`, which is
    # ONE of thirteen `mkdtemp` prefixes in `scripts/`; a fake `lean` in the merge
    # gate's own `x86lean-delta-` worktree was counted as another campaign's
    # build. Each producer gets a real process here, and the last row is the
    # POSITIVE CONTROL that a genuinely foreign tree is still counted — without
    # it, "nothing is foreign" would pass by the filter having stopped looking.
    def _fake_lean_in(d):
        fk = os.path.join(d, "lean")
        # ⛔ `exec` — see the note on the other fixture: without it, killing
        # this process leaves a ppid-1 `sleep` behind for 40 seconds.
        open(fk, "w").write("#!/bin/sh\nexec sleep 40\n")
        os.chmod(fk, 0o755)
        return subprocess.Popen([fk], cwd=d, stdout=subprocess.DEVNULL,
                                stderr=subprocess.DEVNULL)

    def _is_foreign(pid, tries=25):
        for _ in range(tries):
            fb = foreign_builds()
            if fb is not None and any(o["pid"] == pid for o in fb):
                return True
            time.sleep(0.2)
        return False

    # (a) A REAL detached worktree of this repo, which is what the merge gate and
    # the drift gate actually profile. This exercises the STRUCTURAL test; a
    # plain temp directory would not, and an arm that passed on one would be
    # asserting the name rule while claiming to assert the structural one.
    wt_a = tempfile.mkdtemp(prefix="x86lean-delta-")
    wt_tree = os.path.join(wt_a, "base")
    pr_a = None
    try:
        subprocess.run(["git", "worktree", "add", "--detach", wt_tree, "HEAD"],
                       cwd=root, capture_output=True, text=True, timeout=120)
        pr_a = _fake_lean_in(wt_tree)
        out.append((_is_foreign(pr_a.pid) is False,
                    "a Lean build in a REAL detached worktree of this repo "
                    "(x86lean-delta-, what the merge and drift gates profile) is "
                    "NOT counted as another campaign's build"))
    finally:
        if pr_a:
            pr_a.kill()
            pr_a.wait()
        subprocess.run(["git", "worktree", "remove", "--force", wt_tree],
                       cwd=root, capture_output=True, text=True)
        _sh.rmtree(wt_a, ignore_errors=True)

    # (b) THE POSITIVE CONTROL. Without it "nothing is foreign" passes by the
    # filter having stopped looking. Its prefix is declared in FOREIGN_FIXTURES.
    d_b = tempfile.mkdtemp(prefix="some-other-campaign-")
    pr_b = None
    try:
        pr_b = _fake_lean_in(d_b)
        out.append((_is_foreign(pr_b.pid) is True,
                    "a genuinely foreign tree IS counted as another campaign's "
                    "build (the control that keeps the row above honest)"))
    finally:
        if pr_b:
            pr_b.kill()
            pr_b.wait()
        _sh.rmtree(d_b, ignore_errors=True)

    # (c) THE POST-KILL CASE THE NAME FALLBACK EXISTS FOR: the process is alive
    # and its worktree DIRECTORY HAS BEEN REMOVED, so nothing structural is left
    # to read. ⚠️ If `lsof` no longer reports a cwd for a process whose directory
    # is gone, this arm has no input and is reported INAPPLICABLE rather than
    # green — an assertion no input reaches is not a second gate.
    # [[feedback-an-implied-assertion-is-not-a-second-gate]]
    d_c = tempfile.mkdtemp(prefix="x86lean-delta-")
    pr_c, reachable = None, False
    try:
        pr_c = _fake_lean_in(d_c)
        time.sleep(0.5)
        _sh.rmtree(d_c, ignore_errors=True)
        for _ in range(15):
            fb = foreign_builds()
            lf = subprocess.run(["lsof", "-a", "-d", "cwd", "-p", str(pr_c.pid)],
                                capture_output=True, text=True, timeout=30)
            if "COMMAND" in lf.stdout and str(pr_c.pid) in lf.stdout:
                reachable = True
                out.append((fb is not None
                            and not any(o["pid"] == pr_c.pid for o in fb),
                            "a process whose worktree DIRECTORY WAS REMOVED is "
                            "still recognised as this seat's (the name fallback's "
                            "only job)"))
                break
            time.sleep(0.2)
        if not reachable:
            print("  ⚠️  INAPPLICABLE: lsof reports no cwd for a process whose "
                  "directory was removed, so the deleted-worktree arm has no "
                  "input on this platform and is NOT counted as passing")
    finally:
        if pr_c:
            pr_c.kill()
            pr_c.wait()
        _sh.rmtree(d_c, ignore_errors=True)

    # ⭐⭐ ARM 3e — THE CONVENTION IS DERIVED FROM THE SOURCE, NOT TYPED HERE.
    # `_own_tree`'s name fallback recognises this repository's scratch space by
    # `TMP_PREFIX`. That is only sound while every producer obeys it, so this
    # reads every `mkdtemp(prefix=...)` in `scripts/` and requires it — a
    # fourteenth producer with a different prefix reds this arm instead of
    # silently becoming another campaign's build.
    # [[feedback-a-declared-list-inherits-its-default]]
    prefixes, offenders = set(), []
    for fn in sorted(glob.glob(os.path.join(os.path.dirname(
            os.path.abspath(__file__)), "*.py"))):
        for m in re.finditer(r'mkdtemp\(prefix="([^"]+)"', open(fn).read()):
            prefixes.add(m.group(1))
            if not (m.group(1).startswith(TMP_PREFIX)
                    or m.group(1) in FOREIGN_FIXTURES):
                offenders.append(f"{os.path.basename(fn)}:{m.group(1)}")
    stale = [k for k in FOREIGN_FIXTURES if k not in prefixes]
    out.append((bool(prefixes) and not offenders and not stale,
                f"all {len(prefixes)} mkdtemp prefixes in scripts/ start with "
                f"{TMP_PREFIX!r} or are declared impersonation fixtures"
                + (f" — OFFENDERS: {offenders}" if offenders else "")
                + (f" — STALE declarations: {stale}" if stale else "")))

    # ⭐⭐⭐ ARM 3f — QUEUE ITEM 10 ITSELF: an orphan in a WORKTREE, which is what a
    # killed timing job actually leaves, must be reported as MINE. Under the old
    # filter this process was invisible to `repo_orphans` (whose test was cwd ==
    # the repo root, exactly) AND counted as somebody else's build.
    wt_root = tempfile.mkdtemp(prefix="x86lean-delta-")
    wt = os.path.join(wt_root, "base")
    opid, mine_seen, other_seen = None, False, False
    try:
        # ⛔ A REAL worktree, not a bare temp directory: since the name fallback
        # was narrowed to REMOVED directories, an existing scratch dir is
        # correctly NOT this seat's, and an arm built on one would be asserting
        # the old, too-broad rule.
        subprocess.run(["git", "worktree", "add", "--detach", wt, "HEAD"],
                       cwd=root, capture_output=True, text=True, timeout=120)
        r = subprocess.run(["sh", "-c", "sleep 45 >/dev/null 2>&1 & echo $!"],
                           capture_output=True, text=True, cwd=wt, timeout=20)
        opid = int(r.stdout.strip())
        for _ in range(30):
            got = repo_orphans()
            if got is not None and any(o["pid"] == opid for o in got):
                mine_seen = True
                break
            time.sleep(0.2)
        fb = foreign_builds()
        other_seen = fb is not None and any(o["pid"] == opid for o in fb)
    except Exception:
        pass
    finally:
        # ⛔ BY PID, the pid this arm created. Never a name pattern.
        if opid:
            try:
                os.kill(opid, 9)
            except Exception:
                pass
            # ⛔ WAIT FOR IT TO ACTUALLY GO. The next arm asks whether any orphan
            # of mine is alive, and a SIGKILLed process lingers in the table until
            # init reaps it — the first spelling read that lingering pid and the
            # control went red against a correct tool.
            for _ in range(50):
                try:
                    os.kill(opid, 0)
                except OSError:
                    break
                time.sleep(0.1)
        subprocess.run(["git", "worktree", "remove", "--force", wt],
                       cwd=root, capture_output=True, text=True)
        _sh.rmtree(wt_root, ignore_errors=True)
    out.append((mine_seen, "an orphan in a delta-gate WORKTREE is reported as "
                           "MINE (the case a killed timing job leaves behind)"))
    out.append((other_seen is False, "...and the same orphan is NOT also counted "
                                     "as another campaign's build"))

    # ⚠️ ARM 3g — the post-flight probe's own HELD-OUT control: with no orphan of
    # mine alive, it must return 0 and say so. A checker that reported trouble
    # unconditionally would pass every arm above.
    rc_clean, _ = post_flight()
    out.append((rc_clean in (0, 2), "the post-flight probe returns 0 (or 2 if it "
                                    "could not look) when nothing of mine is left "
                                    "detached — the caller's own pid included, "
                                    "since a backgrounded probe is itself ppid 1"))

    # ⚠️ ARM 3h — THE WORKTREE HALF (D163), CONTROL FIRST AND THEN PLANTED. The
    # arm above is the control: with no extra checkout registered, `stale_worktrees`
    # is empty and the probe is clean. ⛔ Without the plant below that silence has
    # two causes, and "the repo happens to have no worktrees" is the likelier one.
    # [[feedback-a-probe-must-create-its-condition]]
    import shutil as _sh_wt
    wt_clean = stale_worktrees()
    out.append((wt_clean == [], "CONTROL — no extra worktree is registered, so the "
                                "probe's silence is about the repository"))
    _wt = tempfile.mkdtemp(prefix="x86lean-postflight-arm-")
    _wtp = os.path.join(_wt, "wt")
    try:
        subprocess.run(["git", "worktree", "add", "--detach", _wtp, "HEAD"],
                       cwd=root, capture_output=True, text=True, timeout=120)
        seen = stale_worktrees() or []
        out.append((any(os.path.realpath(t["path"]) == os.path.realpath(_wtp)
                        for t in seen),
                    "a registered extra worktree IS FOUND and named by path — the "
                    "leaving `kernel_delta` makes two of when it is killed"))
        rc_wt, ln_wt = post_flight()
        out.append((rc_wt == 1 and any("WORKTREE" in l for l in ln_wt),
                    "...and the post-flight VERDICT goes to 1 for it, so a stale "
                    "checkout can no longer ride under `nothing of mine is running "
                    "detached` — which was TRUE while 293 MB sat in five of them"))
    finally:
        subprocess.run(["git", "worktree", "remove", "--force", _wtp],
                       cwd=root, capture_output=True, text=True, timeout=120)
        _sh_wt.rmtree(_wt, ignore_errors=True)
    # ⭐ AND THE OTHER SHAPE, or the report has a branch nothing reaches. A
    # registration whose DIRECTORY is gone is the only case `git worktree prune`
    # alone would clear, and the message above distinguishes it — so it needs an
    # input. The plant above sits under $TMPDIR exactly like the real leak, which
    # is why this second one varies the dimension that plant holds fixed.
    # [[feedback-a-control-can-share-the-blind-spot]]
    # [[feedback-an-implied-assertion-is-not-a-second-gate]]
    _wt2 = tempfile.mkdtemp(prefix="x86lean-postflight-gone-")
    _wtp2 = os.path.join(_wt2, "wt")
    try:
        subprocess.run(["git", "worktree", "add", "--detach", _wtp2, "HEAD"],
                       cwd=root, capture_output=True, text=True, timeout=120)
        _sh_wt.rmtree(_wt2, ignore_errors=True)          # the directory, not the registration
        gone = [t for t in (stale_worktrees() or [])
                if os.path.realpath(t["path"]) == os.path.realpath(_wtp2)]
        out.append((len(gone) == 1 and gone[0]["exists"] is False,
                    "a registration whose DIRECTORY IS GONE is found and flagged as "
                    "such — the one case `git worktree prune` alone would clear"))
    finally:
        subprocess.run(["git", "worktree", "prune"], cwd=root,
                       capture_output=True, text=True, timeout=120)
        _sh_wt.rmtree(_wt2, ignore_errors=True)

    # ⛔ AND THE RESTORE IS ITSELF AN ARM: an arm that leaves its plant behind
    # makes every later run of this selftest report the plant as a finding.
    out.append((stale_worktrees() == [], "...and the plant is REMOVED, so this "
                                         "selftest does not leave the very leak it "
                                         "was written to catch"))

    # ⛔ ARM 4 — THE DUPLICATED PARSE HAS NOT DIVERGED.  `threads_ab` carries its
    # own copy of the `type checking` parse (its docstring says "copied from
    # kernel_cost.kernel_ms").  The copy cannot simply be deleted: importing
    # THIS module would run its module-level `os.chdir(root)` and re-read the
    # importer's argv for `--root`.  So the two are held to agreement instead,
    # on the cases that differ between plausible implementations — the `s` vs
    # `ms` unit, the real zero, and the missing block that must NOT read as one.
    # [[feedback-duplicate-born-in-agreement]] [[feedback-two-readings-are-not-two-witnesses]]
    cases = [
        ("cumulative profiling times\n    type checking 1.5s\n", 1500.0),
        ("cumulative profiling times\n    type checking 250ms\n", 250.0),
        ("cumulative profiling times\n    elaboration 3ms\n", 0.0),   # a real zero
        ("lean: something exploded\n", None),                          # NOT a zero
    ]
    agree = True
    for blob, want in cases:
        m = re.search(r'^\s*type checking\s+([\d.]+)(ms|s)\s*$', blob, re.M)
        if m:
            mine = float(m.group(1)) * (1000 if m.group(2) == "s" else 1)
        else:
            mine = 0.0 if "cumulative profiling times" in blob else None
        theirs = _tab.parse_type_checking(blob)
        if mine != want or theirs != want:
            agree = False
    out.append((agree, "kernel_cost's and threads_ab's `type checking` parses "
                       "still agree (units, a real zero, and a missing block)"))

    # ⚠️ ARM 5 — THE LEGACY SENTINEL SURVIVES A FAILED PROBE.  Three analysers
    # format the top-level `load1` with `:.2f`; a `None` there would surface as a
    # crash in a different tool reading the corpus months later.
    try:
        sentinel_ok = (_sentinel(None) == -1.0 and f"{_sentinel(None):.2f}" == "-1.00"
                       and _sentinel(3.5) == 3.5)
    except Exception:
        sentinel_ok = False
    out.append((sentinel_ok, "an unreadable load still formats for the legacy "
                             "`:.2f` readers (-1.0, not None)"))

    # ⚠️ ARM 6 — A MODULE NAME IS LOGICAL AND CARRIES NO PLATFORM SEPARATOR.
    # `glob` returns `os.sep`-joined paths, so before 2026-09-09 every module on
    # Windows came back as `X86\Basic` and `--decl-modules Tests.Coverage`
    # matched NOTHING. The walk would still have completed and written a corpus.
    # ⛔ THE BACKSLASH CASES ARE THE ARM: the forward-slash ones passed for the
    # whole life of the defect, so a probe built only from them proves nothing.
    bs = chr(92)
    name_ok = (mod_name("X86/Basic.lean") == "X86.Basic"
               and mod_name(f"X86{bs}Basic.lean") == "X86.Basic"
               and mod_name(f"Tests{bs}Coverage.lean") == "Tests.Coverage"
               and mod_name("X86.lean") == "X86")
    out.append((name_ok, "a module name is the same on both platforms — "
                         f"`X86{bs}Basic.lean` and `X86/Basic.lean` both give X86.Basic"))
    return out


def selftest():
    """⛔ DRIVE THE PER-DECLARATION GATE RED, EACH FAILURE MODE ALONE.

    A ceiling gate is the easiest kind to have and not have: it passes when the
    numbers are fine, and it also passes when it has stopped looking. This one
    has FOUR ways to stop looking and each is planted separately, in the CEILING
    FILE rather than in the model — a probe that edits its subject can leave it
    edited."""
    import shutil, tempfile
    saved = open(CEIL_FILE).read()
    probe_dir = tempfile.mkdtemp(prefix="x86lean-ceilprobe-")
    probe_ceil = os.path.join(probe_dir, "kernel_ceilings.txt")
    arms = [
        ("a declaration OVER its ceiling",
         lambda t: re.sub(r"(@decl memDestSweep )\S+", r"\g<1>100", t),
         "OVER"),
        ("the TAIL over its ceiling",
         lambda t: re.sub(r"(@tail )\S+", r"\g<1>100", t), "OVER"),
        # ⛔ the arm that matters most: a gated declaration that is renamed or
        # deleted takes its ceiling with it, and a gate that cannot find its
        # subject must not report a pass.
        ("a gated declaration that is NOT in the profile",
         lambda t: t.replace("@decl vectorCoverage ", "@decl vectorCoverageXX "),
         "NOT FOUND"),
        # ⛔ and the way this design could be used to become ungated: gate a few
        # declarations, omit the tail, and the rest of the module is free.
        ("declarations gated with NO tail ceiling",
         lambda t: re.sub(r"^.*@tail.*$", "", t, flags=re.M), "no @tail"),
    ]
    # ⭐ THE FIFTH ARM CREATES ITS OWN CONDITION.  The refusal branch fires on a
    # machine state, not on a file, so it cannot be planted in the ceiling file
    # like the four above; the load is overridden instead, and the arm requires
    # the word UNMEASURABLE and a non-zero exit.  Without it the branch would be
    # shipped untested on any machine quiet enough to run the selftest.
    load_arms = [("the load OUTSIDE the calibrated band", "9.99", "UNMEASURABLE"),
                 # ⚠️ AND THE HELD-OUT ARM: at a load INSIDE the band the refusal
                 # must NOT fire, or the gate has simply stopped gating.
                 ("the load INSIDE the band (must NOT refuse)", "1.00", None)]
    # ⭐ A SIXTH ARM, ON ITS OWN SEAM: a platform with NO load average at all.
    #    ⛔ It exists because the branch it drives was, for about ten minutes,
    #    written so that an unknown load fell through to `if fail:` — reporting
    #    "FAILED (over ceiling)" when a ceiling was breached and, with none
    #    breached, it would have returned **CLEAN** for a reading whose conditions
    #    are unknown. That is the exact defect the branch was added to fix,
    #    reintroduced one line below it, and only DRIVING it showed that.
    noload_arms = [("a platform with NO load average is UNMEASURABLE, not CLEAN",
                    "UNMEASURABLE")]
    bad = []
    try:
        for name, mutate, expect in arms:
            # ⛔ THE MUTATION GOES TO A TEMP FILE AND THE CHILD IS POINTED AT IT.
            # Nothing under the repository is written; see D75 and the note on
            # CEIL_FILE for the commit that paid for this line.
            open(probe_ceil, "w").write(mutate(saved))
            r = subprocess.run([sys.executable, os.path.abspath(__file__)],
                               capture_output=True, text=True,
                               env=dict(os.environ, X86LEAN_CEIL_FILE=probe_ceil))
            out = r.stdout + r.stderr
            ok = r.returncode != 0 and expect in out
            print(("  ✔ " if ok else "  ⛔ ") + name +
                  ("" if ok else f"   (rc={r.returncode}, expected {expect!r})"))
            if not ok:
                bad.append(name)
        for name, fake, expect in load_arms:
            r = subprocess.run([sys.executable, os.path.abspath(__file__)],
                               capture_output=True, text=True,
                               env=dict(os.environ, X86LEAN_FAKE_LOADAVG=fake))
            out = r.stdout + r.stderr
            if expect is None:
                ok = "UNMEASURABLE" not in out
            else:
                ok = r.returncode != 0 and expect in out
            print(("  ✔ " if ok else "  ⛔ ") + name +
                  ("" if ok else f"   (rc={r.returncode}, expected {expect!r})"))
            if not ok:
                bad.append(name)
        for name, expect in noload_arms:
            env = dict(os.environ, X86LEAN_NO_LOADAVG="1")
            env.pop("X86LEAN_FAKE_LOADAVG", None)   # the fake would SUPPLY a load
            r = subprocess.run([sys.executable, os.path.abspath(__file__)],
                               capture_output=True, text=True, env=env)
            out = r.stdout + r.stderr
            # ⛔ rc 3 SPECIFICALLY, not merely non-zero: rc 1 is "over ceiling",
            # and the whole point is that an unknown-conditions run must NOT be
            # reported as a verdict about the commit.
            ok = r.returncode == 3 and expect in out and "no load average" in out
            print(("  ✔ " if ok else "  ⛔ ") + name +
                  ("" if ok else f"   (rc={r.returncode}, wanted 3 + {expect!r})"))
            if not ok:
                bad.append(name)
    finally:
        shutil.rmtree(probe_dir, ignore_errors=True)
    # ⭐ THE POSITIVE CONTROL: four reds prove the gate can fail; only this proves
    # it can pass.
    #
    # ⚠️ ITS BYTE CHECK IS NOW TRIVIALLY TRUE, AND IS KEPT ON PURPOSE.  With the
    # seam the probe cannot write the shipped file, so "byte-restored" is no
    # longer a fact about a restore — it is the REGRESSION GUARD if the seam is
    # ever removed and the mutations come back into the tree.  Stated rather
    # than left to read as a live check (D75).
    # ⛔⛔ THIS CONTROL WAS WRITTEN ONCE WITH `X86LEAN_FAKE_LOADAVG="1.00"` AND
    # THAT WAS A DEFECT, CAUGHT BY ITS OWN FAILURE.  Forcing the load suppresses
    # the VERDICT but not the CONDITION: the child still profiled a busy machine,
    # only with the refusal disabled, so the arm asserted "the ceilings pass"
    # about a reading that cannot support either answer.  That is D111's own
    # confusion — a machine reading read as a code fact — reproduced inside the
    # probe written to prevent it, one hour later.
    #
    # ⇒ It runs at the REAL load and admits THREE outcomes, because there are
    # three:
    #     rc 0  the ceilings pass                     → the control did its job
    #     rc 3  UNMEASURABLE at this load             → it could not, and SAYS SO
    #     rc 1  over ceiling AT A CALIBRATED LOAD     → a real regression, FAIL
    # ⚠️ The middle case is a PASS that prints its own uselessness. It is not an
    # escape hatch: rc 1 — the only outcome that means "the code got slower on a
    # machine quiet enough to tell" — still fails the selftest.
    r = subprocess.run([sys.executable, os.path.abspath(__file__)],
                       capture_output=True, text=True)
    out0 = r.stdout + r.stderr
    untouched = open(CEIL_FILE).read() == saved
    unmeas = r.returncode == 3 and "UNMEASURABLE" in out0
    ok = untouched and (r.returncode == 0 or unmeas)
    print(("  ✔ " if ok else "  ⛔ ") +
          "control: the shipped ceilings PASS at a calibrated load, and the tree "
          "file is UNTOUCHED" +
          ("  ⚠️ UNMEASURABLE at this load — the control PASSED WITHOUT CHECKING "
           "THE CEILINGS; the only thing it verified today is that the gate "
           "refused rather than guessed" if unmeas else ""))
    # ⛔⛔ AND WHEN IT FAILS, PRINT WHY.  This arm used to DISCARD `r.stdout`, so a
    # CI log said only "a control failed" and never named the declaration that
    # was over its ceiling — the reading a developer actually needs, and the one
    # that cannot be recovered from a remote runner afterwards.  It cost two
    # diagnosis cycles (D94) before it was worth fixing: both times the answer
    # was only obtainable by re-running the whole gate locally, on a DIFFERENT
    # machine from the one that failed, which for a TIMING gate is precisely the
    # measurement that cannot be transferred.
    #
    # ⇒ 🔑 A GATE THAT REFUSES MUST SAY WHAT IT SAW.  A refusal with no reading
    # attached turns every remote failure into a local re-run, and for anything
    # machine-dependent the local re-run answers a different question.
    if not ok:
        if r.returncode == 0 or unmeas:
            print("     (the ceiling file was MODIFIED by the probe — a restore failed)")
        print("     ── the failing run's own output ──")
        for line in (r.stdout + r.stderr).splitlines():
            print("     " + line)
    if not ok:
        bad.append("control")
    # ⭐ the conditions/CPU/orphan arms (items 4d, 7, 8) — cheap and in-process
    cond_arms = conditions_selftest()
    for cok, cname in cond_arms:
        print(("  ✔ " if cok else "  ⛔ ") + cname)
        if not cok:
            bad.append(cname)
    n = len(arms) + len(load_arms) + 1 + len(cond_arms)
    if bad:
        print(f"kernel-cost selftest: FAIL ({len(bad)} of {n} arms)")
        return 1
    print(f"kernel-cost selftest: PASS ({n} arms — every way this gate "
          f"could stop looking, driven separately, plus the control)")
    return 0


def main():
    if "--selftest" in sys.argv:
        return selftest()
    if "--post-flight" in sys.argv:
        rc, lines = post_flight()
        print("\n".join(lines))
        return rc
    if "--emit-json" in sys.argv:
        return emit_json()
    register = "--register" in sys.argv
    subprocess.run(["lake", "build", "X86", "Tests", "X86Native"],
                   capture_output=True, text=True)
    ceil, decl_ceils, tail_ceils = read_ceilings()
    nrows = roster_size()
    nvecs = vector_count()
    rows, total, fail = [], 0.0, False
    for f in modules():
        n = mod_name(f)
        ms = kernel_ms(f)
        total += ms
        rows.append((n, ms))
    if register:
        with open(CEIL_FILE, "w") as fh:
            fh.write("# Registered KERNEL (type-checking) ceilings, milliseconds.\n")
            fh.write("# Generated by scripts/kernel_cost.py --register on the P0 baseline.\n")
            fh.write(f"# Ceiling = max(measured x {HEADROOM}, {FLOOR_MS}ms): below the floor,\n")
            fh.write("# timing noise dominates and a ratio would fail on a loaded machine.\n")
            for n, ms in rows:
                prev = ceil.get(n)
                if prev and prev[0] == "perRow":
                    fh.write(f"{n} {PER_ROW_TAG} "
                             f"{max(ms * HEADROOM / nrows, FLOOR_MS / nrows):.1f}\n")
                else:
                    fh.write(f"{n} {max(ms * HEADROOM, FLOOR_MS):.0f}\n")
        print(f"registered {len(rows)} ceilings → {CEIL_FILE}")
        ceil, decl_ceils, tail_ceils = read_ceilings()

    # ⭐⭐⭐ P2 BATCH 14 (D111) — THE BAND THIS TOOL'S OWN EFFECT MEASUREMENT
    # COVERS, AND THE VERDICT IT IS ALLOWED TO REACH OUTSIDE IT.
    #
    # The note printed below is a real measurement and it is a measurement AT
    # FOUR LOADS: 2.20, 3.42, 3.88, 4.08.  It says nothing whatever about load
    # 7.9, and this gate spent batch 14 asserting a 740 ms overrun and a
    # +1,490 ms regression at loads of 6.5-7.9 — of which the regression was
    # ~0 and the overrun belonged to the PARENT COMMIT.  Measured, by
    # alternating the two trees in one session:
    #
    #     parent 144e9a3   12,970 · 13,030 · 13,060   (loads 5.2 · 6.7 · 7.3)
    #     + batch 14       13,040 · 13,160 · 13,680   (loads 6.6 · 6.5 · 7.9)
    #     the same parent, measured earlier the same day        11,670
    #
    # ⇒ 🔑 A CEILING WHOSE MARGIN IS UNDER THE MACHINE'S OWN SPREAD REPORTS THE
    # MACHINE, NOT THE CODE.  The margin was 6.4%; the across-session shift at
    # ONE commit is 11%.
    #
    # ⛔ SO THE CEILING IS NOT RAISED — deriving a gate's new allowance from the
    # thing it checks is how a gate stops being one.  What changes is the VERDICT
    # this tool is entitled to reach: outside the calibrated band it reports
    # UNMEASURABLE and names the load it saw, instead of naming a commit.  It
    # still exits NON-ZERO; a refusal is not a pass, and the per-declaration
    # `OVER ⛔` markers below are printed unchanged so the readings are visible.
    #
    # ⚠️ THE HONEST COST, STATED: on a machine that is never this quiet, this gate
    # is now SILENT.  That is worse than a gate that works and better than one
    # that lies.  The repair is to gate the DELTA between two trees measured in
    # ONE session — the instrument the table above was produced by hand — and it
    # is a batch with its own red probes, not a tack-on.
    CALIBRATED_LOAD = (0.0, 4.1)
    faked = os.environ.get("X86LEAN_FAKE_LOADAVG")
    # ⚠️ A SECOND TEST SEAM, SAME DOCTRINE AS THE ONE BELOW: it can only make the
    # verdict STRICTER (UNMEASURABLE), never turn a red into a pass, and it prints
    # itself. It exists because the no-load-average branch fires on a PLATFORM,
    # which this machine cannot become — so without it the branch is shipped
    # tested-once-by-hand, which is what it was for about ten minutes.
    if os.environ.get("X86LEAN_NO_LOADAVG"):
        print("⚠️ LOAD AVERAGE SUPPRESSED by X86LEAN_NO_LOADAVG — this run is a PROBE "
              "of the unknown-conditions branch and its figures are not a measurement.")
        la1, la5, load_known = -1.0, -1.0, False
    else:
        try:
            la1, la5, _ = os.getloadavg()
            load_known = True
        except (AttributeError, OSError):
            # ⛔ AttributeError too, not just OSError: on Windows `os.getloadavg`
            # does not EXIST, so the original clause did not catch the case the
            # second machine actually produces.
            la1, la5 = -1.0, -1.0
            load_known = False
    if faked is not None:
        # ⚠️ A TEST SEAM THAT ANNOUNCES ITSELF.  `--selftest` needs to CREATE the
        # high-load condition rather than wait for one, so it can drive the
        # refusal red like every other arm.  The override is printed on every run
        # that uses it, so a measurement taken under it can never be quoted as a
        # clean one — and it can only make the verdict STRICTER (UNMEASURABLE),
        # never turn a red into a pass, so it is not an escape hatch.
        la1 = float(faked)
        print(f"⚠️ LOAD AVERAGE OVERRIDDEN by X86LEAN_FAKE_LOADAVG={faked} — this "
              f"run is a PROBE and its figures are not a measurement of anything.")
    if faked is not None:
        load_known = True          # the override SUPPLIES a load, and announces itself
    load = "unavailable" if not load_known else f"{la1:.2f} (1 min) / {la5:.2f} (5 min)"
    # ⛔⛔ AN UNKNOWN LOAD IS UNMEASURABLE, NOT MEASURABLE. This line read
    # `unmeasurable = la1 > CALIBRATED_LOAD[1]` alone, and with the -1.0 sentinel
    # that made a platform with NO load average come out as `False` -- i.e. FINE.
    # ⇒ 🔑 THE ABSENCE OF A CONDITION WOULD HAVE READ AS THE MOST FAVOURABLE
    #   POSSIBLE VALUE OF IT, in a gate whose whole purpose is to refuse readings
    #   taken under conditions it cannot vouch for. This function's own docstring
    #   two hundred lines up already says it: "the conditions a reading must be
    #   quoted with. `None` never a default."
    unmeasurable = (not load_known) or la1 > CALIBRATED_LOAD[1]
    # ⚠️ WHAT THIS LINE SAYS IS MEASURED, NOT INHERITED.  A first version quoted
    # scripts/kernel_ceilings.txt's "~15% high under load" — and batch 17 then
    # measured it: ordinary background load moves `Tests.Coverage` by NOTHING
    # (31 200 / 31 200 / 31 000 / 31 300 ms at one-minute loads of 2.20 / 4.08 / 3.42 / 3.88),
    # while CONTENTION WITH THE 56-ARM SELFTEST — a CPU-saturating Lean-and-ACL2
    # mix — moved it 4%-8% (32 500 and 33 600).  So the rule is not "load", it is
    # "contention for the same resource", and printing the inherited figure would
    # have been this repository's own D47 in the line added to prevent it.
    print(f"⚠️ LOAD AVERAGE DURING THIS MEASUREMENT: {load}. Measured effect on "
          f"Tests.Coverage: ordinary background load, none (four runs within "
          f"1% at loads 2.2-4.1); contention with the full selftest, 4%-8%. "
          f"A figure quoted without this line cannot be compared with another.")
    print(f"coverage-table rows (kernel-pinned rosterSize): {nrows}")
    print(f"{'MODULE':<24}{'KERNEL(ms)':>12}{'CEILING(ms)':>13}   VERDICT")
    for n, ms in rows:
        e = ceil.get(n)
        if e is None and n in decl_ceils:
            # ⚠️ NOT unregistered: gated PER DECLARATION below, which is a
            # stronger statement than a module total and is why the module total
            # has no ceiling of its own. The tail ceiling covers the remainder,
            # and the block below REFUSES if a module gates declarations without
            # one — so this branch cannot become a way to be ungated.
            v, cs = "gated per declaration ↓", "-"
        elif e is None:
            v, fail = "UNREGISTERED ⛔", True
            cs = "-"
        else:
            kind, val = e
            c = val * nrows if kind == "perRow" else val
            if ms > c:
                v, fail = "OVER CEILING ⛔", True
            else:
                v = "ok" if kind == "abs" else f"ok ({val:.1f}/row x {nrows})"
            cs = f"{c:.0f}"
        print(f"{n:<24}{ms:>12.1f}{cs:>13}   {v}")
    # ⭐⭐ THE PER-DECLARATION GATE.  No denominator anywhere in it.
    for mod, want in sorted(decl_ceils.items()):
        f = [x for x in modules() if mod_name(x) == mod]
        if not f:
            print(f"⛔ {mod} has per-declaration ceilings but no source file.")
            fail = True
            continue
        got = {name: ms for _l, name, ms in per_declaration(f[0])}
        total = dict(rows).get(mod)
        print(f"--- {mod}: per-declaration ceilings (ABSOLUTE ms, no denominator)")
        named = 0.0
        for name, c in sorted(want.items(), key=lambda kv: -kv[1]):
            ms = got.get(name)
            if ms is None:
                # ⛔ A MISSING READING IS NOT A ZERO.  A renamed or deleted
                # declaration takes its ceiling with it, and this gate must not
                # go quiet when its subject leaves.
                print(f"  ⛔ {name:44s} NOT FOUND in the profile — renamed, "
                      f"deleted, or now below the profiler threshold")
                fail = True
                continue
            named += ms
            v = "OVER ⛔" if ms > c else "ok"
            if ms > c:
                fail = True
            print(f"  {name:44s}{ms:>9.0f}{c:>9.0f}   {v}")
        tc = tail_ceils.get(mod)
        if tc is not None and total is not None:
            tail = total - named
            v = "OVER ⛔" if tail > tc else "ok"
            if tail > tc:
                fail = True
            print(f"  {'(everything else in the module)':44s}{tail:>9.0f}"
                  f"{tc:>9.0f}   {v}")
        elif tc is None:
            print(f"  ⛔ {mod} gates declarations but has no {TAIL_TAG} ceiling, "
                  f"so the rest of the module is ungated.")
            fail = True

    print("---")
    cov = dict(rows).get("Tests.Coverage")
    if cov:
        thms, vecs = coverage_growth_denominator()
        if thms and vecs:
            print(f"Tests.Coverage growth law (REPORTED, not gated): {cov:.0f}ms "
                  f"= {cov/nrows:.1f} ms/row over {nrows} rows, "
                  f"{cov/nvecs:.2f} ms/vector over {nvecs} kernel-pinned vectors "
                  f"({thms} assertions)")
            # ⛔ THIS SENTENCE USED TO NAME `memDestSweep` AS "~half the module"
            # AS A LITERAL, and P2 batch 11 took it from 18 500 to 4 400 ms —
            # 23% — while the sentence went on saying half.  A gate's own OUTPUT
            # is prose too, and prose in a tool nobody re-reads is exactly the
            # ungated claim this repository keeps paying for (D65, D94, D102).
            # ⇒ The share and the name are DERIVED from the profile now, so the
            # warning cannot describe a distribution the tool is not seeing.
            decls = per_declaration("Tests/Coverage.lean")
            top_ms, top_name = (decls[0][2], decls[0][1]) if decls else (0.0, "?")
            print(f"  ⚠️  NEITHER unit is flat: the largest single declaration "
                  f"({top_name}) is {100.0*top_ms/cov:.0f}% of the module on its "
                  f"own. See D62, D63 and D103 and the per-declaration table "
                  f"below; do not gate on a whole-module density.")
            for line, name, ms in decls[:8]:
                print(f"    {ms:9.0f} ms  {name}  (Tests/Coverage.lean:{line})")
    print(f"total kernel time across the development: {total:.1f}ms")
    # ⛔ THE REFUSAL COMES FIRST, because at a load outside the calibrated band
    # this tool cannot tell a regression from an afternoon — and a red that names
    # the wrong culprit is worse than no red, since it trains a reader to
    # discount the next one.
    if unmeasurable and not load_known:
        print("⛔ kernel-cost gate UNMEASURABLE — this platform has no load average, "
              "so the CONDITIONS of the reading are unknown. The readings above are "
              "printed and are NOT a verdict: a gate that refuses readings taken "
              "under conditions it cannot vouch for cannot make an exception for "
              "conditions it cannot SEE. Gate the DELTA between two trees measured "
              "in one session instead (D111).")
        # ⛔⛔ `return 3` — THE SAME EXIT CODE AS THE OTHER UNMEASURABLE BRANCH, and
        # it is here because I left it out on the first write. Without it this
        # branch FELL THROUGH to `if fail:` — so an unknown-conditions run reported
        # rc 1 "FAILED (over ceiling)" when a ceiling was breached, and, worse,
        # would have returned 0 "CLEAN" when none was. ⇒ 🔑 **I REINTRODUCED, ONE
        # LINE BELOW, THE EXACT DEFECT THIS BRANCH WAS ADDED TO FIX**: an absent
        # condition resolving to the most favourable available verdict. Caught by
        # driving the branch instead of reading it.
        return 3
    elif unmeasurable:
        print(f"⛔ kernel-cost gate UNMEASURABLE — one-minute load was {la1:.2f}, "
              f"outside the band this tool's own effect measurement covers "
              f"(loads {CALIBRATED_LOAD[0]:.1f}-{CALIBRATED_LOAD[1]:.1f}). The "
              f"readings above are printed and are NOT a verdict about this "
              f"commit: at load 6.5-7.9 the unchanged parent of P2 batch 14 read "
              f"550ms over this same ceiling. Re-run on a quiet machine, or gate "
              f"the DELTA between two trees measured in one session (D111).")
        return 3
    if fail:
        print("⛔ kernel-cost gate FAILED (over ceiling, or unregistered).")
        return 1
    print("kernel-cost gate: CLEAN")
    return 0


# ⛔⛔ THE GUARD IS LOAD-BEARING (D151).  Without it, `import kernel_cost` RAN THE
# WHOLE GATE — a two-minute profiling pass and a `sys.exit` — so the module could
# not be imported by its own selftest, by a probe, or by any future tool.  I hit
# this while writing the arms below and the symptom was a probe that appeared to
# hang: it was profiling the development.  `kernel_delta.py` was given the same
# guard by D148 for the same reason, which is the tell — the defect was already
# named once in this repository and its sibling was never swept for.
# [[feedback-naming-a-defect-is-not-finding-its-siblings]]
if __name__ == "__main__":
    sys.exit(main())
