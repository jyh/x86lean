#!/usr/bin/env python3
"""THE ONE DOOR: every Lean ELABORATION this repository starts goes through here (desk MB).

⛔⛔ THE FLEET RULE, ratified 2026-08-06 after TWO OOM INCIDENTS IN ONE MORNING: a single
elaboration on a heavy file reaches 6-9 GB, and five seats at default parallelism exhausted
64 GB plus 8 GB of swap on the box this repository shares. Every `lake build` and every
`lake env lean FILE` on a shared seat goes through `../saltbuild.sh`, which takes the fleet's
one-heavy-job lock, caps `LEAN_NUM_THREADS` at 4, passes `-M 24000`, and appends a line to the
fleet audit log. Until 2026-09-14 x86lean's CLAUDE.md did not carry that rule and 19 call
sites in 14 scripts called `lake` directly (math's sibling sweep, 09/13, found it; the count is
`check_lean_route.py`'s red-first run, which found more than the three sites the desk row named).

⚖️ A CONDITIONAL, NOT A SUBSTITUTION — salt PR #128's shape. `saltbuild.sh` lives OUTSIDE this
tree, so it does not travel with a clone and a CI runner has none. There the bare call is
REQUIRED, and it is also harmless: a runner is a private box with one job. The route is chosen
from THIS FILE'S checkout (`<root>/../saltbuild.sh`), never from the working directory, so a
profiler pointed at a detached worktree in a scratch directory still takes the lock.
EITHER WAY THE ROUTE IS PRINTED (to stderr, so no parsed stdout moves): a gate that silently
picks one of two paths reports the same green for both.

⚠️ WHAT THE WRAPPER ROUTE CHANGES FOR A MEASUREMENT, declared rather than discovered:
  * `LEAN_NUM_THREADS=4` instead of the machine default. D150 measured `--threads 1` moving the
    gated `type checking` level to 0.76x; 4 threads sits between. Every delta tool compares two
    trees under the SAME route, and A′'s yukon ceilings carry a x3 margin, so neither can red
    on this — but a reading taken before 2026-09-14 and one taken after are different
    conditions, and a caller that records conditions records `route()` with them.
  * a child's WALL time now includes any wait for the fleet lock, and its child CPU includes
    the wrapper's own shell (`git status`, `shasum`: tens of ms). No gate reads either.
  * the profiler's own numbers, and ku, are unaffected by the lock by construction.

⚠️ WHAT IS NOT ROUTED, BECAUSE IT IS NOT AN ELABORATION (measured 2026-09-14, /usr/bin/time -l):
  `lake env .lake/build/bin/<binary> …` runs compiled code — x86lean-axioms peaked at 0.35 GB,
  x86lean-diff `emit` at 1.19 GB, against 6-9 GB for the elaborations the rule exists for — and
  `lake env lean --version` elaborates nothing. `check_lean_route.py` prints both classes as
  EXEMPT rather than ignoring them, so the exemption is visible where the gate runs.

THE WRAPPER'S STDOUT GRAMMAR, which `unwrap` reads and REFUSES when it does not hold:
    (saltqueue:… | saltbuild:…)*          before Lean starts; after a `saltqueue: still queued`
                                           line, indented census rows until the next prefixed line
    <Lean's own stdout, byte for byte>
    saltbuild EXIT=<rc>                   last line, and <rc> is the process's exit status
  Exit 75/76 means THE WRAPPER NEVER STARTED LEAN (lock-wait abort / refused configuration):
  that is not a failure of the tree, and it is reported as its own refusal.

USAGE
    import lean_route
    r = lean_route.run("build", ["X86", "Tests"], cwd=wt)         # lake build X86 Tests
    r = lean_route.run("lean", [f, "-D", "profiler=true"])         # lake env lean f -D …
    # r is a CompletedProcess: text stdout (wrapper lines removed), stderr, returncode
  from a shell script:
    python3 scripts/lean_route.py build X86 x86lean-axioms
    python3 scripts/lean_route.py lean "$FILE" -D profiler=true
    python3 scripts/lean_route.py --route          # print the route this checkout takes
    python3 scripts/lean_route.py --selftest
"""
import os
import re
import stat
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

NEVER_STARTED = (75, 76)
_PREFIXES = ("saltqueue:", "saltbuild:")
_CENSUS_OPENER = "saltqueue: still queued"
_TRAILER = re.compile(r"^saltbuild EXIT=(\d+)\b")


class RouteRefused(SystemExit):
    """The wrapper did something this module cannot read, or never started Lean.

    ⛔ A SystemExit WITH CODE 2, NOT A PLAIN EXCEPTION. Uncaught, a plain exception exits 1 — and
    rc 1 is `ku_delta`'s and `kernel_delta`'s code for YOUR CHANGE FAILED. A route that could not be
    read is a structural refusal, which is rc 2 in every gate here, and it says why on stderr.
    """
    loud = True

    def __init__(self, msg):
        super().__init__(2)
        self.msg = msg
        if RouteRefused.loud:
            print(f"⛔ lean_route REFUSED (rc 2, never a verdict about the tree): {msg}",
                  file=sys.stderr, flush=True)

    def __str__(self):
        return self.msg


def wrapper_path(root=ROOT):
    return os.path.normpath(os.path.join(root, os.pardir, "saltbuild.sh"))


def lake_path():
    p = os.path.expanduser("~/.elan/bin/lake")
    return p if os.path.exists(p) else "lake"


def route(root=ROOT):
    """('wrapper', path) when `<root>/../saltbuild.sh` is executable, else ('bare', lake)."""
    w = wrapper_path(root)
    if os.path.isfile(w) and os.access(w, os.X_OK):
        return "wrapper", w
    return "bare", lake_path()


def describe(how, exe):
    if how == "wrapper":
        return (f"lean-route: via {exe} (fleet lock · LEAN_NUM_THREADS=4 · -M 24000 · audit log)")
    return (f"lean-route: via bare {exe} (no ../saltbuild.sh beside this checkout — "
            f"expected on a CI runner, a defect on a shared seat)")


def argv(kind, args, root=ROOT):
    """The command for one elaboration, and the route it takes."""
    how, exe = route(root)
    args = list(args)
    if kind == "build":
        if args and args[0].endswith(".lean"):
            # the wrapper reads a leading `.lean` as an AUDIT, not a build target
            raise RouteRefused(f"build target {args[0]!r} looks like a file; use kind 'lean'")
        return ([exe, *args] if how == "wrapper" else [exe, "build", *args]), how
    if kind == "lean":
        files = [i for i, a in enumerate(args) if a.endswith(".lean")]
        if len(files) != 1:
            raise RouteRefused(f"kind 'lean' needs exactly one .lean file, got {len(files)}: {args!r}")
        if how == "bare":
            return [exe, "env", "lean", *args], how
        # the wrapper dispatches on "$1" being a .lean file, so the file goes FIRST; the
        # other arguments keep their order, which keeps every `-D key=value` pair intact.
        # Measured 2026-09-14: `lean FILE -D profiler=true` and `lean FILE --json` honour
        # options placed after the file (profiler output present; absent in the no-flag control).
        i = files[0]
        return [exe, args[i], *args[:i], *args[i + 1:]], how
    raise RouteRefused(f"unknown kind {kind!r} (expected 'build' or 'lean')")


def unwrap(stdout, returncode):
    """Lean's own stdout out of the wrapper's. Refuses when the grammar does not hold."""
    lines = stdout.split("\n")
    end = len(lines)
    while end > 0 and lines[end - 1] == "":
        end -= 1
    if returncode in NEVER_STARTED:
        tail = "\n".join(lines[max(0, end - 5):end])
        raise RouteRefused(f"the wrapper exited {returncode}: Lean NEVER STARTED (lock-wait abort or a "
                           f"refused configuration). NOT a failure of this tree — retry.\n{tail}")
    m = _TRAILER.match(lines[end - 1]) if end else None
    if not m or int(m.group(1)) != returncode:
        tail = "\n".join(lines[max(0, end - 5):end]) or "(empty stdout)"
        raise RouteRefused(f"the wrapper's last stdout line is not `saltbuild EXIT={returncode}` — its "
                           f"output grammar has changed, and a guessed strip could eat Lean's output. "
                           f"Last lines seen:\n{tail}")
    i, census = 0, False
    while i < end - 1:
        ln = lines[i]
        if ln.startswith(_PREFIXES):
            census = ln.startswith(_CENSUS_OPENER)
        elif not (census and ln.startswith("  ")):
            break
        i += 1
    body = lines[i:end - 1]
    return "\n".join(body) + ("\n" if body else "")


_said = set()


def run(kind, args, *, cwd=None, root=ROOT, timeout=None, announce=True):
    """subprocess.run(capture_output=True, text=True) over the routed command."""
    cmd, how = argv(kind, args, root)
    if announce and (how, cmd[0]) not in _said:
        _said.add((how, cmd[0]))
        print(describe(how, cmd[0]), file=sys.stderr, flush=True)
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    if how == "wrapper":
        r = subprocess.CompletedProcess(r.args, r.returncode, unwrap(r.stdout, r.returncode), r.stderr)
    return r


# ── selftest ───────────────────────────────────────────────────────────────────────────────
def selftest() -> int:
    out = []
    RouteRefused.loud = False

    def arm(name, ok):
        out.append((bool(ok), name))

    def refuses(fn, needle):
        try:
            fn()
        except RouteRefused as e:
            return needle in str(e)
        return False

    with tempfile.TemporaryDirectory(prefix="x86lean-leanroute-") as tmp:
        repo = os.path.join(tmp, "repo")
        os.makedirs(repo)
        w = os.path.join(tmp, "saltbuild.sh")

        # ROUTE — absent, present-but-not-executable, executable
        arm("route: no sibling saltbuild.sh -> bare", route(repo)[0] == "bare")
        open(w, "w", encoding="utf-8").write("#!/bin/sh\nexit 0\n")
        arm("route: a NON-executable saltbuild.sh -> bare", route(repo)[0] == "bare")
        os.chmod(w, os.stat(w).st_mode | stat.S_IXUSR)
        arm("route: an executable sibling saltbuild.sh -> wrapper", route(repo) == ("wrapper", w))
        # (the first spelling used tmp/elsewhere, whose parent IS tmp — it holds the wrapper, and the
        # arm went red on its own fixture. The sibling test is exactly one level: ../saltbuild.sh.)
        arm("route: only the IMMEDIATE parent counts — a wrapper two levels up -> bare",
            route(os.path.join(tmp, "deeper", "repo"))[0] == "bare")

        # ARGV
        c, h = argv("build", ["X86", "Tests"], repo)
        arm("argv: wrapper build passes targets straight through", c == [w, "X86", "Tests"])
        c, h = argv("lean", ["-D", "profiler=true", "--json", "F.lean"], repo)
        arm("argv: wrapper lean puts the file FIRST and keeps -D pairs in order",
            c == [w, "F.lean", "-D", "profiler=true", "--json"])
        arm("argv: two .lean files refuse", refuses(lambda: argv("lean", ["a.lean", "b.lean"], repo), "exactly one"))
        arm("argv: no .lean file refuses", refuses(lambda: argv("lean", ["--version"], repo), "exactly one"))
        arm("argv: a .lean build target refuses", refuses(lambda: argv("build", ["X.lean"], repo), "looks like a file"))
        os.chmod(w, 0o644)
        c, h = argv("lean", ["-D", "x=1", "F.lean"], repo)
        arm("argv: bare lean keeps the caller's order under `lake env lean`",
            h == "bare" and c[1:] == ["env", "lean", "-D", "x=1", "F.lean"])
        c, h = argv("build", [], repo)
        arm("argv: bare build with no targets is `lake build`", c[1:] == ["build"])

        # UNWRAP — every mutation asserts its own difference from the control
        plain = "saltqueue: ticket P2 seat=root pid=1\n{\"data\":\"42\"}\nsaltbuild EXIT=0\n"
        arm("unwrap: control — ticket, one line, trailer", unwrap(plain, 0) == "{\"data\":\"42\"}\n")
        queued = ("saltqueue: ticket P2 seat=root pid=1\n"
                  "saltqueue: QUEUED behind 1 ticket(s) — waiting (no timeout, by ruling)\n"
                  "saltqueue: still queued (300s) —\n"
                  "  CLASS  AGE        SEAT         PID\n"
                  "  P1     310s       math         777\n"
                  "saltqueue: HEAD OF QUEUE after 305s — attempting acquisition\n"
                  "saltbuild: waiting on the fleet lock (300s)\n"
                  "  type checking 12ms\n"
                  "done\n"
                  "saltbuild EXIT=1\n")
        arm("unwrap: census rows removed, an INDENTED Lean line after them kept",
            unwrap(queued, 1) == "  type checking 12ms\ndone\n")
        indented_first = "saltqueue: ticket P2 seat=root pid=1\n  indented lean line\nsaltbuild EXIT=0\n"
        arm("unwrap: an indented FIRST Lean line is kept when no census opened",
            unwrap(indented_first, 0) == "  indented lean line\n")
        arm("unwrap: silent Lean -> empty string",
            unwrap("saltqueue: ticket P2 seat=root pid=1\nsaltbuild EXIT=0\n", 0) == "")
        no_queue = "saltbuild: saltqueue.sh NOT FOUND at /x — running UNQUEUED\nout\nsaltbuild EXIT=0\n"
        arm("unwrap: the unqueued banner is a wrapper line", unwrap(no_queue, 0) == "out\n")
        arm("unwrap: trailer rc DISAGREES with the process rc -> refuse",
            refuses(lambda: unwrap(plain, 1), "grammar has changed"))
        arm("unwrap: no trailer -> refuse", refuses(lambda: unwrap("out\n", 0), "grammar has changed"))
        arm("unwrap: empty stdout -> refuse, naming it", refuses(lambda: unwrap("", 0), "(empty stdout)"))
        abort = ("saltqueue: ticket P2 seat=root pid=1\nsaltbuild EXIT=75 (LOCK-WAIT ABORT: the build "
                 "NEVER STARTED - this is NOT a build failure; RETRY the same command)\n")
        arm("unwrap: rc 75 -> NEVER STARTED, not a tree failure", refuses(lambda: unwrap(abort, 75), "NEVER STARTED"))
        arm("unwrap: rc 76 with an empty stdout -> NEVER STARTED", refuses(lambda: unwrap("", 76), "NEVER STARTED"))

        # END TO END through a fake wrapper that records its argv and speaks the grammar
        rec = os.path.join(tmp, "argv.txt")
        open(w, "w", encoding="utf-8").write(
            "#!/bin/sh\n"
            f"printf '%s\\n' \"$@\" > '{rec}'\n"
            "echo 'saltqueue: ticket P2 seat=root pid=1'\n"
            "echo payload-out\n"
            "echo payload-err >&2\n"
            "echo 'saltbuild EXIT=3'\n"
            "exit 3\n")
        os.chmod(w, 0o755)
        r = run("lean", ["-D", "a=b", "P.lean"], root=repo, announce=False)
        arm("run: stdout unwrapped, stderr passed through, rc preserved",
            (r.stdout, r.stderr, r.returncode) == ("payload-out\n", "payload-err\n", 3))
        arm("run: the wrapper received the file first",
            open(rec, encoding="utf-8").read().split("\n")[:3] == ["P.lean", "-D", "a=b"])
        open(w, "w", encoding="utf-8").write("#!/bin/sh\necho 'saltbuild EXIT=75 (LOCK-WAIT ABORT)'\nexit 75\n")
        arm("run: a wrapper abort surfaces as RouteRefused",
            refuses(lambda: run("build", ["X86"], root=repo, announce=False), "NEVER STARTED"))
        try:
            raise RouteRefused("probe")
        except SystemExit as e:
            arm("refusal: a SystemExit whose code is 2 (REFUSED), never 1 (a failed change)",
                isinstance(e, RouteRefused) and e.code == 2 and str(e) == "probe")

    bad = [n for ok, n in out if not ok]
    for ok, n in out:
        print(f"  {'✔' if ok else '⛔'} {n}")
    print(f"lean_route selftest: {len(out) - len(bad)}/{len(out)} arms")
    return 1 if bad else 0


def main(argv_=None):
    a = list(sys.argv[1:] if argv_ is None else argv_)
    if a and a[0] in ("build", "lean"):
        try:
            r = run(a[0], a[1:])
        except RouteRefused:
            return 2          # the reason is already on stderr
        sys.stdout.write(r.stdout)
        sys.stderr.write(r.stderr)
        return r.returncode
    sys.path.insert(0, HERE)
    from portable import strict_flags
    strict_flags(__file__, a)
    if "--selftest" in a:
        return selftest()
    if "--route" in a:
        print(describe(*route()))
        return 0
    print(__doc__.split("USAGE", 1)[1].rstrip())
    return 2


if __name__ == "__main__":
    sys.exit(main())
