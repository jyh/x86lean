#!/usr/bin/env python3
"""THE THREE THINGS THAT BREAK WHEN A SECOND MACHINE APPEARS.

⛔⛔ WHY THIS FILE EXISTS. On 2026-09-09 the Captain allocated a second machine
for QUEUE item 4b. Every measurement tool in this repository had been written on
one box, and the walk failed on the other THREE TIMES IN A ROW, each time one
line further in:

    1. `open(src).read()`      UnicodeDecodeError -- Python's default text
                               encoding is LOCALE-dependent (utf-8 here,
                               cp1252 on Windows) and Lean sources are unicode.
    2. `print("⚠️ …")`         UnicodeEncodeError -- the SAME defect on the
                               output side. Repairing the read half bought
                               exactly one more line of progress.
    3. `os.getloadavg()`       AttributeError -- POSIX only.

⇒ 🔑 **A PORTABILITY DEFECT IS INVISIBLE UNTIL THE SECOND MACHINE EXISTS, AND
THEN IT IS THE FIRST THING THAT BREAKS.** And they arrive one at a time, each
looking like the last one, which is what makes "I fixed it" premature three
times running [[feedback-naming-a-defect-is-not-finding-its-siblings]].

⭐ THEY LIVE HERE, IN ONE FILE, SO THE FIX HAS ONE HOME. The alternative — the
same two lines pasted into each tool — is how the third instance happens again
in the fourth tool.

⚠️ SCOPE, MEASURED AND DECLARED RATHER THAN QUIETLY WIDENED. This is imported by
the tools that actually run on a second machine. **Of ~25 scripts here that print
unicode, most still do not import it**, and unencoded `open()` calls run from 1 to
22 per file. That is a real, repo-wide condition and it is NAMED rather than
churned: a blanket rewrite of tools that only ever run on this Mac would be
change without a measurement behind it.
"""
import os
import subprocess
import sys


def utf8_stdio():
    """Make stdout/stderr utf-8 whatever the platform's locale says.

    Guarded: a stream without `.reconfigure` (a pipe replaced by a test, an old
    Python) must not turn a measurement tool into a crash.
    """
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8")
        except (AttributeError, ValueError):
            pass


def loadavg():
    """(1-min, 5-min, source), or (None, None, reason) where there is no such thing.

    ⛔⛔ NEVER ZERO ON FAILURE, AND THIS IS THE ONE THAT WOULD HAVE COST SOMETHING.
    The obvious repair for a POSIX-only API is `except: return 0.0`. That writes
    **load1 = 0.0** into every reading taken on the second machine — and `load1`
    is exactly the covariate this campaign's usability rules are argued over.
    ⇒ 🔑 **A MISSING MEASUREMENT DEFAULTED TO ZERO DOES NOT READ AS MISSING. IT
    READS AS THE MOST FAVOURABLE POSSIBLE OBSERVATION** — a perfectly idle box,
    on the machine chosen precisely because it is quiet.
    [[feedback-a-tool-has-no-concept-of-not-applicable]]
    """
    try:
        a, b, _ = os.getloadavg()
        return a, b, "os.getloadavg"
    except (AttributeError, OSError) as e:
        return None, None, f"unavailable on this platform ({type(e).__name__})"


def machine_id(root=None):
    """What machine and toolchain produced a reading.

    A reading that does not name its origin cannot be checked for the one failure
    that makes a cross-machine claim vacuous: two readings from the SAME machine
    agree because they share an origin.
    [[feedback-two-readings-are-not-two-witnesses]]
    """
    import platform
    lean = ""
    try:
        lean = subprocess.run(["lake", "env", "lean", "--version"], cwd=root,
                              capture_output=True, text=True, timeout=60).stdout.strip()
    except (OSError, subprocess.SubprocessError):
        pass
    return {"node": platform.node(), "platform": platform.platform(),
            "machine": platform.machine(), "python": platform.python_version(),
            "lean": lean}


def strict_flags(source_file, argv=None):
    """Refuse a `--flag` this script does not mention ANYWHERE in its own source.

    ⛔⛔ WHY, AND IT IS WORSE THAN A FALSE GREEN. 22 of 42 scripts here dispatch on
    `"--selftest" in sys.argv` and otherwise fall through to their main path. Given
    a flag they do not know, they do not refuse — they RUN. Measured 2026-09-09:
    `threads_ab.py --definitely-not-a-real-flag-xyz` started
    `lake env lean -D profiler=true` on `Tests/Coverage.lean`, saturated a core for
    over 300 seconds on a machine six other seats were using, and **survived its
    caller's timeout as an orphan** that had to be killed by pid.
    ⇒ 🔑 **A SCRIPT THAT FALLS THROUGH ON AN UNKNOWN FLAG DOES NOT MERELY REPORT
    SUCCESS — IT EXECUTES ITS MAIN JOB.** For a gate that is a green about the
    wrong subject; for a profiler it is minutes of somebody else's CPU.
    *(This was found by a census that invoked its subjects. **A census that invokes
    is not read-only** — I caused the incident I am documenting.)*

    ⭐ THE KNOWN SET IS DERIVED FROM THE SOURCE, WHICH IS WHY ADOPTING THIS CANNOT
    BREAK A WORKING INVOCATION. Any flag a script handles must appear in it as a
    literal, so "mentioned nowhere in this file" is a sound test for "not mine". A
    hand-typed allowlist beside each call site would be a second roster that goes
    stale against the code [[feedback-a-duplicate-born-in-agreement]].
    ⚠️⚠️ DECLARED BLIND SPOTS, BOTH MEASURED, BECAUSE THIS GUARD IS SAFETY-BIASED
    AND NOT PRECISE:
      (a) A flag assembled at run time (`"--" + name`) is not a literal and WOULD
          be refused. No script here does that; if one ever does, it must pass its
          own set rather than this being loosened.
      (b) ⛔ THE SET IS EVERY QUOTED `--x` IN THE FILE, INCLUDING ONES IN TEST
          FIXTURES AND EXAMPLES. Measured on this very file: `portable.py --bogus`
          is ACCEPTED, because `"--bogus"` appears in an arm below. So the guard
          admits some flags a script does not actually implement.
    ⇒ 🔑 **THAT ASYMMETRY IS THE DESIGN, NOT AN OVERSIGHT.** The failure this exists
    to stop is a script RUNNING WORK it was not asked for; the failure it must never
    cause is refusing a call that works. Erring permissive costs a missed typo;
    erring strict breaks production. It catches the case that actually happens — a
    flag that appears NOWHERE in the file — which is every instance measured today.
    ⚠️ It is therefore NOT a substitute for a real parser. A script that wants exact
    flags should use `argparse` with `parse_args()`, which refuses by construction.
    """
    import re as _re
    argv = list(sys.argv[1:] if argv is None else argv)
    try:
        text = open(source_file, encoding="utf-8").read()
    except OSError:
        return                      # cannot read our own source: refuse nothing
    known = set(_re.findall(r'"(--[A-Za-z][A-Za-z0-9-]*)"', text))
    known |= set(_re.findall(r"'(--[A-Za-z][A-Za-z0-9-]*)'", text))
    unknown = [a for a in argv
               if a.startswith("--") and a.split("=", 1)[0] not in known]
    if unknown:
        name = os.path.basename(source_file)
        raise SystemExit(
            f"⛔ {name}: unknown flag(s) {' '.join(unknown)}.\n"
            f"   REFUSING rather than falling through to this script's main path — "
            f"which for a gate prints a green about the wrong subject, and for a "
            f"profiler starts minutes of work nobody asked for.\n"
            f"   Flags this script mentions: {' '.join(sorted(known)) or '(none)'}")


def selftest() -> int:
    utf8_stdio()
    bad = []

    def ok(cond, what):
        print(f"   {'ok  ' if cond else '⛔ FAIL'} {what}")
        if not cond:
            bad.append(what)

    real = os.getloadavg if hasattr(os, "getloadavg") else None

    def boom():
        raise AttributeError("simulated: no getloadavg on this platform")

    if real:
        try:
            os.getloadavg = boom
            a, b, src = loadavg()
            ok(a is None and b is None, "no getloadavg -> (None, None), NEVER 0.0")
            ok("unavailable" in src, "and the reason is NAMED, so a consumer sees the absence")
        finally:
            os.getloadavg = real
        a, b, src = loadavg()
        ok(isinstance(a, float) and src == "os.getloadavg",
           "CONTROL - restored, a real reading returns floats (else the arms above "
           "would pass on a function that always returns None)")
    else:
        ok(loadavg()[0] is None, "on a platform without getloadavg, the value is None")

    ok(utf8_stdio() is None, "utf8_stdio is idempotent and returns nothing")

    class Dumb:
        pass
    _o, _e = sys.stdout, sys.stderr
    try:
        sys.stdout = sys.stderr = Dumb()          # no .reconfigure at all
        utf8_stdio()
        crashed = False
    except Exception:
        crashed = True
    finally:
        sys.stdout, sys.stderr = _o, _e
    ok(not crashed, "a stream WITHOUT .reconfigure must not crash the tool")

    mid = machine_id()
    ok(all(mid.get(k) for k in ("node", "machine", "platform")),
       "machine_id names node, machine and platform, none of them blank")

    # ⛔ strict_flags, driven on a REAL temp file so the source-derived known set is
    #    exercised the way production uses it, not from a string fixture.
    import tempfile
    fd, fx = tempfile.mkstemp(suffix=".py")
    with os.fdopen(fd, "w") as fh:
        fh.write('if "--selftest" in sys.argv: pass\n'
                 'ap.add_argument("--readings")\n'
                 "ap.add_argument('--single-quoted')\n")
    try:
        def refuses(argv):
            try:
                strict_flags(fx, argv)
                return False
            except SystemExit:
                return True
        ok(not refuses(["--selftest"]), "a flag the source MENTIONS is accepted")
        ok(not refuses(["--readings", "x.jsonl"]),
           "a flag with a VALUE is accepted, and its value is not mistaken for a flag")
        ok(not refuses(["--readings=x.jsonl"]), "the `--flag=value` form is accepted")
        ok(not refuses(["--single-quoted"]),
           "a SINGLE-quoted literal counts — missing that idiom would refuse working calls")
        ok(refuses(["--self-test"]),
           "a flag the source does not mention is REFUSED (the misspelling that started this)")
        ok(refuses(["--readings", "x", "--bogus"]),
           "one unknown flag among known ones still refuses")
        ok(not refuses([]), "no flags at all is not a refusal")
        ok(not refuses(["positional", "args"]), "positional arguments are not flags")
        # ⛔ CONTROL: an unreadable source must refuse NOTHING rather than refuse
        #    everything — a guard that cannot read itself must not become a wall.
        ok(not refuses.__call__(["--anything"]) if False else
           (strict_flags("/nonexistent/nope.py", ["--anything"]) is None),
           "CONTROL — an unreadable source refuses nothing, never everything")
    finally:
        os.unlink(fx)

    if bad:
        return 1
    print("portable SELF-TEST: OK (load absence is None and NAMED, never 0.0, with the "
          "restored-call control; utf8_stdio survives a stream with no .reconfigure; "
          "machine_id is populated)")
    return 0


if __name__ == "__main__":
    # ⛔ THE HELPER HOLDS ITSELF TO ITS OWN RULE. A guard whose own tool is exempt
    # is the shape this repository has recorded before: the anti-staleness gate
    # with a stale literal in its own selftest.
    strict_flags(__file__)
    sys.exit(selftest())
