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

    if bad:
        return 1
    print("portable SELF-TEST: OK (load absence is None and NAMED, never 0.0, with the "
          "restored-call control; utf8_stdio survives a stream with no .reconfigure; "
          "machine_id is populated)")
    return 0


if __name__ == "__main__":
    sys.exit(selftest())
