#!/usr/bin/env python3
"""EVERY SCRIPT MUST REFUSE A FLAG IT DOES NOT KNOW, RATHER THAN RUN.

⛔⛔ THE MEASUREMENT THAT ORDERED THIS GATE (2026-09-09). 22 of 42 scripts here
dispatched on `"--selftest" in sys.argv` and otherwise **fell through to their
main path**, and 10 more declared no flags at all and ignored everything. Given a
flag they did not know, they did not fail — they RAN:

    check_encodings.py  --self-test   ->  rc 0, "synonym collapse: CLEAN"
    check_windows.py    --self-test   ->  rc 0, "✅ watch windows agree"
    threads_ab.py       --bogus-flag  ->  started `lake env lean -D profiler=true`
                                          on Tests/Coverage.lean, saturated a core
                                          for 300+ s on a machine six seats were
                                          using, and ORPHANED past its caller.

⇒ 🔑 **A SCRIPT THAT FALLS THROUGH ON AN UNKNOWN FLAG DOES NOT MERELY REPORT
SUCCESS — IT EXECUTES ITS MAIN JOB.** For a gate that is a green about the wrong
subject; for a profiler it is minutes of somebody else's CPU.

📌 **HOW IT WAS FOUND, because the method matters more than the bug.** A sweep of
this repository's gates printed a false RED on one script — the *lucky* direction
— because the sweep had guessed `--self-test` where that script says `--selftest`.
The three that had been quietly answering CLEAN were found only by chasing the
one that complained. **The repo spells the flag two ways (26 vs 4), and two of the
four minority spellings had been added that same morning by copying a neighbour.**

⛔ **AND THE CENSUS ITSELF WAS THE INCIDENT.** The first version probed every
script by INVOKING it with a bogus flag. That is what started the profiler above.
**A census that invokes its subjects is not read-only** — this gate is therefore
STATIC and reads source, never runs it.
[[feedback-a-probe-must-create-its-condition]] [[feedback-make-the-probe-cheap]]

## WHAT COUNTS AS PROTECTED
* `argparse` with `.parse_args()` — refuses unknown flags by construction.
  `.parse_known_args()` does NOT count: it swallows them, which is the defect.
* a call to `portable.strict_flags(__file__)` before any work.

## ⚠️ WHAT THIS GATE DOES NOT CLAIM
It checks that a REFUSAL MECHANISM IS PRESENT, not that it is correctly placed.
A `strict_flags` call sitting after an expensive block would pass here and still
run the block. Placement is a reader's job; this catches the population that has
no mechanism at all, which is the one that was 32 scripts wide this morning.
**Stated so the green is not read wider than it is measured.**
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASELINE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "flag_strictness_baseline.txt")

if __name__ == "__main__":
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from portable import strict_flags, utf8_stdio
    utf8_stdio()
    strict_flags(__file__)


def protected(src: str) -> bool:
    if "strict_flags(__file__)" in src:
        return True
    return bool("argparse" in src
                and re.search(r"\.parse_args\(", src)
                and not re.search(r"\.parse_known_args\(", src))


def scan(scripts_dir=None):
    """[(name, protected)] for every .py under scripts/."""
    import pathlib
    d = pathlib.Path(scripts_dir or os.path.join(ROOT, "scripts"))
    out = []
    for p in sorted(d.glob("*.py")):
        out.append((p.name, protected(p.read_text(encoding="utf-8"))))
    return out


def load_baseline():
    try:
        with open(BASELINE, encoding="utf-8") as fh:
            return {l.strip() for l in fh if l.strip() and not l.startswith("#")}
    except FileNotFoundError:
        return set()


def selftest() -> int:
    bad = []

    def ok(c, w):
        print(f"   {'ok  ' if c else '⛔ FAIL'} {w}")
        if not c:
            bad.append(w)

    ok(protected('x = 1\nstrict_flags(__file__)\n'), "a strict_flags call counts as protected")
    ok(protected('import argparse\nap.parse_args()\n'), "argparse .parse_args() counts")
    ok(not protected('import argparse\nap.parse_known_args()\n'),
       "⛔ .parse_known_args() does NOT count — it SWALLOWS unknown flags, which is the defect")
    ok(not protected('if "--selftest" in sys.argv:\n    pass\n'),
       "the sys.argv idiom alone is NOT protection — this is the 22-script population")
    ok(not protected('print("hello")\n'), "a script with no flag handling at all is unprotected")
    # ⛔ A MIXED FILE: argparse present but parse_known_args used somewhere is the
    #    trap — the presence of the word `argparse` must not be the test.
    ok(not protected('import argparse\nap.parse_args()\nb.parse_known_args()\n'),
       "argparse + parse_known_args ANYWHERE is unprotected — presence of the "
       "module is not the test")
    ok(scan() and all(isinstance(t, tuple) for t in scan()),
       "CONTROL — scan() reads the real scripts directory and returns rows")

    for b in bad:
        pass
    if bad:
        return 1
    print("check_flag_strictness SELF-TEST: OK (strict_flags and argparse both count; "
          "parse_known_args refused as protection; the bare sys.argv idiom refused; a "
          "mixed file refused; scan drives the real directory)")
    return 0


def main() -> int:
    if "--selftest" in sys.argv or "--self-test" in sys.argv:
        return selftest()
    rows = scan()
    unprotected = [n for n, p in rows if not p]
    base = load_baseline()
    if "--write-baseline" in sys.argv:
        with open(BASELINE, "w", encoding="utf-8", newline="") as fh:
            fh.write("# flag_strictness_baseline.txt — scripts ACCEPTED as having no\n"
                     "# unknown-flag refusal. This list may only SHRINK.\n")
            for n in sorted(unprotected):
                fh.write(n + "\n")
        print(f"wrote baseline: {len(unprotected)} accepted")
        return 0
    new = sorted(set(unprotected) - base)
    gone = sorted(base - set(unprotected))
    if new:
        print(f"⛔ flag-strictness gate: {len(new)} script(s) can be handed an unknown "
              f"flag and will RUN THEIR MAIN PATH instead of refusing:\n")
        for n in new:
            print(f"    {n}")
        print("\n  Add `strict_flags(__file__)` (see scripts/portable.py) before any work, "
              "or use argparse with .parse_args().")
        return 1
    print(f"flag-strictness gate: CLEAN — {len(rows) - len(unprotected)} of {len(rows)} "
          f"scripts refuse an unknown flag"
          + (f"; {len(unprotected)} accepted by the baseline" if unprotected else
             "; the baseline is EMPTY, which is the strongest form")
          + (f"; {len(gone)} baseline entr{'y' if len(gone)==1 else 'ies'} now protected "
             f"— shrink it with --write-baseline" if gone else "") + ".")
    return 0


if __name__ == "__main__":
    sys.exit(main())
