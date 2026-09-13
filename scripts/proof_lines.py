#!/usr/bin/env python3
"""Count the lines of one theorem, by a stated rule, so a published proof size can be re-derived.

WHY.  `docs/P2-PROOF-INTERFACE.md` and the paper quote proof sizes (14, 34, 50, 57, 76 lines) that
were "counted, not estimated" and never said HOW.  A count with an unstated rule fails reproduction
exactly like a wrong one (D202).  Measured 2026-09-12 (D217): one rule reproduces all six published
figures exactly, and this script is that rule, so the rule is the derivation rather than a comment.

THE RULE.  From the line `theorem NAME` up to, not including, the next line that starts a top-level
item (`theorem`, `private theorem`, `def`, `abbrev`, `example`, `/--`, `/-!`, `@[`, `namespace`,
`section`, `end`, `open`), count the lines that are neither blank nor a `--` comment.  The statement
lines are included; the docstring above the theorem is not.

It REFUSES (exit 2) when the theorem is absent or appears twice, printing what it looked for, because
an empty count would read as a value.

Usage:  proof_lines.py NAME [--sha SHA] [--file Tests/Program.lean]
"""
import argparse, re, subprocess, sys

TOP = re.compile(r"^(theorem |private theorem |def |abbrev |example|/--|/-!|@\[|namespace |section|end |open )")


def count(text, name):
    lines = text.split("\n")
    starts = [k for k, l in enumerate(lines) if re.match(r"^(private )?theorem " + re.escape(name) + r"(\s|$)", l)]
    if len(starts) != 1:
        return None, len(starts)
    i = starts[0]
    j = i + 1
    while j < len(lines) and not TOP.match(lines[j]):
        j += 1
    return sum(1 for x in lines[i:j] if x.strip() and not x.strip().startswith("--")), 1


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("name")
    ap.add_argument("--sha", default=None)
    ap.add_argument("--file", default="Tests/Program.lean")
    a = ap.parse_args(argv)
    if a.sha:
        r = subprocess.run(["git", "show", f"{a.sha}:{a.file}"], capture_output=True, text=True)
        if r.returncode != 0:
            print(f"proof_lines: cannot read {a.file} at {a.sha}: {r.stderr.strip()}", file=sys.stderr)
            return 2
        text = r.stdout
    else:
        text = open(a.file, encoding="utf-8").read()
    n, found = count(text, a.name)
    if n is None:
        print(f"proof_lines: `theorem {a.name}` found {found} time(s) in {a.file}"
              f"{' at ' + a.sha if a.sha else ''}; need exactly 1 -- refusing", file=sys.stderr)
        return 2
    print(n)
    return 0


if __name__ == "__main__":
    sys.exit(main())
