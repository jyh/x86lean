#!/usr/bin/env python3
"""⭐⭐ THE CI MATRIX AND THE SHARD DIVISOR MUST AGREE, AND NOTHING ELSE CHECKS IT.

`x86lean-diff selftest-shard k n` computes its own slice from
`selftestArms.length`, so **adding an arm can never leave that arm uncovered** —
the partition is arithmetic, and `selftest-shards n` proves shards 1..n name
every arm exactly once.

⛔ WHAT THAT ARGUMENT DOES NOT COVER IS THE MATRIX.  The divisor `n` is written in
`.github/workflows/ci.yml` twice — once as the length of `matrix.shard` and once
in the command — and if those two ever disagree the arithmetic is still perfect
while whole RESIDUE CLASSES OF ARMS NEVER RUN.  A matrix of `[1,2,3]` against a
command saying `6` runs half the arms and reports green, and every per-shard log
says PASS, because each shard really did pass.

⇒ 🔑 **SHARDING A COVERAGE GATE MOVES THE COVERAGE QUESTION FROM THE CODE INTO
THE ORCHESTRATOR**, where none of this repository's other gates can see it. This
file is the gate for that one seam.

It checks four things, and each one is a way the seam has to fail:
  1. `matrix.shard` is exactly `1..n` — no gaps, no duplicates, starting at 1;
  2. every `selftest-shard` command passes that same `n` as its divisor;
  3. the `selftest-shards` partition gate in the other job asserts the same `n`;
  4. the shard command's `k` is the matrix variable, not a literal — a literal
     would run one shard six times and still be green six times.

LANE.  Personal lane; nothing here touches an employer-lane tree.
"""
import os, re, sys

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(root)
CI = ".github/workflows/ci.yml"
text = open(CI).read()

bad = []

m = re.search(r'^\s*shard:\s*\[([0-9,\s]+)\]\s*$', text, re.M)
if not m:
    print(f"⛔ no `shard: [...]` matrix found in {CI}. A gate that cannot find its "
          f"subject must refuse, not pass.")
    sys.exit(2)
matrix = [int(x) for x in m.group(1).replace(" ", "").split(",") if x != ""]

# ⚠️ `k` may be a matrix expression — `${{ matrix.shard }}` — which contains
# spaces, so `\S+` cannot match it; that was this gate's own first defect.
runs = re.findall(r'selftest-shard\s+(\$\{\{[^}]*\}\}|\S+)\s+(\d+)', text)
if not runs:
    print(f"⛔ no `selftest-shard <k> <n>` command found in {CI}.")
    sys.exit(2)

gates = [int(x) for x in re.findall(r'selftest-shards\s+(\d+)', text)]
if not gates:
    print(f"⛔ no `selftest-shards <n>` partition gate found in {CI}. The shards "
          f"would run with nothing asserting they cover every arm.")
    sys.exit(2)

divisors = {int(n) for _k, n in runs}
if len(divisors) != 1:
    bad.append(f"the `selftest-shard` commands disagree about the divisor: {sorted(divisors)}")
n = sorted(divisors)[0]

if matrix != list(range(1, n + 1)):
    bad.append(f"matrix.shard is {matrix}, which is not 1..{n} — "
               f"{sorted(set(range(1, n + 1)) - set(matrix))} would never run")

for k, _n in runs:
    if not k.startswith("${{"):
        bad.append(f"the shard command passes a LITERAL k={k!r} instead of the matrix "
                   f"variable; every job would run the same shard and all would pass")

for g in gates:
    if g != n:
        bad.append(f"the partition gate asserts `selftest-shards {g}` but the shards "
                   f"run with divisor {n}; the gate is describing a different split")

if bad:
    print(f"⛔ CI shard gate: FAIL ({CI})")
    for b in bad:
        print("   " + b)
    sys.exit(1)

print(f"CI shard gate: CLEAN — matrix.shard is 1..{n}, every `selftest-shard` "
      f"passes divisor {n} with the matrix variable as k, and the partition gate "
      f"asserts the same {n}")
