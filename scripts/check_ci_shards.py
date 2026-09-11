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

It checks EIGHT things, and each one is a way the seam has to fail:
  1. `matrix.shard` is exactly `1..n` — no gaps, no duplicates, starting at 1;
  2. every `selftest-shard` command passes that same `n` as its divisor;
  3. the `selftest-shards` partition gate in the other job asserts the same `n`;
  4. the shard command's `k` is the matrix variable, not a literal — a literal
     would run one shard six times and still be green six times.

⛔⛔ 5-8 WERE ADDED 2026-09-11 WITH THE `CI-3` SKIP GATE, WHICH MOVES THE COVERAGE
QUESTION FURTHER INTO THE ORCHESTRATOR — the shards may now be SKIPPED ENTIRELY
on a digest match, and the condition deciding that lives in YAML where no Lean
arm and no Python selftest can see it.
  5. the `selftest` job `needs: selftest-gate` — without it the expression cannot
     resolve and the gate is decorative;
  6. ⛔ its `if:` is the NEGATION, `skip != 'true'`.  **An inverted condition
     (`== 'true'`) is the catastrophic direction: the shards would run ONLY when
     they were supposed to skip, i.e. NEVER on a changed artifact, and CI would
     report green having tested nothing.**  That is precisely the state the
     helm's condition (1) exists to prevent, reached through a one-character typo;
  7. the `selftest-gate` job checks out with `fetch-depth: 0` — the decision reads
     the tree at the PRIOR GREEN SHA, and a depth-1 checkout does not have it, so
     the gate would silently degrade to "always MEASURE" (safe, but dead, and
     dead-while-reading-as-coverage is this repo's recurring defect);
  8. the gate actually invokes `selftest_skip.py --decide`, and proves it with
     `--selftest` first.
⇒ 🔑 ***5-8 GUARD A GATE WITH A PERMITTING PATH. 1-4 GUARD ONE WITH ONLY A
MEASURING PATH.*** The failure modes are not the same size and the checks are not
written as if they were.

LANE.  Personal lane; nothing here touches an employer-lane tree.
"""
import os, re, sys

# ⛔ REFUSE AN UNKNOWN FLAG BEFORE ANY WORK HAPPENS — see portable.strict_flags.
# A script that declares no flags is the SHARPEST case: it ignores anything and
# runs its main path, so a mistyped flag produced a confident green about a
# subject nobody asked about (measured: check_encodings.py --self-test -> rc 0,
# "synonym collapse: CLEAN", having never run its self-test).
if __name__ == "__main__":
    import os as _os, sys as _sys
    _sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
    from portable import strict_flags as _strict_flags
    _strict_flags(__file__)

SKIP_IF = "needs.selftest-gate.outputs.skip != 'true'"


def check_skip_seam(text):
    """5-8: the CI-3 skip seam. Returns a list of findings (empty = clean).

    ⛔ PyYAML IS THIS GATE'S ONLY NON-STDLIB DEPENDENCY AND CHECKS 5-8 INTRODUCED
    IT — checks 1-4 are pure `re`.  If it is unavailable this REFUSES rather than
    skipping: a structural gate that cannot parse its subject must say so and go
    red.  Silently passing 5-8 because the parser is missing would be a gate
    disabling itself and still reading as coverage, which is the exact defect
    `CLAIM-1`/`CLAIM-2` exist for.  The workflow installs it explicitly rather
    than betting on the runner image.
    """
    try:
        import yaml
    except ImportError:
        return ["PyYAML is unavailable, so checks 5-8 (the CI-3 skip seam) COULD NOT RUN. "
                "This is a REFUSAL, not a pass: the skip seam is unverified."]
    out = []
    try:
        d = yaml.safe_load(text)
    except Exception as e:
        return [f"ci.yml does not parse as YAML ({e})"]
    jobs = (d or {}).get("jobs") or {}

    gate = jobs.get("selftest-gate")
    st = jobs.get("selftest")
    if st is None:
        return ["there is no `selftest` job at all"]
    if gate is None:
        # No gate job: the shards must then be UNCONDITIONAL. That is the old,
        # safe world, and it is legal -- but `selftest` must not carry a
        # dangling `if:` referring to a job that does not exist.
        if st.get("if"):
            out.append("`selftest` has an `if:` but there is no `selftest-gate` job to "
                       "supply it; the condition cannot resolve")
        return out

    needs = gate and st.get("needs")
    needs = [needs] if isinstance(needs, str) else (needs or [])
    if "selftest-gate" not in needs:
        out.append("`selftest` does not `needs: selftest-gate`, so "
                   "`needs.selftest-gate.outputs.skip` cannot resolve and the gate is decorative")

    cond = (st.get("if") or "").strip()
    if not cond:
        out.append("`selftest` has no `if:`, so the gate can never skip anything")
    elif cond != SKIP_IF:
        # ⛔ THE INVERSION IS THE ONE THAT COSTS EVERYTHING, so it is named.
        if "==" in cond and "skip" in cond:
            out.append(f"⛔⛔ `selftest`'s `if:` is INVERTED: {cond!r}. The shards would run "
                       f"ONLY when the gate said SKIP -- i.e. never on a changed artifact -- "
                       f"and CI would report green having tested nothing. Expected: {SKIP_IF!r}")
        else:
            out.append(f"`selftest`'s `if:` is {cond!r}, not the expected {SKIP_IF!r}")

    steps = gate.get("steps") or []
    co = [x for x in steps if "checkout" in str(x.get("uses", ""))]
    if not co:
        out.append("`selftest-gate` does not check out the repository")
    elif (co[0].get("with") or {}).get("fetch-depth") != 0:
        out.append("`selftest-gate` does not check out with `fetch-depth: 0`; the decision "
                   "reads the tree at the PRIOR GREEN SHA, which a depth-1 clone lacks, so "
                   "the gate would silently degrade to always-MEASURE")

    runs = " ".join(str(x.get("run", "")) for x in steps)
    if "selftest_skip.py --decide" not in runs:
        out.append("`selftest-gate` never runs `selftest_skip.py --decide`; nothing computes "
                   "the decision its outputs claim to carry")
    if "selftest_skip.py --selftest" not in runs:
        out.append("`selftest-gate` does not run `selftest_skip.py --selftest` before trusting "
                   "the decision; a gate proven only on the developer box is proven where it "
                   "cannot fail")
    return out


def _skip_seam_selftest():
    """Drive checks 5-8 both ways.  A gate watched only passing has been probed
    for NOISE and not for SILENCE, and an arm that cannot fire is
    indistinguishable from one that found nothing."""
    import copy, yaml
    base_text = open(os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        ".github", "workflows", "ci.yml")).read()
    base = yaml.safe_load(base_text)
    red = 0
    arms = []

    def arm(name, text, expect_finding, needle=None):
        nonlocal red
        out = check_skip_seam(text if isinstance(text, str) else yaml.safe_dump(text))
        got = len(out) > 0
        ok = (got == expect_finding) and (needle is None or any(needle in o for o in out))
        arms.append(name)
        print(("  v " if ok else "  x ") + name + ("" if ok else f"   -> {out}"))
        if not ok:
            red += 1

    print("check_ci_shards --selftest (checks 5-8, the CI-3 skip seam)")
    # CONTROL FIRST.  If the live file does not pass, every plant below is
    # uninterpretable.
    arm("control: the REAL ci.yml passes the skip-seam checks", base_text, False)

    d = copy.deepcopy(base); d["jobs"]["selftest"]["if"] = \
        "needs.selftest-gate.outputs.skip == 'true'"
    arm("⛔ PLANT: an INVERTED if: is caught and NAMED as inverted", d, True, "INVERTED")

    d = copy.deepcopy(base); d["jobs"]["selftest"].pop("if", None)
    arm("PLANT: a missing if: is caught (the gate could never skip)", d, True, "no `if:`")

    d = copy.deepcopy(base); d["jobs"]["selftest"].pop("needs", None)
    arm("PLANT: a missing needs: is caught (the expression cannot resolve)", d, True, "needs")

    d = copy.deepcopy(base)
    for stp in d["jobs"]["selftest-gate"]["steps"]:
        if "checkout" in str(stp.get("uses", "")):
            stp["with"] = {"fetch-depth": 1}
    arm("PLANT: fetch-depth 1 on the gate is caught (always-MEASURE, silently)", d, True,
        "fetch-depth: 0")

    d = copy.deepcopy(base)
    d["jobs"]["selftest-gate"]["steps"] = [
        x for x in d["jobs"]["selftest-gate"]["steps"]
        if "--decide" not in str(x.get("run", ""))]
    arm("PLANT: a gate that never runs --decide is caught", d, True, "--decide")

    d = copy.deepcopy(base)
    d["jobs"]["selftest-gate"]["steps"] = [
        x for x in d["jobs"]["selftest-gate"]["steps"]
        if "--selftest" not in str(x.get("run", ""))]
    arm("PLANT: a gate that does not prove itself first is caught", d, True, "--selftest")

    # ⭐ AND THE OTHER DIRECTION: removing the gate ENTIRELY is legal (the old,
    # unconditional world) -- but only if the dangling `if:` goes with it.
    d = copy.deepcopy(base); d["jobs"].pop("selftest-gate")
    arm("⭐ PLANT: no gate job + a dangling if: is caught", d, True, "cannot resolve")
    d = copy.deepcopy(base); d["jobs"].pop("selftest-gate")
    d["jobs"]["selftest"].pop("if", None); d["jobs"]["selftest"].pop("needs", None)
    arm("⭐ CONTROL: no gate job AND no if: is LEGAL — the unconditional world passes",
        d, False)

    # ⛔ AND THE REFUSAL PATH ITSELF, DRIVEN.  A refusal that has never fired is
    # a branch nobody has executed, and this one decides whether a missing parser
    # reads as "clean" or as "unverified".
    import sys as _sys
    _saved = _sys.modules.get("yaml", "__absent__")
    _sys.modules["yaml"] = None          # makes `import yaml` raise ImportError
    try:
        out = check_skip_seam(base_text)
        ok = len(out) == 1 and "COULD NOT RUN" in out[0] and "REFUSAL" in out[0]
    finally:
        if _saved == "__absent__":
            _sys.modules.pop("yaml", None)
        else:
            _sys.modules["yaml"] = _saved
    arms.append("refusal path")
    print(("  v " if ok else "  x ") + "⛔ PLANT: PyYAML unavailable ⇒ REFUSES (not a silent pass)"
          + ("" if ok else f"   -> {out}"))
    if not ok:
        red += 1

    print(f"\n  arms={len(arms)} red={red}")
    return 1 if red else 0


if "--selftest" in sys.argv:
    sys.exit(_skip_seam_selftest())


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

# ── 5-8: THE SKIP SEAM (CI-3).  Parsed as YAML, not regexed: these are
# STRUCTURAL facts about jobs, and a regex over YAML would be a second parser
# disagreeing with the one GitHub actually uses.
bad += check_skip_seam(text)

if bad:
    print(f"⛔ CI shard gate: FAIL ({CI})")
    for b in bad:
        print("   " + b)
    sys.exit(1)

print(f"CI shard gate: CLEAN — matrix.shard is 1..{n}, every `selftest-shard` "
      f"passes divisor {n} with the matrix variable as k, the partition gate "
      f"asserts the same {n}, and the skip seam is wired in the permitting "
      f"direction with fetch-depth 0")
