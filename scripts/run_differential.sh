#!/usr/bin/env bash
# THE P0 EXIT CRITERION (plan v1 §5): one differential run of the twenty scalar
# forms against ACL2 x86isa, with every disagreement filed with its class.
#
# Lean side and oracle side both emit the same record format; `x86lean-diff
# compare` classifies. A disagreement is EXPLAINED only if it lies inside the
# flags this model marks undefined for that (instruction, state) — a set DERIVED
# from the semantics, never declared here (docs/DECISIONS.md D6).
set -euo pipefail
cd "$(dirname "$0")/.."
ACL2=${ACL2:-$PWD/vendor/acl2/saved_acl2}
mkdir -p run

[ -x "$ACL2" ] || { echo "⛔ no ACL2 image at $ACL2 — run scripts/setup_oracle.sh" >&2; exit 2; }

# ⭐ D218: THE REFERENCE MODEL'S REVISION, CHECKED FIRST AND PRINTED, so the run's output carries the
# commit every agreement below is agreement WITH. A record written from this run quotes the line.
echo "── checking the reference model's pinned revision ──"
bash scripts/check_oracle_revision.sh || exit 2

# ⭐ P1 BATCH 21 (D65).  THE UNAVAILABLE LIST IS CHECKED FIRST, because it is
# the only other gate in this repository that needs the oracle and because a
# differential run over a stale residue answers a question about the wrong
# roster.  Six seconds, gated both ways, red-first.
echo "── checking the oracle-availability declarations ──"
python3 scripts/oracle_availability.py || {
  echo "⛔ the unavailable list disagrees with the oracle; the residue is stale." >&2
  exit 2; }

# ⭐⭐ P2 VECTOR WAVE, BATCH 1 (D86).  DOES THE PATH BELOW ACTUALLY ENABLE SSE?
# The gate above measures the ORACLE's capability through a call site it builds
# itself; this one measures the DRIVER's, through `x86l-run-case` — the only call
# site anything below this line uses. They are different questions, and the
# second went unasked from P0 until the batch that set `*x86l-ctrs*`. Nineteen
# seconds, both arms, before a twenty-five-minute run that would otherwise
# compare a model that computes against an oracle that declines.
echo "── checking that the DIFFERENTIAL PATH enables SSE (CR4.OSFXSR) ──"
python3 scripts/check_driver_cr4.py || {
  echo "⛔ the driver's CR4 configuration is not what the gate declares." >&2
  exit 2; }

echo "── building the Lean side ──"
lake build x86lean-diff >/dev/null
lake env .lake/build/bin/x86lean-diff emit       run/lean.txt
lake env .lake/build/bin/x86lean-diff emit-acl2  run/cases.lsp

CASES=${1:-run/cases.lsp}
echo "── running the oracle (ACL2 x86isa) over $CASES ──"
cat > run/drive.lsp <<LSP
(include-book "projects/x86isa/tools/execution/init-state" :dir :system :ttags :all)
(include-book "projects/x86isa/machine/x86" :dir :system :ttags :all)
; ACL2's printer FILLS at the right margin, which would break every record
; across several lines and make the comparator see truncated states.
(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 99000 state)
(ld "scripts/x86isa_driver.lisp")
(ld "$CASES")
; The stobj is \`x86isa::x86\`; at the ACL2 top level the bare symbol \`x86\`
; is \`acl2::x86\` and the call is rejected. Hence the package switch.
(in-package "X86ISA")
(x86l-run-all *x86lean-cases* x86 state)
LSP
"$ACL2" < run/drive.lsp > run/acl2.out 2>&1 || true

# Keep only the record lines; ACL2's banner and proof output are not records.
grep -E '^(CASE|POST) ' run/acl2.out > run/oracle.txt || true
n=$(grep -c '^CASE ' run/oracle.txt || true)
echo "oracle produced $n case records"
if [ "$n" -eq 0 ]; then
  echo "⛔ the oracle produced NO records. That is a HARNESS failure, not agreement."
  echo "   Last 30 lines of run/acl2.out:"; tail -30 run/acl2.out
  exit 2
fi

echo "── comparing ──"
lake env .lake/build/bin/x86lean-diff compare run/lean.txt run/oracle.txt

# ⭐⭐⭐ AND THE KERNEL-COST GATE, HERE BECAUSE THIS IS WHERE IT IS CALIBRATED.
#
# `scripts/kernel_ceilings.txt` registers ABSOLUTE milliseconds at `measured x
# 1.6`, taken on a quiet DEVELOPMENT machine with the load conditions written
# beside each line.  A GitHub runner is a different machine and measures about
# twice as slow, by a factor that VARIES per declaration (1.7x-3.1x), so the gate
# cannot be enforced there and `ci.yml` says so in its header.
#
# ⛔ IT USED TO DEPEND ON A HEAD REMEMBERING TO RUN IT, AND THAT FAILED.  The
# session that added the P2 vector wave ran this differential six times and
# `kernel_cost.py` NOT ONCE — until CI complained about a regression that had
# been sitting in the tree for three batches (prose written into a field the
# kernel walks character by character, D94).  A gate whose schedule is "somebody
# will think of it" is D65's ungated claim wearing a habit.
#
# ⇒ It runs on the same trigger as the differential: the BATCH.  Ten minutes
# against the thirty this script already costs, and it runs LAST, when the oracle
# is done and the machine is quiet again — which is the condition the ceilings
# were registered under.
echo "── kernel-cost ceilings (calibrated for THIS machine; see ci.yml on why not in CI) ──"
python3 scripts/kernel_cost.py
