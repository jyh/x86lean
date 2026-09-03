#!/bin/bash
# ⭐⭐ P1 BATCH 21 — THE RED PROBE FOR THE TWO SHARED REDUCTIONS.
#
# `memDestSweep` and `vectorCoverage` each check THREE claims in one kernel
# reduction so the sweeps behind them are paid once (batch 21; 37 900 -> 21 900
# ms on Tests.Coverage).  Merging claims is exactly the move that can go silent:
# a conjunction is green if the kernel never reaches a conjunct, and nothing in
# a green build says which of the six was actually exercised.
#
# So each conjunct is planted with a defect ALONE and REQUIRED TO REPORT FALSE.
# ⚠️ The arms prove `... = false` rather than merely failing to compile: a
# `decide` that errors could be erroring for any reason (recursion depth, a
# typo), while a proof of `false` is the kernel positively agreeing that the
# planted defect is visible at that conjunct.  A `sorry`-free `= false` is the
# only form that distinguishes "the gate saw it" from "the file did not build".
#
# ⚠️ The plants live HERE and never in Tests/Coverage.lean: a probe that edits
# the artifact it checks can leave it edited.
set -u
cd "$(dirname "$0")/.."
TMP="${TMPDIR:-/tmp}/x86lean-redprobe-$$"
mkdir -p "$TMP"
# ⛔ THE PROBE FILE LIVES OUTSIDE THE REPOSITORY, and that is a repair rather
# than a preference.  It used to be written to `Tests/RedProbe21.lean` and
# deleted by the EXIT trap — which does not run on SIGKILL, so an interrupted
# probe left a stray `.lean` file inside a public-destined tree, where the next
# `lake build` would compile it and the next `git status` would carry it.
# ⇒ 🔑 A CLEANUP THAT ONLY RUNS ON A CLEAN EXIT IS NOT CLEANUP.  `lake env lean`
# resolves `import Tests.Coverage` from anywhere, so the file never needs to be
# in the tree at all — and a file that is never created cannot be left behind.
PROBE="$TMP/RedProbe21.lean"
trap 'rm -rf "$TMP"' EXIT

cat > "$PROBE" <<'EOF'
import Tests.Coverage
namespace X86.Tests
open X86
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

-- ── memDestSweep, conjunct by conjunct ────────────────────────────────────
-- R1: the disagreement list, with ONE entry removed from what it is compared to.
theorem r1 :
    (tableP0.filterMap (fun r =>
        match claimsMemDestLoose r, claimsMemDest r with
        | true,  false => some (r.mnemonic, true)
        | false, true  => some (r.mnemonic, false)
        | _,     _     => none)
      == [("sarx", true), ("shlx", true), ("shrx", true),
          ("cmps", false), ("scas", false), ("repe", false)]) = false := by decide

-- R2: a claiming row whose backing vector set has lost a mnemonic.
theorem r2 :
    tableP0.all (fun r =>
      !claimsMemDest r || (memDestMnemonics.drop 1).contains r.mnemonic) = false := by decide

-- R3: a memory-writing mnemonic that no row claims.
theorem r3 :
    ((("zzz" :: memDestMnemonics).filter (fun m =>
      !(tableP0.any (fun r => r.mnemonic == m && claimsMemDest r)))) == []) = false := by decide

-- ── vectorCoverage, conjunct by conjunct ──────────────────────────────────
-- R4: a table row with no vector.
theorem r4 :
    (tableP0.map Row.mnemonic).all
      (fun m => (vectorMnemonics.drop 1).contains m) = false := by decide

-- R5: a vector mnemonic with no table row.
theorem r5 :
    ("zzz" :: vectorMnemonics).all
      (fun m => (tableP0.map Row.mnemonic).contains m) = false := by decide

-- R6: the count, off by one.
theorem r6 : ((vectorMnemonics.drop 1).length == rosterSize) = false := by decide

-- ⭐ THE POSITIVE CONTROL, in the SAME run: an arm at the same shape with NO
-- planted defect must be TRUE.  Without it, six `false`s are also what a probe
-- that has stopped seeing its subject would print.
theorem control : ((vectorMnemonics.length == rosterSize)
  && tableP0.all (fun r => !claimsMemDest r || hasMemDestVector r.mnemonic)) = true := by decide
EOF

# ⛔⛔ THE PROBE RESTATES THE CONJUNCTS, WHICH IS A DUPLICATE BORN IN AGREEMENT.
# If `memDestSweep` or `vectorCoverage` is edited, these arms go on passing while
# testing a shape that is no longer shipped — green, and about nothing. So each
# planted arm's SUBJECT is required to OCCUR in Tests/Coverage.lean, and a
# missing anchor REFUSES (rc 2) instead of passing.
#
# ⚠️ Occurrence, not equality: the shipped text carries line breaks and comments
# this file cannot reproduce, and a gate that cried wolf on ordinary reformatting
# would be switched off. What it catches is the case that matters — a conjunct
# deleted, renamed, or rewritten, leaving an arm that plants a defect in
# something the repository no longer checks.
ANCHORS=(
  'tableP0.all (fun r => !claimsMemDest r || hasMemDestVector r.mnemonic)'
  'memDestMnemonics.filter (fun m =>'
  '!(tableP0.any (fun r => r.mnemonic == m && claimsMemDest r))'
  'match claimsMemDestLoose r, claimsMemDest r with'
  '("repe", false), ("repne", false)'
  '(tableP0.map Row.mnemonic).all (fun m => vectorMnemonics.contains m)'
  'vectorMnemonics.all (fun m => (tableP0.map Row.mnemonic).contains m)'
  'vectorMnemonics.length == rosterSize'
)
missing=0
for a in "${ANCHORS[@]}"; do
  if ! grep -qF -- "$a" Tests/Coverage.lean; then
    echo "⛔ RED PROBE REFUSES — this arm's subject is not in Tests/Coverage.lean:"
    echo "     $a"
    missing=1
  fi
done
if [ $missing -ne 0 ]; then
  echo "   The shipped declaration has changed and these arms would plant defects"
  echo "   in a shape the repository no longer checks. Update both together."
  exit 2
fi

# ⭐ AND THE ANCHOR CHECK IS ITSELF PROVEN TO FIRE, in the same run, because an
# anchor list that silently matched nothing would be the defect it exists to
# prevent.
if grep -qF -- 'vectorMnemonics.length == rosterSizeXX' Tests/Coverage.lean; then
  echo "⛔ the anchor self-test found a string that cannot exist."; exit 2; fi
if ! grep -qF -- "${ANCHORS[0]}" Tests/Coverage.lean; then
  echo "⛔ the anchor self-test cannot find a string it just matched."; exit 2; fi

OUT="$TMP/out.txt"
lake env lean "$PROBE" > "$OUT" 2>&1
rc=$?
if [ $rc -ne 0 ]; then
  echo "⛔ RED PROBE FAILED — an arm did not typecheck, so at least one conjunct"
  echo "   did NOT see its planted defect (or the control did not hold):"
  sed -n '1,60p' "$OUT"
  exit 1
fi
if grep -q "declaration uses 'sorry'" "$OUT"; then
  echo "⛔ RED PROBE FAILED — an arm was closed by sorry."
  exit 1
fi
echo "✔ red probe: 6 arms + 1 positive control, all PASS."
echo "  ${#ANCHORS[@]} anchors: every planted subject OCCURS in the shipped Tests/Coverage.lean"
echo "  memDestSweep  conjuncts 1-3 each report a planted defect ALONE (r1 r2 r3)"
echo "  vectorCoverage conjuncts 1-3 each report a planted defect ALONE (r4 r5 r6)"
echo "  control: the unplanted shape is TRUE in the same run"
exit 0
