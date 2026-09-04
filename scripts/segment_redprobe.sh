#!/bin/bash
# ⭐⭐ P2 ITEM 1 (BATCH 22) — THE RED PROBE FOR THE SEGMENT-BASE CLAIMS.
#
# Four theorems landed in Tests/Coverage.lean with this batch, and every one of
# them is the kind that can be green because it is EMPTY rather than because it
# is true:
#
#   * `segmented_vectors_are_all_extracted` compares an AST walk against the
#     encoded bytes — a `match` with a `_ => []` default whose gaps all fall the
#     silent way;
#   * `segmentedAddressesAreCanonical` bounds a NAMED departure from x86isa, and
#     a sweep over an empty vector set proves nothing about it;
#   * `segmentedAddressesLandInAWatchedWindow` is the claim D72 says the whole
#     observability of this batch rests on — an address outside the windows is
#     read as zeros by BOTH models and reports agreement about nothing.
#
# So each is planted with a defect ALONE and required to report `false`, in one
# run, with an unplanted positive control beside them.  ⚠️ `= false` rather than
# a failed build: a `decide` that errors could be erroring for any reason, while
# a proof of `false` is the kernel positively agreeing the defect is visible.
#
# ⚠️ The plants live HERE and never in the tree (P1 seal, a467a22: a cleanup that
# only runs on a clean exit is not cleanup).  `lake env lean` resolves
# `import Tests.Coverage` from anywhere.
set -u
cd "$(dirname "$0")/.."
TMP="${TMPDIR:-/tmp}/x86lean-segprobe-$$"
mkdir -p "$TMP"
PROBE="$TMP/SegRedProbe.lean"
trap 'rm -rf "$TMP"' EXIT

cat > "$PROBE" <<'EOF'
import Tests.Coverage
namespace X86.Tests
open X86
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

/-- The extraction with its `.mov` case removed — the commonest segmented form
in the corpus and in this table.  ⚠️ This plants a WRONG BODY, not a missing
arm: a missing arm is a compile error in `X86.opOperands`, which is the point of
that function having no wildcard.  What is left to probe is the case the
compiler cannot see. -/
def opOperandsNoMov : Op → List Operand
  | .mov _ _ _ => []
  | o => opOperands o

def segEasNoMov (i : Instr) : List Ea :=
  let fromOps := (opOperandsNoMov i.op).filterMap
    (fun o => match o with | .mem e => some e | _ => none)
  let fromLea := match i.op with | .lea _ _ e => [e] | _ => []
  (fromOps ++ fromLea).filter (fun e => e.seg.isSome)

/-- The extraction that forgets to look at the segment field at all. -/
def segEasNoFilter (i : Instr) : List Ea :=
  ((opOperands i.op).filterMap (fun o => match o with | .mem e => some e | _ => none))
    ++ (match i.op with | .lea _ _ e => [e] | _ => [])

-- S1: an extraction that has lost a constructor must move the COUNT.
theorem s1 :
    ((vectors.filter (fun v => !(segEasNoMov v.instr).isEmpty)).length == 8) = false := by decide

-- S2: an extraction that has lost the `seg.isSome` filter must move it too —
--     the opposite direction, and the one that would make the two sweeps below
--     sweep the WHOLE vector table while still reporting green.
theorem s2 :
    ((vectors.filter (fun v => !(segEasNoFilter v.instr).isEmpty)).length == 8) = false := by decide

-- S3: a segment base that makes the linear address NON-CANONICAL.  Bit 47 set
--     with bits 63:48 clear is the smallest non-canonical address there is.
theorem s3 :
    (segVectors.all (fun v =>
      ((preStates 1 8).map (fun s => { s with fsBase := (0x800000000000 - 0x28 : BitVec 64) })).all
        (fun s => (segEas v.instr).all (fun e =>
          canonical (e.addr s (s.rip + BitVec.ofNat 64 v.instr.len)))))) = false := by decide

-- S4: a segment base that is canonical and OUTSIDE the watched windows — the
--     exact failure D72 says the displacements are chosen to avoid.  Note S3
--     still passes at this base, which is why the two claims are two theorems.
theorem s4 :
    (segVectors.all (fun v =>
      match v.instr.op with
      | .lea _ _ _ => true
      | _ =>
        ((preStates 1 8).map (fun s => { s with fsBase := (0x3fd8 : BitVec 64) })).all
          (fun s => (segEas v.instr).all (fun e =>
            let a := e.addr s (s.rip + BitVec.ofNat 64 v.instr.len)
            windows.any (fun w =>
              w.base ≤ a && a + 8 ≤ w.base + BitVec.ofNat 64 w.len))))) = false := by decide

-- ⭐ THE POSITIVE CONTROL, in the SAME run and at the SAME shape: the unplanted
-- claims must be TRUE.  Without it, four `false`s are also what a probe that has
-- stopped seeing its subject would print.
theorem control :
    (segVectors.length == 8
      && ((vectors.filter (fun v => !(segEas v.instr).isEmpty)).length == 8)
      && (segVectors.all (fun v =>
            (preStates 1 8).all (fun s => (segEas v.instr).all (fun e =>
              canonical (e.addr s (s.rip + BitVec.ofNat 64 v.instr.len))))))) = true := by decide
EOF

# ⛔⛔ THE PROBE RESTATES ITS SUBJECTS, WHICH IS A DUPLICATE BORN IN AGREEMENT.
# If a shipped theorem is renamed or rewritten, these arms would go on planting
# defects in a shape the repository no longer checks — green, and about nothing.
# So each subject is required to OCCUR in Tests/Coverage.lean, and a missing
# anchor REFUSES (rc 2) rather than passing.
ANCHORS=(
  'def opOperands : Op → List Operand'
  'def segEas (i : Instr) : List Ea'
  'theorem segmentedAddressesAreCanonical'
  'theorem segmentedAddressesLandInAWatchedWindow'
  'def segVectors : List Vec'
  'theorem some_vector_carries_a_segment : segVectors.length = 8'
)

missing=0
for a in "${ANCHORS[@]}"; do
  if ! grep -qF -- "$a" Tests/Coverage.lean X86/Coverage.lean; then
    echo "⛔ SEGMENT RED PROBE REFUSES — this arm's subject is in neither Tests/Coverage.lean nor X86/Coverage.lean:"
    echo "     $a"
    missing=1
  fi
done
if [ $missing -ne 0 ]; then
  echo "   The shipped declaration has changed and these arms would plant defects"
  echo "   in a shape the repository no longer checks. Update both together."
  exit 2
fi

# ⭐ AND THE ANCHOR CHECK IS PROVEN TO FIRE, in the same run: an anchor list that
# silently matched nothing would be the defect it exists to prevent.
if grep -qF -- 'theorem segmentedAddressesAreCanonicalXX' Tests/Coverage.lean X86/Coverage.lean; then
  echo "⛔ the anchor self-test found a string that cannot exist."; exit 2; fi
if ! grep -qF -- "${ANCHORS[0]}" Tests/Coverage.lean X86/Coverage.lean; then
  echo "⛔ the anchor self-test cannot find a string it just matched."; exit 2; fi

OUT="$TMP/out.txt"
lake env lean "$PROBE" > "$OUT" 2>&1
rc=$?
if [ $rc -ne 0 ]; then
  echo "⛔ SEGMENT RED PROBE FAILED — an arm did not typecheck, so at least one"
  echo "   claim did NOT see its planted defect (or the control did not hold):"
  sed -n '1,60p' "$OUT"
  exit 1
fi
if grep -q "declaration uses 'sorry'" "$OUT"; then
  echo "⛔ SEGMENT RED PROBE FAILED — an arm was closed by sorry."
  exit 1
fi
echo "✔ segment red probe: 4 arms + 1 positive control, all PASS."
echo "  ${#ANCHORS[@]} anchors: every planted subject OCCURS in the shipped Tests/ or X86/ Coverage.lean"
echo "  s1 the AST extraction loses .mov           -> the segmented COUNT moves"
echo "  s2 the extraction loses its seg filter     -> the count moves the other way"
echo "  s3 a non-canonical segment base            -> canonicity claim goes false"
echo "  s4 a canonical base OUTSIDE the windows    -> window claim goes false (s3 still holds)"
echo "  control: the unplanted shape is TRUE in the same run"
exit 0
