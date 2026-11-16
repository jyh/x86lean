/-
# Tests.CoverageVexMem — V9a (D353): the VEX memory twins' vectors, held against the VEX table and the taken set

`vexMemVectors` is a fourth vector list beside `vectors`, `vexVectors` and `vex256Vectors`, and these checks are
a NEW kernel unit (`scripts/kernel_ceilings.txt`). Appending V9a's 104 rows to the two existing VEX lists made
their coverage units walk them too: `Tests.CoverageVex256` read 791 → 3,050 ms on katmai (K1), past a per-unit
delta budget that is a fraction of the unit's own size. D341 put the VEX table in a module of its own for the
same reason.

The checks:
1. the list has 104 rows (50 VEX.128, 54 VEX.256);
2. every row's mnemonic is a VEX table row;
3. every row is a memory twin (`vexbinm` or `vexbinm256`) of a kind `VBinKind.vexMemTaken` lists, so no row is
   one `step` refuses and the list cannot drift from the set the model takes;
4. no row's id is an id of `vexVectors` or `vex256Vectors`.

LANE. Personal lane, public sources only.
-/
import X86
import Tests.Vectors

namespace X86.Tests.CoverageVexMem
open X86 X86.Tests

def vexMnemonics : List String := vexTable.map (·.row.mnemonic)

/-- 1. Two vectors per (kind, length) for the 26 kinds, less `vpxor`'s two VEX.128 rows (in `vexVectors`
since D342), plus the two `_hi` rows: 50 + 54. -/
theorem vexmem_vectors_size : vexMemVectors.length = 104 := by decide

/-- 2. Every mnemonic is a VEX table row. -/
theorem vexmem_vectors_have_rows :
    (vexMemVectors.all fun v => vexMnemonics.contains v.mnemonic) = true := by decide

/-- 3. Every row is a memory twin of a kind the model takes on the differential's word. -/
theorem vexmem_vectors_are_taken_twins :
    (vexMemVectors.all fun v => match v.instr.op with
      | .vex (.vexbinm k _ _ _) => k.vexMemTaken
      | .vex (.vexbinm256 k _ _ _) => k.vexMemTaken
      | _ => false) = true := by decide

/-- 4. Their ids are not the other VEX lists' ids. -/
theorem vexmem_ids_new :
    (vexMemVectors.all fun v =>
      !(vexVectors.any (·.id == v.id)) && !(vex256Vectors.any (·.id == v.id))) = true := by decide

end X86.Tests.CoverageVexMem
