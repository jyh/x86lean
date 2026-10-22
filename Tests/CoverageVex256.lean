/-
# Tests.CoverageVex256 — V6 (D344): the VEX.256 twins' vectors, held against the VEX table

The VEX.256 (VEX.L = 1) twins are the SAME mnemonics as `X86.vexTable`'s rows, in a second operand size,
so they add no row to any table. Their checks sit in a module of their own so the kernel cost is a NEW unit
(`scripts/kernel_ceilings.txt`, `scripts/ku_delta_budget.txt`) rather than a move of `Tests.CoverageVex`,
whose theorems are over the 39 VEX.128 vectors.

The checks:
1. there are 39 VEX.256 vectors, one per VEX.128 register vector;
2. every VEX.256 vector's mnemonic is a VEX row, and every VEX row has a VEX.256 vector;
3. no VEX.256 vector's id is an id of `vexVectors`.

The encodings are `scripts/check_encodings.py`'s (clang re-assembles each `asm`), never re-stated here, and
no check walks the 1,198 main vectors: a string comparison per pair is kernel cost, and the ids carry `_y`.

LANE. Personal lane, public sources only.
-/
import X86
import Tests.Vectors

namespace X86.Tests.CoverageVex256
open X86 X86.Tests

def vexMnemonics : List String := vexTable.map (·.row.mnemonic)

/-- 1. One VEX.256 vector per VEX.128 REGISTER vector (39), plus V9a's (D353) 52 VEX.256 MEMORY vectors: two per
kind of `VBinKind.vexMemTaken`, and a third for `vpcmpeqw` and `vpcmpeqd` (an operand that makes the high lane's
equality fire, D353), so 93. -/
theorem vex256_vectors_size : vex256Vectors.length = 93 := by decide

/-- 2. The mnemonics are exactly the VEX table's. -/
theorem vex256_vectors_have_rows :
    (vex256Vectors.all fun v => vexMnemonics.contains v.mnemonic) = true := by decide

theorem vex_rows_have_vex256_vectors :
    (vexMnemonics.all fun m => vex256Vectors.any (·.mnemonic == m)) = true := by decide

/-- 3. Their ids are not the VEX.128 vectors' ids. -/
theorem vex256_ids_new :
    (vex256Vectors.all fun v => !(vexVectors.any (·.id == v.id))) = true := by decide

end X86.Tests.CoverageVex256
