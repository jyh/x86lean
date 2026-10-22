/-
# Tests.CoverageVex — V3 (D341): the VEX.128 twins' table, held against its vectors and the main table

`X86.vexTable` is a third population beside `tableP0` and `siliconTable`, in a module of its own so
its kernel cost is a NEW unit (`scripts/kernel_ceilings.txt`): as rows of `tableP0` the 33 twins
moved `Tests.Coverage`, whose table theorems are quadratic in the row count, by +5,300 ms (D341).

The checks, each linear in the main table or confined to the 33:
1. the VEX rows are distinct;
2. no VEX mnemonic is a mnemonic of `tableP0` or of `siliconTable`;
3. every VEX row names its legacy TWIN, the twin is a row of `tableP0`, and the VEX mnemonic is
   the twin's spelling with a `v` in front;
4. every VEX row has a vector in `vexVectors`, and every `vexVectors` mnemonic is a VEX row;
5. no `vexVectors` mnemonic is a mnemonic of `vectors` (so the main table's figures are untouched).

LANE. Personal lane, public sources only.
-/
import X86
import Tests.Vectors

namespace X86.Tests.CoverageVex
open X86 X86.Tests

def vexMnemonics : List String := vexTable.map (·.row.mnemonic)

/-- The VEX table has 33 rows, as D339 measured: the twins x86isa executes. -/
theorem vex_table_size : vexTable.length = 33 := by decide

/-- 1. The rows are distinct. -/
theorem vex_rows_distinct : vexMnemonics.eraseDups.length = vexTable.length := by decide

/-- 2. No VEX row is a row of either other table. -/
theorem vex_rows_not_in_other_tables :
    (vexMnemonics.all fun m =>
      !(tableP0.any (·.mnemonic == m)) && !(siliconTable.any (·.mnemonic == m))) = true := by
  decide

/-- 3. Every VEX row names its legacy twin; the twin is a row of `tableP0`; and the VEX mnemonic is
the twin's spelling with a `v` in front. -/
theorem vex_twins_are_main_rows :
    (vexTable.all fun r =>
      tableP0.any (·.mnemonic == r.twin) && r.row.mnemonic == "v" ++ r.twin) = true := by
  decide

/-- 4. Every VEX row has a vector, and every VEX vector's mnemonic is a VEX row. -/
theorem vex_rows_have_vectors :
    (vexMnemonics.all fun m => vexVectors.any (·.mnemonic == m)) = true := by decide

theorem vex_vectors_have_rows :
    (vexVectors.all fun v => vexMnemonics.contains v.mnemonic) = true := by decide

/-- 5. No VEX vector shares a mnemonic with the main vector table. -/
theorem vex_vectors_not_in_main :
    (vexVectors.all fun v => !(tableP0.any (·.mnemonic == v.mnemonic))) = true := by decide

end X86.Tests.CoverageVex
