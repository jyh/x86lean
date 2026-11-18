/-
# Tests.CoverageMmx — the MMX twins of processor-refereed rows (D405)

`X86.mmxTwinTable` is a population beside `tableP0`, `siliconTable` and `vexTable`, in a module of its own as
`Tests.CoverageVex` is, so the main table's theorems and figures do not move. The statements below are the table's
bookkeeping: its size, distinct rows, that each row's XMM form is a `siliconTable` row and not a main-table row, and that
the rows and `mmxTwinVectors` name each other exactly.
-/
import X86
import Tests.Vectors

namespace X86.Tests.CoverageMmx
open X86 X86.Tests

def twinMnemonics : List String := mmxTwinTable.map (·.mnemonic)

theorem mmx_twin_table_size : mmxTwinTable.length = 7 := by decide

theorem mmx_twin_rows_distinct : twinMnemonics.eraseDups.length = mmxTwinTable.length := by decide

/-- Each twin's mnemonic is a processor-refereed row and NOT a main-table row: the twin exists because of that split. -/
theorem mmx_twins_are_silicon_rows :
    (twinMnemonics.all fun m => siliconTable.any (·.mnemonic == m) && !(tableP0.any (·.mnemonic == m))) = true := by
  decide

theorem mmx_twin_rows_have_vectors :
    (twinMnemonics.all fun m => mmxTwinVectors.any (·.mnemonic == m)) = true := by decide

theorem mmx_twin_vectors_have_rows :
    (mmxTwinVectors.all fun v => twinMnemonics.contains v.mnemonic) = true := by decide

end X86.Tests.CoverageMmx
