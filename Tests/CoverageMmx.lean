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

/-! ## D405 §6 — the MMX forms of main-table mnemonics (`X86.mmxTable`)

The 23 rows D404 d1 and d2 had written into `tableP0`'s shapes column, moved to a table of their own so that
`Tests.Coverage`'s `memDestSweep`, which reads that column character by character, returns to its base cost. -/

def mmxMnemonics : List String := mmxTable.map (·.mnemonic)

theorem mmx_table_size : mmxTable.length = 31 := by decide

theorem mmx_rows_distinct : mmxMnemonics.eraseDups.length = mmxTable.length := by decide

/-- Each row's mnemonic is a main-table row and not a processor-refereed one: the row is the MMX form of a differential
mnemonic, and the twins of the processor-refereed ones are `mmxTwinTable`'s. -/
theorem mmx_rows_are_main_rows :
    (mmxMnemonics.all fun m => tableP0.any (·.mnemonic == m) && !(siliconTable.any (·.mnemonic == m))) = true := by
  decide

set_option maxRecDepth 40000 in  -- `Tests.Coverage`'s file-wide value, scoped here
/-- ⭐ D406 K1: the mnemonics of the packed MMX vectors of `vectors` (`mmbin`, `mmbinm`, `mmshifti`), read ONCE. The two
theorems below used to scan `vectors` themselves, and `mmx_rows_have_vectors` did it once PER ROW (rows × vectors), so
D406's 8 rows and 16 vectors cost the unit +1,505 ms against a 310 ms budget on katmai (K1, 6a12679 → ce83341): +35 %,
the rows × vectors ratio. Both now read this one linear pass. -/
def mmxVectorMnemonics : List String :=
  vectors.filterMap (fun v => match v.instr.op with
    | .mmbin .. | .mmbinm .. | .mmshifti .. => some v.mnemonic
    | _ => none)

set_option maxRecDepth 40000 in  -- the same scoped value
/-- Every packed MMX vector of `vectors` names a row of this table. -/
theorem mmx_vectors_have_rows :
    mmxVectorMnemonics.all (fun m => mmxMnemonics.contains m) = true := by decide

set_option maxRecDepth 40000 in  -- the same scoped value
/-- …and every row has a packed MMX vector in `vectors`. -/
theorem mmx_rows_have_vectors :
    mmxMnemonics.all (fun m => mmxVectorMnemonics.contains m) = true := by decide

/-! ## D407 — the MMX forms refereed by a processor (`X86.mmxSilTable`)

Neither reference model executes these NP forms, so no `vectors` entry carries them; their rows are `Tests.AnchorsMmxSil`'s. -/

def mmxSilMnemonics : List String := mmxSilTable.map (·.mnemonic)

theorem mmx_sil_table_size : mmxSilTable.length = 9 := by decide

theorem mmx_sil_rows_distinct : mmxSilMnemonics.eraseDups.length = mmxSilTable.length := by decide

/-- No D407 row is a differentially tested mnemonic of the main table, or one of D404's or D405's MMX rows: one referee
per row. -/
theorem mmx_sil_rows_are_not_differential :
    (mmxSilMnemonics.all fun m => !(tableP0.any (·.mnemonic == m)) && !(mmxMnemonics.contains m)
      && !(twinMnemonics.contains m)) = true := by decide

end X86.Tests.CoverageMmx
