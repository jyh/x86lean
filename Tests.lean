/-
# Tests — the whole P0 test tree

`lake build Tests` builds every check in this repository that the KERNEL can
make: the SDM anchors, the nonvacuity obligations, and the coverage-table
consistency theorems.  What it cannot make is the differential comparison
against another model; that is `lake exe x86lean-diff` and the ACL2 side.
-/
import Tests.Anchors
import Tests.AnchorsBmi
import Tests.AnchorsShuf
import Tests.AnchorsShufM
import Tests.AnchorsSimd
import Tests.AnchorsSimdB
import Tests.AnchorsSha
import Tests.AnchorsAes
import Tests.AnchorsVexSil
import Tests.AnchorsVexSilB
import Tests.AnchorsVexSilC
import Tests.AnchorsVexSilE
import Tests.AnchorsVexSilF
import Tests.AnchorsVexSilG
import Tests.AnchorsVexSilH
import Tests.AnchorsVexSilI
import Tests.AnchorsVex
import Tests.Nonvacuity
import Tests.Vectors
import Tests.Coverage
import Tests.CoverageVex
import Tests.CoverageVex256
import Tests.CoverageVexMem
import Tests.CoverageVexMov
import Tests.AnchorsVexSilD
import Tests.Program
import Tests.Logic
import Tests.LogicLoop
import Tests.LogicKit
import Tests.LogicRead
import Tests.LogicMemRel
