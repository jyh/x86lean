/-
# Tests — the whole P0 test tree

`lake build Tests` builds every check in this repository that the KERNEL can
make: the SDM anchors, the nonvacuity obligations, and the coverage-table
consistency theorems.  What it cannot make is the differential comparison
against another model; that is `lake exe x86lean-diff` and the ACL2 side.
-/
import Tests.Anchors
import Tests.Nonvacuity
import Tests.Vectors
import Tests.Coverage
import Tests.Program
