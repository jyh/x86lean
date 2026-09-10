/-
# x86lean — a user-level x86-64 ISA semantics in Lean 4

PERSONAL LANE, PUBLIC SOURCES ONLY.  See `PROVENANCE.md` for every source and
its licence, `TRUSTBASE.md` for what this development trusts and what it proves,
and `docs/DECISIONS.md` for the decisions taken at P0 that depart from, or
sharpen, the plan of record.

Importing `X86` gives the whole model: state, syntax, semantics, and the
characterization theorems.  It does NOT give the native-computation tier
(`X86Native`), which is separately labelled and separately gated on purpose.
-/
import X86.Basic
import X86.Value
import X86.Oracle
import X86.Memory
import X86.State
import X86.Syntax
import X86.Flags
import X86.Semantics
import X86.Theorems
import X86.Program
import X86.Coverage
import X86.Serialize
