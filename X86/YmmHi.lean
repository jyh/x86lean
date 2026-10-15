/-
# X86.YmmHi — bits 255:128 of the sixteen YMM registers (V3, D341)

THE STRUCTURE ONLY.  It is nested in `Xmms` as the field `hi` (`X86/Basic.lean`), so
`Cpu` does not grow.  Its accessors, the VEX.128 setter and every lemma about them
live in `X86/Vex.lean`.

⭐ A MODULE OF ITS OWN BECAUSE NEW STATE IS PRICED AS A NEW UNIT. Built inside
`X86.Basic`, this structure, its derived instances and its lemmas moved that unit's
kernel time by +54.9 ms on the first build and +37.7 ms after one lemma was made
cheaper, against a 21.6 ms delta budget (`kernel_delta.py`, base 76b6890, on yukon).
The budget was not widened; the cost moved here and to `X86.Vex`, each a new unit
with its own registered ceiling (`scripts/kernel_ceilings.txt`).

LANE. Personal lane, public sources only.  See CLAUDE.md.
-/

namespace X86

/-- ⭐⭐⭐ V3 (D341): bits 255:128 of the sixteen YMM registers, by register.  The
same shape as `Xmms`'s low halves; nested inside `Xmms` as its field `hi`. -/
structure YmmHi where
  hi0  : BitVec 128 := 0
  hi1  : BitVec 128 := 0
  hi2  : BitVec 128 := 0
  hi3  : BitVec 128 := 0
  hi4  : BitVec 128 := 0
  hi5  : BitVec 128 := 0
  hi6  : BitVec 128 := 0
  hi7  : BitVec 128 := 0
  hi8  : BitVec 128 := 0
  hi9  : BitVec 128 := 0
  hi10 : BitVec 128 := 0
  hi11 : BitVec 128 := 0
  hi12 : BitVec 128 := 0
  hi13 : BitVec 128 := 0
  hi14 : BitVec 128 := 0
  hi15 : BitVec 128 := 0
  deriving DecidableEq, Repr, Inhabited, BEq

end X86
