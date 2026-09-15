/-
# X86.SoftFloat — IEEE-754 predicates over `BitVec`, and nothing more

⭐⭐⭐ **THE SOFT-FLOAT COMMISSION, SUB-GROUP A** (`docs/SOFT-FLOAT-COMMISSION.md`,
D139).  This file is the first floating-point vocabulary in this model, and it is
deliberately the part of IEEE-754 that needs **no rounding**: the ordering
predicate the `COMISS`/`COMISD`/`UCOMISS`/`UCOMISD` family computes.

⛔⛔ **WHY NOT `Float`.**  Lean's `Float` is a structure over `opaque floatSpec :
FloatSpec`, so the kernel has nothing to unfold: `(2.0 : Float) + 2.0 = 4.0` is
not closed by `rfl`, and it is not closed by `native_decide` either — propositional
equality on `Float` has no `Decidable` instance at all.  There is no route through
`Float` at ANY axiom price.  Measured, not assumed; the evidence is in D139 §1,
with the `BitVec` control (`(2#8) + (2#8) = 4#8` by `decide`, zero axioms) taken
in the same run.

⚠️ **NO MATHLIB** (D1, and `lakefile.toml` says so): Lean core's `BitVec` only.

## The representation choice, and why it is not a typed field split

Every function here takes the operand as a **`BitVec 64`** together with a `Fmt`
saying how wide the format actually is, rather than as a `BitVec 32` / `BitVec 64`
pair of separate rules.  Two reasons, and the second is the load-bearing one:

* `getXmm` already hands back a `BitVec 128`, so both widths arrive right-aligned
  in a 64-bit slice and no dependent-width juggling is needed to read them;
* **one rule serves both formats.**  `comiss` and `comisd` are the same ordering
  at different exponent and mantissa widths, and writing them as one function
  makes that a fact of the code rather than a claim in a comment.  Two copies of
  a rule are two things that can disagree, and a divergence between them would be
  invisible to any test that exercises one width.
-/
import X86.Basic

namespace X86
namespace SoftFloat

/-- An IEEE-754 binary interchange format: `ew` exponent bits, `mw` mantissa bits,
one sign bit above them. -/
structure Fmt where
  ew : Nat
  mw : Nat
  deriving DecidableEq, Repr

/-- binary32 — SDM's "single precision". -/
def binary32 : Fmt := ⟨8, 23⟩
/-- binary64 — SDM's "double precision". -/
def binary64 : Fmt := ⟨11, 52⟩

namespace Fmt

/-- Total width in bits: sign + exponent + mantissa. -/
def w (f : Fmt) : Nat := 1 + f.ew + f.mw

/-- The mantissa field. -/
def mant (f : Fmt) (x : BitVec 64) : BitVec 64 := x &&& ((1 <<< f.mw) - 1)

/-- The biased exponent field. -/
def expo (f : Fmt) (x : BitVec 64) : BitVec 64 := (x >>> f.mw) &&& ((1 <<< f.ew) - 1)

/-- The sign bit — the top bit of the FORMAT, not of the 64-bit carrier. -/
def sign (f : Fmt) (x : BitVec 64) : Bool := x.getLsbD (f.ew + f.mw)

/-- ⭐ THE MAGNITUDE: everything below the sign bit, read as an unsigned integer.

⚠️ This is the whole reason IEEE-754 lays out exponent-above-mantissa: for two
values of the SAME sign, the ordering of the magnitudes as plain unsigned
integers **is** the ordering of the numbers — across normals, denormals and
infinity alike, with no case analysis.  The model relies on that and says so
here, because a reader who does not know it will read `mag` as a bit trick. -/
def mag (f : Fmt) (x : BitVec 64) : BitVec 64 := x &&& ((1 <<< (f.ew + f.mw)) - 1)

/-- A NaN: exponent all ones, mantissa non-zero (SDM Vol. 1 §4.8.3.4). -/
def isNaN (f : Fmt) (x : BitVec 64) : Bool :=
  f.expo x == ((1 <<< f.ew) - 1) && f.mant x != 0

/-- ±0: exponent and mantissa both zero, either sign. -/
def isZero (f : Fmt) (x : BitVec 64) : Bool := f.mag x == 0

end Fmt

/-- The four-way result of an IEEE-754 comparison.  `unord` is a genuine fourth
outcome, not "not equal": it is what the flags report when either operand is NaN,
and a three-valued model has nowhere to put it. -/
inductive FCmp where
  | lt | eq | gt | unord
  deriving DecidableEq, Repr, Inhabited, BEq

/-- ⭐⭐ THE ORDERING RULE (SDM Vol. 2A, COMISS/COMISD; Vol. 1 §4.8.4).

⛔ THE FOUR CASES A RAW BITVECTOR COMPARE GETS WRONG, each of which is a wrong
model that agrees with this one on ordinary positive normals:

* **`+0` and `-0` are EQUAL** and have different bit patterns, so `a == b` is not
  equality of values;
* **either operand NaN is UNORDERED**, which is not "less" and not "not equal" —
  it sets CF, PF and ZF together, a combination no ordered result produces;
* **for two negatives the magnitude order REVERSES**: `-1 > -2` while
  `mag(-1) < mag(-2)`;
* **a signed comparison of the whole word** gets the negatives backwards for the
  same reason and additionally mis-handles `-0`.

⚠️ Denormals and infinities need NO case of their own — they are ordered
correctly by `mag`, which is the property `Fmt.mag`'s docstring records. A model
that special-cases them is not more careful, it is more surface. -/
def fcmp (f : Fmt) (a b : BitVec 64) : FCmp :=
  if f.isNaN a || f.isNaN b then .unord
  else if f.isZero a && f.isZero b then .eq          -- ±0 compare equal
  else if f.sign a != f.sign b then (if f.sign a then .lt else .gt)
  else if f.mag a == f.mag b then .eq
  else if (f.mag a < f.mag b) != f.sign a then .lt else .gt

/-- ⭐⭐ MINIMUM (SDM Vol. 2B, MINSS/MINSD/MINPS): `a` is the DESTINATION (the
first operand), `b` the SOURCE, and the result is `a` only when `a < b` STRICTLY.
Every other outcome returns the SOURCE, including the two that are not orderings:

* **either operand NaN** (SDM: *"If only one value is a NaN … the second operand
  (source operand) … is written to the result"*): `fcmp` says `unord`, not `lt`;
* **two zeros of either sign** (SDM: *"If the values being compared are both 0.0s
  (of either sign), the value in the second operand (source operand) is
  returned"*): `fcmp` says `eq`, not `lt`.

⛔ SO THIS IS NOT COMMUTATIVE, and it is not IEEE-754's `minNum`. `fmin f a b` and
`fmin f b a` differ exactly on those two cases — the asymmetry the SDM states, and
the one a symmetric model gets wrong while agreeing everywhere else.

⚠️ The rule is ONE comparison because `fcmp` already carries both exceptions as
outcomes: no case of its own for NaN or ±0 is needed here, and a second copy of
either test would be a second thing that can disagree with `fcmp`. -/
def fmin (f : Fmt) (a b : BitVec 64) : BitVec 64 :=
  if fcmp f a b == .lt then a else b

/-- ⭐⭐ MAXIMUM (SDM Vol. 2B, MAXSS/MAXSD/MAXPS): `fmin`'s rule with `gt` for `lt`
— the destination only when STRICTLY greater, the source otherwise, so NaN and
two zeros return the SOURCE here too. -/
def fmax (f : Fmt) (a b : BitVec 64) : BitVec 64 :=
  if fcmp f a b == .gt then a else b

end SoftFloat
end X86
