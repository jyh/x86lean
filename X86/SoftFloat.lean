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
import X86.Value

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

/-! ### ⭐⭐⭐ P2 BATCH 39 — THE TWO WIDENINGS THAT NEED NO ROUNDING (D258).

`cvtss2sd` (binary32 → binary64) and `cvtsi2sd` from a 32-bit source (int32 →
binary64) are EXACT: every binary32 value and every int32 is a binary64 value.
So neither reads MXCSR.RC, and both belong to sub-group A of the soft-float
commission, the part this model can state without an MXCSR (D2).

⚠️ ONE ENCODER SERVES BOTH, because both are "place a non-zero integer
significand at a known scale".  A normal binary32 is the integer `2^23 + mant`
at scale `2^(expo − 150)`; a denormal is `mant` at scale `2^(1 − 150)`; an int32
is its magnitude at scale `2^0`.  Writing the three as one call to `toBinary64`
makes "a denormal is normalised exactly as a normal is" a fact of the code. -/

/-- ⭐⭐ THE BINARY64 ENCODING OF `±m × 2^(eb − 1023)` for a NON-ZERO `m` below
`2^32`.  The top set bit is at `p = 31 − clz₃₂ m`; the biased exponent is
`eb + p`; the mantissa is `m` shifted LEFT so that bit `p` lands on bit 52, with
that bit dropped (it is the implicit leading one), so the value is exact.

⛔ THE SEARCH IS OVER 32 BITS, NOT 64, AND THE PRECONDITION IS WHAT PAYS FOR IT.
Both callers meet `m < 2^32` by construction (an int32 magnitude is at most
`2^31`, a binary32 significand below `2^24`), and the kernel then walks half the
recursion: the two `Tests/Anchors.lean` differentials measured ~45 ms of type
checking with a 64-bit search and ~20 ms with this one (D258 §4).  A magnitude
at or above `2^32` would be encoded WRONG, silently.  `eb + p` stays inside
874 … 1150, so no overflow and no underflow is possible. -/
def toBinary64 (neg : Bool) (m : BitVec 64) (eb : Nat) : BitVec 64 :=
  let p := 31 - Value.clzN m 32
  let mant := (m <<< (52 - p)) &&& ((1 <<< 52) - 1)
  (if neg then 1 <<< 63 else 0) ||| (BitVec.ofNat 64 (eb + p) <<< 52) ||| mant

/-- ⭐⭐ CVTSS2SD's LANE RULE (SDM Vol. 2B, CVTSS2SD; IEEE-754 §5.4.2): the low
binary32 of `x` as a binary64.  The sign always travels.

* **±0 → ±0**, and **±∞ → ±∞**;
* **a NaN keeps its payload**, shifted up 29 bits, and **a signalling NaN is
  QUIETED** by setting the binary64 quiet bit (bit 51).  A quiet NaN already has
  its quiet bit (bit 22), and the shift puts it on bit 51, so setting bit 51 for
  EVERY NaN is the one rule for both kinds;
* **a denormal is NORMALISED.**  Its biased exponent is 0 and its value is
  `mant × 2^−149`, so the binary64 exponent comes from the top bit of `mant` and
  not from the field.  A model that shifted the mantissa and re-biased the
  field (`0 + 896`) is right on every normal and wrong on every denormal.

⚠️ NO EXCEPTION HERE: the invalid (signalling NaN) and denormal flags are
MXCSR's, raised by `preFlags` through `Cpu.withSimd` (D266), and masked in every
pre-state. -/
def f32to64 (x : BitVec 64) : BitVec 64 :=
  let f := binary32
  let s := f.sign x
  let e := f.expo x
  let m := f.mant x
  if e == 0xFF then
    (if s then 1 <<< 63 else 0) ||| (0x7FF <<< 52) ||| (m <<< 29) |||
      (if m == 0 then 0 else 1 <<< 51)
  else if e == 0 && m == 0 then (if s then 1 <<< 63 else 0)
  else if e == 0 then toBinary64 s m 874
  else toBinary64 s (m ||| (1 <<< 23)) (e.toNat + 873)

/-- ⭐⭐ CVTSI2SD's RULE AT A 32-BIT SOURCE (SDM Vol. 2B, CVTSI2SD): the low 32
bits of `x`, read as a SIGNED integer, as a binary64.  Exact for every int32.

⛔ THE MAGNITUDE OF INT32_MIN IS 2^31, which is not an int32: it is computed as
the 32-bit negation read UNSIGNED, where `−0x80000000 = 0x80000000`.  A model
that took the magnitude as a signed 32-bit value would have no answer there. -/
def i32to64 (x : BitVec 64) : BitVec 64 :=
  let v := x.setWidth 32
  if v == 0 then 0
  else
    let neg := v.getLsbD 31
    toBinary64 neg ((if neg then -v else v).setWidth 64) 1023

/-! ### ⭐⭐⭐ P2 BATCH 40 — SUB-GROUP A′: TRUNCATION TO AN INTEGER (D261).

`cvttsd2si` and `cvttss2si` convert the low binary64 / binary32 lane to a signed
integer of the destination's width, ROUNDING TOWARD ZERO whatever MXCSR.RC says.
That is why they are sub-group A′ and not B: the opcode fixes the rounding, so
the model states them without an MXCSR (D2). -/

/-- ⭐⭐ CVTTSD2SI / CVTTSS2SI's RULE (SDM Vol. 2A, CVTTSD2SI and CVTTSS2SI): the
low `f`-format lane of `x`, truncated toward zero, as a `w`-bit two's-complement
integer, zero-extended to 64 bits (`w` is 32 or 64).

* **|x| < 1 gives 0**, including ±0 and every denormal. A negative fraction
  gives +0, because an integer has no signed zero.
* **A NaN, ±∞, or any value whose truncation is outside
  `[−2^(w−1), 2^(w−1) − 1]` gives the INTEGER INDEFINITE `2^(w−1)`**, which is
  the sign bit alone. The invalid exception that goes with it is an MXCSR flag,
  raised by `truncFlags` (D266) and masked in every pre-state here.
* **−2^(w−1) itself is in range.** A value in `(−2^(w−1) − 1, −2^(w−1)]`
  truncates to it, which has the same bits as the indefinite by a different rule.

The significand is placed as an integer. A normal's value is
`(2^mw + mant) × 2^(k − mw)`, with `k` the unbiased exponent, so the truncation is
one shift: left when `k ≥ mw`, right (dropping the fraction) otherwise.
`k < w ≤ 64` bounds the left shift, so the integer fits in 64 bits for both
formats: below `2^53 × 2^11` for binary64 and `2^24 × 2^40` for binary32. -/
def truncToInt (f : Fmt) (w : Nat) (x : BitVec 64) : BitVec 64 :=
  let e := (f.expo x).toNat
  let bias := 2 ^ (f.ew - 1) - 1
  let ind : BitVec 64 := 1 <<< (w - 1)
  if e == 2 ^ f.ew - 1 then ind
  else if e < bias then 0
  else
    let k := e - bias
    if w ≤ k then ind
    else
      let sig := f.mant x ||| (1 <<< f.mw)
      let n := if f.mw ≤ k then sig <<< (k - f.mw) else sig >>> (f.mw - k)
      if f.sign x then
        (if n.ule ind then ((-n).setWidth w).setWidth 64 else ind)
      else
        (if n.ult ind then n else ind)

/-! ### ⭐⭐⭐ SUB-GROUP B0 — THE STICKY EXCEPTION FLAGS OF THE FORMS ALREADY HERE (D266).

MXCSR's low six bits (SDM Vol. 1 §10.2.3) are STICKY: an instruction ORs in what it
raises and never clears one. These functions say WHICH bits a form raises. Every
pre-state masks every exception, so the flag is all that is observable; an unmasked
one makes the step refuse (`Cpu.withSimd`). -/

/-- MXCSR.IE, the invalid-operation flag (bit 0). -/
def fIE : BitVec 32 := 0x01
/-- MXCSR.DE, the denormal-operand flag (bit 1). -/
def fDE : BitVec 32 := 0x02
/-- MXCSR.PE, the precision (inexact) flag (bit 5). -/
def fPE : BitVec 32 := 0x20

namespace Fmt
/-- A signalling NaN: a NaN whose quiet bit (the mantissa's top bit) is clear. -/
def isSNaN (f : Fmt) (x : BitVec 64) : Bool := f.isNaN x && !(x.getLsbD (f.mw - 1))
/-- A denormal: exponent zero, mantissa non-zero. -/
def isDenormal (f : Fmt) (x : BitVec 64) : Bool := f.expo x == 0 && f.mant x != 0
end Fmt

/-- ⭐⭐ THE PRE-COMPUTATION FLAGS OF A TWO-OPERAND FORM (SDM Vol. 2A/2B exception lists).
* **IE** when an operand is a NaN that SIGNALS here. An SNaN always does. A QNaN does
  when `quietSignals`: COMIS*, MIN*, MAX* (SDM: "including QNaN source operand"), not
  UCOMIS*.
* **DE** when an operand is a denormal, and ONLY WHEN NO OPERAND IS A NaN. Measured on
  the reference model (D266 §1): the other reading fails two cases on every min/max form.
⛔ COMIS AND UCOMIS DIFFER HERE AND NOWHERE ELSE. x86isa dispatches COMIS as UCOMIS
(`inst-listing.lisp`, OPERATION #x9), so the QNaN arm is pinned in the kernel against
the SDM and declared as an oracle divergence (D266 §1). -/
def preFlags (f : Fmt) (quietSignals : Bool) (a b : BitVec 64) : BitVec 32 :=
  if f.isNaN a || f.isNaN b then
    (if quietSignals || f.isSNaN a || f.isSNaN b then fIE else 0)
  else if f.isDenormal a || f.isDenormal b then fDE else 0

/-- ⭐⭐ CVTTSD2SI / CVTTSS2SI's FLAGS (SDM Vol. 2A: "Invalid, Precision"), on
`truncToInt`'s case split: IE exactly where that function returns the indefinite by
the invalid rule, PE where a finite in-range value had a fraction. No DE: the SDM does
not list it, and a denormal truncates to 0 with PE. -/
def truncFlags (f : Fmt) (w : Nat) (x : BitVec 64) : BitVec 32 :=
  let e := (f.expo x).toNat
  let bias := 2 ^ (f.ew - 1) - 1
  let ind : BitVec 64 := 1 <<< (w - 1)
  if e == 2 ^ f.ew - 1 then fIE
  else if e < bias then (if f.isZero x then 0 else fPE)
  else
    let k := e - bias
    if w ≤ k then fIE
    else
      let sig := f.mant x ||| (1 <<< f.mw)
      let n := if f.mw ≤ k then sig <<< (k - f.mw) else sig >>> (f.mw - k)
      let frac := if f.mw ≤ k then false else (sig &&& ((1 <<< (f.mw - k)) - 1)) != 0
      if !(if f.sign x then n.ule ind else n.ult ind) then fIE
      else if frac then fPE else 0

/-! ### ⭐⭐⭐ SUB-GROUP B1 — MULSS / MULSD, THE FIRST ROUNDING RULE (D262 K4, D266 §6 B1).

**The rule is K4's draft** (D262 §1), checked against an independent reference on 24,000 rows. It is changed in two
ways only, both from D262 §3:
- **RC is MXCSR's 2-bit field, read as a `Nat`** (0 nearest · 1 down · 2 up · 3 zero, SDM Vol. 1 §10.2.3). An `RC`
  inductive cost 175 ku, three times this module's allowance.
- **No power above 256 on any path:** a discarding shift is clamped at `bitlen + 1`.
The flags are computed in the same pass, so a result and its flags cannot disagree about the rounding. -/

/-- The unbiased-exponent offset. -/
def bias (f : Fmt) : Nat := 2 ^ (f.ew - 1) - 1

/-- Does `q` (with remainder `r` of a discarded part whose half is `half`) round up under RC `rc`? -/
def roundsUp (rc : Nat) (neg : Bool) (q r half : Nat) : Bool :=
  r != 0 &&
    (if rc == 0 then r > half || (r == half && q % 2 == 1)
     else if rc == 1 then neg
     else if rc == 2 then !neg
     else false)

/-- `m >>> s` with its remainder and the remainder's half, or `m <<< −s` exactly. The shift is clamped at
`bitlen m + 1`: past that, every bit of `m` is discarded and the rounding decision is the same (D262 §3.1). -/
def shiftOut (m : Nat) (s : Int) : Nat × Nat × Nat :=
  let t : Nat := min s.toNat (Nat.log2 m + 2)
  if s ≤ 0 then (m <<< s.natAbs, 0, 0) else (m >>> t, m % 2 ^ t, 2 ^ (t - 1))

/-- ⭐ `±m × 2^e` (`m > 0`) rounded to `f` under `rc`, AND the flags that rounding raises: PE when inexact, UE when also
TINY AFTER ROUNDING (D266 §3: rounded at an unbounded exponent, below the normal range), OE with PE on overflow.

One encoding for normal and subnormal results: the exponent field below the significand is `be − 1` for a normal and
0 for a subnormal, so a carry out of the rounded significand lands in the exponent field by itself. -/
def roundPack (f : Fmt) (rc : Nat) (neg : Bool) (m : Nat) (e : Int) : BitVec 64 × BitVec 32 :=
  let n := Nat.log2 m + 1
  let sN : Int := (n : Int) - (f.mw + 1)
  let sS : Int := (1 : Int) - bias f - f.mw - e
  let (q, r, half) := shiftOut m (max sN sS)
  let q' := if roundsUp rc neg q r half then q + 1 else q
  let k : Nat := if sS ≤ sN then (e + sN + f.mw + bias f - 1).toNat else 0
  let bits : Nat := k * 2 ^ f.mw + q'
  let sgn : Nat := if neg then 2 ^ (f.ew + f.mw) else 0
  let top : Nat := (2 ^ f.ew - 1) * 2 ^ f.mw
  if bits < top then
    -- TINY AFTER ROUNDING: the value rounded to `mw + 1` bits at an unbounded exponent is below 2^emin.
    let (qn, rn, hn) := shiftOut m sN
    let qn' := if roundsUp rc neg qn rn hn then qn + 1 else qn
    let lead : Int := e + sN + (if qn' == 2 ^ (f.mw + 1) then f.mw + 1 else f.mw)
    let fl : BitVec 32 :=
      if r == 0 then 0
      else if lead < (1 : Int) - bias f then 0x30 else 0x20
    (BitVec.ofNat 64 (sgn + bits), fl)
  else
    let away := if rc == 0 then true else if rc == 1 then neg else if rc == 2 then !neg else false
    (BitVec.ofNat 64 (sgn + if away then top else top - 1), 0x28)

namespace Fmt
/-- An infinity: exponent all ones, mantissa zero. -/
def isInf (f : Fmt) (x : BitVec 64) : Bool := f.expo x == ((1 <<< f.ew) - 1) && f.mant x == 0
end Fmt

/-- A finite operand as `(m, e)` with value `m × 2^e` (sign separate). -/
def sig (f : Fmt) (x : BitVec 64) : Nat × Int :=
  let e := (f.expo x).toNat
  if e == 0 then ((f.mant x).toNat, (1 : Int) - bias f - f.mw)
  else ((f.mant x).toNat + 2 ^ f.mw, (e : Int) - bias f - f.mw)

/-- ⭐⭐ MULSS / MULSD's lane rule and flags (SDM Vol. 2B MULSD: "Overflow, Underflow, Invalid, Precision, Denormal").
* **NaN** (SDM Vol. 1 Table 4-7): the FIRST source if it is a NaN, else the second, quieted. IE when either is an SNaN.
* **∞ × 0** is invalid: IE and the QNaN floating-point indefinite, whose sign bit is SET (D265; x86isa's is clear).
* **DE** on a denormal operand when no operand is a NaN (D266 §1).
* Otherwise one `Nat` multiply of the significands, rounded by `roundPack`. -/
def fmul (f : Fmt) (rc : Nat) (a b : BitVec 64) : BitVec 64 × BitVec 32 :=
  let lane : BitVec 64 := (1 <<< f.w) - 1
  let quiet : BitVec 64 := 1 <<< (f.mw - 1)
  let infE : BitVec 64 := ((1 <<< f.ew) - 1) <<< f.mw
  let neg := f.sign a != f.sign b
  let sgn : BitVec 64 := if neg then 1 <<< (f.ew + f.mw) else 0
  let snan : BitVec 32 := if f.isSNaN a || f.isSNaN b then fIE else 0
  let de : BitVec 32 := if f.isDenormal a || f.isDenormal b then fDE else 0
  if f.isNaN a then ((a ||| quiet) &&& lane, snan)
  else if f.isNaN b then ((b ||| quiet) &&& lane, snan)
  else if f.isInf a || f.isInf b then
    (if f.isZero a || f.isZero b then ((1 <<< (f.ew + f.mw)) ||| infE ||| quiet, fIE)
     else (sgn ||| infE, de))
  else if f.isZero a || f.isZero b then (sgn, de)
  else
    let (ma, ea) := sig f a
    let (mb, eb) := sig f b
    let (r, fl) := roundPack f rc neg (ma * mb) (ea + eb)
    (r, fl ||| de)

/-! ### ⭐⭐⭐ SUB-GROUP B2 (DRAFT) — ADD, SUB AND DIV ON `roundPack`.
No power above 256 on any path (D262 §3): an addend whose exponent is more than `mw + 3` below the other's is
replaced by a STICKY unit three places below the larger one's scale, and a quotient is taken to `2·mw + 4` extra
bits with a sticky bit. -/

/-- The divide-by-zero flag, MXCSR bit 2. -/
def fZE : BitVec 32 := 0x04

/-- ⭐⭐ ADDSS/ADDSD and, with `sub`, SUBSS/SUBSD (SDM Vol. 2B: "Overflow, Underflow, Invalid, Precision, Denormal").
* **NaN** as `fmul`: the first source if it is a NaN, else the second, quieted; IE on an SNaN.
* **∞ − ∞** (effective subtraction of infinities) is invalid: the negative QNaN indefinite and IE.
* **An exact zero sum** is +0, and −0 under round-down; two zeros of one sign keep it (IEEE 754 §6.3).
* **A zero addend** returns the other operand exactly; DE still rises on a denormal.
* Otherwise one signed `Int` sum, rounded by `roundPack`.
  ⚠️ WHY THE STICKY UNIT IS EXACT FOR ROUNDING: with `d > mw + 3` the larger operand is normal, so the result's unit
  is at least `2^(eL−1)` and its guard bit at `2^(eL−2)`. The smaller operand is below `2^(eL−2)`, and so is
  `2^(eL−3)`. The open interval between them holds no representable value and no midpoint. -/
def faddsub (f : Fmt) (rc : Nat) (sub : Bool) (a b : BitVec 64) : BitVec 64 × BitVec 32 :=
  let lane : BitVec 64 := (1 <<< f.w) - 1
  let quiet : BitVec 64 := 1 <<< (f.mw - 1)
  let infE : BitVec 64 := ((1 <<< f.ew) - 1) <<< f.mw
  let sbit : BitVec 64 := 1 <<< (f.ew + f.mw)
  let sa := f.sign a
  let sb := f.sign b != sub
  let zs (s : Bool) : BitVec 64 := if s then sbit else 0
  let snan : BitVec 32 := if f.isSNaN a || f.isSNaN b then fIE else 0
  let de : BitVec 32 := if f.isDenormal a || f.isDenormal b then fDE else 0
  if f.isNaN a then ((a ||| quiet) &&& lane, snan)
  else if f.isNaN b then ((b ||| quiet) &&& lane, snan)
  else if f.isInf a && f.isInf b then
    (if sa == sb then (zs sa ||| infE, 0) else (sbit ||| infE ||| quiet, fIE))
  else if f.isInf a then (zs sa ||| infE, de)
  else if f.isInf b then (zs sb ||| infE, de)
  else if f.isZero a && f.isZero b then (zs (if sa == sb then sa else rc == 1), 0)
  else if f.isZero b then (a &&& lane, de)
  else if f.isZero a then ((if sub then b ^^^ sbit else b) &&& lane, de)
  else
    let (ma, ea) := sig f a
    let (mb, eb) := sig f b
    let d : Int := ea - eb
    let k : Nat := f.mw + 3
    let (x, y, e) : Nat × Nat × Int :=
      if d.natAbs ≤ k then
        (if 0 ≤ d then (ma <<< d.toNat, mb, eb) else (ma, mb <<< d.natAbs, ea))
      else if 0 < d then (ma <<< 3, 1, ea - 3) else (1, mb <<< 3, eb - 3)
    let v : Int := (if sa then -(x : Int) else x) + (if sb then -(y : Int) else y)
    if v == 0 then (zs (rc == 1), de)
    else
      let (r, fl) := roundPack f rc (v < 0) v.natAbs e
      (r, fl ||| de)

/-- ⭐⭐ DIVSS/DIVSD (SDM Vol. 2B: "Overflow, Underflow, Invalid, Divide-by-Zero, Precision, Denormal").
* **NaN** as `fmul`. **0/0 and ∞/∞** are invalid: the negative QNaN indefinite and IE.
* **x/0** for a finite non-zero `x` is ±∞ with ZE, and WITHOUT DE even when `x` is denormal: SDM Vol. 1 §4.9.2 ranks
  divide-by-zero above the denormal-operand exception, and a masked one returns its special result (Rosetta 2 and
  x86isa read ZE alone; the processors' reading is hwprobe's `div*_den_zero`).
* **∞/x** is ±∞, **x/∞** and **0/x** are ±0, each with DE on a denormal operand.
* Otherwise the quotient to `2·mw + 4` extra bits, with a sticky bit, rounded by `roundPack`. -/
def fdiv (f : Fmt) (rc : Nat) (a b : BitVec 64) : BitVec 64 × BitVec 32 :=
  let lane : BitVec 64 := (1 <<< f.w) - 1
  let quiet : BitVec 64 := 1 <<< (f.mw - 1)
  let infE : BitVec 64 := ((1 <<< f.ew) - 1) <<< f.mw
  let sbit : BitVec 64 := 1 <<< (f.ew + f.mw)
  let neg := f.sign a != f.sign b
  let sgn : BitVec 64 := if neg then sbit else 0
  let snan : BitVec 32 := if f.isSNaN a || f.isSNaN b then fIE else 0
  let de : BitVec 32 := if f.isDenormal a || f.isDenormal b then fDE else 0
  if f.isNaN a then ((a ||| quiet) &&& lane, snan)
  else if f.isNaN b then ((b ||| quiet) &&& lane, snan)
  else if (f.isInf a && f.isInf b) || (f.isZero a && f.isZero b) then (sbit ||| infE ||| quiet, fIE)
  else if f.isInf a then (sgn ||| infE, de)
  else if f.isInf b then (sgn, de)
  else if f.isZero b then (sgn ||| infE, fZE)
  else if f.isZero a then (sgn, de)
  else
    let (ma, ea) := sig f a
    let (mb, eb) := sig f b
    let kk : Nat := 2 * f.mw + 4
    let n := ma <<< kk
    let q := n / mb
    let s := if n % mb == 0 then 0 else 1
    let (r, fl) := roundPack f rc neg (2 * q + s) (ea - eb - kk - 1)
    (r, fl ||| de)

/-- ⭐⭐ SUB-GROUP B3 — CVTSD2SS's LANE RULE AND FLAGS (SDM Vol. 2A CVTSD2SS: "Overflow, Underflow, Invalid,
Precision, Denormal"; Vol. 1 §4.8.3.5 and Table 4-7): the binary64 `x` as a binary32 under RC `rc`, in the low 32
bits of the result.
* **A NaN keeps its sign and the top 23 bits of its fraction, and is QUIETED** (bit 22 set). The payload's low 29
  bits are DROPPED, never rounded, and IE is raised on a signalling NaN (hwprobe's NARROW-NAN, D272).
* **±∞ and ±0 convert exactly** and raise nothing.
* Otherwise the value is rounded by `roundPack` at binary32, which raises OE with PE on overflow, UE with PE when the
  result is inexact and tiny AFTER rounding, and PE when it is inexact.
* **DE on a binary64 denormal** (hwprobe's DE-NARROW, D272), beside the UE and PE its rounding raises. Every binary64
  denormal lies far below binary32's least subnormal, so the result is ±0 or the least subnormal.
⚠️ `sig binary64` gives a significand below `2^53`, and `roundPack` clamps every discarding shift (D262 §3), so no
power above 256 is taken on any path. -/
def f64to32 (rc : Nat) (x : BitVec 64) : BitVec 64 × BitVec 32 :=
  let f := binary64
  let sgn : BitVec 64 := if f.sign x then 1 <<< 31 else 0
  if f.isNaN x then (sgn ||| 0x7FC00000 ||| (f.mant x >>> 29), if f.isSNaN x then fIE else 0)
  else if f.isInf x then (sgn ||| 0x7F800000, 0)
  else if f.isZero x then (sgn, 0)
  else
    let (m, e) := sig f x
    let (r, fl) := roundPack binary32 rc (f.sign x) m e
    (r, fl ||| (if f.isDenormal x then fDE else 0))

/-- ⭐⭐ CVTSI2SS / CVTSI2SD's RULE AT BOTH SOURCE WIDTHS (SDM Vol. 2B, CVTSI2SS /
CVTSI2SD): the source GPR read as a SIGNED integer of width 32 or 64 (`wide`),
rounded under MXCSR.RC into the destination format `f`.

This is `i32to64` generalised in the two directions B4 makes statable — the source
may be an int64, and the destination may be binary32.  `i32to64`'s own pairing
(int32 into binary64) is the ONE case that is exact at every rounding mode, which
is why the landed model could encode it with `toBinary64` and raise no flag.

⛔ `toBinary64` CANNOT SERVE HERE, and the reason is mechanical rather than
stylistic: its top-bit search is 32 bits wide (`31 - Value.clzN m 32`), so it
mis-encodes any magnitude at or above `2^32`.  The wide path must go through
`roundPack`, which takes a `Nat` significand at an unbounded exponent.  The same
fact is recorded in `Main.lean`'s `wrongCvtWholeRegister`, where it justifies a
WRONG model rather than this one.

⛔ THE MAGNITUDE OF INT_MIN is the negation read UNSIGNED at the source's own
width, so INT64_MIN's is `2^63` and INT32_MIN's is `2^31` — neither is a value of
its own signed type.  A model taking the magnitude as a signed value would have no
answer at either.  The sign and the magnitude are therefore taken at the SOURCE
width and only then widened, which is `i32to64`'s idiom one width up.

⚠️ PE IS THE ONLY FLAG THIS CAN RAISE, and that is STRUCTURAL rather than
asserted: an int64's magnitude is below both formats' overflow threshold and is
never tiny, so `roundPack`'s `bits < top` branch always holds and its `lead` test
is always false.  D274 corroborates PE-only on two vendors, 488/488 over 127 rows.

The flags come out of the SAME call as the value, so a result and its flags cannot
disagree about the rounding — the reason `varith` gives for the same shape. -/
def i2f (f : Fmt) (wide : Bool) (rc : Nat) (x : BitVec 64) : BitVec 64 × BitVec 32 :=
  let neg := if wide then x.getLsbD 63 else (x.setWidth 32).getLsbD 31
  let mag : BitVec 64 :=
    if wide then (if neg then -x else x)
    else
      let v := x.setWidth 32
      (if neg then -v else v).setWidth 64
  if mag == 0 then (0, 0)
  else roundPack f rc neg mag.toNat 0

/-! ### ⭐⭐⭐ SUB-GROUP B6a — CVTSD2SI / CVTSS2SI, THE ROUNDING CONVERSION TO AN INTEGER (D288).

`truncToInt`'s sibling that READS MXCSR.RC. The significand is placed as an integer the same way, and the part
shifted off rounds under `roundsUp`, which is `roundPack`'s own decision, so the four modes are stated once in this
file. The flags come out of the same pass: IE ALONE on a NaN, ±∞, or a ROUNDED result outside the destination's
range; otherwise PE iff anything was shifted off. No DE: the SDM lists Invalid and Precision only, and silicon
agrees on both vendors (D287 §4). -/

/-- ⭐⭐ CVTS?2SI's RULE (SDM Vol. 2A): the low `f`-format lane of `x` rounded to an integer under `rc` (0 nearest ·
1 down · 2 up · 3 zero), as a `w`-bit two's-complement integer zero-extended to 64 bits, with its flags.
* **±0 gives 0** with no flag; a denormal rounds like any other value (to 0, or to ±1 away from zero).
* **The range test is AFTER rounding**: binary64 `2^31 − 1/2` is in range at down and zero, and out at nearest and up.
* **The integer indefinite is `2^(w−1)`**, the sign bit alone, as `truncToInt`'s.
* ⛔ **No power above 256 on any path** (D262 §3): an exponent at or past `w` is out of range before any shift, and
  `shiftOut` clamps a long right shift, so a binary64 denormal's 1,074-bit shift never becomes a literal power. -/
def cvtToInt (f : Fmt) (w : Nat) (rc : Nat) (x : BitVec 64) : BitVec 64 × BitVec 32 :=
  let e := (f.expo x).toNat
  let ind : BitVec 64 := 1 <<< (w - 1)
  if e == 2 ^ f.ew - 1 || bias f + w ≤ e then (ind, fIE)
  else if f.isZero x then (0, 0)
  else
    let neg := f.sign x
    let m : Nat := (f.mant x).toNat + (if e == 0 then 0 else 2 ^ f.mw)
    let (q, r, half) := shiftOut m ((bias f + f.mw : Nat) - (max e 1 : Nat) : Int)
    let n := if roundsUp rc neg q r half then q + 1 else q
    if (if neg then n ≤ 2 ^ (w - 1) else n < 2 ^ (w - 1)) then
      let v := BitVec.ofNat 64 n
      ((if neg then ((-v).setWidth w).setWidth 64 else v), if r != 0 then fPE else 0)
    else (ind, fIE)

end SoftFloat
end X86
