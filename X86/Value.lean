/-
# X86.Value — the uniform 64-bit value representation

EVERY operand value in this model is a `BitVec 64` of which only the low
`sz.bits` are significant, with the width carried beside it as a `Size` datum.

WHY, since it is the decision the whole model rests on: the alternative — a
`BitVec sz.bits` indexed by the operand width — makes `step` a dependently-typed
function, and then every characterization lemma has to transport across width
equalities before it can say anything.  ACL2 x86isa makes the same choice for the
same reason (its register accessors are 64-bit and its `n08`/`n16`/`n32` families
truncate), and it costs exactly one invariant, stated and then discharged by
lemma: `Value.trunc sz` is idempotent and every read in this model is truncated.

⛔ AXIOM DISCIPLINE (TRUSTBASE.md, plan v1 §3.3).  Nothing in this file — or
anywhere in the `X86` library — uses `bv_decide`, `native_decide`, or `decide`
over a quantified bit index.  The routes here are `decide` on closed terms,
`simp`, and `omega`.  The CI gate is an ALLOWLIST of {propext, Classical.choice,
Quot.sound}, because Lean ≥ 4.29 mints a fresh per-computation axiom NAME for
each native evaluation and a denylist of `Lean.ofReduceBool` would miss them.

LANE. Personal lane, public sources only.  The SDM is a READING reference
(Vol. 1 §3.4.1.1 for the 32-bit zero-extension rule; Vol. 1 §3.4.3.1 for PF).
-/
import X86.Basic

namespace X86

/-- A machine value: 64 bits wide, of which the low `sz.bits` carry meaning. -/
abbrev Val := BitVec 64

namespace Size

/-- The all-ones mask of this width, as a 64-bit value. -/
def mask : Size → Val
  | .b => 0xFF
  | .w => 0xFFFF
  | .d => 0xFFFFFFFF
  | .q => 0xFFFFFFFFFFFFFFFF

/-- The index of the most-significant (sign) bit of this width. -/
def signBit : Size → Nat
  | .b => 7
  | .w => 15
  | .d => 31
  | .q => 63

theorem signBit_eq (sz : Size) : sz.signBit = sz.bits - 1 := by cases sz <;> rfl

theorem signBit_lt (sz : Size) : sz.signBit < sz.bits := by cases sz <;> decide

/-- THE bit-level fact this file rests on: a width mask is exactly the
characteristic function of "below the width".  One lemma, both directions, so no
later proof has to re-derive either half. -/
@[simp] theorem mask_getLsbD (sz : Size) (i : Nat) :
    sz.mask.getLsbD i = decide (i < sz.bits) := by
  have h : sz.mask.toNat = 2 ^ sz.bits - 1 := by cases sz <;> decide
  show sz.mask.toNat.testBit i = _
  rw [h, Nat.testBit_two_pow_sub_one]

theorem mask_getLsbD_high (sz : Size) (i : Nat) (h : sz.bits ≤ i) :
    sz.mask.getLsbD i = false := by simp; omega

theorem mask_getLsbD_low (sz : Size) (i : Nat) (h : i < sz.bits) :
    sz.mask.getLsbD i = true := by simp [h]

end Size

namespace Value

/-- Keep only the low `sz.bits` bits. -/
def trunc (sz : Size) (v : Val) : Val := v &&& sz.mask

/-- The sign bit of the `sz`-wide view of `v`. -/
def msb (sz : Size) (v : Val) : Bool := v.getLsbD sz.signBit

/-- Sign-extend an `sz`-wide value into all 64 bits.  P1 BATCH 7 needs this
because SAR propagates the sign, and the sign it propagates is the sign at the
OPERAND's width, not at 64. -/
def signExt (sz : Size) (v : Val) : Val :=
  if msb sz v then (trunc sz v) ||| (~~~ sz.mask) else trunc sz v

/-- ARITHMETIC right shift at width `sz`: the vacated high bits take the value of
the operand's sign bit (SDM Vol. 2A, SAL/SAR/SHL/SHR).  Sign-extending first and
truncating afterwards is what makes `sarb` fill from bit 7 rather than bit 63. -/
def sar (sz : Size) (v : Val) (n : Nat) : Val :=
  trunc sz ((signExt sz v).sshiftRight n)

/-- Sign-extend the low `sz.bits` of `v` to all 64 bits. -/
def sext (sz : Size) (v : Val) : Val :=
  if msb sz v then trunc sz v ||| ~~~sz.mask else trunc sz v

/-- Zero-extend.  The same operation as `trunc` at this representation, named
separately because the SDM's two rules read differently and a reader should be
able to see which one a definition meant. -/
def zext (sz : Size) (v : Val) : Val := trunc sz v

/-- Parity of the low EIGHT bits of a value — SDM Vol. 1 §3.4.3.1: PF is set
when the low-order byte of the result has an EVEN number of set bits, and this
is true at EVERY operand width, not only at `Size.b`.  Getting that wrong is the
classic parity bug, so the width is deliberately absent from this signature. -/
def parity8 (v : Val) : Bool :=
  !(v.getLsbD 0 ^^ v.getLsbD 1 ^^ v.getLsbD 2 ^^ v.getLsbD 3 ^^
    v.getLsbD 4 ^^ v.getLsbD 5 ^^ v.getLsbD 6 ^^ v.getLsbD 7)

/-- Is the `sz`-wide view of `v` zero? -/
def isZero (sz : Size) (v : Val) : Bool := trunc sz v == 0

/-- Unsigned interpretation of the `sz`-wide view. -/
def uval (sz : Size) (v : Val) : Nat := (trunc sz v).toNat

/-- Signed interpretation of the `sz`-wide view. -/
def sval (sz : Size) (v : Val) : Int :=
  let u : Int := (uval sz v : Nat)
  if msb sz v then u - ((2 ^ sz.bits : Nat) : Int) else u

/-! ### The truncation pack (plan v1 §3.7's "one-shot projection-lemma pack") -/

@[simp] theorem trunc_getLsbD (sz : Size) (v : Val) (i : Nat) :
    (trunc sz v).getLsbD i = (v.getLsbD i && decide (i < sz.bits)) := by
  simp [trunc]

theorem trunc_getLsbD_high (sz : Size) (v : Val) (i : Nat) (h : sz.bits ≤ i) :
    (trunc sz v).getLsbD i = false := by simp; omega

theorem trunc_getLsbD_low (sz : Size) (v : Val) (i : Nat) (h : i < sz.bits) :
    (trunc sz v).getLsbD i = v.getLsbD i := by simp [h]

@[simp] theorem trunc_trunc (sz : Size) (v : Val) :
    trunc sz (trunc sz v) = trunc sz v := by
  apply BitVec.eq_of_getLsbD_eq; intro i _; simp

@[simp] theorem trunc_q (v : Val) : trunc .q v = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [trunc_getLsbD]
  simp [hi]

@[simp] theorem msb_trunc (sz : Size) (v : Val) : msb sz (trunc sz v) = msb sz v := by
  simp [msb, sz.signBit_lt]

end Value

/-! ## Writing a narrow view of a 64-bit register

SDM Vol. 1 §3.4.1.1, read at the source and stated once here because it is the
single most-cited x86-64 asymmetry:

* a 64-bit write replaces the register;
* a **32-bit write ZERO-EXTENDS** into the upper 32 bits (this is the rule that
  makes `mov eax, eax` a real instruction);
* a 16-bit write **preserves** the upper 48 bits;
* an 8-bit write **preserves** the other 56 bits.

The high-byte registers AH/CH/DH/BH occupy bits 8..15 and are reachable only in
an encoding with NO REX prefix (Vol. 2A §2.2.1.2); they are a separate operand
*shape*, not a width, and so they are not a `Size`. -/
namespace Value

/-- Merge the low `sz.bits` of `v` into `old` under the x86-64 write rules. -/
def writeView (sz : Size) (old v : Val) : Val :=
  match sz with
  | .q => v
  | .d => trunc .d v                       -- ZERO-EXTENDS: upper 32 cleared
  | .w => (old &&& ~~~Size.mask .w) ||| trunc .w v
  | .b => (old &&& ~~~Size.mask .b) ||| trunc .b v

/-- Merge an 8-bit value into bits 8..15 (AH/CH/DH/BH). -/
def writeHigh8 (old v : Val) : Val :=
  (old &&& ~~~(Size.mask .b <<< 8)) ||| (trunc .b v <<< 8)

/-- Read bits 8..15 (AH/CH/DH/BH). -/
def readHigh8 (v : Val) : Val := trunc .b (v >>> 8)

@[simp] theorem writeView_q (old v : Val) : writeView .q old v = v := rfl

/-- The MERGE shape that both preserving widths share: keep `old` above the
width, take `v` below it.  Proven once, at an arbitrary bit index, and then both
`writeView` cases are this lemma by definitional unfolding. -/
theorem merge_getLsbD (sz : Size) (old v : Val) (i : Nat) :
    ((old &&& ~~~sz.mask) ||| trunc sz v).getLsbD i
      = (if i < sz.bits then v.getLsbD i else old.getLsbD i) := by
  by_cases hlt : i < 64
  · simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hlt,
      decide_true, Bool.true_and, Size.mask_getLsbD, trunc_getLsbD]
    by_cases h : i < sz.bits <;> simp [h]
  · rw [BitVec.getLsbD_of_ge _ i (by omega), BitVec.getLsbD_of_ge old i (by omega),
      BitVec.getLsbD_of_ge v i (by omega)]
    split <;> rfl

@[simp] theorem writeView_getLsbD_w (old v : Val) (i : Nat) :
    (writeView .w old v).getLsbD i = (if i < 16 then v.getLsbD i else old.getLsbD i) :=
  merge_getLsbD .w old v i

@[simp] theorem writeView_getLsbD_b (old v : Val) (i : Nat) :
    (writeView .b old v).getLsbD i = (if i < 8 then v.getLsbD i else old.getLsbD i) :=
  merge_getLsbD .b old v i

/-- The 32-bit write really does clear the upper half — the SDM rule as a
theorem rather than as a comment, and the reason `writeView` is not just `|||`. -/
theorem writeView_d_clears_high (old v : Val) (i : Nat) (h : 32 ≤ i) :
    (writeView .d old v).getLsbD i = false :=
  trunc_getLsbD_high .d v i (by simpa using h)

/-- A narrow write PRESERVES the bits above its width — for the two widths where
the SDM says so.  `.d` is deliberately excluded, because for `.d` the claim is
FALSE and that asymmetry is the whole point of the previous theorem. -/
theorem writeView_preserves_high (sz : Size) (h : sz = .w ∨ sz = .b)
    (old v : Val) (i : Nat) (hi : sz.bits ≤ i) :
    (writeView sz old v).getLsbD i = old.getLsbD i := by
  rcases h with h | h <;> subst h
  · have hi' : 16 ≤ i := hi
    rw [writeView_getLsbD_w, if_neg (by omega)]
  · have hi' : 8 ≤ i := hi
    rw [writeView_getLsbD_b, if_neg (by omega)]

/-- A narrow write DELIVERS the bits below its width. -/
theorem writeView_low (sz : Size) (h : sz = .w ∨ sz = .b)
    (old v : Val) (i : Nat) (hi : i < sz.bits) :
    (writeView sz old v).getLsbD i = v.getLsbD i := by
  rcases h with h | h <;> subst h
  · have hi' : i < 16 := hi
    rw [writeView_getLsbD_w, if_pos hi']
  · have hi' : i < 8 := hi
    rw [writeView_getLsbD_b, if_pos hi']

/-- Reading back what `writeHigh8` wrote. -/
@[simp] theorem readHigh8_writeHigh8 (old v : Val) :
    readHigh8 (writeHigh8 old v) = trunc .b v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [readHigh8, writeHigh8, trunc_getLsbD, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    Size.mask_getLsbD, Size.bits_b]
  by_cases h : i < 8
  · have h1 : 8 + i < 64 := by omega
    have h2 : ¬ (8 + i < 8) := by omega
    simp [h, h1, h2]
  · simp [h]

end Value
end X86
