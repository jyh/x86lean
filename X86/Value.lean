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

/-- P1 BATCH 10: reverse the low `n` BYTES of a value (SDM Vol. 2A, BSWAP).

Written as a fold over byte positions rather than as a chain of shifts and
masks, because the chain has to be written once per width and the widths are
where this instruction is interesting: `bswapl` reverses FOUR bytes and then
zero-extends, `bswapq` reverses eight.  A per-width chain would put the width in
two places — the number of terms and the destination size — and they would be
free to disagree. -/
def byteRev (n : Nat) (v : Val) : Val :=
  (List.range n).foldl
    (fun acc i => acc ||| (((v >>> (8 * i)) &&& 0xFF) <<< (8 * (n - 1 - i)))) 0

/-- Byte-reverse the `sz`-wide view.

⚠️ THE CALLERS DISAGREE ABOUT WHICH WIDTHS ARE LEGAL, and the disagreement is in
the INSTRUCTIONS rather than here.  `BSWAP` is called only at `.d` and `.q`,
because the SDM leaves BSWAP with a 16-bit operand UNDEFINED and `step` declines
it; `MOVBE` (P1 batch 13) is called at `.w` as well, because MOVBE's 16-bit form
is defined and encodable.  So this function answers for w/l/q and the refusal
lives at each call site, where the reason for it differs.

⛔ THIS COMMENT USED TO READ "the model only ever calls this at `.d` and `.q`".
That was true when `bswap` had one caller and became false the moment `movbe`
arrived — the ordinary way a scope claim rots, and one no gate reads. -/
def bswap (sz : Size) (v : Val) : Val := byteRev sz.bytes (trunc sz v)

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

/-- ⭐ P1 BATCH 17: A NARROW WRITE READS BACK NARROW, WHATEVER WAS THERE — the
`sz`-wide view after a `sz`-wide write does not depend on the old contents.
Obvious at `.q` and `.d`, and the whole point at `.w` and `.b`, where
`writeView` MERGES: the merged bits all sit above the width, so `trunc` drops
exactly them.  Batch 17 needed it to say that IMUL's three-operand form ignores
its destination at every width rather than only at `.q`. -/
@[simp] theorem trunc_writeView (sz : Size) (old v : Val) :
    trunc sz (writeView sz old v) = trunc sz v := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  cases sz <;> simp only [trunc_getLsbD, Size.bits] <;>
    rcases Nat.lt_or_ge i 8 with hi | hi <;> rcases Nat.lt_or_ge i 16 with hj | hj <;>
    rcases Nat.lt_or_ge i 32 with hk | hk <;>
    simp [writeView_getLsbD_b, writeView_getLsbD_w, writeView_q, hi, hj, hk,
      writeView, Nat.not_lt.mpr] <;> omega

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

/-! ### P1 BATCH 14 — counting bits, and the two functions that are NOT each
other's mirror

`popcnt`, `lzcnt`, `tzcnt`, `bsf` and `bsr` all answer a question about WHICH
bits of the source are set, and the SDM answers it three different ways at a
zero source: `popcnt` says 0, `lzcnt`/`tzcnt` say the OPERAND WIDTH, and
`bsf`/`bsr` say the destination is UNDEFINED.  Each is written here as a total
function so that `step` never has to invent a value, and the undefined one is
handled in `step` by the oracle rather than by a made-up number here.

⚠️ ALL THREE RECURSE ON A FUEL ARGUMENT rather than on the value.  The kernel
must be able to REDUCE these — every characterization theorem below and every
coverage assertion is a `decide` — and structural recursion on `Nat` reduces
where well-founded recursion on a shrinking `BitVec` would not.  That is the
same reason `isInfixOfChars` exists in `Tests/Coverage.lean`. -/

/-- Set bits among the low `n`. -/
def popCountN (v : Val) : Nat → Nat
  | 0 => 0
  | n + 1 => (if v.getLsbD n then 1 else 0) + popCountN v n

/-- POPCNT: the number of set bits in the source at its operand width. -/
def popCount (sz : Size) (v : Val) : Nat := popCountN (trunc sz v) sz.bits

/-- Trailing zeros among the low `n` bits — `n` when all of them are clear.

⚠️ Scanning UPWARD from bit 0, so the `n` returned for an all-clear field is the
width itself, which is exactly what TZCNT is defined to return for a zero
source.  It is NOT a sentinel this model chose. -/
def ctzN (v : Val) : Nat → Nat
  | 0 => 0
  | n + 1 => if v.getLsbD 0 then 0 else 1 + ctzN (v >>> 1) n

/-- Leading zeros among the low `n` bits — `n` when all of them are clear. -/
def clzN (v : Val) : Nat → Nat
  | 0 => 0
  | n + 1 => if v.getLsbD n then 0 else 1 + clzN v n

/-- LZCNT: leading zeros at the operand width; the width itself for a zero
source (SDM Vol. 2A, LZCNT). -/
def clz (sz : Size) (v : Val) : Nat := clzN (trunc sz v) sz.bits

/-- TZCNT: trailing zeros at the operand width; the width itself for a zero
source (SDM Vol. 2A, TZCNT). -/
def ctz (sz : Size) (v : Val) : Nat := ctzN (trunc sz v) sz.bits

/-- BSF's index: the position of the LOWEST set bit.  ⚠️ Defined only where the
source is non-zero — at a zero source the SDM leaves the DESTINATION undefined
and `step` draws it from the oracle instead of calling this. -/
def bitScanForward (sz : Size) (v : Val) : Nat := ctz sz v

/-- BSR's index: the position of the HIGHEST set bit.  ⚠️ Note this is NOT
`clz`: LZCNT counts the zeros ABOVE the top set bit and BSR reports that bit's
INDEX, so they add up to the width minus one.  Writing `bsr` as `clz` (or the
reverse) is a model that is right at exactly one source value — `1` at `.b`,
where both answer 7 and 0 respectively — and the deliberately wrong model
`wrongBsrIsLzcnt` in `Main.lean` is that mistake, planted.  Defined only where
the source is non-zero. -/
def bitScanReverse (sz : Size) (v : Val) : Nat := sz.bits - 1 - clz sz v

/-- BLSI: isolate the lowest set bit — `(-src) AND src` (SDM Vol. 2A, BLSI),
at the operand width.  Zero in, zero out. -/
def blsi (sz : Size) (v : Val) : Val :=
  let a := trunc sz v
  trunc sz ((0 - a) &&& a)

/-! ### The double-width products and the dividing pair (P1 BATCH 17)

⭐ EVERY FUNCTION BELOW IS WRITTEN OVER `Nat` OR `Int` AND TRUNCATED AT THE END,
rather than over a `BitVec (2 * sz.bits)`.  The reason is the same one the file
header gives for `Val = BitVec 64`: a doubled width would be a dependent type
indexed by the operand size, and `step` would have to carry a proof to get at
its own result.  ⚠️ The cost is that these are the only arithmetic definitions
in the model that leave the bitvector world, so each one ends by coming back
through `trunc`, and the characterization lemmas in `X86/Theorems.lean` are what
say the round trip is faithful.

⚠️ AND THE SIGNED PRODUCT COMES BACK THROUGH `Int.emod`, NOT `Int.div`.  Lean's
`%` on `Int` is the EUCLIDEAN remainder, so `p % 2 ^ (2 * bits)` is in
`[0, 2 ^ (2 * bits))` for every `p` including a negative one — which is exactly
the two's-complement representation the machine holds.  Reaching for `Int.tdiv`
here would give the high half a sign that x86 does not put there. -/

/-- The unsigned double-width product, as `(low, high)` at the operand width.
MUL (SDM Vol. 2A, MUL). -/
def mulPair (sz : Size) (a b : Val) : Val × Val :=
  let p := uval sz a * uval sz b
  (BitVec.ofNat 64 (p % 2 ^ sz.bits), BitVec.ofNat 64 (p / 2 ^ sz.bits))

/-- The SIGNED double-width product, as `(low, high)` at the operand width, in
two's complement.  IMUL's one-operand form (SDM Vol. 2A, IMUL). -/
def imulPair (sz : Size) (a b : Val) : Val × Val :=
  let p : Int := sval sz a * sval sz b
  let n : Nat := (p % ((2 : Int) ^ (2 * sz.bits))).toNat
  (BitVec.ofNat 64 (n % 2 ^ sz.bits), BitVec.ofNat 64 (n / 2 ^ sz.bits))

/-- ⭐ IMUL's CF/OF RULE, WRITTEN ONCE AND SHARED BY ALL THREE OPERAND SHAPES.
"CF and OF are set when the signed integer value of the intermediate product
differs from the sign-extended operand-size-truncated product" (SDM Vol. 2A,
IMUL) — which is the same sentence for the one-, two- and three-operand forms,
and this is that sentence.

⚠️ NOT "the high half is non-zero", which is MUL's rule.  The two agree on
positive products and disagree on every negative one: `-1 * 1` at `.b` has high
half `0xFF`, and IMUL does not set CF for it.  A model that shared MUL's rule
here would be right on more than half of `adversarial` and wrong on the rest. -/
def imulOverflow (sz : Size) (a b : Val) : Bool :=
  sval sz a * sval sz b != sval sz (imulPair sz a b).1

/-- MUL's CF/OF rule: set exactly when the product does not fit the operand
width, i.e. when the high half is non-zero (SDM Vol. 2A, MUL). -/
def mulOverflow (sz : Size) (a b : Val) : Bool :=
  (mulPair sz a b).2 != 0

/-- The DIVIDEND, assembled from the high and low halves at the operand width.
⚠️ At `.b` the caller passes AH and AL rather than RDX and RAX — see
`Cpu.mdHi` and `Cpu.setMdPair` in `X86/Semantics.lean` for why that is the same
shape and not a special case. -/
def dividendU (sz : Size) (hi lo : Val) : Nat :=
  uval sz hi * 2 ^ sz.bits + uval sz lo

/-- The signed dividend: the same `2 * sz.bits` bit pattern, read as two's
complement. -/
def dividendS (sz : Size) (hi lo : Val) : Int :=
  let u : Int := (dividendU sz hi lo : Nat)
  if msb sz hi then u - ((2 ^ (2 * sz.bits) : Nat) : Int) else u

/-- DIV: `(quotient, remainder)` at the operand width, or `none` when the
instruction's meaning is #DE — a zero divisor, or a quotient too wide for the
destination (SDM Vol. 2A, DIV: "#DE — If the source operand (divisor) is 0 / If
the quotient is too large for the designated register").

⭐ THE REFUSAL IS PART OF THE FUNCTION AND NOT A CHECK BESIDE IT.  Returning
`Option` means a caller cannot compute a quotient without having decided what to
do about the fault, which is the property `step` needs: batch 12's `ud2` taught
that a form whose meaning is a fault must be modelled as one, and this is the
first form whose fault depends on the OPERANDS. -/
def divPairU (sz : Size) (hi lo d : Val) : Option (Val × Val) :=
  let dv := uval sz d
  if dv == 0 then none
  else
    let n := dividendU sz hi lo
    let q := n / dv
    if q ≥ 2 ^ sz.bits then none else some (BitVec.ofNat 64 q, BitVec.ofNat 64 (n % dv))

/-- IDIV: `(quotient, remainder)`, or `none` for #DE (SDM Vol. 2A, IDIV).

⚠️ THE QUOTIENT TRUNCATES TOWARD ZERO AND THE REMAINDER TAKES THE DIVIDEND'S
SIGN — `Int.tdiv`/`Int.tmod`, NOT `/` and `%`, which on `Int` in Lean are the
EUCLIDEAN pair and round the other way for a negative dividend.  `-7 / 2` is
`-3` on the machine and `-4` in Lean's `/`.  This one substitution is the whole
difference between IDIV and a plausible model of it, and it is invisible on
every non-negative dividend — which is most of `adversarial` at `.b`.

⚠️ AND THE RANGE CHECK IS ASYMMETRIC because two's complement is: the quotient
must lie in `[-2 ^ (bits - 1), 2 ^ (bits - 1) - 1]`, so `-2 ^ 63 / -1` faults
while `2 ^ 63 / -1`… cannot arise, the dividend being wider than the quotient. -/
def divPairS (sz : Size) (hi lo d : Val) : Option (Val × Val) :=
  let dv := sval sz d
  if dv == 0 then none
  else
    let n := dividendS sz hi lo
    let q := n.tdiv dv
    let lim : Int := 2 ^ (sz.bits - 1)
    if q < -lim || q > lim - 1 then none
    else some (BitVec.ofNat 64 ((q % (2 ^ sz.bits : Int)).toNat)
             , BitVec.ofNat 64 (((n.tmod dv) % (2 ^ sz.bits : Int)).toNat))

end Value
end X86
