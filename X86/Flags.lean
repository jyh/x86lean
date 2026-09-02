/-
# X86.Flags — the flag rules, as pure functions of the operands

Plan v1 §4.2 asks that every flag rule be cited to SDM + ACL2 x86isa + K.  ⚠️
STATUS, STATED HONESTLY RATHER THAN CLAIMED: the citations below are to the SDM,
which is the source read directly for this file.  The x86isa and K cross-reads
are an OPEN P0 item; what discharges them is not a comment but the DIFFERENTIAL
RUN (plan v1 §4.3, and the P0 exit criterion), which compares this file's
predictions against x86isa's executable model on every form.  A comment claiming
a cross-read that did not happen is worth less than nothing, so this file does
not carry any.

THE UNDEFINED BITS ARE NOT COMPUTED HERE.  Every function in this file is a
TOTAL, PURE function of its arguments; where the SDM says a flag is undefined,
the corresponding argument is passed IN by the caller, which drew it from the
oracle (`Cpu.undefBit`).  That is what keeps the undefined bits greppable — the
complete list of places this model declines to commit is the list of
`undefBit` call sites in `X86/Semantics.lean` — and it keeps these functions
free of the state, so `decide` can evaluate them in an anchor test.

SDM sections read for this file:
* Vol. 1 §3.4.3.1 (the status flags, and PF being the parity of the LOW BYTE);
* Vol. 2A, entries ADD, SUB, INC, DEC, NEG, NOT, AND, OR, XOR, CMP, TEST, SHL,
  SHR ("Flags Affected" in each).

LANE. Personal lane, public sources only.
-/
import X86.Syntax

namespace X86
namespace Flags

/-- SF, ZF and PF are the same function of the result for every instruction that
writes them.  PF is the parity of the LOW BYTE at every width. -/
def fromResult (sz : Size) (res : Val) (f : Flags) : Flags :=
  { f with
    sf := Value.msb sz res
    zf := Value.isZero sz res
    pf := Value.parity8 res }

/-- The auxiliary carry: the carry out of bit 3.  For both addition and
subtraction this is bit 4 of `a ⊕ b ⊕ result`, which is the standard identity
and holds because the low four bits of the sum are `a ⊕ b ⊕ carry_in` and the
carry into bit 4 is what distinguishes them. -/
def auxCarry (a b res : Val) : Bool := (a ^^^ b ^^^ res).getLsbD 4

/-! ### ADD (SDM Vol. 2A, ADD — "Flags Affected: The OF, SF, ZF, AF, CF, and PF
flags are set according to the result.") -/

def addResult (sz : Size) (a b : Val) : Val := Value.trunc sz (a + b)

/-- CF: the unsigned sum did not fit in `sz.bits` bits. -/
def addCF (sz : Size) (a b : Val) : Bool :=
  decide (2 ^ sz.bits ≤ Value.uval sz a + Value.uval sz b)

/-- OF: the two operands had the SAME sign and the result has the other one. -/
def addOF (sz : Size) (a b res : Val) : Bool :=
  (Value.msb sz a == Value.msb sz b) && (Value.msb sz res != Value.msb sz a)

def add (sz : Size) (a b : Val) (f : Flags) : Flags :=
  let res := addResult sz a b
  { fromResult sz res f with
    cf := addCF sz a b
    af := auxCarry a b res
    of := addOF sz a b res }

/-! ### SUB and CMP (SDM Vol. 2A, SUB and CMP; CMP is SUB with the result
discarded — "the result is discarded" is the entire difference). -/

def subResult (sz : Size) (a b : Val) : Val := Value.trunc sz (a - b)

/-- CF for subtraction is a BORROW: the unsigned minuend was smaller. -/
def subCF (sz : Size) (a b : Val) : Bool :=
  decide (Value.uval sz a < Value.uval sz b)

/-- OF: the operands had DIFFERENT signs and the result took the subtrahend's. -/
def subOF (sz : Size) (a b res : Val) : Bool :=
  (Value.msb sz a != Value.msb sz b) && (Value.msb sz res != Value.msb sz a)

def sub (sz : Size) (a b : Val) (f : Flags) : Flags :=
  let res := subResult sz a b
  { fromResult sz res f with
    cf := subCF sz a b
    af := auxCarry a b res
    of := subOF sz a b res }

/-! ### The logic group: AND, OR, XOR, TEST

SDM Vol. 2A, AND: "The OF and CF flags are cleared; the SF, ZF, and PF flags are
set according to the result.  The state of the AF flag is undefined."  OR, XOR
and TEST carry the identical sentence.  `afUndef` is the oracle bit. -/

def logic (sz : Size) (res : Val) (afUndef : Bool) (f : Flags) : Flags :=
  { fromResult sz res f with
    cf := false
    of := false
    af := afUndef }

/-! ### INC and DEC

SDM Vol. 2A, INC: "The CF flag is not affected."  Everything else behaves as an
ADD of 1 — and the fact that CF is PRESERVED rather than computed is the entire
reason `inc` is not `add reg, 1`, and the classic source of a wrong model. -/

def inc (sz : Size) (a : Val) (f : Flags) : Flags :=
  let res := addResult sz a 1
  { fromResult sz res f with
    af := auxCarry a 1 res
    of := addOF sz a 1 res }
    -- cf deliberately untouched: it is carried through from `f`.

def dec (sz : Size) (a : Val) (f : Flags) : Flags :=
  let res := subResult sz a 1
  { fromResult sz res f with
    af := auxCarry a 1 res
    of := subOF sz a 1 res }

/-! ### NEG

SDM Vol. 2A, NEG: "The CF flag set to 0 if the source operand is 0; otherwise it
is set to 1.  The OF, SF, ZF, AF, and PF flags are set according to the result." -/

def neg (sz : Size) (a : Val) (f : Flags) : Flags :=
  let res := subResult sz 0 a
  { fromResult sz res f with
    cf := !Value.isZero sz a
    af := auxCarry 0 a res
    of := subOF sz 0 a res }

/-! ### SHL and SHR

SDM Vol. 2A, SHL/SHR — the three separate undefined regions, each its own oracle
bit:

1. "The CF flag contains the value of the last bit shifted out of the
   destination operand; it is UNDEFINED for SHL and SHR instructions where the
   count is greater than or equal to the size (in bits) of the destination
   operand."
2. "The OF flag is affected only on 1-bit shifts... otherwise it is UNDEFINED."
3. "The AF flag is UNDEFINED" (for a non-zero count).

And the rule that governs all three: "If the count is 0, the flags are NOT
affected."  A masked count of zero leaves every flag alone even though the
unmasked count was not zero — `shl rax, 64` masks to 0 and touches nothing.

⚠️ THE DRAW ORDER IS PART OF THE MODEL and is fixed here: CF, then OF, then AF.
It decides which oracle bit lands in which flag, so a differential harness that
seeds the oracle must use the same order to reproduce a run.  It is stated in
`Semantics.lean` at the call site and in TRUSTBASE.md. -/

/-- The count mask: 6 bits at 64-bit operand size, 5 bits otherwise
(SDM Vol. 2A, SHL/SHR, "Description"). -/
def shiftCount (sz : Size) (c : BitVec 8) : Nat :=
  match sz with
  | .q => c.toNat % 64
  | _  => c.toNat % 32

/-- The flags after a shift with a NON-ZERO masked count `n`.
`cfU`, `ofU`, `afU` are the three oracle bits, used only where the SDM says
undefined. -/
def shiftFlags (k : ShiftKind) (sz : Size) (a res : Val) (n : Nat)
    (cfU ofU afU : Bool) (f : Flags) : Flags :=
  let cf : Bool :=
    if sz.bits ≤ n then cfU
    else match k with
      | .shl => a.getLsbD (sz.bits - n)   -- last bit shifted out of the top
      | .shr => a.getLsbD (n - 1)         -- last bit shifted out of the bottom
  let of : Bool :=
    if n = 1 then
      match k with
      | .shl => Value.msb sz res != cf    -- SDM: MSB(result) XOR CF
      | .shr => Value.msb sz a            -- SDM: the MSB of the ORIGINAL operand
    else ofU
  { fromResult sz res f with cf := cf, af := afU, of := of }

end Flags
end X86
