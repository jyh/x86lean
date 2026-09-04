/-
# X86.Semantics — `step : Instr → Cpu → Cpu`

Plan v1 §3.0: a definitional, executable, SMALL-STEP OPERATIONAL semantics.
Each form is a TOTAL state transformer.  Totality is not achieved by inventing
behaviour: an instruction this model declines to give a meaning to sets `Cpu.ms`
and changes nothing else (the ACL2 x86isa model-state discipline).

WHAT MAKES IT AN INTERPRETER RATHER THAN A RELATION: `step` computes, so the
same definition that the theorems are about is the one the differential harness
RUNS against ACL2 x86isa and (P1) against real hardware.  A relational or
axiomatic semantics could not be differentially tested at all, and a separate
executable "reference" would be a second model to keep honest.

WHERE HOARE LOGIC LIVES: on top, never underneath.  The characterization lemmas
in `X86/Theorems.lean` have the shape `step i s = { s with … }`, which is
exactly what a machine-code Hoare triple (Myreen's `SPEC`) or a big-step block
semantics consumes.  Every such rule is a THEOREM about `step`, so any logic
layered on it is sound by construction.

⚠️ THE ORACLE DRAW ORDER IS PART OF THE MODEL.  A shift with a non-zero masked
count draws exactly THREE bits, in the order CF, OF, AF, whether or not each is
needed; the logic group draws exactly ONE (AF).  Fixing the COUNT as well as the
order is what makes the oracle cursor a deterministic function of the
instruction stream, which is what lets the harness replay a run.

LANE. Personal lane, public sources only.  SDM read per instruction, cited at
each case.
-/
import X86.Flags

namespace X86

/-- The EFFECTIVE ADDRESS — the offset within a segment — of a memory operand.
All arithmetic is `BitVec 64`, so it wraps at 2^64 exactly as 64-bit-mode
address computation does.  `nextRip` is the address of the FOLLOWING
instruction, which is what RIP-relative addressing is defined against (SDM
Vol. 2A §2.2.1.6).

⛔ NO SEGMENT BASE IS ADDED HERE.  This is the quantity `lea` writes, and the
separation is the whole content of P2 item 1's correctness risk: see
`Ea.addr`. -/
def Ea.offset (ea : Ea) (s : Cpu) (nextRip : BitVec 64) : Val :=
  if ea.ripRel then nextRip + ea.disp
  else
    let b := match ea.base with | some r => s.regs.get r | none => 0
    let i := match ea.index with | some r => s.regs.get r * ea.scale.toVal | none => 0
    b + i + ea.disp

/-- ⭐⭐ P2 ITEM 1: THE LINEAR ADDRESS A MEMORY ACCESS ACTUALLY USES — the
effective address plus the base of the segment the prefix selected (SDM Vol. 3A
§3.4, Figure 3-5).  In 64-bit mode only FS and GS have a base, so `Cpu.segBase`
is zero for every other case and this reduces to `Ea.offset` on every
instruction that carries no override — which is every vector this repository had
before this batch, and why not one of their results moves.

⛔⛔ AND THE POINT OF THERE BEING TWO FUNCTIONS IS `lea`, WHICH MUST NOT CALL
THIS ONE.  LEA computes the EFFECTIVE ADDRESS (SDM Vol. 2A, LEA), so a segment
prefix on a `lea` changes nothing; ACL2 x86isa agrees structurally — its
`x86-lea` uses `x86-effective-addr` and never calls `ea-to-la`, while every
memory read and write goes through `rme-size`/`wme-size`, which do.  Writing one
function and using it in both places is the defect this split exists to prevent,
and `leaq %fs:...` is a vector, so the differential run would see it.

⚠️ ONE DEPARTURE FROM x86isa, NAMED RATHER THAN LEFT TO BE FOUND: x86isa's
`ea-to-la` also requires the resulting LINEAR address to be canonical and faults
if it is not, for segmented and unsegmented accesses alike.  This model checks
canonicity on branch TARGETS only (D9) and on no data address at all — a
pre-existing gap that this batch does not widen and does not close.  It is
unreachable in this harness by construction rather than by luck, and
`segmentedAddressesAreCanonical` in `Tests/Coverage.lean` is the assertion that
says so over the whole vector × pre-state cross product; the day a swept segment
base or a large displacement makes it reachable, that theorem goes red before
the oracle does. -/
def Ea.addr (ea : Ea) (s : Cpu) (nextRip : BitVec 64) : Val :=
  -- ⚠️ MATCHED, NOT `s.segBase ea.seg + ea.offset s nextRip`.  The two are equal
  -- (`addr_eq_segBase_add` below proves it), but the summed form puts a
  -- `BitVec 64` ADDITION on the path of EVERY memory access in the model,
  -- including the hundreds that carry no override — and a `+ 0` the kernel must
  -- still reduce is not free.  Written as a sum, this batch blew the heartbeat
  -- limit on three pre-existing `bsf`/`bsr` frame proofs that had never been
  -- near it, before it had added a single instruction.  Matched, the
  -- unsegmented path is byte-for-byte the old `Ea.addr` and reduces exactly as
  -- it did; the cost lands only where the feature is used.  D8's kernel-cost
  -- discipline, arriving as a design constraint rather than a ceiling.
  match ea.seg with
  | none => ea.offset s nextRip
  | some g => s.segBase (some g) + ea.offset s nextRip

@[simp] theorem Ea.addr_of_no_seg (ea : Ea) (s : Cpu) (nr : BitVec 64) (h : ea.seg = none) :
    ea.addr s nr = ea.offset s nr := by
  simp [Ea.addr, h]

/-- `Ea.offset` does not read the segment field, stated so the LEA theorem can
use it rather than relying on a defeq the reader has to reconstruct. -/
@[simp] theorem Ea.offset_set_seg (ea : Ea) (g : Option Seg) (s : Cpu) (nr : BitVec 64) :
    Ea.offset { ea with seg := g } s nr = Ea.offset ea s nr := rfl

/-- The summed form, as a THEOREM rather than the definition, so the reading in
SDM Vol. 3A Figure 3-5 — linear address = segment base + effective address — is
still stated somewhere and is checked, without being what the kernel reduces. -/
theorem Ea.addr_eq_segBase_add (ea : Ea) (s : Cpu) (nr : BitVec 64) :
    ea.addr s nr = s.segBase ea.seg + ea.offset s nr := by
  cases h : ea.seg <;> simp [Ea.addr, h]

/-- CANONICAL ADDRESS (SDM Vol. 1 §3.3.7.1).  In 64-bit mode only the low 48
bits of a linear address are implemented; bits 63:48 must be a sign extension of
bit 47.  A branch to a non-canonical target raises #GP(0) (SDM Vol. 2A, JMP and
CALL, "64-Bit Mode Exceptions").

⭐ THIS PREDICATE EXISTS BECAUSE THE DIFFERENTIAL RUN FOUND ITS ABSENCE.  The
first run against ACL2 x86isa produced 80 unexplained disagreements, every one
of them an indirect `jmp` or `call` to a non-canonical target: this model set
RIP to it, and x86isa raised #GP.  No anchor and no characterization theorem
could have caught that — the model was self-consistently wrong, which is exactly
the failure a second model is for. -/
def canonical (v : BitVec 64) : Bool :=
  -- bits 63:47 are all equal: shifting them down leaves all-zeros or all-ones
  (v >>> 47) == 0 || (v >>> 47) == 0x1FFFF

/-- ⭐ SIXTEEN-BYTE ALIGNMENT: the predicate `movdqa` faults on and `movdqu` does
not (SDM Vol. 2B, MOVDQA).  It lives beside `canonical` because they are the same
KIND of thing — a property of a computed address that decides whether the access
happens at all — and neither is a property of the `Cpu`. -/
def aligned16 (a : BitVec 64) : Bool := (a &&& 0xF) == 0

namespace Cpu

/-- Set RIP to a branch target, CHECKING that the target is canonical.

A non-canonical target HALTS this model rather than raising #GP, because
exceptions need the fault machinery that system mode brings and system mode is a
v0.x non-goal (plan v1 §1).  Halting is the honest answer: the model declines to
say what happens, which is different from — and much safer than — quietly
jumping somewhere impossible.

⚠️ NAMED GAP, since it is now the only unchecked RIP write: the FALL-THROUGH
`rip + len` is not checked.  x86isa checks it too (`:rip-increment-error`).  It
is unreachable in the P0 vectors (RIP is 0x400000 and instructions are short) so
the differential run has not exercised it, and an unexercised fix is a guess —
it is recorded in docs/DECISIONS.md as a P1 item rather than written blind. -/
def setRipChecked (s : Cpu) (v : BitVec 64) : Cpu :=
  if canonical v then { s with rip := v }
  else s.halt (.unimplemented "non-canonical branch target (#GP(0) in hardware)")

/-- Read an operand at width `sz`. -/
def readOperand (s : Cpu) (sz : Size) (nextRip : BitVec 64) : Operand → Val
  | .reg r h8 => s.getReg sz r h8
  | .mem ea => s.readMem sz (ea.addr s nextRip)
  | .imm v => Value.trunc sz v

/-- Write an operand at width `sz`.  An immediate destination cannot be
encoded, so it stops the model rather than being silently dropped. -/
def writeOperand (s : Cpu) (sz : Size) (nextRip : BitVec 64) : Operand → Val → Cpu
  | .reg r h8, v => s.setReg sz r v h8
  | .mem ea, v => s.writeMem sz (ea.addr s nextRip) v
  | .imm _, _ => s.halt (.illegalOperands "immediate destination")

/-- Draw `n` oracle bits at once, in order, as a list.  Used so a case can name
its draws positionally and the COUNT is visible at the call site. -/
def undefBits (s : Cpu) : Nat → List Bool × Cpu
  | 0 => ([], s)
  | n + 1 =>
    let (b, s₁) := s.undefBit
    let (bs, s₂) := s₁.undefBits n
    (b :: bs, s₂)

end Cpu

/-- Two memory operands cannot be encoded in one instruction: there is one
ModR/M byte (SDM Vol. 2A §2.1.5). -/
def wellFormed2 (dst src : Operand) : Bool := !(dst.isMem && src.isMem)

namespace Cpu

/-- The stack pointer, and the two stack primitives.  In 64-bit mode the stack
pointer moves by the OPERAND size (SDM Vol. 2A, PUSH: "in 64-bit mode the
default operand size is 64 bits"), which is why `sz` is threaded rather than
assumed. -/
def push (s : Cpu) (sz : Size) (v : Val) : Cpu :=
  let sp := s.regs.get .rsp - BitVec.ofNat 64 sz.bytes
  (s.writeMem sz sp v).setReg .q .rsp sp

def popValue (s : Cpu) (sz : Size) : Val × Cpu :=
  let sp := s.regs.get .rsp
  let v := s.readMem sz sp
  (v, s.setReg .q .rsp (sp + BitVec.ofNat 64 sz.bytes))

end Cpu

/-- P1 BATCH 14: BSF and BSR, which differ in ONE expression.

⭐ THEY ARE ONE FUNCTION BECAUSE EVERYTHING THAT IS SUBTLE ABOUT THEM IS SHARED:
five undefined flags drawn in a fixed order, ZF from the SOURCE, and the
UNDEFINED DESTINATION at a zero source.  `rev` selects which index the non-zero
case reports.  Writing the two arms out separately would have duplicated the
undefined-destination branch — the one thing in this batch that had never been
written before — and a duplicate born in agreement diverges on the next edit.

⚠️ It is also what lets the characterization theorems reduce: a combined
`| .bsf | .bsr =>` arm inside `step`'s match compiles to a matcher that does NOT
unfold for either constructor, so `step_bsf_zf` could not be proved through it. -/
def bitScanStep (rev : Bool) (sz : Size) (dst : GPR) (a : Val)
    (nr : BitVec 64) (s : Cpu) : Cpu :=
  let (cfU, s) := s.undefBit
  let (pfU, s) := s.undefBit
  let (afU, s) := s.undefBit
  let (sfU, s) := s.undefBit
  let (ofU, s) := s.undefBit
  let s := s.setFlags (Flags.bitScan sz a cfU pfU afU sfU ofU s.flags)
  if Value.isZero sz a then
    -- the SDM's "the content of the destination operand is undefined", drawn
    -- rather than invented.  `sz.bits` bits, so the draw is the operand's width.
    let (u, s) := s.undefVal sz.bits
    (s.setReg sz dst u).setRip nr
  else
    let idx := if rev then Value.bitScanReverse sz a else Value.bitScanForward sz a
    (s.setReg sz dst (BitVec.ofNat 64 idx)).setRip nr

/-- ⭐ P1 BATCH 16: ONE ITERATION OF A STRING OPERATION, WITHOUT THE RIP WRITE.

This is P1 batch 15's `.strop` body verbatim, with the single `setRip nr` at the
end of each arm lifted out to the caller.  It is factored rather than copied
because batch 16 needs the SAME five iterations under a repeat prefix, and a
second copy of five subtly-ordered arms — the access-before-update rule, the
`.q` pointer write against the `sz` data access, `cmps`'s reversed operand order
— is five chances for the two copies to drift.  ⚠️ The refactor is guarded: the
twenty batch-15 vectors and their characterization lemmas run against it
unchanged, so a slip here is a RED differential and not a silent regression.

⛔ IT DELIBERATELY DOES NOT TOUCH RIP.  Both callers write RIP exactly once and
explicitly, so "which address this instruction leaves behind" is a decision
visible at the call site rather than an absence to be inferred.  Batch 16 is the
first form in this model whose RIP is sometimes its OWN address, and an
implicit-fallthrough spelling of that would be indistinguishable from a
forgotten write. -/
def stringIter (k : StringOp) (sz : Size) (s : Cpu) : Cpu :=
  let step : BitVec 64 := BitVec.ofNat 64 sz.bytes
  let d : BitVec 64 := if s.flags.df then 0 - step else step
  let si := s.regs.get .rsi
  let di := s.regs.get .rdi
  match k with
  | .movs =>
      let v := s.readMem sz si
      let s := s.writeMem sz di v
      ((s.setReg .q .rsi (si + d)).setReg .q .rdi (di + d))
  | .stos =>
      let v := s.getReg sz .rax
      let s := s.writeMem sz di v
      s.setReg .q .rdi (di + d)
  -- ⚠️ LODS WRITES THE ACCUMULATOR THROUGH THE ORDINARY WIDTH RULE, so
  -- `lodsl` ZERO-EXTENDS into RAX while `lodsw` and `lodsb` MERGE (SDM
  -- Vol. 1 §3.4.1.1).  This is the one place in the group where `setReg`'s
  -- width behaviour is wanted rather than bypassed.
  | .lods =>
      let v := s.readMem sz si
      let s := s.setReg sz .rax v
      s.setReg .q .rsi (si + d)
  -- ⛔ SOURCE MINUS DESTINATION: `[RSI] − [RDI]`, not the AT&T print order.
  | .cmps =>
      let a := s.readMem sz si
      let b := s.readMem sz di
      let s := s.setFlags (Flags.sub sz a b s.flags)
      ((s.setReg .q .rsi (si + d)).setReg .q .rdi (di + d))
  -- SCAS is `RAX − [RDI]`, and only RDI moves.
  | .scas =>
      let a := s.getReg sz .rax
      let b := s.readMem sz di
      let s := s.setFlags (Flags.sub sz a b s.flags)
      s.setReg .q .rdi (di + d)


/-! ### The double-width accumulator pair (P1 BATCH 17)

⭐ THE PAIR IS ADDRESSED THROUGH TWO FUNCTIONS AND NOT WRITTEN OUT AT FOUR CALL
SITES, because the `.b` asymmetry is the whole difficulty and it should exist in
exactly one place.  "byte → AX, word → DX:AX, doubleword → EDX:EAX, quadword →
RDX:RAX" (SDM Vol. 2A, MUL, Table 3-x): at three widths the high half is RDX and
at the fourth it is **AH, the high byte of the SAME register the low half is
in**.  Both functions are total and neither has a special case a caller can
forget. -/
namespace Cpu

/-- The HIGH half of the accumulator pair at this width: `AH` at `.b`, the
`sz`-wide view of RDX otherwise. -/
def mdHi (s : Cpu) (sz : Size) : Val :=
  match sz with
  | .b => s.getReg .b .rax true
  | _ => s.getReg sz .rdx

/-- Write the pair: `lo` to the accumulator, `hi` to AH at `.b` and to RDX
otherwise.  ⚠️ The two writes go to the SAME register at `.b`, which is why the
low half is written first and the high half merges into the result — the other
order would leave AL holding the low bits of the high half. -/
def setMdPair (s : Cpu) (sz : Size) (lo hi : Val) : Cpu :=
  match sz with
  | .b => (s.setReg .b .rax lo).setReg .b .rax hi true
  | _ => (s.setReg sz .rax lo).setReg sz .rdx hi

end Cpu

/-! ## The packed (SIMD) operations -/

/-- One lane of a packed operation, folded from the top down.  ⚠️ `n` is the lane
COUNT and is never written by a caller: `vlanes` derives it. -/
private def vlanesAux (w : Nat) (f : BitVec w → BitVec w → BitVec w)
    (a b : BitVec 128) : Nat → BitVec 128
  | 0 => 0
  | n + 1 =>
      (vlanesAux w f a b n) |||
        (((f (a.extractLsb' (n * w) w) (b.extractLsb' (n * w) w)).setWidth 128) <<< (n * w))

/-- ⭐⭐ THE PACKED COMBINATOR.  A packed operation applies `f` to each aligned
`w`-bit lane INDEPENDENTLY: no carry, no borrow and no flag crosses a lane
boundary (SDM Vol. 2B, PADDB/PADDW/PADDD/PADDQ — "the instructions do not record
a carry").  That independence is the whole content of "packed", and writing it
as one combinator rather than eight open-coded loops is what makes it checkable.

⚠️ **THE LANE COUNT IS DERIVED FROM THE WIDTH, NOT WRITTEN BESIDE IT.**  A first
draft passed the count as an argument — `vlanes 32 (· + ·) a b 4` — which is a
width and a count side by side, i.e. two sources for one fact, and the wrong pair
is a silently truncated register rather than a type error. `128 / w` cannot
disagree with `w`. -/
def vlanes (w : Nat) (f : BitVec w → BitVec w → BitVec w) (a b : BitVec 128) : BitVec 128 :=
  vlanesAux w f a b (128 / w)

/-- One interleaved PAIR of an unpack, folded from the top down.  Each pair is
`2*w` bits: the DESTINATION's lane low, the SOURCE's lane high — which is the
order SDM Vol. 2B gives and the order objdump prints
(`xmm0 = xmm0[0],xmm1[0],xmm0[1],xmm1[1],…`). -/
private def vunpackAux (w base : Nat) (dst src : BitVec 128) : Nat → BitVec 128
  | 0 => 0
  | i + 1 =>
      (vunpackAux w base dst src i)
        ||| (((dst.extractLsb' ((base + i) * w) w).setWidth 128) <<< (2 * i * w))
        ||| (((src.extractLsb' ((base + i) * w) w).setWidth 128) <<< ((2 * i + 1) * w))

/-- ⭐⭐ THE UNPACK COMBINATOR.  `hi` chooses which half of each operand is
consumed, and — as with `vlanes` — the COUNT is DERIVED rather than passed: an
unpack at lane width `w` produces `128 / (2*w)` pairs and consumes exactly that
many lanes from each operand, so the count and the base cannot disagree with the
width. -/
def vunpack (w : Nat) (hi : Bool) (dst src : BitVec 128) : BitVec 128 :=
  let pairs := 128 / (2 * w)
  vunpackAux w (if hi then pairs else 0) dst src pairs

/-- One lane of a UNARY packed operation, folded from the top down.  ⚠️ `n` is
the lane COUNT and is never written by a caller: `vlanes1` derives it, for the
reason `vlanes` does. -/
private def vlanes1Aux (w : Nat) (f : BitVec w → BitVec w) (a : BitVec 128) :
    Nat → BitVec 128
  | 0 => 0
  | n + 1 =>
      (vlanes1Aux w f a n) |||
        (((f (a.extractLsb' (n * w) w)).setWidth 128) <<< (n * w))

/-- ⭐⭐ THE UNARY PACKED COMBINATOR, and the reason it is not `vlanes` with a
constant second operand.

A packed SHIFT applies ONE count to every lane.  `vlanes` pairs lane `i` of `a`
with lane `i` of `b`, so expressing a shift through it would mean broadcasting
the count into all sixteen lanes first — which is a `BitVec 128` the SDM never
mentions, is wrong at any lane width where the count does not fit, and would make
the saturation rule below apply per lane to a value that has already been
truncated.  The count is a Nat here and stays one. -/
def vlanes1 (w : Nat) (f : BitVec w → BitVec w) (a : BitVec 128) : BitVec 128 :=
  vlanes1Aux w f a (128 / w)

/-- ⭐⭐⭐ ONE LANE OF A PACKED SHIFT — THE SATURATING COUNT RULE, WHICH IS THE
WHOLE CONTENT OF THE GROUP (SDM Vol. 2B, PSLLW/PSRLW/PSRAW and their D and Q
forms).

A count at or above the lane width does NOT wrap and does not shift:

  * a LOGICAL shift, either direction, sets the lane to **all 0s**;
  * an ARITHMETIC right shift fills the lane with **the initial value of its own
    sign bit** — all 1s for a negative lane, all 0s for a non-negative one.

⛔⛔ **THE GUARD IS NOT A CONVENIENCE AND IT IS NOT REDUNDANT.**  Lean's own
`BitVec` shifts already saturate this way, so the two right-shift branches would
be correct without it — and the LEFT one would not merely be slow, it would
CRASH.  `x <<< (4294967299 : Nat)` — the exact count `psllw %xmm1,%xmm0` reads
when the count register's low quadword is 2^32 + 3 — is `INTERNAL PANIC:
Nat.shiftl exponent is too big`, measured on this toolchain in BOTH TIERS: the
interpreter (`#eval`) and the KERNEL (`by decide`).  So the guard must
short-circuit BEFORE the shift, and it is the left shift alone that needs it,
which is exactly the asymmetry that would let a partial repair look complete:
every `psrl`/`psra` vector would pass while `psll` at a large register count
took down the build.  `scripts/shift_guard_redprobe.sh` plants the unguarded
spelling and requires the panic — it cannot be a Lean red arm, because a
declaration that panics kills the process rather than failing to elaborate.

⚠️ Written uniformly over the three operations even though two do not need it,
because the SDM states the rule for all three and the code is where a reader
looks for it.  A guard present only where it is load-bearing would read as an
optimisation rather than as the architecture. -/
def vshiftLane (op : VShiftOp) (w : Nat) (x : BitVec w) (cnt : Nat) : BitVec w :=
  if cnt ≥ w then
    match op with
    | .sll | .srl => 0
    -- all sign bits: `-1` is `allOnes` at every width this is called at.
    | .sra => if x.msb then -1 else 0
  else
    match op with
    | .sll => x <<< cnt
    | .srl => x >>> cnt
    | .sra => x.sshiftRight cnt

/-- The packed shifts.  ⚠️ NO FLAG IS WRITTEN — "Flags Affected: None" for every
entry in the group, as for `vbinApply`.

⚠️ THE LANE COUNT IS DERIVED FROM THE WIDTH by `vlanes1`, never written here. -/
def vshiftApply (op : VShiftOp) (w : VShiftW) (a : BitVec 128) (cnt : Nat) :
    BitVec 128 :=
  match w with
  | .w8  => vlanes1 8  (fun x => vshiftLane op 8  x cnt) a
  | .w16 => vlanes1 16 (fun x => vshiftLane op 16 x cnt) a
  | .w32 => vlanes1 32 (fun x => vshiftLane op 32 x cnt) a
  | .w64 => vlanes1 64 (fun x => vshiftLane op 64 x cnt) a

/-- ⭐⭐⭐ `pslldq` / `psrldq` — THE WHOLE-REGISTER BYTE SHIFT, which is not a
packed operation and does not go through `vlanes1` at all.

⛔ Routing it through the lane combinator would be a claim that the SDM defines
it lane-wise, which it does not: it crosses every lane boundary by construction.
That is the same reason `vbinApply` keeps `pxor`/`pand`/`por` out of `vlanes`.

⚠️ THE COUNT IS IN BYTES AND SATURATES AT 16, not at 128.  `pslldq $0x14` zeroes
the register.  The guard is load-bearing here for the same reason it is in
`vshiftLane`, one step weaker: an immediate count cannot exceed 255, so
`8 * cnt` cannot reach the panic — but without the guard a count of 16..255
would still be a shift of 128..2040 bits, which Lean's `BitVec` truncates to the
right answer by luck rather than by the rule being written down. -/
def vshiftdqApply (left : Bool) (a : BitVec 128) (cnt : Nat) : BitVec 128 :=
  if cnt > 15 then 0
  else if left then a <<< (8 * cnt) else a >>> (8 * cnt)

/-- One selected lane of a permute, folded from the top down.  `base` is the
lane index the group starts at — 0 for `pshufd` and `pshuflw`, 4 for `pshufhw` —
and it offsets BOTH the source lane read and the destination lane written, which
is what makes one recursion serve all three kinds. -/
private def vselectAux (w : Nat) (src : BitVec 128) (sel base : Nat) :
    Nat → BitVec 128
  | 0 => 0
  | i + 1 =>
      (vselectAux w src sel base i)
        ||| (((src.extractLsb' ((base + (sel >>> (2 * i)) % 4) * w) w).setWidth 128)
              <<< ((base + i) * w))

/-- ⭐⭐ THE PERMUTE COMBINATOR — and the count it folds over comes from a
DIFFERENT place than every other combinator here.

⛔⛔ **`vlanes` DERIVES ITS COUNT FROM THE LANE WIDTH (`128 / w`); THIS ONE
CANNOT, AND TAKING THE REFLEX WOULD BE WRONG FOR BOTH WORD FORMS.**  A permute's
count is a property of the SELECTOR: an 8-bit immediate holds exactly four 2-bit
fields, so exactly four lanes are written — four of four at `w = 32`, and four of
EIGHT at `w = 16`, where the other four are copied through untouched.  `128 / 16`
is 8 and would permute the whole register, silently destroying the half
`pshuflw`/`pshufhw` are defined to preserve.

⇒ The literal 4 here is `8 / 2` — the immediate's width over a field's width —
and it is written once, in the one place the selector is decoded. -/
def vselect (w : Nat) (src : BitVec 128) (sel base : Nat) : BitVec 128 :=
  vselectAux w src sel base 4

/-- The permute group (SDM Vol. 2B, PSHUFD/PSHUFLW/PSHUFHW).

⚠️ **NO ARGUMENT IS THE DESTINATION'S OLD VALUE.**  Every lane of the result comes
from `src`: the permuted ones by selection, the untouched quadword by a copy.
A model that preserved the destination's other half instead — the reflex from
`vmovs`'s merge rule — is bit-identical to this one on every vector whose
destination already holds its source.

⚠️ NO FLAG IS WRITTEN ("Flags Affected: None" for all three). -/
def vshufApply (k : VShufKind) (src : BitVec 128) (sel : BitVec 8) : BitVec 128 :=
  match k with
  | .d  => vselect 32 src sel.toNat 0
  -- ⭐ THE TWO WORD FORMS ARE A SELECTION **OR-ED WITH A COPY**, and the two
  -- halves are disjoint by construction: `vselect 16 … 0` writes only lanes 0-3
  -- (bits 63:0) and `vselect 16 … 4` only lanes 4-7 (bits 127:64), so the `|||`
  -- cannot collide with the quadword beside it.
  | .lw => vselect 16 src sel.toNat 0 ||| ((src >>> 64) <<< 64)
  | .hw => vselect 16 src sel.toNat 4 ||| ((src <<< 64) >>> 64)

/-- The packed binary operations.  ⚠️ NO FLAG IS WRITTEN BY ANY OF THEM — SDM
Vol. 2B gives "Flags Affected: None" for every entry here, and the easiest way to
get a packed operation wrong is to reach for `BinKind`'s flag machinery by
analogy.  `step`'s arm below writes XMM and RIP and nothing else. -/
def vbinApply (k : VBinKind) (a b : BitVec 128) : BitVec 128 :=
  match k with
  -- The bitwise trio: lane-independent, so they do not go through `vlanes` at
  -- all.  Routing them through a one-lane call would be a claim that the SDM
  -- defines them lane-wise, which it does not.
  | .xor  => a ^^^ b
  | .and  => a &&& b
  | .or   => a ||| b
  | .addb => vlanes 8  (· + ·) a b
  | .addw => vlanes 16 (· + ·) a b
  | .addd => vlanes 32 (· + ·) a b
  | .addq => vlanes 64 (· + ·) a b
  | .subb => vlanes 8  (· - ·) a b
  | .subw => vlanes 16 (· - ·) a b
  | .subd => vlanes 32 (· - ·) a b
  | .subq => vlanes 64 (· - ·) a b
  -- ⭐ THE UNPACKS: `a` is the DESTINATION and takes the low half of each pair.
  | .unpcklb => vunpack 8  false a b
  | .unpcklw => vunpack 16 false a b
  | .unpckld => vunpack 32 false a b
  | .unpcklq => vunpack 64 false a b
  | .unpckhb => vunpack 8  true  a b
  | .unpckhw => vunpack 16 true  a b
  | .unpckhd => vunpack 32 true  a b
  | .unpckhq => vunpack 64 true  a b

/-- The small-step transition.  A stopped model does not move. -/
def step (i : Instr) (s : Cpu) : Cpu :=
  if s.stopped then s else
  -- ⭐⭐ P2 ITEM 2: THE LOCK WELL-FORMEDNESS RULE, CHECKED ONCE AND BEFORE THE
  -- MATCH.  A `lock` on a form the SDM does not list is #UD on real silicon
  -- (SDM Vol. 2A, "LOCK"), and it is `byDesign` rather than `unimplemented`
  -- here for the reason batch 12 recorded for `ud2`: the instruction is fully
  -- modelled, and what it is modelled as is a FAULT.  Filing it under
  -- `unimplemented` would put a covered form in the `T-absent` tier and make
  -- the fidelity table lie in the one direction it exists to prevent.
  --
  -- ⚠️ BEFORE THE MATCH, not inside each case: there are nineteen lockable
  -- forms and a check per case is nineteen chances to forget one, which is
  -- exactly the shape D29 found in the selftest's two drifting lists.  One
  -- check, over the operand walk every other consumer of the AST already uses.
  if i.op.lockIllegal then
    s.halt (.byDesign "lock prefix on a form the SDM does not permit it on (#UD)")
  else
  -- the address of the NEXT instruction: what RIP-relative addressing and every
  -- relative branch are defined against.
  let nr : BitVec 64 := s.rip + BitVec.ofNat 64 i.len
  match i.op with

  -- ⭐⭐⭐ MOVDQA / MOVDQU, register to register — THE FIRST INSTRUCTION IN THIS
  -- MODEL THAT WRITES AN XMM REGISTER.  Until this arm existed, `Cpu.xmm` was a
  -- channel every differential case reported and no instruction could move, so
  -- the comparator was watching sixteen constants and agreeing about them (D85
  -- said so in as many words).  This is the line that makes that claim non-vacuous.
  --
  -- ⚠️ `aligned` IS IGNORED HERE, ON PURPOSE.  Between two registers there is no
  -- address, so the rule that separates MOVDQA from MOVDQU has nothing to apply
  -- to (SDM Vol. 2B, MOVDQA: the alignment requirement is stated of a MEMORY
  -- operand).  This is a claim about the architecture, so it is a theorem —
  -- `vmov_aligned_irrelevant` — and not this comment.
  | .vmov _ dst src =>
      (s.setXmm dst (s.getXmm src)).setRip nr

  -- PADD* / PSUB* / PXOR / PAND / POR (SDM Vol. 2B).  DEST := DEST op SRC, and
  -- "Flags Affected: None" — the flags are not read and not written.
  | .vbin k dst src =>
      (s.setXmm dst (vbinApply k (s.getXmm dst) (s.getXmm src))).setRip nr

  -- ⭐⭐⭐ MOVDQA / MOVDQU AT MEMORY — the forms where `aligned` finally bites.
  --
  -- ⛔ AN UNALIGNED `movdqa` IS #GP(0) (SDM Vol. 2B, MOVDQA), and this model
  -- HALTS on it with `byDesign` rather than `unimplemented`.  The distinction is
  -- D34's and it decides a coverage TIER: `unimplemented` means "this model
  -- cannot say", which would file a fully-modelled form under `T-absent`;
  -- `byDesign` means "this model says: it faults", which is the true claim here
  -- and is exactly what `lockIllegal` already does one screen up for a `lock` on
  -- a form the SDM does not permit it on.
  --
  -- ⚠️ THE ALIGNMENT IS CHECKED ON THE LINEAR ADDRESS `Ea.addr` PRODUCES, not on
  -- the displacement or on the base register.  With a segment base in play those
  -- differ, and it is the address the machine actually accesses that hardware
  -- checks.
  | .vload k dst ea =>
      let a := ea.addr s nr
      if k.aligned && !aligned16 a then
        s.halt (.byDesign "an aligned 128-bit move at an address that is not 16-byte aligned (#GP(0))")
      else (s.setXmm dst (s.readMem128 a)).setRip nr

  -- ⭐⭐⭐ MOVD / MOVQ ACROSS THE REGISTER FILES (SDM Vol. 2B, MOVD/MOVQ).
  --
  -- ⚠️ BOTH DIRECTIONS ZERO WHAT THEY DO NOT WRITE, at two different
  -- granularities, and neither zeroing is optional:
  --   * into XMM, bits above the written width are CLEARED — `movd %ecx,%xmm0`
  --     leaves 127:32 zero, it does not merge into whatever was there;
  --   * out of XMM, the GPR write is an ordinary one, so `.d` zero-extends to 64
  --     by the same rule as every other form here (SDM Vol. 1 §3.4.1.1), which
  --     `Cpu.setReg` already implements — there is no special case for it.
  | .vmovg toXmm sz x r =>
      if toXmm then
        (s.setXmm x ((s.getReg sz r).setWidth 128)).setRip nr
      else
        (s.setReg sz r ((s.getXmm x).setWidth 64)).setRip nr

  -- ⭐ `movq %xmm1, %xmm0` — the LOW QUADWORD, with the upper one ZEROED.  This
  -- is the form that is NOT `movdqa` at a narrower width: `vmov` copies 128 bits
  -- and preserves nothing because there is nothing left over; this one has 64
  -- bits left over and CLEARS them.
  | .vmovq dst src =>
      (s.setXmm dst (((s.getXmm src).setWidth 64).setWidth 128)).setRip nr

  -- ⭐⭐⭐ MOVSS / MOVSD BETWEEN REGISTERS — THE MERGE (SDM Vol. 2B, MOVSS/MOVSD).
  --
  -- ⛔ THE UPPER BITS ARE PRESERVED, and this is the ONE arm in the vector wave
  -- where that is true.  Every other XMM write here either fills all 128 bits
  -- (`vmov`, `vbin`) or ZEROES what it does not write (`vmovg`, `vmovq`) — so
  -- the reflex built by five batches is exactly the wrong one, and reaching for
  -- `setWidth` (which zero-extends) is how this form gets written wrong.
  --
  -- The low `n` bits of `dst` are cleared and replaced; `>>> n <<< n` is the
  -- clear, and the source's low lane is truncated and zero-extended into place
  -- so the `|||` cannot disturb the half it must preserve.
  | .vmovs sz dst src =>
      let n := sz.bits
      let keep := ((s.getXmm dst) >>> n) <<< n
      let low  := ((s.getXmm src).setWidth n).setWidth 128
      (s.setXmm dst (keep ||| low)).setRip nr

  -- ⭐⭐⭐ MOVSS / MOVSD FROM MEMORY — THE ZERO-EXTEND, and the same mnemonic as
  -- the arm above.  The SDM gives MOVSS two separate operation clauses selected
  -- by the source operand's KIND, and this is the second one: bits above the
  -- loaded lane are CLEARED, not preserved.
  --
  -- ⚠️ NO ALIGNMENT CHECK, unlike `vload`.  A scalar move states no alignment
  -- requirement in the SDM, so there is no `#GP` branch to write — its absence
  -- is the rule, not an omission (`Op.vmovsld`).
  | .vmovsld sz dst ea =>
      let a := ea.addr s nr
      (s.setXmm dst (((s.readMem sz a).setWidth sz.bits).setWidth 128)).setRip nr

  -- MOVSS / MOVSD TO MEMORY: `sz` bytes of the low lane.  `writeMem` is the same
  -- `Size`-indexed path every scalar store uses; the only vector-specific step is
  -- taking the low quadword out of the XMM register.
  | .vmovsst sz ea src =>
      let a := ea.addr s nr
      (s.writeMem sz a ((s.getXmm src).setWidth 64)).setRip nr

  -- ⭐⭐⭐ THE PACKED SHIFTS (SDM Vol. 2B), all three count shapes.  DEST is
  -- shifted lane-wise by ONE count; "Flags Affected: None".
  --
  -- ⛔ THE UNENCODABLE PAIRS ARE REFUSED HERE, in the shape `bitcnt` uses: a
  -- form with no encoding is `illegalOperands`, not a silent fallthrough, so the
  -- fidelity table cannot file a form this model has no opcode for as covered.
  -- `vshiftEncodable` is the table and `Tests/Coverage.lean` asserts its exact
  -- declined set.
  | .vshifti op w dst cnt =>
      if !(vshiftEncodable op w) then
        s.halt (.illegalOperands
          "there is no packed byte shift, and no psraq outside AVX-512")
      else
        (s.setXmm dst (vshiftApply op w (s.getXmm dst) cnt.toNat)).setRip nr

  -- ⚠️ `.toNat` OF THE LOW QUADWORD, NOT OF A TRUNCATED BYTE.  The count is all
  -- sixty-four bits (SDM Vol. 2B: "COUNT ← SRC[63:0]"), which is why
  -- `vshiftLane`'s guard has to survive a Nat of that size rather than merely be
  -- correct on small ones.
  | .vshiftx op w dst src =>
      if !(vshiftEncodable op w) then
        s.halt (.illegalOperands
          "there is no packed byte shift, and no psraq outside AVX-512")
      else
        let cnt := ((s.getXmm src).setWidth 64).toNat
        (s.setXmm dst (vshiftApply op w (s.getXmm dst) cnt)).setRip nr

  -- ⛔⛔ P2 BATCH 14 (D110) — THIS ARM HAD NO ALIGNMENT CHECK AND THE COMMENT
  -- HERE SAID THE ABSENCE WAS THE RULE.  It was a defect.  `psrlw xmm,m128` is
  -- SDM `Table 2-21, "Type 4 Class Exception Conditions"` — the same table as
  -- `pand` and as `movdqu`, and it is MOVDQU's entry that decides it: its
  -- operand *"may be unaligned to any alignment without causing a
  -- general-protection exception (#GP) to be generated"*.  An exemption is proof
  -- of the rule it exempts from, and the shifts are not exempted.
  --
  -- ⛔⛔ AND THE DEFECT WAS NOT INVISIBLE FOR WANT OF A VECTOR.  `psraw_m_disp`
  -- addressed `0x8(%rbx)` = 0x2008 — UNALIGNED — was added in the same commit as
  -- this arm, and PASSED at all 88 pre-states.  x86isa implements the 16-byte
  -- rule in one file of its tree and not in `pshift.lisp`, so the differential
  -- compared a model that should have faulted against an oracle that also does
  -- not fault.  ⇒ 🔑 TWO DEFECTS THAT CANCEL SURVIVE EVERY GREEN RUN THAT
  -- COMPARES THEM TO EACH OTHER, and a differential is blind to exactly the
  -- errors its two sides share.  The rule is a theorem
  -- (`vshiftm_unaligned_faults`) because nothing in the run could reach it.
  | .vshiftm op w dst ea =>
      if !(vshiftEncodable op w) then
        s.halt (.illegalOperands
          "there is no packed byte shift, and no psraq outside AVX-512")
      else
        let a := ea.addr s nr
        if !aligned16 a then
          s.halt (.byDesign
            "a Type-4 128-bit memory operand at an address that is not 16-byte aligned (#GP(0))")
        else
          let cnt := ((s.readMem128 a).setWidth 64).toNat
          (s.setXmm dst (vshiftApply op w (s.getXmm dst) cnt)).setRip nr

  -- ⭐ `pslldq` / `psrldq`: the WHOLE REGISTER, by BYTES.  No lane width, no
  -- encodability table — both forms exist and the only count shape is the
  -- immediate.
  | .vshiftdq left dst cnt =>
      (s.setXmm dst (vshiftdqApply left (s.getXmm dst) cnt.toNat)).setRip nr

  -- ⭐⭐⭐ P2 BATCH 14 — THE PERMUTE GROUP.  ⚠️ `s.getXmm src`, NEVER `s.getXmm
  -- dst`: the destination's old value is not read, at either shape.
  | .vshuf k dst src sel =>
      (s.setXmm dst (vshufApply k (s.getXmm src) sel)).setRip nr

  -- ⛔ AND THE SAME 16-BYTE `#GP` THE SHIFT ARM NOW CARRIES.  `Op.vshufm`'s
  -- docstring has the SDM chain; this is the branch it names.
  | .vshufm k dst ea sel =>
      let a := ea.addr s nr
      if !aligned16 a then
        s.halt (.byDesign
          "a Type-4 128-bit memory operand at an address that is not 16-byte aligned (#GP(0))")
      else (s.setXmm dst (vshufApply k (s.readMem128 a) sel)).setRip nr

  -- ⭐⭐⭐ P2 BATCH 15 — THE PACKED BINARY GROUP AT A MEMORY SOURCE.
  --
  -- ⚠️ THE OPERAND ORDER IS `dst` THEN `mem`, AND IT IS NOT SYMMETRIC.  Eleven of
  -- the nineteen operations commute, and the eight that do not — `psub*` and the
  -- eight unpacks — would be silently wrong the other way round: `vbinApply`'s
  -- unpack arm takes `a` as the DESTINATION, whose lane goes LOW in each pair.
  -- Measured against the oracle at all 88 pre-states before this line was
  -- written, at every one of the nineteen.
  --
  -- ⛔ AND THE SAME 16-BYTE `#GP` AS `vshufm` AND `vshiftm` (D110).  Here it is
  -- the first such branch in this repository that a RUN can check: x86isa
  -- implements the rule for `pand`/`por`/`pxor` (`logical.lisp`), so at those
  -- three an unaligned address makes BOTH models refuse and `bothRefused` reports
  -- agreement.  At the other sixteen the oracle still executes, and the rule is
  -- theorem-only exactly as D91 described.
  | .vbinm k dst ea =>
      let a := ea.addr s nr
      if !aligned16 a then
        s.halt (.byDesign
          "a Type-4 128-bit memory operand at an address that is not 16-byte aligned (#GP(0))")
      else (s.setXmm dst (vbinApply k (s.getXmm dst) (s.readMem128 a))).setRip nr

  | .vstore k ea src =>
      let a := ea.addr s nr
      if k.aligned && !aligned16 a then
        s.halt (.byDesign "an aligned 128-bit move at an address that is not 16-byte aligned (#GP(0))")
      else (s.writeMem128 a (s.getXmm src)).setRip nr

  -- MOV (SDM Vol. 2A, MOV): "Flags Affected: None."
  | .mov sz dst src =>
      if !wellFormed2 dst src then s.halt (.illegalOperands "mov: two memory operands")
      else
        let v := s.readOperand sz nr src
        (s.writeOperand sz nr dst v).setRip nr

  -- ADD SUB AND OR XOR CMP TEST (SDM Vol. 2A, each entry's "Flags Affected").
  | .bin k sz dst src =>
      if !wellFormed2 dst src then s.halt (.illegalOperands "two memory operands")
      else
        let a := s.readOperand sz nr dst
        let b := s.readOperand sz nr src
        match k with
        | .add =>
            let res := Flags.addResult sz a b
            let s := s.setFlags (Flags.add sz a b s.flags)
            (s.writeOperand sz nr dst res).setRip nr
        | .sub =>
            let res := Flags.subResult sz a b
            let s := s.setFlags (Flags.sub sz a b s.flags)
            (s.writeOperand sz nr dst res).setRip nr
        -- ADC / SBB (SDM Vol. 2A).  ⚠️ The carry is read from the INCOMING
        -- flags, before any of them are written: `s.flags.cf`, not the flags of
        -- the state being built.  Reading it after would make the instruction
        -- depend on its own output.
        | .adc =>
            let cin := s.flags.cf
            let res := Flags.adcResult sz a b cin
            let s := s.setFlags (Flags.adc sz a b cin s.flags)
            (s.writeOperand sz nr dst res).setRip nr
        | .sbb =>
            let cin := s.flags.cf
            let res := Flags.sbbResult sz a b cin
            let s := s.setFlags (Flags.sbb sz a b cin s.flags)
            (s.writeOperand sz nr dst res).setRip nr
        -- CMP is SUB with the result DISCARDED (SDM Vol. 2A, CMP).
        | .cmp =>
            (s.setFlags (Flags.sub sz a b s.flags)).setRip nr
        | .and =>
            let res := Value.trunc sz (a &&& b)
            let (afU, s) := s.undefBit          -- SDM: "the AF flag is undefined"
            let s := s.setFlags (Flags.logic sz res afU s.flags)
            (s.writeOperand sz nr dst res).setRip nr
        | .or =>
            let res := Value.trunc sz (a ||| b)
            let (afU, s) := s.undefBit
            let s := s.setFlags (Flags.logic sz res afU s.flags)
            (s.writeOperand sz nr dst res).setRip nr
        | .xor =>
            let res := Value.trunc sz (a ^^^ b)
            let (afU, s) := s.undefBit
            let s := s.setFlags (Flags.logic sz res afU s.flags)
            (s.writeOperand sz nr dst res).setRip nr
        -- TEST is AND with the result DISCARDED (SDM Vol. 2A, TEST).
        | .test =>
            let res := Value.trunc sz (a &&& b)
            let (afU, s) := s.undefBit
            (s.setFlags (Flags.logic sz res afU s.flags)).setRip nr

  -- INC DEC NEG NOT (SDM Vol. 2A; note INC/DEC do NOT touch CF, and NOT touches
  -- no flag at all).
  | .un k sz dst =>
      let a := s.readOperand sz nr dst
      match k with
      | .inc =>
          let res := Flags.addResult sz a 1
          let s := s.setFlags (Flags.inc sz a s.flags)
          (s.writeOperand sz nr dst res).setRip nr
      | .dec =>
          let res := Flags.subResult sz a 1
          let s := s.setFlags (Flags.dec sz a s.flags)
          (s.writeOperand sz nr dst res).setRip nr
      | .neg =>
          let res := Flags.subResult sz 0 a
          let s := s.setFlags (Flags.neg sz a s.flags)
          (s.writeOperand sz nr dst res).setRip nr
      | .not =>
          -- SDM Vol. 2A, NOT: "Flags Affected: None."
          let res := Value.trunc sz (~~~a)
          (s.writeOperand sz nr dst res).setRip nr

  -- SHL SHR (SDM Vol. 2A).  Count 0 (AFTER masking) affects no flag.
  | .shift k sz dst amt =>
      let cnt : BitVec 8 :=
        match amt with
        | .imm8 v => v
        | .cl => (s.getReg .b .rcx).setWidth 8
      let n := Flags.shiftCount sz cnt
      let a := s.readOperand sz nr dst
      let res : Val :=
        match k with
        | .shl => Value.trunc sz (a <<< n)
        | .shr => (Value.trunc sz a) >>> n
        -- SAR (SDM Vol. 2A, SAL/SAR/SHL/SHR): the vacated bits take the SIGN.
        | .sar => Value.sar sz a n
      if n = 0 then
        -- "If the count is 0, the flags are not affected."  The destination is
        -- still written back (the instruction is a read-modify-write), with the
        -- value it already had.
        (s.writeOperand sz nr dst res).setRip nr
      else
        -- THREE draws, in the fixed order CF, OF, AF.  See the file header.
        let (cfU, s) := s.undefBit
        let (ofU, s) := s.undefBit
        let (afU, s) := s.undefBit
        let s := s.setFlags (Flags.shiftFlags k sz a res n cfU ofU afU s.flags)
        (s.writeOperand sz nr dst res).setRip nr

  -- ROL ROR RCL RCR (SDM Vol. 2A).  ONE oracle draw (OF) whenever the masked
  -- count is non-zero, drawn whether or not it is needed — the same discipline
  -- the shifts follow, and for the same reason: the cursor must be a function
  -- of the instruction stream alone.  A masked count of zero touches nothing.
  | .rot k sz dst amt =>
      let cnt : BitVec 8 :=
        match amt with
        | .imm8 v => v
        | .cl => (s.getReg .b .rcx).setWidth 8
      let n := Flags.rotMasked sz cnt
      let t := Flags.rotReduced k sz n
      let a := s.readOperand sz nr dst
      let res := Flags.rotResult k sz a s.flags.cf t
      if n = 0 then
        (s.writeOperand sz nr dst res).setRip nr
      else
        let (ofU, s) := s.undefBit
        let s := s.setFlags (Flags.rotFlags k sz a res n t ofU s.flags)
        (s.writeOperand sz nr dst res).setRip nr

  -- BT / BTS / BTR / BTC (SDM Vol. 2A).  ⚠️ ZF IS THE ONLY ARITHMETIC FLAG THAT
  -- SURVIVES: "the ZF flag is unaffected... the OF, SF, AF and PF flags are
  -- undefined".  Four oracle draws, in the fixed order PF, AF, SF, OF.
  --
  -- ⛔ NAMED GAP: the MEMORY destination with a REGISTER offset is not here.
  -- That shape is not a bit within the addressed operand — it is an index into
  -- a BIT STRING, signed, reaching outside the operand entirely, and the
  -- effective address moves with it.  Modelling it is a real piece of work and
  -- guessing at it would be worse than declining, so the four `m,r` forms of
  -- roster family 31/41 are NOT claimed (docs/DECISIONS.md D23).  The forms
  -- here take the offset MODULO the operand width, which is what the SDM
  -- specifies for a register destination and for an immediate offset.
  | .bit k sz dst off =>
      let a := s.readOperand sz nr dst
      let n := (s.readOperand sz nr off).toNat % sz.bits
      let bit := a.getLsbD n
      let res : Val :=
        match k with
        | .bt  => a
        | .bts => Value.trunc sz (a ||| (BitVec.ofNat 64 1 <<< n))
        | .btr => Value.trunc sz (a &&& ~~~(BitVec.ofNat 64 1 <<< n))
        | .btc => Value.trunc sz (a ^^^ (BitVec.ofNat 64 1 <<< n))
      let (pfU, s) := s.undefBit
      let (afU, s) := s.undefBit
      let (sfU, s) := s.undefBit
      let (ofU, s) := s.undefBit
      let s := s.setFlags { s.flags with
        cf := bit, pf := pfU, af := afU, sf := sfU, of := ofU }
      match k with
      -- BT writes nothing, exactly as `cmp` does.
      | .bt => s.setRip nr
      | _ => (s.writeOperand sz nr dst res).setRip nr

  -- LEA (SDM Vol. 2A, LEA): computes the effective address and writes it under
  -- the ordinary register-width rules, so `lea eax, [...]` zero-extends.
  -- "Flags Affected: None."
  | .lea sz dst ea =>
      -- ⛔ `Ea.offset`, NOT `Ea.addr`: LEA writes the effective address and no
      -- segment base is added to it (SDM Vol. 2A, LEA).  P2 item 1.
      ((s.setReg sz dst (ea.offset s nr)).setRip nr)

  -- PUSH POP (SDM Vol. 2A).  "Flags Affected: None."
  | .push sz src =>
      -- the value is read BEFORE RSP moves, so `push rsp` pushes the OLD RSP.
      let v := s.readOperand sz nr src
      (s.push sz v).setRip nr
  | .pop sz dst =>
      -- RSP is incremented BEFORE the destination's effective address is
      -- computed (SDM Vol. 2A, POP: the address is computed after the
      -- increment), and a `pop rsp` therefore ends with the LOADED value.
      let (v, s) := s.popValue sz
      (s.writeOperand sz nr dst v).setRip nr

  -- JMP Jcc CALL (SDM Vol. 2A).  "Flags Affected: None" for all three.
  | .jmp t =>
      match t with
      | .rel d => s.setRipChecked (nr + d)
      | .indirect o => s.setRipChecked (s.readOperand .q nr o)
  | .jcc c d =>
      if c.eval s.flags then s.setRipChecked (nr + d) else s.setRip nr
  -- JRCXZ / JECXZ (SDM Vol. 2A, JCC).  ⚠️ THE ONLY BRANCH WHOSE CONDITION IS A
  -- REGISTER, and the width of the register it reads is what the address-size
  -- prefix selects: `jecxz` tests ECX — the LOW 32 BITS — and `jrcxz` tests all
  -- of RCX.  A model that read the same width for both is wrong exactly when
  -- RCX's upper half is non-zero and its lower half is zero, which is one point
  -- in the state space and is this batch's planted hard half.
  -- "Flags Affected: None."
  | .jcxz addr32 d =>
      let c := if addr32 then Value.trunc .d (s.regs.get .rcx) else s.regs.get .rcx
      if c == 0 then s.setRipChecked (nr + d) else s.setRip nr
  -- SETcc (SDM Vol. 2A, SETcc): ONE BYTE, 1 or 0.  "Flags Affected: None."
  | .setcc c dst =>
      (s.writeOperand .b nr dst (if c.eval s.flags then 1 else 0)).setRip nr

  -- CMOVcc (SDM Vol. 2A, CMOVcc).  ⚠️ THE WRITE IS UNCONDITIONAL; only the
  -- VALUE is conditional.  On a false condition the destination is rewritten
  -- with what it already held — which is a no-op at widths w and q and is NOT
  -- one at width d, where the write zero-extends and clears the upper half
  -- (SDM Vol. 1 §3.4.1.1).  Writing this as "if the condition holds, move" is
  -- the natural mistake and it is wrong on exactly the 32-bit forms.
  | .cmov c sz dst src =>
      let v := if c.eval s.flags then s.readOperand sz nr src else s.getReg sz dst
      ((s.setReg sz dst v).setRip nr)

  -- ══ P1 BATCH 10 ═══════════════════════════════════════════════════════
  -- The width-changing and two-destination moves.  NOT ONE OF THEM TOUCHES A
  -- FLAG (SDM Vol. 2A: "Flags Affected: None" on every entry in this block), so
  -- there is not one oracle draw in the whole batch — which makes every
  -- disagreement it can produce a DATA-path disagreement.

  -- MOVZX / MOVSX / MOVSXD (SDM Vol. 2A).  Read at `ssz`, extend to 64, write
  -- at `dsz` under the ordinary register-width rules.  The write is what makes
  -- `movzbl` clear the upper half of RAX and `movzbw` preserve it: the
  -- extension is the same computation in both, and `setReg dsz` is the only
  -- thing that differs.
  | .movx k dsz ssz dst src =>
      let v := s.readOperand ssz nr src
      let e := match k with
        | .zero => Value.zext ssz v
        | .sign => Value.sext ssz v
      ((s.setReg dsz dst e).setRip nr)

  -- CBW/CWDE/CDQE and CWD/CDQ/CQO (SDM Vol. 2A).  ⚠️ THE SECOND TRIO IS THE
  -- FIRST THING IN THIS MODEL TO WRITE A REGISTER OTHER THAN THE ONE ITS
  -- OPERANDS NAME: it fills rDX with the accumulator's sign and leaves the
  -- accumulator alone.  And `cltd`'s write is 32 bits wide, so it CLEARS
  -- RDX's upper half — invisible unless the pre-state put something there,
  -- which is why `mkPre` now gives RDX a value (docs/DECISIONS.md D26).
  | .cext k =>
      let a := s.regs.get .rax
      match k with
      | .cbw  => ((s.setReg .w .rax (Value.sext .b a)).setRip nr)
      | .cwde => ((s.setReg .d .rax (Value.sext .w a)).setRip nr)
      | .cdqe => ((s.setReg .q .rax (Value.sext .d a)).setRip nr)
      | .cwd  => ((s.setReg .w .rdx (if Value.msb .w a then Size.mask .w else 0)).setRip nr)
      | .cdq  => ((s.setReg .d .rdx (if Value.msb .d a then Size.mask .d else 0)).setRip nr)
      | .cqo  => ((s.setReg .q .rdx (if Value.msb .q a then Size.mask .q else 0)).setRip nr)

  -- XCHG (SDM Vol. 2A).  ⚠️ BOTH VALUES ARE READ BEFORE EITHER IS WRITTEN.
  -- With two distinct registers the order does not matter; with the SAME
  -- register twice it is the difference between a swap and a clobber, and with
  -- a memory operand whose base is the other operand it would be the difference
  -- between the old address and the new one.  Reading first costs one `let` and
  -- removes the question.
  --
  -- ⭐⭐ P2 ITEM 2 UN-DECLINED THE MEMORY FORMS, AND THE CHANGE IS ONE DELETED
  -- BRANCH.  D25 refused `xchg` at memory because its implicit LOCK is an
  -- atomicity claim and the model had no vocabulary to make it.  `Ea.lock` is
  -- that vocabulary: the model now RECORDS that the access is architecturally
  -- atomic and states, in `TRUSTBASE.md`, that atomicity has no observable
  -- consequence in a single-threaded step semantics and is carried rather than
  -- verified.  ⛔ The distinction that matters: the model no longer says
  -- "I cannot describe this instruction"; it says "here is the instruction, and
  -- here is the property of it I am not checking."  Two DIFFERENT roster rows
  -- (`xchg m,r` and `xchg r,m`) come back, and no others — the four `bt`-family
  -- `m,r` rows beside them are declined for signed BIT-STRING addressing (D23),
  -- which this addition does not touch.  D76.
  --
  -- ⚠️ NO `lock` FLAG IS REQUIRED ON THE `Ea`.  With a memory operand `xchg`
  -- asserts LOCK whether or not the prefix is written (SDM Vol. 2A, XCHG), so
  -- both spellings are the same instruction and `Op.lockable` answers true for
  -- either.  An immediate still cannot be a destination at all.
  | .xchg sz a b =>
      if a.isImm || b.isImm then
        s.halt (.illegalOperands "xchg: immediate operand")
      else if !wellFormed2 a b then
        s.halt (.illegalOperands "xchg: two memory operands")
      else
        let va := s.readOperand sz nr a
        let vb := s.readOperand sz nr b
        let s := s.writeOperand sz nr a vb
        ((s.writeOperand sz nr b va).setRip nr)

  -- BSWAP (SDM Vol. 2A).  ⛔ "the result of BSWAP with a 16-bit operand size is
  -- undefined" — so this model REFUSES `.b` and `.w` rather than answering.
  -- The undefined-bit oracle is the wrong instrument here: it says "this model
  -- declines to commit to these BITS", and what the SDM declines to define is
  -- the whole RESULT.  D25.
  | .bswap sz dst =>
      match sz with
      | .d | .q => ((s.setReg sz dst (Value.bswap sz (s.getReg sz dst))).setRip nr)
      | _ => s.halt (.unimplemented "bswap at a 16-bit or 8-bit operand size (SDM: undefined)")

  -- ══ P1 BATCH 11 ═══════════════════════════════════════════════════════
  -- The loop group and the flag-control singles.  Between them they are the
  -- batch's whole shape: the loops write a REGISTER and read a flag but write
  -- none, and the flag-control singles write ONE FLAG BIT and nothing else.

  -- LOOP / LOOPE / LOOPNE (SDM Vol. 2A, LOOP/LOOPcc).  "Flags Affected: None."
  --
  -- ⚠️ THE ORDER IS DECREMENT, THEN TEST, AND THE WRITE-BACK IS UNCONDITIONAL.
  -- ACL2 x86isa's `x86-loop` writes the decremented counter on BOTH the taken
  -- and the not-taken path, and its branch condition reads the DECREMENTED
  -- value; the SDM says the same ("Each time the LOOP instruction is executed,
  -- the count register is decremented, then checked for 0").  A model that
  -- tested the incoming counter is wrong at exactly two points — a counter of 1
  -- (which must FALL THROUGH after decrementing to 0) and a counter of 0 (which
  -- must BRANCH, having wrapped to all-ones) — and right everywhere else.
  --
  -- ⚠️ AND `addr32` IS A WIDTH ON BOTH THE READ AND THE WRITE.  With the prefix
  -- the counter is ECX, the decrement wraps at 32 bits, and the write-back
  -- zero-extends and clears RCX's upper half.  Reading ECX but writing RCX — or
  -- writing 32 bits but wrapping at 64 — are both invisible unless the upper
  -- half is non-zero AND the low half is at its boundary.
  | .loop k addr32 d =>
      let sz : Size := if addr32 then .d else .q
      -- ZF is read from the INCOMING flags; nothing here writes a flag, but the
      -- counter write-back is sequenced first below, so naming it now is what
      -- makes the independence explicit rather than accidental.
      let zf := s.flags.zf
      let cnt := s.getReg sz .rcx
      let cnt' := Value.trunc sz (cnt - 1)
      -- the write-back happens on BOTH paths, so it is sequenced before the test
      let s := s.setReg sz .rcx cnt'
      let taken :=
        match k with
        | .loop   => cnt' != 0
        | .loope  => cnt' != 0 && zf
        | .loopne => cnt' != 0 && !zf
      if taken then s.setRipChecked (nr + d) else s.setRip nr

  -- CLC / STC / CMC / CLD / STD (SDM Vol. 2A).  Each writes ONE flag; "all
  -- other flags are unaffected" (ACL2 x86isa `x86-cmc/clc/stc/cld/std` says the
  -- same, one `!flgi` per opcode).  ⭐ `cld` and `std` are the ONLY writers of
  -- `df` in this model, and `df` is the one flag the comparator has been
  -- diffing since P0 with nothing able to move it.  D27.
  | .flagop k =>
      let f := s.flags
      let f := match k with
        | .clc => { f with cf := false }
        | .stc => { f with cf := true }
        | .cmc => { f with cf := !f.cf }
        | .cld => { f with df := false }
        | .std => { f with df := true }
      (s.setFlags f).setRip nr

  -- ── P1 BATCH 12 ───────────────────────────────────────────────────────────
  -- NOP (SDM Vol. 2A).  "Flags Affected: None", no register altered, and — for
  -- the multi-byte form — "does not issue a memory operation".  ⚠️ THE OPERAND
  -- IS DELIBERATELY NOT READ.  `nop (%rbx)` must not fault, must not touch the
  -- watched window, and must not depend on what the window holds; reading it
  -- "harmlessly" would still be wrong, because a read from an unmapped page is
  -- a fault in hardware and the whole point of the form is that it is inert.
  | .nop _ => s.setRip nr

  -- UD2 (SDM Vol. 2A): "Generates an invalid opcode exception."  ⭐ THIS IS THE
  -- ONE HALT THAT IS A MODELLED ANSWER RATHER THAN A DECLINED ONE, which is why
  -- it carries `byDesign` and not `unimplemented`: the record's `refused=1` says
  -- the same thing x86isa's `#UD` fault says, and the two models AGREE.
  | .ud2 => s.halt (.byDesign "ud2: #UD is the instruction's meaning")

  -- RET near (SDM Vol. 2A, RET).  "Flags Affected: None."
  --
  -- ⚠️ THE CANONICAL CHECK COMES FIRST, AND RSP DOES NOT MOVE IF IT FAILS —
  -- the same discipline `call` was forced into by its first differential run.
  -- x86isa raises #GP(0) on the target before committing the pop, so a refused
  -- `retq` that had already incremented RSP would disagree on `rsp` as well as
  -- on `rip`, and the disagreement on `rsp` is the one that says the ORDER is
  -- observable rather than an implementation detail.
  | .ret =>
      let sp := s.regs.get .rsp
      let tgt := s.readMem .q sp
      if canonical tgt then
        { s.setReg .q .rsp (sp + 8) with rip := tgt }
      else s.halt (.unimplemented "non-canonical return address (#GP(0) in hardware)")

  -- LEAVE (SDM Vol. 2A): "Set RSP to RBP, then POP RBP."  Written as those two
  -- steps in that order rather than as one closed form, because the order is
  -- the instruction: the POP reads from the NEW RSP (that is, from RBP), and a
  -- model that popped first would read the caller's stack instead of the
  -- frame's.  "Flags Affected: None."
  | .leave =>
      let s := s.setReg .q .rsp (s.regs.get .rbp)
      let (v, s) := s.popValue .q
      (s.setReg .q .rbp v).setRip nr

  -- ══ P1 BATCH 13 ═══════════════════════════════════════════════════════
  -- The flagless shifts and the byte-swapping move.  Both are forms whose
  -- RESULT this model already knew how to compute — `Flags.shiftCount` and the
  -- three shift expressions came from batches 7/8, `Value.byteRev` from batch
  -- 10 — and whose content is entirely in what they do NOT do.

  -- SARX / SHLX / SHRX (SDM Vol. 2A).  "Flags Affected: None."
  --
  -- ⭐ THE SAME COUNT MASK AS `.shift`, AND IT IS THE SAME SENTENCE OF THE SDM:
  -- "the count is masked to 5 bits (or 6 bits with a 64-bit operand)".  So
  -- `Flags.shiftCount` is called here rather than re-derived — a second copy of
  -- the mask would be a second place for the 5/6 split to be wrong, and the
  -- split is the part of a shift that is easy to get wrong.
  --
  -- ⚠️ THE COUNT IS READ AT WIDTH `.b` AND NOT AT `sz`, and that is not a
  -- shortcut: the mask keeps at most six bits, and the low six bits of a
  -- register are the low six bits of its low byte whatever the operand size.
  -- Reading the count at `sz` would be equally correct and would say something
  -- false about where the count comes from — the count register's width is not
  -- the operand's width.
  --
  -- ⛔ AND THERE IS NO `n = 0` BRANCH, unlike `.shift`.  `.shift` needs one
  -- because "if the count is 0, the flags are not affected"; this form affects
  -- no flags at any count, so a zero count is an ordinary case that copies the
  -- source to the destination — and the destination write still ZERO-EXTENDS at
  -- `.d`, so `shlxl` with a count of zero is observably not a no-op.
  | .shiftx k sz dst src cnt =>
      match sz with
      | .d | .q =>
          let n := Flags.shiftCount sz ((s.getReg .b cnt).setWidth 8)
          let a := s.readOperand sz nr src
          let res : Val :=
            match k with
            | .shl => Value.trunc sz (a <<< n)
            | .shr => (Value.trunc sz a) >>> n
            | .sar => Value.sar sz a n
          (s.setReg sz dst res).setRip nr
      | _ => s.halt (.illegalOperands
          "sarx/shlx/shrx at an 8- or 16-bit operand size (VEX.W selects 32 or 64 only)")

  -- MOVBE (SDM Vol. 2A).  "Flags Affected: None."
  --
  -- ⚠️ THE REVERSAL IS AT THE OPERAND WIDTH, NOT AT 64 BITS.  `movbew` reverses
  -- TWO bytes, `movbel` four, `movbeq` eight — and the destination write then
  -- applies the ordinary width rule on top, so `movbel` zero-extends and
  -- `movbew` merges (SDM Vol. 1 §3.4.1.1).  A model that reversed eight bytes
  -- and truncated would be wrong at both narrow widths and right at `.q`.
  --
  -- ⛔ EXACTLY ONE MEMORY OPERAND.  Both encodings put the memory operand in
  -- ModR/M's r/m field, so `movbe r, r` has no encoding; declining is the same
  -- refusal `wellFormed2` makes for two memory operands, one direction further.
  | .movbe sz dst src =>
      if !(dst.isMem != src.isMem) || dst.isImm || src.isImm then
        s.halt (.illegalOperands "movbe requires exactly one memory operand")
      else match sz with
      | .w | .d | .q =>
          let a := s.readOperand sz nr src
          (s.writeOperand sz nr dst (Value.bswap sz a)).setRip nr
      | .b => s.halt (.illegalOperands "movbe at an 8-bit operand size (no encoding)")

  -- POPCNT (SDM Vol. 2B) · LZCNT/TZCNT · BSF/BSR · BLSI (SDM Vol. 2A).
  --
  -- ⛔⛔ BSF AND BSR AT A ZERO SOURCE ARE THIS MODEL'S FIRST UNDEFINED
  -- DESTINATION.  "If the content source operand is 0, the content of the
  -- destination operand is undefined" — a REGISTER, not a flag.  Real silicon
  -- leaves the destination unmodified and AMD documents that it does; Intel
  -- does not, and this model follows its stated source rather than the folklore.
  -- Writing the old value back would be INVENTING A FACT in exactly the sense
  -- X86/Oracle.lean's header forbids, and it is the more tempting invention
  -- because it happens to match the machine on the desk.
  --
  -- ⚠️ THE ZERO SOURCE IS REACHABLE, not hypothetical: `adversarial` contains 0,
  -- so every `bsf`/`bsr` vector runs this branch at one pre-state in eleven.
  --
  -- ⚠️ THE FIVE FLAG DRAWS HAPPEN BEFORE THE BRANCH, unconditionally, so that
  -- the flags always read the same five positions of the stream whichever way
  -- the source falls.  ⛔ THE TOTAL a `bsf` consumes IS still data-dependent —
  -- a zero source draws `sz.bits` more for the destination — and saying
  -- otherwise would be a comment claiming a property the code does not have.
  -- What matters is the weaker fact, and it holds: the cursor depends on the
  -- SOURCE, never on the oracle's own BITS, so the two opposite-oracle runs
  -- that derive the undefined set always take the same branch and end at the
  -- same position (`cursor_independent_of_bits`, `Tests/Nonvacuity.lean`).
  | .bitcnt k sz dst src =>
      if !(bitcntEncodable k sz) then
        s.halt (.illegalOperands
          "the bit-counting group has no 8-bit form, and blsi has no 16-bit form")
      else
        let a := s.readOperand sz nr src
        match k with
        | .popcnt =>
            let res : Val := BitVec.ofNat 64 (Value.popCount sz a)
            ((s.setFlags (Flags.popcnt sz a s.flags)).setReg sz dst res).setRip nr
        | .lzcnt =>
            let res : Val := BitVec.ofNat 64 (Value.clz sz a)
            let (pfU, s) := s.undefBit
            let (afU, s) := s.undefBit
            let (sfU, s) := s.undefBit
            let (ofU, s) := s.undefBit
            ((s.setFlags (Flags.bitCount sz a res pfU afU sfU ofU s.flags)).setReg
              sz dst res).setRip nr
        | .tzcnt =>
            let res : Val := BitVec.ofNat 64 (Value.ctz sz a)
            let (pfU, s) := s.undefBit
            let (afU, s) := s.undefBit
            let (sfU, s) := s.undefBit
            let (ofU, s) := s.undefBit
            ((s.setFlags (Flags.bitCount sz a res pfU afU sfU ofU s.flags)).setReg
              sz dst res).setRip nr
        | .bsf => bitScanStep false sz dst a nr s
        | .bsr => bitScanStep true sz dst a nr s
        | .blsi =>
            let res := Value.blsi sz a
            let (pfU, s) := s.undefBit
            let (afU, s) := s.undefBit
            ((s.setFlags (Flags.blsi sz a res pfU afU s.flags)).setReg sz dst res).setRip nr

  -- MOVS / STOS / LODS / CMPS / SCAS (SDM Vol. 2A/2B).  See `StringOp`.
  --
  -- ⭐ THE DELTA IS THE WHOLE GROUP'S SHARED CONTENT, and it is the first thing
  -- in this model that READS DF.  "If the DF flag is 0, the pointer is
  -- incremented; if the DF flag is 1, it is decremented" — by the OPERAND
  -- WIDTH, not by a fixed eight.  ⚠️ DF was a dead bit in this repository for
  -- ten batches (D27) and is written by `cld`/`std` since batch 11; this is
  -- where it finally changes an ANSWER rather than a field of the output.
  --
  -- ⛔ THE ACCESS HAPPENS AT THE CURRENT POINTER AND THE UPDATE COMES AFTER.
  -- Measured, not assumed: with DF set, the oracle's `movsq` still WROTE at
  -- RDI's original 0x2000 and only then left RDI at 0x1ff8.  A model that
  -- decremented first would touch the eight bytes below on every backward step
  -- and agree with this one on every forward one.
  --
  -- ⚠️ THE POINTER WRITE IS `.q` AND THE DATA ACCESS IS `sz`; the two widths in
  -- each line are different on purpose.  See the note on the constructor.
  --
  -- "Flags Affected: None" for MOVS, STOS and LODS.  CMPS and SCAS set all six
  -- arithmetic flags and leave NONE undefined — the whole group draws nothing
  -- from the oracle, which is why every row of it is `T-exact`.
  | .strop k sz => (stringIter k sz s).setRip nr

  -- ⭐⭐ P1 BATCH 16: THE REPEAT PREFIXES (SDM Vol. 2B, REP/REPE/REPZ/REPNE/
  -- REPNZ).  ONE ITERATION PER `step`, and the loop-back is a RIP that does not
  -- move.
  --
  -- ⛔⛔ COUNT EXHAUSTION DOES NOT ADVANCE RIP, AND THIS IS THE ONE THING HERE
  -- THAT IS NOT WHAT IT LOOKS LIKE.  The obvious model — and the SDM's own
  -- pseudocode read as a single step — decrements RCX, notices it has reached
  -- zero, and falls through to the next instruction.  x86isa does not: measured,
  -- `rep movsq` with RCX = 1 performs the copy, leaves RCX = 0, and leaves RIP
  -- AT THE INSTRUCTION.  It takes one FURTHER step, which finds RCX already
  -- zero, to move past it.  So the count is tested only ON ENTRY, and the
  -- SDM's loop is decomposed with its `while` test at the TOP.
  --
  -- ⚠️ A MODEL THAT ADVANCED ON THE DECREMENT REACHING ZERO IS RIGHT EVERYWHERE
  -- EXCEPT RCX = 1.  It agrees on every RCX = 0 case (no iteration at all) and
  -- on every RCX ≥ 2 case (the count does not reach zero), so exactly one value
  -- of one register separates the two models — and `adversarial` contains 1, so
  -- the pre-states reach it.  `wrongRepAdvanceOnCountZero` in Main.lean is that
  -- model, and it is caught.  Had the sweep skipped 1, this whole branch would
  -- have been green and wrong, which is D43 in the shape it takes when the
  -- state DOES happen to express the difference.
  --
  -- THE ZF PREDICATE READS THE FLAGS THE ITERATION JUST WROTE (`RepPrefix.
  -- terminates` on `s'.flags.zf`, not `s.flags.zf`).  `repe cmpsq` on differing
  -- operands ended the repeat in the same step it made the comparison.
  --
  -- ⚠️ AND THE COUNT WRITE IS `.q`, like the pointer writes beside it: `rep
  -- movsb` decrements the whole of RCX.  Measured at RCX = 0x1_0000_0001, which
  -- became 0x1_0000_0000 — a value whose low half alone would have wrapped.
  --
  -- "Flags Affected: None" for the prefix itself; the flags are whatever the
  -- iteration left, and on the RCX = 0 path they are untouched.
  | .repstrop r k sz =>
      if !repApplies r k then
        s.halt (.unimplemented "repeat prefix not filed for this string op")
      else
        let cx := s.regs.get .rcx
        -- RCX = 0 ON ENTRY: no iteration at all.  No memory access, no flag
        -- write, no pointer move, and RCX is NOT decremented — it does not wrap
        -- to all-ones.  This is the only path that always advances.
        if cx == 0 then s.setRip nr
        else
          let s' := (stringIter k sz s).setReg .q .rcx (cx - 1)
          s'.setRip (if r.terminates s'.flags.zf then nr else s.rip)

  | .call t =>
      match t with
      | .rel d =>
          -- ⚠️ THE CHECK COMES FIRST.  x86isa raises #GP(0) BEFORE the return
          -- address is pushed, so a refused call must not have pushed either —
          -- the first run disagreed on `rsp` and on the stack window as well as
          -- on `rip`, which is what says the ordering is observable and not a
          -- detail.
          if canonical (nr + d) then (s.push .q nr).setRip (nr + d)
          else s.halt (.unimplemented "non-canonical branch target (#GP(0) in hardware)")
      | .indirect o =>
          -- the target is read BEFORE the return address is pushed, so a
          -- `call [rsp]` reads the pre-push stack.
          let tgt := s.readOperand .q nr o
          if canonical tgt then (s.push .q nr).setRip tgt
          else s.halt (.unimplemented "non-canonical branch target (#GP(0) in hardware)")

  -- MUL · IMUL · DIV · IDIV, the ONE-OPERAND forms (SDM Vol. 2A).  See
  -- `MulDivKind` and `Cpu.setMdPair`.
  --
  -- ⛔⛔ THE TWO DIVISIONS ARE THE FIRST FORMS IN THIS MODEL WHOSE REFUSAL IS A
  -- FUNCTION OF THE OPERANDS.  `ud2` (batch 12) refuses because of what it IS;
  -- `divq %rcx` refuses because of what RDX, RAX and RCX happen to hold, so the
  -- same vector refuses at one pre-state and divides at the next.  The refusal
  -- carries `byDesign` for `ud2`'s reason: #DE is the instruction's meaning
  -- here, not a gap in the roster, and filing it as `unimplemented` would put a
  -- covered form in the `T-absent` tier.
  --
  -- ⚠️ AND THE FAULT IS DECIDED BEFORE ANYTHING IS WRITTEN.  `Value.divPairU`
  -- and `Value.divPairS` return `Option`, so there is no path on which a
  -- quotient exists and the fault has not been considered; a `halt` beside the
  -- arithmetic could be forgotten, and this cannot.  Measured against x86isa on
  -- all eighty-two pre-states at four widths and both signednesses — 656 cases,
  -- 656 agreements, before this constructor was written — the oracle refuses on
  -- exactly the operand pairs the SDM's two sentences name.
  --
  -- ⚠️ THE UNDEFINED DRAWS HAPPEN ONLY ON THE NON-FAULTING PATH, so a division's
  -- consumption of the oracle depends on its OPERANDS.  That is `bsf`'s
  -- situation from batch 14 and it obeys the same weaker property that matters:
  -- the cursor depends on the operands, never on the oracle's own BITS, so the
  -- two opposite-oracle runs that derive the undefined set take the same branch.
  | .muldiv k sz src =>
      let a := s.readOperand sz nr src
      let lo := s.getReg sz .rax
      match k with
      | .mul =>
          let (l, h) := Value.mulPair sz lo a
          let ovf := Value.mulOverflow sz lo a
          let (sfU, s) := s.undefBit
          let (zfU, s) := s.undefBit
          let (afU, s) := s.undefBit
          let (pfU, s) := s.undefBit
          ((s.setFlags (Flags.mulFlags ovf sfU zfU afU pfU s.flags)).setMdPair sz l h).setRip nr
      | .imul =>
          let (l, h) := Value.imulPair sz lo a
          let ovf := Value.imulOverflow sz lo a
          let (sfU, s) := s.undefBit
          let (zfU, s) := s.undefBit
          let (afU, s) := s.undefBit
          let (pfU, s) := s.undefBit
          ((s.setFlags (Flags.mulFlags ovf sfU zfU afU pfU s.flags)).setMdPair sz l h).setRip nr
      | .div =>
          match Value.divPairU sz (s.mdHi sz) lo a with
          | none => s.halt (.byDesign "div: #DE is the instruction's meaning at this divisor")
          | some (q, r) =>
              let (cfU, s) := s.undefBit
              let (pfU, s) := s.undefBit
              let (afU, s) := s.undefBit
              let (zfU, s) := s.undefBit
              let (sfU, s) := s.undefBit
              let (ofU, s) := s.undefBit
              ((s.setFlags (Flags.divFlags cfU pfU afU zfU sfU ofU s.flags)).setMdPair
                sz q r).setRip nr
      | .idiv =>
          match Value.divPairS sz (s.mdHi sz) lo a with
          | none => s.halt (.byDesign "idiv: #DE is the instruction's meaning at this divisor")
          | some (q, r) =>
              let (cfU, s) := s.undefBit
              let (pfU, s) := s.undefBit
              let (afU, s) := s.undefBit
              let (zfU, s) := s.undefBit
              let (sfU, s) := s.undefBit
              let (ofU, s) := s.undefBit
              ((s.setFlags (Flags.divFlags cfU pfU afU zfU sfU ofU s.flags)).setMdPair
                sz q r).setRip nr

  -- IMUL, the TWO- and THREE-operand forms (SDM Vol. 2A, IMUL).  One register
  -- destination, no pair, and the SAME CF/OF rule as the one-operand form —
  -- which is why `Value.imulOverflow` is shared rather than restated.
  --
  -- ⚠️ THE THREE-OPERAND FORM DOES NOT READ ITS DESTINATION.  `imul $7, %rcx,
  -- %rax` is `rax := rcx * 7`; a model that multiplied the destination in would
  -- agree with this one only where RAX already held the immediate.
  | .imulr sz dst src imm =>
      if !(imulrEncodable sz) then
        s.halt (.illegalOperands
          "imul's two- and three-operand forms have no 8-bit encoding")
      else
        let b := s.readOperand sz nr src
        let (x, y) := match imm with
          | none => (s.getReg sz dst, b)
          | some i => (b, Value.trunc sz i)
        let (l, _) := Value.imulPair sz x y
        let ovf := Value.imulOverflow sz x y
        let (sfU, s) := s.undefBit
        let (zfU, s) := s.undefBit
        let (afU, s) := s.undefBit
        let (pfU, s) := s.undefBit
        ((s.setFlags (Flags.mulFlags ovf sfU zfU afU pfU s.flags)).setReg sz dst l).setRip nr

  -- ══ P1 BATCH 18 ═══════════════════════════════════════════════════════
  -- The compare-exchange pair and the double-precision shifts.

  -- CMPXCHG (SDM Vol. 2A).  ⭐ THE FIRST FORM IN THIS MODEL WHOSE DESTINATION IS
  -- CHOSEN BY A COMPARISON IT MAKES ITSELF, and the comparison is against a
  -- register that is not an operand: the accumulator, AL/AX/EAX/RAX by opcode.
  --
  -- ⚠️ THE FLAGS ARE THE COMPARISON'S, IN FULL AND WITH NOTHING UNDEFINED.  The
  -- SDM's pseudo-code writes only ZF, and the "Flags Affected" paragraph then
  -- says "the ZF flag is set if the values ... are equal; otherwise it is
  -- cleared.  The CF, PF, AF, SF and OF flags are set according to the results
  -- of the comparison operation" — so this is `Flags.sub` of the accumulator
  -- against the destination, exactly `cmp`, and NOT a hand-written ZF.  Measured
  -- on the oracle before this constructor existed: `cmpxchg` draws nothing from
  -- x86isa's undefined generator at any width or shape, in all eighty-two
  -- pre-states.
  --
  -- ⛔⛔ AND THE UNEQUAL BRANCH DOES **NOT** WRITE THE DESTINATION, THOUGH THE
  -- SDM'S PSEUDO-CODE SAYS `DEST := TEMP`.  This model wrote it, as the
  -- pseudo-code reads, and the differential run refused: EIGHTY disagreements,
  -- every one of them `cmpxchg_r_l`, every one of them RCX's upper half.  A
  -- 32-bit register write ZERO-EXTENDS in 64-bit mode, so writing the
  -- destination back with the value it already had is not the no-op the line
  -- looks like — it clears bits 63:32.
  --
  -- ⭐ TWO INDEPENDENT PUBLIC MODELS SAY OTHERWISE, AND ONE OF THEM IS EVIDENCE
  -- ABOUT SILICON.  ACL2 x86isa's `x86-cmpxchg` takes the else branch as
  -- `(!rgfi-size reg/mem-size *rax* reg/mem …)` and nothing else — no write to
  -- the destination at all.  K's `CMPXCHGL-R32-R32`, which was LEARNED BY
  -- EXECUTION rather than read off the manual, is explicit in the same
  -- direction: on the unequal branch the accumulator becomes
  -- `concatenateMInt(mi(32,0), R2[32:64])` — zero-extended — while the
  -- destination becomes `getParentValue(R2, RSMap)`, the FULL 64-bit parent
  -- value, unchanged.  Both halves of that rule are visible at `.d` and at no
  -- other width, which is why one vector out of seven found it.
  --
  -- ⇒ THE SDM'S `DEST := TEMP` DESCRIBES THE MEMORY WRITE-BACK, the one that
  -- matters under LOCK and for a read-only page, and applying it literally to a
  -- register destination invents a zero-extension no processor performs.  This
  -- model does not model LOCK or page protection, so it writes nothing on this
  -- branch and says so.  D53.
  | .cmpxchg sz dst src =>
      if dst.isImm then s.halt (.illegalOperands "cmpxchg: immediate destination")
      else
        let acc := s.getReg sz .rax
        let tmp := s.readOperand sz nr dst
        let s := s.setFlags (Flags.sub sz acc tmp s.flags)
        if Value.trunc sz acc == Value.trunc sz tmp then
          (s.writeOperand sz nr dst (s.getReg sz src)).setRip nr
        else
          ((s.setReg sz .rax tmp)).setRip nr

  -- ══ P1 BATCH 21 ═══════════════════════════════════════════════════════
  -- CMPXCHG8B (SDM Vol. 2A).  The eight-byte compare-exchange, and the LAST
  -- claimable row of the roster.
  --
  --   IF EDX:EAX = DEST  THEN ZF := 1; DEST := ECX:EBX
  --                      ELSE ZF := 0; EDX:EAX := DEST
  --
  -- ⭐ THE FLAG RULE IS MEASURED, NOT READ.  The SDM says ZF is set by the
  -- comparison and "the CF, PF, AF, SF, and OF flags are unaffected" — which is
  -- the opposite of `cmpxchg` three declarations above, whose flags are the
  -- whole comparison.  Two forms in one family with opposite flag rules is
  -- exactly the place a reader assumes rather than checks, so it was measured
  -- against the oracle BEFORE this constructor existed: over all eighty-two
  -- pre-states, with flag seeds sweeping from all-clear to all-set, `cmpxchg8b`
  -- moves ZF ALONE, while `cmpxchg` at the same shape in the same run moves all
  -- six.  The control is what makes the first reading mean something — a form
  -- that changed no flag at all would look identical if the harness had stopped
  -- watching flags.
  --
  -- ⚠️ AND `Flags.sub` IS NOT THE RULE HERE, though it is for `cmpxchg`.  ZF is
  -- set by an EQUALITY, not by a subtraction whose other five flags happen to be
  -- discarded: the two agree on ZF and the second would be a false description
  -- of what this instruction computes.
  --
  -- ⛔ EVERY REGISTER WRITE ON THE UNEQUAL BRANCH IS THIRTY-TWO BITS AND NONE IS
  -- A NO-OP.  `EDX:EAX := DEST` clears bits 63:32 of both RDX and RAX, so a
  -- state whose RDX already held the right low half is still changed. This is
  -- D53's rule arriving as a design constraint rather than as eighty
  -- disagreements: measured on the oracle at pre-state 13, RDX comes back
  -- `ffffffff00000000` on the EQUAL branch (untouched) and zero-extended on
  -- every other one.
  | .cmpxchg8b dst =>
      if !dst.isMem then
        s.halt (.illegalOperands "cmpxchg8b: memory destination required")
      else
        let tmp := s.readOperand .q nr dst
        -- EDX:EAX, assembled from the two 32-bit halves.  ⚠️ `getReg .d` is the
        -- 32-bit view, so this is EDX and EAX rather than RDX and RAX; writing
        -- it with `.q` would compare the wrong 128 bits of state.
        let acc := (s.getReg .d .rdx) <<< 32 ||| s.getReg .d .rax
        if tmp == acc then
          let src := (s.getReg .d .rcx) <<< 32 ||| s.getReg .d .rbx
          ((s.writeOperand .q nr dst src).setFlags { s.flags with zf := true }).setRip nr
        else
          let s := s.setReg .d .rdx (tmp >>> 32)
          let s := s.setReg .d .rax tmp
          (s.setFlags { s.flags with zf := false }).setRip nr

  -- XADD (SDM Vol. 2A).  `TEMP := SRC + DEST; SRC := DEST; DEST := TEMP`.
  --
  -- ⚠️ THE ORDER IS SDM's AND IT MATTERS FOR ONE SHAPE THIS MODEL DOES NOT SHIP:
  -- `xadd %rax, %rax` names the same register twice, and the two writes then
  -- disagree about what the answer is.  Writing SRC first and DEST second is
  -- what the pseudo-code says, so this model says it too rather than choosing
  -- the order that reads better.
  --
  -- ⭐ THE FLAGS ARE THE ADDITION'S, complete — `xadd` is the second form in
  -- this model to write both operands and the FIRST to write flags while doing
  -- it (`xchg`, batch 10, writes none at all).
  | .xadd sz dst src =>
      if dst.isImm then s.halt (.illegalOperands "xadd: immediate destination")
      else
        let a := s.readOperand sz nr dst
        let b := s.getReg sz src
        let res := Flags.addResult sz a b
        let s := s.setFlags (Flags.add sz a b s.flags)
        let s := s.setReg sz src a
        (s.writeOperand sz nr dst res).setRip nr

  -- SHLD / SHRD (SDM Vol. 2A).  THREE BRANCHES, and the third is why this batch
  -- is not the shift group again.
  --
  --   count = 0            no operation at all, and NO FLAG IS TOUCHED
  --   1 ≤ count ≤ size     the double shift, with AF undefined and OF undefined
  --                        unless the count is 1
  --   count > size         "the result is undefined" — the DESTINATION and all
  --                        six arithmetic flags, reachable at `.w` alone
  --
  -- ⛔⛔ THE COUNT-ZERO BRANCH **DOES** WRITE THE DESTINATION, THOUGH THE SDM
  -- SAYS "IF COUNT = 0 THEN no operation".  This model took the manual at its
  -- word and wrote nothing; the differential run answered with FIFTY-ONE
  -- disagreements, every one of them at `.d`, every one of them the destination
  -- register's upper half.  A 32-bit register write zero-extends, so "write the
  -- value it already had" is observable at exactly one width — and it happens.
  --
  -- ⭐ K's SEMANTICS CALLS THIS AN INTEL BUG IN SO MANY WORDS.  Its
  -- `SHLDL-R32-R32` rule for a masked count of zero is
  -- `setParentValue(concatenateMInt(mi(32,0), MIdest), R) // Intel Bug`, and K's
  -- rules were LEARNED BY EXECUTION on real hardware rather than read off the
  -- manual.  ACL2 x86isa agrees with it.  ⚠️ AND `.shift` IN THIS VERY FILE
  -- ALREADY KNEW: its count-zero branch writes the unchanged value back, with a
  -- comment saying the instruction is a read-modify-write.  The first draft of
  -- this branch departed from the code beside it on the strength of SDM prose,
  -- and the prose was the thing that was wrong.  D54.
  --
  -- ⛔ THE REFUSAL IS THE ONE THING THIS BATCH DECLINES.  See
  -- `dshiftMemUndefined` for why an undefined value in MEMORY is refused rather
  -- than answered, and docs/DECISIONS.md D52.
  | .dshift k sz dst src amt =>
      if !(dshiftEncodable sz) then
        s.halt (.illegalOperands "shld/shrd have no 8-bit encoding")
      else if dst.isImm then
        s.halt (.illegalOperands "shld/shrd: immediate destination")
      else
        let cnt : BitVec 8 :=
          match amt with
          | .imm8 v => v
          | .cl => (s.getReg .b .rcx).setWidth 8
        let n := Flags.shiftCount sz cnt
        let a := s.readOperand sz nr dst
        if dshiftMemUndefined sz dst.isMem n then
          s.halt (.unimplemented
            "shld/shrd: an undefined RESULT in memory (16-bit operand, count > 16)")
        else if n = 0 then
          -- The write-back with the unchanged value, and NO FLAG: see D54.
          (s.writeOperand sz nr dst a).setRip nr
        else if sz.bits < n then
          -- THE BAD-PARAMETERS BRANCH.  SEVEN draws: the six flags in the fixed
          -- order CF, PF, AF, ZF, SF, OF — `divFlags`' order, because it is the
          -- same six — and then the destination's `sz.bits` bits.  The order is
          -- part of the model exactly as the shifts' three draws are.
          let (cfU, s) := s.undefBit
          let (pfU, s) := s.undefBit
          let (afU, s) := s.undefBit
          let (zfU, s) := s.undefBit
          let (sfU, s) := s.undefBit
          let (ofU, s) := s.undefBit
          let (u, s) := s.undefVal sz.bits
          ((s.setFlags (Flags.dshiftBadFlags cfU pfU afU zfU sfU ofU s.flags)).writeOperand
            sz nr dst u).setRip nr
        else
          let b := s.getReg sz src
          let res := Flags.dshiftRes k sz a b n
          -- TWO draws, in the fixed order OF, AF.
          let (ofU, s) := s.undefBit
          let (afU, s) := s.undefBit
          let s := s.setFlags (Flags.dshiftFlags k sz a res n ofU afU s.flags)
          (s.writeOperand sz nr dst res).setRip nr

/-- Run `n` steps of a straight-line list of decoded instructions, taking each
in order.  P0 does not fetch-and-decode from memory (that is P4's Lean decoder);
this is the shape the differential harness drives. -/
def run (is : List Instr) (s : Cpu) : Cpu := is.foldl (fun s i => step i s) s

@[simp] theorem run_nil (s : Cpu) : run [] s = s := rfl
@[simp] theorem run_cons (i : Instr) (is : List Instr) (s : Cpu) :
    run (i :: is) s = run is (step i s) := rfl

/-- A stopped model does not move: the property that makes `Cpu.ms` a real
halt rather than a flag nobody honours. -/
@[simp] theorem step_stopped (i : Instr) (s : Cpu) (h : s.stopped = true) :
    step i s = s := by simp [step, h]

end X86
