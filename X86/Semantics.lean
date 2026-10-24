/-
# X86.Semantics — `step : Instr → Cpu → Cpu`

Plan v1 §3.0: a definitional, executable, SMALL-STEP OPERATIONAL semantics.
Each form is a TOTAL state transformer.  Totality is not achieved by inventing
behaviour: an instruction this model declines to give a meaning to sets `Cpu.ms`
and changes nothing else (the ACL2 x86isa model-state discipline).

WHAT MAKES IT AN INTERPRETER RATHER THAN A RELATION: `step` computes, so the
same definition that the theorems are about is the one the differential harness
RUNS against ACL2 x86isa (no hardware co-simulation has been run).  A relational or
axiomatic semantics could not be differentially tested at all, and a separate
executable "reference" would be a second model to keep honest.

WHERE HOARE LOGIC LIVES: on top, never underneath.  The characterization lemmas
in `X86/Theorems.lean` have the shape `step i s = { s with … }`, which is
exactly what a machine-code Hoare triple (Myreen's `SPEC`) or a big-step block
semantics consumes.  Every such rule is a THEOREM about `step`, so any logic
layered on it is sound by construction.

⚠️ THE ORACLE DRAW ORDER IS PART OF THE MODEL.  A shift with a non-zero masked
count draws exactly THREE bits, in the order CF, OF, AF, whether or not each is
needed; the logic group draws exactly ONE (AF).  Once an instruction's branch is
decided its draws are UNCONDITIONAL, so they never depend on WHICH flags are
undefined — but the draw COUNT does depend on operand values through that branch
(a masked count of zero draws nothing; BSF/BSR drew a further destination width
at a zero source until D346, which made the destination unmodified there).  What must never happen is a branch reading a bit
drawn in the same step: the two opposite-oracle runs that derive the undefined set
could then take different branches and report a difference of CONTROL as undefined
fields (D213).  *(This paragraph said fixing the count makes the cursor "a
deterministic function of the instruction stream" until 2026-09-12. That is false
across a stream — a later branch can read a register an earlier draw wrote — and
what holds is per instruction, the unit a differential case is. D213.)*

LANE. Personal lane, public sources only.  SDM read per instruction, cited at
each case.
-/
import X86.Flags
import X86.Vex

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
canonicity on branch TARGETS (D9) and on one data address only — the byte a
bit-string BT/BTS/BTR/BTC touches (D331), whose register offset can carry it
anywhere in the address space — a pre-existing gap that this batch does not
widen and does not close.  It is
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

/-- ⭐⭐ V9b (D354) — the alignment a VEX packed move requires, AT ITS OWN WIDTH: 16 bytes at VEX.128,
32 at VEX.256 (SDM Vol. 2B, MOVDQA: "aligned on a 16 (VEX.128) / 32 (VEX.256)-byte boundary").  One
definition for both widths, so the 16 and the 32 cannot drift apart; `alignedVex false` is `aligned16`
(`alignedVex_false`, X86/Theorems.lean). -/
def alignedVex (wide : Bool) (a : BitVec 64) : Bool :=
  (a &&& (if wide then 0x1F else 0xF)) == 0

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

/-- ⭐⭐ D331: THE BYTE A BIT-STRING BT/BTS/BTR/BTC ADDRESSES — a memory bit base `ea`
with the register offset `r` at operand size `sz`.  The offset is SIGNED at `sz`, and the
byte is `EA + (offset SAR 3)` (SDM Vol. 2A §3.1.1.9, Table 3-2: `BitBase + offset DIV 8`,
DIV rounding toward negative infinity); the bit inside it is `offset AND 7`.  A function
rather than a `let` in `step` because the harness's ACL2 emitter must name the same byte:
the oracle's memory persists between cases, so a byte outside the watched windows that
the case reads has to be written into its pre-state explicitly. -/
def bitStringByte (s : Cpu) (sz : Size) (ea : Ea) (r : GPR) (h8 : Bool)
    (nr : BitVec 64) : BitVec 64 :=
  ea.addr s nr + (Value.sext sz (s.getReg sz r h8)).sshiftRight 3

/-- P1 BATCH 14: BSF and BSR, which differ in ONE expression.

⭐ THEY ARE ONE FUNCTION BECAUSE EVERYTHING THAT IS SUBTLE ABOUT THEM IS SHARED:
five undefined flags drawn in a fixed order, ZF from the SOURCE, and the
destination at a zero source (UNMODIFIED since D346; drawn from the oracle before it).  `rev` selects which index the non-zero
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
    -- ⭐ D346: the destination is UNMODIFIED — no write at all, so a 32-bit form does not
    -- zero-extend either.  SDM 253666-093US Vol. 2A BSF/BSR: "If the content of the source
    -- operand is zero, the destination operand is unmodified"; AMD APM Vol. 3 and x86isa
    -- (`(if (equal source 0) x86 …)`) agree.  Until D346 this arm drew `sz.bits` oracle bits,
    -- on the SDM's older "undefined" (D40).
    s.setRip nr
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

/-- ⭐⭐⭐ P2 BATCH 37 — `shufps`, folded lane by lane.  Lanes 0-1 are read from
`a` (the DESTINATION) and lanes 2-3 from `b` (the SOURCE); lane `i`'s 2-bit
selector is the immediate's field `i`, and it indexes the FOUR lanes of whichever
operand that lane reads.

⚠️ `if i < 2 then a else b` IS THE WHOLE TWO-SOURCE CONTENT, and it is the one
line a reader coming from `vselectAux` must not skim: that combinator has a single
`src` and this one switches operand at the halfway point.  Getting it backwards
produces a model that is bit-identical to this one whenever `a = b`. -/
private def vshufpsAux (a b : BitVec 128) (sel : Nat) : Nat → BitVec 128
  | 0 => 0
  | i + 1 =>
      let src := if i < 2 then a else b
      (vshufpsAux a b sel i)
        ||| (((src.extractLsb' (((sel >>> (2 * i)) % 4) * 32) 32).setWidth 128)
              <<< (i * 32))

/-- ⭐⭐ THE TWO-SOURCE SHUFFLE COMBINATOR.  `a` is the DESTINATION and `b` the
SOURCE at both operand shapes, the same convention `vbinApply`'s unpack arm uses.

⛔ THE FOUR IS THE IMMEDIATE'S FIELD COUNT (8 bits over 2), not `128 / w` —
`vselect`'s reason, restated because this combinator folds a different count for
each kind: `ps` writes four 32-bit lanes and `pd` writes two 64-bit ones, and
`pd` reads only the immediate's LOW TWO BITS.

⚠️ `shufpd` IS WRITTEN OUT RATHER THAN FOLDED.  Two lanes and two one-bit
selectors is a fold whose recursion would be longer than the thing it computes,
and a fold here would put a `%` and a shift on the kernel's path for no reuse. -/
def vshufpApply (k : VShufpKind) (a b : BitVec 128) (sel : BitVec 8) : BitVec 128 :=
  match k with
  | .ps => vshufpsAux a b sel.toNat 4
  | .pd =>
      ((a.extractLsb' ((sel.toNat % 2) * 64) 64).setWidth 128)
        ||| (((b.extractLsb' (((sel.toNat >>> 1) % 2) * 64) 64).setWidth 128) <<< 64)

/-! ### D336 (V1b) — PSHUFB, PALIGNR, PINSRD/Q, PEXTRD/Q

x86isa refuses all six (`scripts/oracle_availability.py`), so each is refereed by a
processor (`hwprobe/mk_shuf_rows.py`, D336) and pinned to the same rows by `decide`
in `Tests/AnchorsShuf.lean`.  None writes a flag. -/

/-- One byte of PSHUFB, folded from the top down: control byte `i` of `ctl` either
zeroes result byte `i` (its bit 7) or selects byte `ctl[8i+3:8i]` of `a`, the
destination's ORIGINAL value.  ⚠️ Bits 6:4 of the control byte are ignored — the
index is taken `% 16`, never the whole low seven bits. -/
def vshufbAux (a ctl : BitVec 128) : Nat → BitVec 128
  | 0 => 0
  | i + 1 =>
      let c := ctl.extractLsb' (8 * i) 8
      (vshufbAux a ctl i)
        ||| (if c.msb then 0
             else ((a.extractLsb' (8 * (c.toNat % 16)) 8).setWidth 128) <<< (8 * i))

/-- PSHUFB (SDM Vol. 2B): sixteen bytes, each from `a` (the destination) by the
matching control byte of `ctl` (the source), or zero. -/
def vshufbApply (a ctl : BitVec 128) : BitVec 128 := vshufbAux a ctl 16

/-- PALIGNR (SDM Vol. 2B): `((DEST << 128) OR SRC) >> (imm × 8)`, low 128 bits.
⚠️ The guard is the rule, not an optimisation: at `imm ≥ 32` the whole 256-bit
concatenation has been shifted out and the result is zero. -/
def valignrApply (dst src : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  if imm.toNat > 31 then 0
  else ((((dst.setWidth 256) <<< 128) ||| src.setWidth 256) >>> (8 * imm.toNat)).setWidth 128

/-- The lane PINSR*/PEXTR* select: `imm[1:0]` at 32 bits, `imm[0]` at 64 — the
lane count is `128 / width`, and the imm8 bits above it are ignored. -/
def vlaneSel (sz : Size) (imm : BitVec 8) : Nat := imm.toNat % (128 / sz.bits)

/-- PINSRD/PINSRQ (SDM Vol. 2B): the `sz`-bit `v` replaces lane `vlaneSel sz imm`
of `dst`; every other bit of `dst` is kept. -/
def vinsrApply (sz : Size) (dst : BitVec 128) (v : Val) (imm : BitVec 8) : BitVec 128 :=
  let sh := sz.bits * vlaneSel sz imm
  let m : BitVec 128 := ((Value.trunc sz (BitVec.allOnes 64)).setWidth 128) <<< sh
  (dst &&& ~~~m) ||| (((Value.trunc sz v).setWidth 128) <<< sh)

/-- PEXTRD/PEXTRQ (SDM Vol. 2B): lane `vlaneSel sz imm` of `src`, zero above the
width (the GPR write then zero-extends a 32-bit lane by the ordinary rule). -/
def vextrApply (sz : Size) (src : BitVec 128) (imm : BitVec 8) : Val :=
  (src.extractLsb' (sz.bits * vlaneSel sz imm) sz.bits).setWidth 64

/-! ### D338 (V2) — SHA256MSG1, SHA256MSG2, SHA256RNDS2 (SHA-NI, legacy SSE)

x86isa refuses all three (`scripts/oracle_availability.py`, D338 prediction 1), so
each is refereed by a processor (`hwprobe/mk_sha_rows.py`, D338) and pinned to the
same rows by `decide` in `Tests/AnchorsSha.lean`.  None writes a flag.  The six
functions of FIPS 180-4 §4.1.2 are stated once, on 32-bit words, and every rule
below is built from them; dword `i` of a 128-bit value is bits `32i+31 : 32i`. -/

/-- FIPS 180-4 σ0 (the SDM's `σ0`): `ROR 7 ⊕ ROR 18 ⊕ SHR 3`. -/
def shaSig0 (w : BitVec 32) : BitVec 32 := w.rotateRight 7 ^^^ w.rotateRight 18 ^^^ (w >>> 3)
/-- FIPS 180-4 σ1: `ROR 17 ⊕ ROR 19 ⊕ SHR 10`. -/
def shaSig1 (w : BitVec 32) : BitVec 32 := w.rotateRight 17 ^^^ w.rotateRight 19 ^^^ (w >>> 10)
/-- FIPS 180-4 Σ0: `ROR 2 ⊕ ROR 13 ⊕ ROR 22`. -/
def shaSum0 (a : BitVec 32) : BitVec 32 := a.rotateRight 2 ^^^ a.rotateRight 13 ^^^ a.rotateRight 22
/-- FIPS 180-4 Σ1: `ROR 6 ⊕ ROR 11 ⊕ ROR 25`. -/
def shaSum1 (e : BitVec 32) : BitVec 32 := e.rotateRight 6 ^^^ e.rotateRight 11 ^^^ e.rotateRight 25
/-- FIPS 180-4 Ch: `(E ∧ F) ⊕ (¬E ∧ G)`. -/
def shaCh (e f g : BitVec 32) : BitVec 32 := (e &&& f) ^^^ (~~~e &&& g)
/-- FIPS 180-4 Maj: `(A ∧ B) ⊕ (A ∧ C) ⊕ (B ∧ C)`. -/
def shaMaj (a b c : BitVec 32) : BitVec 32 := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)

/-- Dword `i` of a 128-bit value. -/
def shaD (x : BitVec 128) (i : Nat) : BitVec 32 := x.extractLsb' (32 * i) 32

/-- Four dwords to a 128-bit value, HIGH first: `shaPack d3 d2 d1 d0` (the SDM's
`DEST[127:96] … DEST[31:0]` order). -/
def shaPack (d3 d2 d1 d0 : BitVec 32) : BitVec 128 :=
  (d3.setWidth 128 <<< 96) ||| (d2.setWidth 128 <<< 64) ||| (d1.setWidth 128 <<< 32) ||| d0.setWidth 128

/-- SHA256MSG1 (SDM Vol. 2B) on the dword `w4 = SRC2[31:0]`: `W3 + σ0(W4) : W2 + σ0(W3) :
W1 + σ0(W2) : W0 + σ0(W1)`, W3..W0 the dwords of SRC1.  Stated on `w4` so that "only
SRC2's LOW dword is read" is the TYPE of the argument, not a remark. -/
def sha256msg1W (src1 : BitVec 128) (w4 : BitVec 32) : BitVec 128 :=
  shaPack (shaD src1 3 + shaSig0 w4) (shaD src1 2 + shaSig0 (shaD src1 3))
    (shaD src1 1 + shaSig0 (shaD src1 2)) (shaD src1 0 + shaSig0 (shaD src1 1))

/-- SHA256MSG2 (SDM Vol. 2B) on `w14 = SRC2[95:64]`, `w15 = SRC2[127:96]`:
`W16 := SRC1[31:0] + σ1(W14)`, `W17 := SRC1[63:32] + σ1(W15)`, and ⚠️ `W18`, `W19`
from `W16`, `W17` — the serial chain the SDM's Operation states.  DEST = W19:W18:W17:W16. -/
def sha256msg2W (src1 : BitVec 128) (w14 w15 : BitVec 32) : BitVec 128 :=
  let w16 := shaD src1 0 + shaSig1 w14
  let w17 := shaD src1 1 + shaSig1 w15
  shaPack (shaD src1 3 + shaSig1 w17) (shaD src1 2 + shaSig1 w16) w17 w16

/-- One FIPS 180-4 round on `(A, B, C, D, E, F, G, H)` with the word `wk` (= K[t] + W[t]):
`T1 := H + Σ1(E) + Ch(E,F,G) + wk`, `T2 := Σ0(A) + Maj(A,B,C)`, and the state shifts to
`(T1+T2, A, B, C, D+T1, E, F, G)`. -/
def shaRound (st : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32)
    (wk : BitVec 32) :
    BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  let (a, b, c, d, e, f, g, h) := st
  let t1 := h + shaSum1 e + shaCh e f g + wk
  let t2 := shaSum0 a + shaMaj a b c
  (t1 + t2, a, b, c, d + t1, e, f, g)

/-- SHA256RNDS2 (SDM Vol. 2B) on `wk0 = XMM0[31:0]`, `wk1 = XMM0[63:32]`: A B E F from
SRC2 (`[127:96] [95:64] [63:32] [31:0]`), C D G H from SRC1 (the same positions), two
rounds, DEST := A₂ : B₂ : E₂ : F₂.  ⚠️ Stated on the two words, so "XMM0's high
quadword is not read" is the TYPE again. -/
def sha256rnds2W (src1 src2 : BitVec 128) (wk0 wk1 : BitVec 32) : BitVec 128 :=
  let s0 := (shaD src2 3, shaD src2 2, shaD src1 3, shaD src1 2,
             shaD src2 1, shaD src2 0, shaD src1 1, shaD src1 0)
  let (a, b, _, _, e, f, _, _) := shaRound (shaRound s0 wk0) wk1
  shaPack a b e f

/-- The three kinds on the WHOLE operands — SRC1 (the destination's value), SRC2, and
XMM0 — each reading only the dwords its rule names. -/
def shaApply (k : ShaKind) (src1 src2 xmm0 : BitVec 128) : BitVec 128 :=
  match k with
  | .msg1 => sha256msg1W src1 (shaD src2 0)
  | .msg2 => sha256msg2W src1 (shaD src2 2) (shaD src2 3)
  | .rnds2 => sha256rnds2W src1 src2 (shaD xmm0 0) (shaD xmm0 1)

/-! ### D342 (V4) — the AES round and the carry-less product

x86isa refuses AESENC, AESENCLAST and PCLMULQDQ (and their VEX forms); `hwprobe/mk_aes_rows.py`
referees them (D342) and `Tests/AnchorsAes.lean` pins this model to the same rows.  The state is
FIPS-197's column-major 4×4 matrix: byte `r + 4c` (bits 8(r+4c)+7 : 8(r+4c)) is s[r][c]. -/

/-- FIPS-197 Figure 7, the S-box, as a TABLE — GENERATED by `hwprobe/mk_aes_rows.py`'s derivation
(the GF(2^8) inverse, then the affine map), never typed; `Tests/AnchorsAes.lean` holds the model
to FIPS-197 Appendix B round by round. -/
def aesSbox : List (BitVec 8) := [
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16 ]

/-- Byte `i` of a 128-bit value. -/
def aesByte (v : BitVec 128) (i : Nat) : BitVec 8 := v.extractLsb' (8 * i) 8

/-- The 128-bit value whose byte `i` is `f i`. -/
def aesOfBytes (f : Nat → BitVec 8) : BitVec 128 :=
  (List.range 16).foldl (fun acc i => acc ||| ((f i).setWidth 128 <<< (8 * i))) 0

/-- ShiftRows (FIPS-197 §5.1.2): s'[r][c] = s[r][(c + r) mod 4]. -/
def aesShiftRows (v : BitVec 128) : BitVec 128 :=
  aesOfBytes fun i => aesByte v (i % 4 + 4 * ((i / 4 + i % 4) % 4))

/-- SubBytes (FIPS-197 §5.1.1): every byte through the S-box. -/
def aesSubBytes (v : BitVec 128) : BitVec 128 :=
  aesOfBytes fun i => aesSbox.getD (aesByte v i).toNat 0

/-- Multiplication by x in GF(2^8) mod x^8 + x^4 + x^3 + x + 1 (FIPS-197 §4.2.1). -/
def aesXtime (b : BitVec 8) : BitVec 8 := (b <<< 1) ^^^ (if b.msb then 0x1b else 0)

/-- MixColumns (FIPS-197 §5.1.3): each column times {03}x³ + {01}x² + {01}x + {02}, i.e.
s'[r][c] = 2·s[r][c] ⊕ 3·s[r+1][c] ⊕ s[r+2][c] ⊕ s[r+3][c] (rows mod 4). -/
def aesMixColumns (v : BitVec 128) : BitVec 128 :=
  aesOfBytes fun i =>
    let a := fun k => aesByte v (4 * (i / 4) + (i % 4 + k) % 4)
    aesXtime (a 0) ^^^ (aesXtime (a 1) ^^^ a 1) ^^^ a 2 ^^^ a 3

/-- One AES encryption round (SDM Vol. 2A AESENC / AESENCLAST): ShiftRows, SubBytes, then
MixColumns unless `last`, then the round key XORed in. -/
def aesRound (last : Bool) (state key : BitVec 128) : BitVec 128 :=
  let s := aesSubBytes (aesShiftRows state)
  (if last then s else aesMixColumns s) ^^^ key

/-- The carry-less product of two 64-bit values: bit 127 is always 0. -/
def clmul64 (a b : BitVec 64) : BitVec 128 :=
  (List.range 64).foldl
    (fun acc i => if b.getLsbD i then acc ^^^ (a.setWidth 128 <<< i) else acc) 0

/-- PCLMULQDQ (SDM Vol. 2B): `src1`'s quadword imm8[0] times `src2`'s quadword imm8[4]; every other
bit of imm8 is ignored. -/
def pclmulApply (src1 src2 : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  clmul64 (if imm.getLsbD 0 then (src1 >>> 64).setWidth 64 else src1.setWidth 64)
    (if imm.getLsbD 4 then (src2 >>> 64).setWidth 64 else src2.setWidth 64)

/-- One saturated byte of `packuswb`, folded from the top down.  ⚠️ The source
lane is read SIGNED and the result lane is UNSIGNED, which is the asymmetry the
instruction is named for: a negative word becomes 0, not 255. -/
private def vpackusAux (src : BitVec 128) (base : Nat) : Nat → BitVec 128
  | 0 => 0
  | i + 1 =>
      let w := src.extractLsb' ((i) * 16) 16
      let b : BitVec 8 :=
        if w.msb then 0                       -- negative saturates DOWN to 0
        else if 255 < w.toNat then 255        -- and above 255 UP to 255
        else w.setWidth 8
      (vpackusAux src base i) ||| ((b.setWidth 128) <<< ((base + i) * 8))

/-- ⭐⭐ `packuswb`'s combinator.  The DESTINATION's eight words become the low
eight bytes and the SOURCE's the high eight — the order the SDM gives and the one
objdump's own comment shows. -/
def vpackus (dst src : BitVec 128) : BitVec 128 :=
  vpackusAux dst 0 8 ||| vpackusAux src 8 8

/-! ### D335 (V1a) — the packed-integer arithmetic x86isa refuses, refereed by silicon

Every helper below is the SDM Vol. 2B Operation of one instruction, read at the lane width the rule
names.  ⚠️ A pair-reading rule (`pmaddwd` reads two words per dword, `pmaddubsw` two bytes per word,
`psadbw` eight bytes per quadword, `pmuludq` the low dword of each quadword) IS lane-wise at the WIDER
width — lane `i` of the result depends only on lane `i` of each operand there — so it goes through
`vlanes` at that width rather than a new fold.  `packssdw` NARROWS, as `packuswb` does, and gets its
own fold for `vpackus`'s reason. -/

/-- SaturateToSignedWord of a value held sign-extended in 32 bits (SDM Vol. 2B, PACKSSDW/PADDSW/PMADDUBSW):
below −32768 gives 8000H, above 32767 gives 7FFFH, else the low word. -/
def ssatW (v : BitVec 32) : BitVec 16 :=
  if v.slt (0xFFFF8000 : BitVec 32) then 0x8000
  else if (0x00007FFF : BitVec 32).slt v then 0x7FFF
  else v.setWidth 16

/-- One dword of `pmaddwd`: two SIGNED word products ADDED, mod 2^32 — no saturation; the one overflowing
case (all four words 8000H) wraps to 80000000H, as the SDM says. -/
def vmaddwdLane (x y : BitVec 32) : BitVec 32 :=
  (x.extractLsb' 0 16).signExtend 32 * (y.extractLsb' 0 16).signExtend 32
    + (x.extractLsb' 16 16).signExtend 32 * (y.extractLsb' 16 16).signExtend 32

/-- One word of `pmaddubsw`: the DESTINATION's two bytes UNSIGNED (`setWidth`), the SOURCE's two SIGNED
(`signExtend`), the pair summed and signed-saturated.  ⛔ The asymmetry is the instruction. -/
def vmaddubswLane (x y : BitVec 16) : BitVec 16 :=
  ssatW ((x.extractLsb' 0 8).setWidth 32 * (y.extractLsb' 0 8).signExtend 32
    + (x.extractLsb' 8 8).setWidth 32 * (y.extractLsb' 8 8).signExtend 32)

/-- One word of `pmulhrsw`: `TEMP := ((x*y) >> 14) + 1; result := TEMP[16:1]`, the product SIGNED 32-bit.
⚠️ The shift may be logical: bits 16:1 of the result read product bits 30:14 and a carry upward, which an
arithmetic and a logical shift agree on. -/
def vmulhrswLane (x y : BitVec 16) : BitVec 16 :=
  (((x.signExtend 32 * y.signExtend 32) >>> 14) + 1).extractLsb' 1 16

/-- One quadword of `psadbw`: the sum of the eight unsigned byte differences' absolute values, in the low
word; the 48 bits above it are ZERO by construction (the sum is at most 8 × 255 = 7F8H). -/
def vsadLane (x y : BitVec 64) : BitVec 64 :=
  (List.range 8).foldl (fun acc i =>
    let p := (x.extractLsb' (8 * i) 8).toNat
    let q := (y.extractLsb' (8 * i) 8).toNat
    acc + BitVec.ofNat 64 (if q ≤ p then p - q else q - p)) 0

/-- One signed-saturated word of `packssdw`, folded from the top down (`vpackusAux`'s shape). -/
private def vpackssAux (src : BitVec 128) (base : Nat) : Nat → BitVec 128
  | 0 => 0
  | i + 1 =>
      (vpackssAux src base i) ||| (((ssatW (src.extractLsb' (i * 32) 32)).setWidth 128) <<< ((base + i) * 16))

/-- `packssdw`: the DESTINATION's four dwords become the LOW four words, the SOURCE's the high four. -/
def vpackss (dst src : BitVec 128) : BitVec 128 :=
  vpackssAux dst 0 4 ||| vpackssAux src 4 4

/-- The packed binary operations.  ⚠️ NO FLAG IS WRITTEN BY ANY OF THEM — SDM
Vol. 2B gives "Flags Affected: None" for every entry here, and the easiest way to
get a packed operation wrong is to reach for `BinKind`'s flag machinery by
analogy.  `step`'s arm below writes XMM and RIP and nothing else. -/
def vbinApply (k : VBinKind) (a b : BitVec 128) : BitVec 128 :=
  match k with
  -- The bitwise trio: lane-independent, so they do not go through `vlanes` at
  -- all.  Routing them through a one-lane call would be a claim that the SDM
  -- defines them lane-wise, which it does not.
  -- ⭐ P2 BATCH 34.  The `ps`/`pd` spellings are the SAME function at another
  -- opcode, so they join the arm rather than copying it: nine new kinds, three
  -- new arms.  A second `a &&& b` under another name would diverge the day one
  -- of them is corrected ([[feedback-a-duplicate-born-in-agreement]]).
  | .xor | .xorps | .xorpd => a ^^^ b
  | .and | .andps | .andpd => a &&& b
  | .or  | .orps  | .orpd  => a ||| b
  -- ⛔⛔ THE DESTINATION IS COMPLEMENTED, NOT THE SOURCE (SDM Vol. 2B, PANDN:
  -- `DEST ← (NOT DEST) AND SRC`), and `a` is the destination at both operand
  -- shapes.  `a &&& (~~~b)` is the model the mnemonic suggests and it is a
  -- different function wherever the operands differ — planted as
  -- `wrongAndnComplementsSource`.  ⭐ K agrees independently: `pandn_xmm_xmm.k`
  -- is `andMInt(negMInt(DEST), SRC)`.
  | .andn | .andnps | .andnpd => (~~~a) &&& b
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
  -- ⭐ P2 BATCH 37: the `ps`/`pd` spellings JOIN the arm they are identical to,
  -- rather than copying it — batch 34's rule, and for its reason: a second
  -- `vunpack 32 false a b` under another name would diverge the day one of them
  -- is corrected.  `unpcklps` IS `punpckldq` at 32-bit lanes and `unpcklpd` IS
  -- `punpcklqdq` at 64, decided on K's leaf sequence (the TEXT of two of the four
  -- differs, by pure re-association) and confirmed by LLVM's disassembler.
  | .unpckld | .unpcklps => vunpack 32 false a b
  | .unpcklq | .unpcklpd => vunpack 64 false a b
  | .unpckhb => vunpack 8  true  a b
  | .unpckhw => vunpack 16 true  a b
  | .unpckhd | .unpckhps => vunpack 32 true  a b
  | .unpckhq | .unpckhpd => vunpack 64 true  a b
  -- ⭐⭐⭐ P2 BATCH 17 — THE PACKED COMPARES.  A lane becomes ALL ONES or all
  -- zeros; `-1` is `allOnes` at every width `vlanes` is called at here, exactly
  -- as it is in `vshiftLane`'s sign-fill arm.
  --
  -- ⛔ `slt`/`sle` ARE THE SIGNED COMPARISONS AND `<` ON `BitVec` IS NOT.  Lean's
  -- `<` on `BitVec` is UNSIGNED, so writing `a < b` here would compile, would be
  -- bit-identical to this on every lane whose operands are both non-negative, and
  -- would be wrong exactly where the SDM's word `signed` is doing work.  The
  -- planted `unsigned` arm is that model, and it agrees with this one at 61 of 88
  -- pre-states for `pcmpgtb %xmm1,%xmm0` — so 27 states carry the whole rule.
  | .cmpeqb => vlanes 8  (fun x y => if x == y then -1 else 0) a b
  | .cmpeqw => vlanes 16 (fun x y => if x == y then -1 else 0) a b
  | .cmpeqd => vlanes 32 (fun x y => if x == y then -1 else 0) a b
  -- ⚠️ `y.slt x`, not `x.sgt y`: the SDM's `DEST > SRC` with `a` the destination.
  | .cmpgtb => vlanes 8  (fun x y => if y.slt x then -1 else 0) a b
  | .cmpgtw => vlanes 16 (fun x y => if y.slt x then -1 else 0) a b
  | .cmpgtd => vlanes 32 (fun x y => if y.slt x then -1 else 0) a b
  -- ⭐⭐⭐ P2 BATCH 18 — `packuswb`.  ⛔ NOT `vlanes`: this is the first operation
  -- here that NARROWS, so lane `i` of the result is not a function of lane `i` of
  -- the operands, and the combinator that pairs them cannot express it.
  | .packuswb => vpackus a b
  -- ⭐⭐ P2 BATCH 38 — MINPS / MAXPS: four binary32 lanes, `a`'s lane first.
  -- The carrier is 64 bits and the lane 32, so the lane is widened in and the
  -- result truncated out; `SoftFloat` masks to the format and never reads above it.
  | .minps => vlanes 32 (fun x y => (SoftFloat.fmin SoftFloat.binary32
                            (x.setWidth 64) (y.setWidth 64)).setWidth 32) a b
  | .maxps => vlanes 32 (fun x y => (SoftFloat.fmax SoftFloat.binary32
                            (x.setWidth 64) (y.setWidth 64)).setWidth 32) a b
  -- ⭐⭐ D335 (V1a) — refereed by silicon (`hwprobe/mk_simda_rows.py`), never by a vector.
  | .maddwd   => vlanes 32 vmaddwdLane a b
  | .maddubsw => vlanes 16 vmaddubswLane a b
  | .mullw    => vlanes 16 (· * ·) a b
  | .mulhrsw  => vlanes 16 vmulhrswLane a b
  -- the EVEN dwords, UNSIGNED, full 64-bit product: the low dword of each quadword lane
  | .muludq   => vlanes 64 (fun x y => (x.setWidth 32).setWidth 64 * (y.setWidth 32).setWidth 64) a b
  | .addsw    => vlanes 16 (fun x y => ssatW (x.signExtend 32 + y.signExtend 32)) a b
  -- ⚠️ `<` on `BitVec` is UNSIGNED, which is exactly the comparison `psubus*` makes.
  | .subusw   => vlanes 16 (fun x y => if x < y then 0 else x - y) a b
  | .subusb   => vlanes 8  (fun x y => if x < y then 0 else x - y) a b
  -- ⛔ SIGNED: `slt`, not `<` (batch 17's trap).  `DEST > SRC` keeps DEST, else SRC.
  | .maxsw    => vlanes 16 (fun x y => if y.slt x then x else y) a b
  | .sadbw    => vlanes 64 vsadLane a b
  | .packssdw => vpackss a b

/-- ⭐⭐ P2 BATCH 38 — THE SCALAR MIN/MAX WRITE (SDM Vol. 2B, MINSS/MINSD/MAXSS/
MAXSD): the destination's low lane becomes `fmin`/`fmax` of `d`'s low lane and
`b`, and every bit above the lane is KEPT.  ONE function for both operand shapes,
so the register and memory forms cannot come to disagree about the write rule;
they differ only in where `b` is read. -/
def vminmaxLow (isMax : Bool) (sz : Size) (d : BitVec 128) (b : BitVec 64) : BitVec 128 :=
  let f := if sz == .q then SoftFloat.binary64 else SoftFloat.binary32
  let n := sz.bits
  let r := (if isMax then SoftFloat.fmax else SoftFloat.fmin) f (d.setWidth 64) b
  ((d >>> n) <<< n) ||| ((r.setWidth n).setWidth 128)

/-- ⭐⭐ P2 BATCH 39 — THE CONVERSION WRITE (SDM Vol. 2B, CVTSS2SD/CVTSI2SD): the
destination's low 64 bits become the binary64 of `b`'s low 32 bits — read as a
binary32 or, when `fromInt`, as a signed int32 — and the upper 64 bits are KEPT.
ONE function for every operand shape, as `vminmaxLow`: the forms differ only in
where `b` is read. -/
def vcvt2sdLow (d : BitVec 128) (b : BitVec 64) : BitVec 128 :=
  ((d >>> 64) <<< 64) ||| (SoftFloat.f32to64 b).setWidth 128

/-- ⭐⭐ SUB-GROUP B4 — THE INTEGER CONVERSION's LANE RULE, one function for every
operand shape (as `vcvt2sdLow` was): `b` read as a signed int32 or int64 (`wide`)
into the low binary64 (`dbl`) or binary32 lane of `d` under MXCSR.RC, with every
bit above the lane PRESERVED — the legacy SSE rule.

⚠️ THE LANE WIDTH VARIES WITH `dbl` AND THE SOURCE WIDTH WITH `wide`, and they are
INDEPENDENT: all four pairings are real encodings.  The binary32 lane write is
`vcvtsd2ssLow`'s, bit for bit.

The flags come out of the SAME call as the value, so a result and its flags cannot
disagree about the rounding — `varith`'s reason, and why this returns a pair where
`vcvt2sdLow` returns a value.  ⛔ Batch 39's int path raised nothing and needed no
pair; three of B4's four pairings ROUND. -/
def cvtsi2Low (dbl wide : Bool) (rc : Nat) (d : BitVec 128) (b : BitVec 64) :
    BitVec 128 × BitVec 32 :=
  let (r, fl) := SoftFloat.i2f (if dbl then SoftFloat.binary64 else SoftFloat.binary32) wide rc b
  if dbl then (((d >>> 64) <<< 64) ||| r.setWidth 128, fl)
  else (((d >>> 32) <<< 32) ||| ((r.setWidth 32).setWidth 128), fl)

/-- ⭐⭐ P2 BATCH 40 — THE TRUNCATION's LANE RULE, one function for both operand
shapes (as `vcvt2sdLow`): `b`'s low binary64 (`dbl`) or binary32 lane, truncated
to an int64 (`wide`) or an int32.  The forms differ only in where `b` is read. -/
def cvttLane (dbl wide : Bool) (b : BitVec 64) : BitVec 64 :=
  SoftFloat.truncToInt (if dbl then SoftFloat.binary64 else SoftFloat.binary32)
    (if wide then 64 else 32) b

/-- ⭐⭐⭐ SUB-GROUP B1/B2 — THE SCALAR FP ARITHMETIC WRITE AND ITS FLAGS, ONE PAIR (SDM
Vol. 2B, ADDS?/SUBS?/MULS?/DIVS?): the destination's low lane becomes the chosen
`SoftFloat` operation of `d`'s low lane and `b` under the rounding mode `rc` (MXCSR bits
13–14), and every bit above the lane is KEPT.  The flags come out of the same call, so a
result and its flags cannot disagree about the rounding; the register and memory forms
differ only in where `b` is read.

⚠️ **THE OPERATION IS THE ONLY THING THAT VARIES**, which is the whole content of D268 §8's
fold: the format, the rounding mode, the lane-preserving write and the flag path are one
piece of code for all four.  ⛔ `sub` dispatches to `faddsub` with its `sub` flag rather
than negating `b` here — a NaN's sign must survive, and negating at this level would change
what a SNaN propagates. -/
def varithCall (op : VArithOp) (f : SoftFloat.Fmt) (rc : Nat) (a b : BitVec 64)
    : BitVec 64 × BitVec 32 :=
  match op with
  | .add => SoftFloat.faddsub f rc false a b
  | .sub => SoftFloat.faddsub f rc true  a b
  | .mul => SoftFloat.fmul    f rc       a b
  | .div => SoftFloat.fdiv    f rc       a b

def varithLow (op : VArithOp) (sz : Size) (rc : Nat) (d : BitVec 128) (b : BitVec 64)
    : BitVec 128 × BitVec 32 :=
  let f := if sz == .q then SoftFloat.binary64 else SoftFloat.binary32
  let n := sz.bits
  let (r, fl) := varithCall op f rc (d.setWidth 64) b
  (((d >>> n) <<< n) ||| ((r.setWidth n).setWidth 128), fl)

/-- ⭐⭐⭐ SUB-GROUP B6b — SQRTSS / SQRTSD's WRITE AND ITS FLAGS, ONE PAIR (D291): the low lane of `d` becomes
`SoftFloat.fsqrt` of `b`'s low lane under `rc`, and every bit above the lane is KEPT, as `varithLow` keeps it. -/
def vsqrtLow (sz : Size) (rc : Nat) (d : BitVec 128) (b : BitVec 64) : BitVec 128 × BitVec 32 :=
  let n := sz.bits
  let (r, fl) := SoftFloat.fsqrt (if sz == .q then SoftFloat.binary64 else SoftFloat.binary32) rc b
  (((d >>> n) <<< n) ||| ((r.setWidth n).setWidth 128), fl)

/-- ⭐⭐⭐ SUB-GROUP B5 — THE PACKED FP ARITHMETIC WRITE AND ITS FLAGS, ONE PAIR (SDM Vol. 2B,
ADDP?/SUBP?/MULP?/DIVP?): lane `i` of the result is `varithCall` of lane `i` of `a` and of `b`, rounded
under `rc`, and the flags are the OR of the lanes' flags (LANE-OR, read on silicon before this
existed: D281).  ⚠️ **THE SCALAR FORM'S OWN CALL, PER LANE** — `varithCall` is factored out of
`varithLow` so the two cannot come to disagree about any operation.  A binary32 lane is widened into
the 64-bit carrier with its neighbour's bits above it; `SoftFloat` masks to the format and never
reads above it (batch 38's `minps` rests on the same fact). -/
def vparithAll (op : VArithOp) (dbl : Bool) (rc : Nat) (a b : BitVec 128)
    : BitVec 128 × BitVec 32 :=
  let f := if dbl then SoftFloat.binary64 else SoftFloat.binary32
  let w := if dbl then 64 else 32
  (List.range (128 / w)).foldl (fun (acc : BitVec 128 × BitVec 32) i =>
    let p := varithCall op f rc ((a >>> (w * i)).setWidth 64) ((b >>> (w * i)).setWidth 64)
    (acc.1 ||| (((p.1.setWidth w).setWidth 128) <<< (w * i)), acc.2 ||| p.2)) (0, 0)

/-- ⭐⭐⭐ SUB-GROUP B7 — SQRTPS's WRITE AND ITS FLAGS (D295): lane `i` of the result is `SoftFloat.fsqrt` of lane `i` of
`b` (binary32, four lanes), and the flags are the OR of the lanes' (LANE-OR, read on silicon: D294). -/
def vsqrtpsAll (rc : Nat) (b : BitVec 128) : BitVec 128 × BitVec 32 :=
  (List.range 4).foldl (fun (acc : BitVec 128 × BitVec 32) i =>
    let p := SoftFloat.fsqrt SoftFloat.binary32 rc ((b >>> (32 * i)).setWidth 64)
    (acc.1 ||| (((p.1.setWidth 32).setWidth 128) <<< (32 * i)), acc.2 ||| p.2)) (0, 0)

/-- ⭐⭐⭐ SUB-GROUP B7 — CVTPD2PS's WRITE AND ITS FLAGS (D295): the two binary64 lanes of `b`, each by
`SoftFloat.f64to32` (CVTSD2SS's own call), become the low two binary32 lanes; bits 127:64 are ZERO. -/
def vcvtpd2psAll (rc : Nat) (b : BitVec 128) : BitVec 128 × BitVec 32 :=
  (List.range 2).foldl (fun (acc : BitVec 128 × BitVec 32) i =>
    let p := SoftFloat.f64to32 rc ((b >>> (64 * i)).setWidth 64)
    (acc.1 ||| (((p.1.setWidth 32).setWidth 128) <<< (32 * i)), acc.2 ||| p.2)) (0, 0)

/-- MXCSR.RC, bits 13–14, as the `Nat` `SoftFloat.roundPack` reads (0 nearest · 1 down · 2 up ·
3 toward zero, SDM Vol. 1 §10.2.3). -/
def mxcsrRC (m : BitVec 32) : Nat := ((m >>> 13) &&& 3#32).toNat

/-- ⭐⭐⭐ SUB-GROUP B3 — CVTSD2SS's WRITE AND ITS FLAGS, ONE PAIR (SDM Vol. 2A): the low binary32
lane of the destination becomes `SoftFloat.f64to32` of `b`, rounded under `rc`, and **every bit
above bit 31 is KEPT** (legacy SSE: `DEST[MAXVL-1:32]` unmodified). The destination's old low lane
is not an input.  The register and memory forms differ only in where `b` is read. -/
def vcvtsd2ssLow (rc : Nat) (d : BitVec 128) (b : BitVec 64) : BitVec 128 × BitVec 32 :=
  let (r, fl) := SoftFloat.f64to32 rc b
  (((d >>> 32) <<< 32) ||| ((r.setWidth 32).setWidth 128), fl)

/-! ### ⭐⭐⭐ SUB-GROUP B0 — THE FLAGS EACH LANDED FP FORM RAISES (D266).
Each function reads exactly the operands its value rule reads, so a form's flags and
its result cannot come to disagree about which lane they looked at. -/

/-- MINSS/MINSD/MAXSS/MAXSD: IE on any NaN, DE on a denormal (SDM Vol. 2B). -/
def vminmaxFlags (sz : Size) (d : BitVec 128) (b : BitVec 64) : BitVec 32 :=
  SoftFloat.preFlags (if sz == .q then SoftFloat.binary64 else SoftFloat.binary32) true
    (d.setWidth 64) b

-- ⚠️ AN EQUALITY TEST, NOT A MATCH: a wildcard match over `VBinKind`'s many
-- constructors cost 197 ku here (D266 §9), the same mechanism as K4's `RC` inductive.
def VBinKind.isMinMax (k : VBinKind) : Bool := k == .minps || k == .maxps

/-- MINPS/MAXPS: `vminmaxFlags`' rule ORed over the four binary32 lanes. Every other
packed kind raises nothing ("Flags Affected: None", and no SIMD exception). -/
def vbinFlags (k : VBinKind) (a b : BitVec 128) : BitVec 32 :=
  if k.isMinMax then
    (List.range 4).foldl (fun acc i => acc ||| SoftFloat.preFlags SoftFloat.binary32 true
      ((a >>> (32 * i)).setWidth 64) ((b >>> (32 * i)).setWidth 64)) 0#32
  else 0#32

/-- CVTSS2SD: IE on an SNaN, DE on a denormal (D258).
⛔ ITS `fromInt` ARM IS GONE: batch 39 could answer `0` there because int32 into
binary64 is EXACT, and B4 makes three inexact pairings statable.  The integer
conversion's flags now come from `cvtsi2Low`'s own call to `SoftFloat.i2f`. -/
def cvtss2sdFlags (b : BitVec 64) : BitVec 32 :=
  SoftFloat.preFlags SoftFloat.binary32 false b b

/-- ⭐⭐ SUB-GROUP B6a — CVTSD2SI / CVTSS2SI's LANE RULE AND ITS FLAGS, ONE PAIR (D288): `b`'s low binary64 (`dbl`)
or binary32 lane rounded under `rc` to an int64 (`wide`) or an int32. The forms differ only in where `b` is read. -/
def cvt2siLow (dbl wide : Bool) (rc : Nat) (b : BitVec 64) : BitVec 64 × BitVec 32 :=
  SoftFloat.cvtToInt (if dbl then SoftFloat.binary64 else SoftFloat.binary32) (if wide then 64 else 32) rc b

/-- CVTTSD2SI / CVTTSS2SI: IE or PE, on `cvttLane`'s own split. -/
def cvttFlags (dbl wide : Bool) (b : BitVec 64) : BitVec 32 :=
  SoftFloat.truncFlags (if dbl then SoftFloat.binary64 else SoftFloat.binary32)
    (if wide then 64 else 32) b

/-- V7 (D345) — the sign bit of each of the sixteen bytes of `v`, at bits 15:0: the legacy `vmovmsk`
arm's fold, with its lane width at `VMovMskKind.b`'s 8.  `Tests.AnchorsVexSil` proves the legacy
`pmovmskb` writes exactly this, so the VEX twins share its arithmetic rather than restate it. -/
def pmovmskbLane (v : BitVec 128) : Val :=
  (List.range (128 / 8)).foldl
    (fun acc i => acc ||| (((v >>> (8 * i + (8 - 1))) &&& 1).setWidth 64 <<< i)) 0

/-- ⭐⭐ V5 (D343) — `step` over the nested VEX forms (`Op.vex`): V3's and V4's arms, VERBATIM,
moved out of `step`'s match and nothing else.  `nr` is `step`'s next-instruction address and the
lock guard has already run in `step`, so no arm here re-checks it.

⭐ `@[simp]`, so `simp [step]` sees through the nesting exactly as it saw the arms in place: every
theorem about a VEX form keeps its proof, and only its statement gains the `.vex` wrap. -/
@[simp] def stepVex (v : VexOp) (s : Cpu) (nr : BitVec 64) : Cpu :=
  match v with
  -- ⭐⭐⭐ V3 (D341) — THE VEX.128 REGISTER TWINS.  Each computes exactly the legacy
  -- form's 128-bit value and writes it through `setXmmVex128`, which zeroes bits
  -- 255:128 of the destination's YMM register (SDM Vol. 1 §14.1.2).  That setter is
  -- the whole difference from the legacy arm, by construction.
  | .vexmov _ dst src =>
      (s.setXmmVex128 dst (s.getXmm src)).setRip nr
  | .vexddup dst src =>
      let lo := ((s.getXmm src).setWidth 64).setWidth 128
      (s.setXmmVex128 dst ((lo <<< 64) ||| lo)).setRip nr
  | .vexbin k dst src1 src =>
      if k.vexTaken || k.vexSilTaken then
        (s.setXmmVex128 dst (vbinApply k (s.getXmm src1) (s.getXmm src))).setRip nr
      else s.halt (.unimplemented s!"v{k.mnemonic}: a VEX twin not taken (D339)")
  -- ⭐⭐ V4 (D342) — the VEX.128 memory twin: `vexbin`'s value with the m128 at `ea` as the
  -- second source, and NO alignment check (VEX Exception Type 4; `vbinm` keeps the legacy #GP).
  | .vexbinm k dst src1 ea =>
      if k.vexMemTaken || k.vexSilMemTaken then
        let a := ea.addr s nr
        (s.setXmmVex128 dst (vbinApply k (s.getXmm src1) (s.readMem128 a))).setRip nr
      else s.halt (.unimplemented s!"v{k.mnemonic} m128: a VEX memory twin not taken (D342)")
  -- ⭐⭐ V4 (D342) — AES-NI, VPCLMULQDQ and the VEX shuffles.  x86isa refuses all nine;
  -- `hwprobe/` referees them.  The legacy AES form writes through `setXmm` (bits 255:128
  -- PRESERVED); every VEX form through `setXmmVex128` (ZEROED).  None writes a flag.
  | .vexaes k dst src1 src =>
      (s.setXmmVex128 dst (aesRound k.last (s.getXmm src1) (s.getXmm src))).setRip nr
  | .vexclmul dst src1 src imm =>
      (s.setXmmVex128 dst (pclmulApply (s.getXmm src1) (s.getXmm src) imm)).setRip nr
  | .vexshufb dst src1 src =>
      (s.setXmmVex128 dst (vshufbApply (s.getXmm src1) (s.getXmm src))).setRip nr
  | .vexalignr dst src1 src imm =>
      (s.setXmmVex128 dst (valignrApply (s.getXmm src1) (s.getXmm src) imm)).setRip nr
  | .vexshiftdq left dst src cnt =>
      (s.setXmmVex128 dst (vshiftdqApply left (s.getXmm src) cnt.toNat)).setRip nr
  -- ⭐⭐⭐ V6 (D344) — THE VEX.256 REGISTER TWINS.  Each lane is the VEX.128 twin's 128-bit
  -- function, applied to the low halves (`getXmm`) and to the high halves (`getYmmHi`)
  -- separately, and both are written through `setYmm`.  That the high lane uses the SAME
  -- function as the low one is the lane rule, by construction.
  | .vexmov256 _ dst src =>
      (s.setYmm dst (s.getXmm src) (s.getYmmHi src)).setRip nr
  | .vexddup256 dst src =>
      let dup := fun (x : BitVec 128) => let lo := (x.setWidth 64).setWidth 128; (lo <<< 64) ||| lo
      (s.setYmm dst (dup (s.getXmm src)) (dup (s.getYmmHi src))).setRip nr
  | .vexbin256 k dst src1 src =>
      if k.vexTaken || k.vexSilTaken then
        (s.setYmm dst (vbinApply k (s.getXmm src1) (s.getXmm src))
                      (vbinApply k (s.getYmmHi src1) (s.getYmmHi src))).setRip nr
      else s.halt (.unimplemented s!"v{k.mnemonic} ymm: a VEX.256 twin not taken (D344)")
  -- ⭐⭐⭐ V7 (D345) — THE SILICON-REFEREED VEX TWINS.  Each VEX.128 arm is its legacy twin's 128-bit
  -- function with `src1` (VEX.vvvv) in the legacy destination's place, written through
  -- `setXmmVex128`; each VEX.256 arm applies that SAME function to the low and the high halves and
  -- writes through `setYmm`.  No arm here has arithmetic of its own (D345 prediction 3).
  | .vexshufps dst src1 src sel =>
      (s.setXmmVex128 dst (vshufpApply .ps (s.getXmm src1) (s.getXmm src) sel)).setRip nr
  | .vexshufps256 dst src1 src sel =>
      (s.setYmm dst (vshufpApply .ps (s.getXmm src1) (s.getXmm src) sel)
                    (vshufpApply .ps (s.getYmmHi src1) (s.getYmmHi src) sel)).setRip nr
  -- ⚠️ ONE COUNT FOR BOTH LANES: the count register's low 64 bits, read from its XMM half even at
  -- VEX.256 (`getXmm cnt`, never `getYmmHi cnt`).
  | .vexsrax w dst src1 cnt =>
      if !(vshiftEncodable .sra w) then
        s.halt (.illegalOperands "there is no packed byte shift, and no psraq outside AVX-512")
      else
        let c := ((s.getXmm cnt).setWidth 64).toNat
        (s.setXmmVex128 dst (vshiftApply .sra w (s.getXmm src1) c)).setRip nr
  | .vexsrax256 w dst src1 cnt =>
      if !(vshiftEncodable .sra w) then
        s.halt (.illegalOperands "there is no packed byte shift, and no psraq outside AVX-512")
      else
        let c := ((s.getXmm cnt).setWidth 64).toNat
        (s.setYmm dst (vshiftApply .sra w (s.getXmm src1) c)
                      (vshiftApply .sra w (s.getYmmHi src1) c)).setRip nr
  | .vexsrai w dst src cnt =>
      if !(vshiftEncodable .sra w) then
        s.halt (.illegalOperands "there is no packed byte shift, and no psraq outside AVX-512")
      else (s.setXmmVex128 dst (vshiftApply .sra w (s.getXmm src) cnt.toNat)).setRip nr
  | .vexsrai256 w dst src cnt =>
      if !(vshiftEncodable .sra w) then
        s.halt (.illegalOperands "there is no packed byte shift, and no psraq outside AVX-512")
      else
        (s.setYmm dst (vshiftApply .sra w (s.getXmm src) cnt.toNat)
                      (vshiftApply .sra w (s.getYmmHi src) cnt.toNat)).setRip nr
  -- ⚠️ THE FLAGS ARE THE OR OVER BOTH LANES at VEX.256: `withSimd` sees `plo.2 ||| phi.2`, so a flag
  -- raised in the high lane alone is raised (D345 wrong rule (b) drops it).
  | .vexparith op dst src1 src =>
      if op == .div then s.halt (.unimplemented "vdivps: a VEX twin not taken (D345)") else
      let p := vparithAll op false (mxcsrRC s.mxcsr) (s.getXmm src1) (s.getXmm src)
      s.withSimd p.2 fun s => (s.setXmmVex128 dst p.1).setRip nr
  | .vexparith256 op dst src1 src =>
      if op == .div then s.halt (.unimplemented "vdivps ymm: a VEX.256 twin not taken (D345)") else
      let rc := mxcsrRC s.mxcsr
      let plo := vparithAll op false rc (s.getXmm src1) (s.getXmm src)
      let phi := vparithAll op false rc (s.getYmmHi src1) (s.getYmmHi src)
      s.withSimd (plo.2 ||| phi.2) fun s => (s.setYmm dst plo.1 phi.1).setRip nr
  -- The legacy `vmovmsk .b` fold, per lane; the high lane's sixteen bits land at 31:16.  `.d`, as the
  -- legacy arm: the 32-bit write zero-extends to 64 (SDM Vol. 1 §3.4.1.1).
  | .vexmovmskb dst src =>
      (s.setReg .d dst (pmovmskbLane (s.getXmm src))).setRip nr
  | .vexmovmskb256 dst src =>
      (s.setReg .d dst (pmovmskbLane (s.getXmm src) ||| (pmovmskbLane (s.getYmmHi src) <<< 16))).setRip nr
  -- ⭐⭐ V8c (D350) — the VEX.256 memory twin and VPBROADCASTD, silicon-refereed.  The memory twin is `vexbin256`'s
  -- per-lane rule with `readMem128` at `a` (the low lane) and at `a + 16` (the high lane); no alignment check.
  | .vexbinm256 k dst src1 ea =>
      if k.vexMemTaken || k.vexSilMemTaken then
        let a := ea.addr s nr
        (s.setYmm dst (vbinApply k (s.getXmm src1) (s.readMem128 a))
                      (vbinApply k (s.getYmmHi src1) (s.readMem128 (a + 16)))).setRip nr
      else s.halt (.unimplemented s!"v{k.mnemonic} m256: a VEX.256 memory twin not taken (D350)")
  | .vexbcastd dst src =>
      (s.setXmmVex128 dst (bcast32x4 ((s.getXmm src).setWidth 32))).setRip nr
  | .vexbcastd256 dst src =>
      let b := bcast32x4 ((s.getXmm src).setWidth 32)
      (s.setYmm dst b b).setRip nr
  | .vexbcastdm dst ea =>
      (s.setXmmVex128 dst (bcast32x4 ((s.readMem .d (ea.addr s nr)).setWidth 32))).setRip nr
  | .vexbcastdm256 dst ea =>
      let b := bcast32x4 ((s.readMem .d (ea.addr s nr)).setWidth 32)
      (s.setYmm dst b b).setRip nr
  -- ⭐⭐⭐ V9b (D354) — THE MOVE MEMORY FORMS.  The value rule is the register twin's with memory on
  -- one side; the alignment rule is `vload`'s at the access's own width (`alignedVex`), checked on the
  -- linear address `Ea.addr` produces.  A VEX.256 access is two 128-bit accesses at `a` and `a + 16`,
  -- the composition `vexbinm256` already uses.
  | .vexddupm dst ea =>
      let lo := (s.readMem .q (ea.addr s nr)).setWidth 128
      (s.setXmmVex128 dst ((lo <<< 64) ||| lo)).setRip nr
  | .vexddupm256 dst ea =>
      let a := ea.addr s nr
      let dup := fun (q : BitVec 64) => let lo := q.setWidth 128; (lo <<< 64) ||| lo
      (s.setYmm dst (dup (s.readMem .q a)) (dup (s.readMem .q (a + 16)))).setRip nr
  | .vexload k dst ea =>
      let a := ea.addr s nr
      if k.aligned && !alignedVex false a then
        s.halt (.byDesign "an aligned VEX.128 move at an address that is not 16-byte aligned (#GP(0))")
      else (s.setXmmVex128 dst (s.readMem128 a)).setRip nr
  | .vexstore k ea src =>
      let a := ea.addr s nr
      if k.aligned && !alignedVex false a then
        s.halt (.byDesign "an aligned VEX.128 move at an address that is not 16-byte aligned (#GP(0))")
      else (s.writeMem128 a (s.getXmm src)).setRip nr
  | .vexload256 k dst ea =>
      let a := ea.addr s nr
      if k.aligned && !alignedVex true a then
        s.halt (.byDesign "an aligned VEX.256 move at an address that is not 32-byte aligned (#GP(0))")
      else (s.setYmm dst (s.readMem128 a) (s.readMem128 (a + 16))).setRip nr
  | .vexstore256 k ea src =>
      let a := ea.addr s nr
      if k.aligned && !alignedVex true a then
        s.halt (.byDesign "an aligned VEX.256 move at an address that is not 32-byte aligned (#GP(0))")
      else ((s.writeMem128 a (s.getXmm src)).writeMem128 (a + 16) (s.getYmmHi src)).setRip nr

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
      s.withSimd (vbinFlags k (s.getXmm dst) (s.getXmm src)) fun s =>
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

  -- ⭐⭐ MOVHPS (SDM Vol. 2B) — the HIGH quadword moves and the LOW one is UNTOUCHED.
  --
  -- ⛔ NO ALIGNMENT BRANCH, and its absence is the rule rather than an omission:
  -- the memory operand is 8 bytes (Exception Type 5), so there is no 16-byte
  -- requirement to check.  D110 is the reason this sentence is not left to a
  -- comment — there, `NO ALIGNMENT CHECK … the absence is the rule` was written
  -- about a group that DID have one.  Here it is measured on the oracle at three
  -- alignments with a two-sided control, and K's rules carry no check either.
  --
  -- ⚠️ COMPOSED FROM `readMem .q` / `writeMem .q`, the same 64-bit path
  -- `readMem128` is built from, rather than a new primitive — a second route to
  -- the same bytes is a place for the two to disagree.
  -- ⚠️ THE SPELLING IS DISCARDED, and it must be: `VQuadKind` is the prefix byte
  -- and the prefix selects only the NAME.  A `step` that branched on it would be
  -- modelling the disassembler.  The halves are held apart by `check_encodings.py`,
  -- which is the instrument that can see a prefix.
  | .vloadq h _ dst ea =>
      let a := ea.addr s nr
      let m := (s.readMem .q a).setWidth 128
      match h with
      -- high ← m64; low ← the destination's own low quadword, PRESERVED.
      | .hi => (s.setXmm dst ((m <<< 64) ||| ((s.getXmm dst).setWidth 64).setWidth 128)).setRip nr
      -- low ← m64; high ← the destination's own high quadword, PRESERVED.
      | .lo => (s.setXmm dst (((((s.getXmm dst) >>> 64).setWidth 64).setWidth 128 <<< 64) ||| m)).setRip nr
  | .vstoreq h _ ea src =>
      let a := ea.addr s nr
      match h with
      | .hi => (s.writeMem .q a (((s.getXmm src) >>> 64).setWidth 64)).setRip nr
      | .lo => (s.writeMem .q a ((s.getXmm src).setWidth 64)).setRip nr

  -- ⭐⭐ MOVHLPS / MOVLHPS (SDM Vol. 2B) — ONE RULE, because they are duals: `d`
  -- is the half of the DESTINATION written, and the half READ is the OPPOSITE.
  -- ⚠️ CONFIRMED ON K, not read off the manual: `movhlps R1,R2` is
  -- `R2[0,192) ++ R1[128,192)` and `movlhps R1,R2` is
  -- `R2[0,128) ++ R1[192,256) ++ R2[192,256)` — MSB-indexed, so `[128,192)` is
  -- the xmm HIGH quadword and `[192,256)` the low.
  | .vmovhl d dst src =>
      let cur := s.getXmm dst
      let sv  := s.getXmm src
      match d with
      -- movhlps: dst[63:0] ← src[127:64]; dst[127:64] PRESERVED.
      | .lo => (s.setXmm dst ((((cur >>> 64).setWidth 64).setWidth 128 <<< 64)
                              ||| ((sv >>> 64).setWidth 64).setWidth 128)).setRip nr
      -- movlhps: dst[127:64] ← src[63:0]; dst[63:0] PRESERVED.
      | .hi => (s.setXmm dst ((((sv.setWidth 64).setWidth 128) <<< 64)
                              ||| (cur.setWidth 64).setWidth 128)).setRip nr

  -- ⭐⭐ MOVDDUP (SDM Vol. 2B) — BOTH halves receive the source's LOW quadword,
  -- so this is the one form of the batch that PRESERVES NOTHING.
  | .vddupR dst src =>
      let lo := ((s.getXmm src).setWidth 64).setWidth 128
      (s.setXmm dst ((lo <<< 64) ||| lo)).setRip nr
  -- V3/V4, nested by V5 (D343): the VEX.128 forms, through `stepVex`.
  | .vex v => stepVex v s nr
  -- ⭐⭐ V4 (D342) — legacy AES-NI.  x86isa refuses it; `hwprobe/` referees it.  It writes
  -- through `setXmm` (bits 255:128 PRESERVED).  No flag is written.
  | .vaes k dst src =>
      (s.setXmm dst (aesRound k.last (s.getXmm dst) (s.getXmm src))).setRip nr
  | .vddupM dst ea =>
      let a := ea.addr s nr
      -- ⚠️ `readMem .q`, the same 64-bit path the half-moves use: a second route
      -- to the same bytes is a place for the two to disagree.
      let m := (s.readMem .q a).setWidth 128
      (s.setXmm dst ((m <<< 64) ||| m)).setRip nr

  -- ⭐⭐ PREFETCHh (SDM Vol. 2B) — ADVANCE RIP AND DO NOTHING ELSE.
  --
  -- ⛔ THE ADDRESS IS NOT COMPUTED HERE, and that is deliberate rather than an
  -- omission: nothing reads it, PREFETCHh does not fault, and computing an
  -- effective address that no branch consumes would be a `let` a reader mistakes
  -- for an access.  `Op.eas` still REPORTS the `Ea` so the segment and lock gates
  -- see it — being named and being read are different things.
  --
  -- ⚠️ THE HINT IS DISCARDED, and it must be: it is architecturally invisible, so
  -- a `step` that branched on it would be modelling the cache.
  | .prefetch _ _ => s.setRip nr

  -- ⭐⭐ PMOVMSKB (SDM Vol. 2B) — the sign bit of each of sixteen bytes, gathered.
  --
  -- ⚠️ WRITTEN AS A FOLD rather than as N `|||` terms so the LANE COUNT is
  -- derived from the width, as `vlanes` derives it — a literal repeated in the
  -- body is a place for a typo no type can catch.
  --
  -- ⭐⭐ P2 BATCH 37 TOOK THAT COMMENT UP ON ITS OWN WARNING.  The body said
  -- `List.range 16` and `8 * i + 7`, so the sixteen and the eight were literals
  -- in exactly the position the sentence above calls a hazard — harmless while
  -- there was ONE kind, and the second kind is the change that would have paid
  -- for it.  Both now come from `VMovMskKind.laneBits`, which is the kind's whole
  -- semantic content: `pmovmskb` reduces 16 byte lanes, `movmskps` 4 dword lanes,
  -- and NOTHING ELSE about the two forms differs.
  --   result bit i  =  src bit (w * i + (w - 1)),  for i < 128 / w
  -- ⚠️ DECIDED ON K BEFORE IT WAS WRITTEN, not derived from the SDM's prose:
  -- `movmskps_r32_xmm.k` is `concatenateMInt(mi(60,0), <bits 128,160,192,224 of
  -- the 256-bit parent>)`.  K indexes the YMM parent big-endian, so those four
  -- are little-endian xmm bits 127, 95, 63 and 31 — the sign of each dword lane,
  -- lane 0 landing in result bit 0 — and `pmovmskb`'s sixteen are 127, 119, …, 7
  -- under the same reading, which is what the pre-batch-37 body computed.
  --
  -- ⚠️ `.d` AND NOT `.q`: the 32-bit write zero-extends to 64 by SDM Vol. 1
  -- §3.4.1.1, which `setReg` already implements, so the upper bits are cleared by
  -- the RULE THIS MODEL ALREADY HAS rather than by a special case here.  That is
  -- also why `Op.vmovmsk` carries no width — see its docstring, where batch 37
  -- re-measured the claim for `movmskps` instead of inheriting it.
  | .vmovmsk k dst src =>
      let v := s.getXmm src
      let w := k.laneBits
      let mask : Val :=
        (List.range (128 / w)).foldl
          (fun acc i => acc ||| (((v >>> (w * i + (w - 1))) &&& 1).setWidth 64 <<< i)) 0
      (s.setReg .d dst mask).setRip nr

  -- ⭐⭐⭐ COMISS / COMISD / UCOMISS / UCOMISD (SDM Vol. 2A) — P2 BATCH 32, and
  -- THE FIRST FLOATING-POINT SEMANTICS IN THIS MODEL.  Sub-group A of the
  -- soft-float commission: an ordering, so no rounding (its flags are MXCSR's, D266).
  --
  -- ⛔ IT WRITES ONLY FLAGS, EFLAGS AND MXCSR's.  No XMM register changes, nor any GPR
  -- or memory byte — a model that also wrote the destination would be
  -- bit-identical here whenever the value written happened to equal what was
  -- there, which is why `wrongComisWritesDst` is a selftest arm.
  --
  -- ⚠️ THE LOW LANE ONLY, at the FORMAT's width: `.q` reads 64 bits (binary64),
  -- `.d` reads 32 (binary32).  `setWidth 64` truncates the 128-bit register to
  -- the carrier `SoftFloat` expects; the bits above the format are never read,
  -- because `Fmt.mag`/`Fmt.sign` mask to `ew + mw`.
  --
  -- ⭐⭐ `ordered` IS READ, AND ONLY BY THE FLAGS (D266).  `comis` and `ucomis`
  -- differ only in WHICH NaN signals the invalid-operation exception: COMIS on any
  -- NaN, UCOMIS on an SNaN.  Until MXCSR joined the record they were one function
  -- on the compared state (record 23 said so); now IE tells them apart.  x86isa
  -- runs COMIS as UCOMIS, so that difference is an oracle divergence (D266 §1).
  | .vcomis ordered sz dst src =>
      let f  := if sz == .q then SoftFloat.binary64 else SoftFloat.binary32
      let a  := (s.getXmm dst).setWidth 64
      let b  := (s.getXmm src).setWidth 64
      s.withSimd (SoftFloat.preFlags f ordered a b) fun s =>
        (s.setFlags (Flags.fcmpFlags (SoftFloat.fcmp f a b) s.flags)).setRip nr
  -- ⭐ D357 — the same rule with the second operand read from memory (`vminmaxm`'s shape).
  | .vcomism ordered sz dst ea =>
      let f  := if sz == .q then SoftFloat.binary64 else SoftFloat.binary32
      let a  := (s.getXmm dst).setWidth 64
      let b  := s.readMem sz (ea.addr s nr)
      s.withSimd (SoftFloat.preFlags f ordered a b) fun s =>
        (s.setFlags (Flags.fcmpFlags (SoftFloat.fcmp f a b) s.flags)).setRip nr

  -- ⭐⭐⭐ MINSS / MINSD / MAXSS / MAXSD (SDM Vol. 2B) — P2 BATCH 38.  The low
  -- lane only; bits above it are preserved; no flag is written — the SDM's
  -- Operation writes DEST alone, and x86isa's writes the XMM register, MXCSR and
  -- RIP (`x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM`).
  -- ⚠️ NO ALIGNMENT CHECK at the memory form: a scalar operand has none.
  | .vminmax mx sz dst src =>
      let b := (s.getXmm src).setWidth 64
      s.withSimd (vminmaxFlags sz (s.getXmm dst) b) fun s =>
        (s.setXmm dst (vminmaxLow mx sz (s.getXmm dst) b)).setRip nr
  | .vminmaxm mx sz dst ea =>
      let b := s.readMem sz (ea.addr s nr)
      s.withSimd (vminmaxFlags sz (s.getXmm dst) b) fun s =>
        (s.setXmm dst (vminmaxLow mx sz (s.getXmm dst) b)).setRip nr

  -- ⭐⭐⭐ CVTSS2SD / CVTSI2SD at a 32-bit source (SDM Vol. 2B) — P2 BATCH 39.
  -- The low binary64 lane only; bits above it are preserved; no flag is written
  -- — x86isa's `x86-cvts?2s?-Op/En-RM` and `x86-cvtsi2s?-Op/En-RM` write the XMM
  -- register (`!xmmi-size 8`, which keeps the rest), MXCSR and RIP.
  -- ⚠️ NO ALIGNMENT CHECK at the memory form: a scalar operand has none.
  | .vcvtss2sd dst src =>
      let b := (s.getXmm src).setWidth 64
      s.withSimd (cvtss2sdFlags b) fun s =>
        (s.setXmm dst (vcvt2sdLow (s.getXmm dst) b)).setRip nr
  | .vcvtss2sdm dst ea =>
      let b := s.readMem .d (ea.addr s nr)
      s.withSimd (cvtss2sdFlags b) fun s =>
        (s.setXmm dst (vcvt2sdLow (s.getXmm dst) b)).setRip nr
  -- ⭐⭐⭐ CVTSI2SS / CVTSI2SD (SDM Vol. 2B) — SUB-GROUP B4.  The source GPR is read
  -- at its own width (REX.W), the memory form reads EIGHT bytes when `wide` and FOUR
  -- otherwise, and the flags ride out of the same call as the value.
  -- ⚠️ THE REGISTER FORM NOW GOES THROUGH `withSimd` WHERE BATCH 39 WROTE DIRECTLY:
  -- that is not a behaviour change at the landed pairing, because `withSimd_zero`
  -- (X86/State.lean) rewrites `withSimd 0` to the bare continuation.
  | .vcvtsi2 dbl wide dst src =>
      let p := cvtsi2Low dbl wide (mxcsrRC s.mxcsr) (s.getXmm dst)
                 (s.getReg (if wide then .q else .d) src)
      s.withSimd p.2 fun s => (s.setXmm dst p.1).setRip nr
  | .vcvtsi2m dbl wide dst ea =>
      let b := s.readMem (if wide then .q else .d) (ea.addr s nr)
      let p := cvtsi2Low dbl wide (mxcsrRC s.mxcsr) (s.getXmm dst) b
      s.withSimd p.2 fun s => (s.setXmm dst p.1).setRip nr

  -- ⭐⭐⭐ CVTTSD2SI / CVTTSS2SI (SDM Vol. 2A) — P2 BATCH 40, sub-group A′.
  -- The low lane, truncated toward zero, into a GPR of the REX.W width; an int32
  -- is zero-extended by `setReg .d`, as every 32-bit GPR write here is.  No flag
  -- is written — x86isa's `x86-cvts?2si/cvtts?2si-Op/En-RM` writes the GPR, MXCSR
  -- and RIP.  ⚠️ NO ALIGNMENT CHECK at the memory form: a scalar operand has none.
  | .vcvtt2si dbl wide dst src =>
      let b := (s.getXmm src).setWidth 64
      s.withSimd (cvttFlags dbl wide b) fun s =>
        (s.setReg (if wide then .q else .d) dst (cvttLane dbl wide b)).setRip nr
  | .vcvtt2sim dbl wide dst ea =>
      let b := s.readMem (if dbl then .q else .d) (ea.addr s nr)
      s.withSimd (cvttFlags dbl wide b) fun s =>
        (s.setReg (if wide then .q else .d) dst (cvttLane dbl wide b)).setRip nr

  -- ⭐⭐⭐ CVTSD2SI / CVTSS2SI (SDM Vol. 2A) — SUB-GROUP B6a. The truncation's shape with MXCSR.RC read: the low
  -- lane ROUNDED, into a GPR of the REX.W width. No EFLAGS bit is written. ⚠️ NO ALIGNMENT CHECK at the memory form.
  | .vcvt2si dbl wide dst src =>
      let p := cvt2siLow dbl wide (mxcsrRC s.mxcsr) ((s.getXmm src).setWidth 64)
      s.withSimd p.2 fun s => (s.setReg (if wide then .q else .d) dst p.1).setRip nr
  | .vcvt2sim dbl wide dst ea =>
      let p := cvt2siLow dbl wide (mxcsrRC s.mxcsr) (s.readMem (if dbl then .q else .d) (ea.addr s nr))
      s.withSimd p.2 fun s => (s.setReg (if wide then .q else .d) dst p.1).setRip nr

  -- ⭐⭐⭐ MULSS / MULSD (SDM Vol. 2B) — SUB-GROUP B1, the first form that ROUNDS
  -- under MXCSR.RC.  The low lane only; bits above it are preserved; no EFLAGS bit
  -- is written — x86isa's `x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM` writes
  -- the XMM register, MXCSR and RIP.  ⚠️ NO ALIGNMENT CHECK at the memory form.
  | .varith op sz dst src =>
      let p := varithLow op sz (mxcsrRC s.mxcsr) (s.getXmm dst) ((s.getXmm src).setWidth 64)
      s.withSimd p.2 fun s => (s.setXmm dst p.1).setRip nr
  | .varithm op sz dst ea =>
      let p := varithLow op sz (mxcsrRC s.mxcsr) (s.getXmm dst) (s.readMem sz (ea.addr s nr))
      s.withSimd p.2 fun s => (s.setXmm dst p.1).setRip nr

  -- ⭐⭐⭐ SQRTSS / SQRTSD (SDM Vol. 2B) — SUB-GROUP B6b. The low lane only; bits above it are preserved; no EFLAGS
  -- bit is written. ⚠️ NO ALIGNMENT CHECK at the memory form.
  | .vsqrt sz dst src =>
      let p := vsqrtLow sz (mxcsrRC s.mxcsr) (s.getXmm dst) ((s.getXmm src).setWidth 64)
      s.withSimd p.2 fun s => (s.setXmm dst p.1).setRip nr
  | .vsqrtm sz dst ea =>
      let p := vsqrtLow sz (mxcsrRC s.mxcsr) (s.getXmm dst) (s.readMem sz (ea.addr s nr))
      s.withSimd p.2 fun s => (s.setXmm dst p.1).setRip nr

  -- ⭐⭐⭐ MULPS/MULPD/ADDPS/ADDPD/SUBPS/SUBPD/DIVPS/DIVPD (SDM Vol. 2B) — SUB-GROUP B5.  EVERY lane is
  -- written; no EFLAGS bit is.  The memory form reads `m128` and is #GP(0) off a 16-byte boundary,
  -- halted `byDesign` exactly as `vbinm` is.
  | .vparith op dbl dst src =>
      let p := vparithAll op dbl (mxcsrRC s.mxcsr) (s.getXmm dst) (s.getXmm src)
      s.withSimd p.2 fun s => (s.setXmm dst p.1).setRip nr
  | .vparithm op dbl dst ea =>
      let a := ea.addr s nr
      if !aligned16 a then
        s.halt (.byDesign
          "a Type-4 128-bit memory operand at an address that is not 16-byte aligned (#GP(0))")
      else
        let p := vparithAll op dbl (mxcsrRC s.mxcsr) (s.getXmm dst) (s.readMem128 a)
        s.withSimd p.2 fun s => (s.setXmm dst p.1).setRip nr

  -- ⭐⭐⭐ SQRTPS / CVTPD2PS (SDM Vol. 2B / 2A) — SUB-GROUP B7. The whole destination is written; the memory forms carry
  -- the Type-4 alignment fault, as `vparithm`.
  | .vsqrtps dst src =>
      let p := vsqrtpsAll (mxcsrRC s.mxcsr) (s.getXmm src)
      s.withSimd p.2 fun s => (s.setXmm dst p.1).setRip nr
  | .vsqrtpsm dst ea =>
      let a := ea.addr s nr
      if !aligned16 a then
        s.halt (.byDesign
          "a Type-4 128-bit memory operand at an address that is not 16-byte aligned (#GP(0))")
      else
        let p := vsqrtpsAll (mxcsrRC s.mxcsr) (s.readMem128 a)
        s.withSimd p.2 fun s => (s.setXmm dst p.1).setRip nr
  | .vcvtpd2ps dst src =>
      let p := vcvtpd2psAll (mxcsrRC s.mxcsr) (s.getXmm src)
      s.withSimd p.2 fun s => (s.setXmm dst p.1).setRip nr
  | .vcvtpd2psm dst ea =>
      let a := ea.addr s nr
      if !aligned16 a then
        s.halt (.byDesign
          "a Type-4 128-bit memory operand at an address that is not 16-byte aligned (#GP(0))")
      else
        let p := vcvtpd2psAll (mxcsrRC s.mxcsr) (s.readMem128 a)
        s.withSimd p.2 fun s => (s.setXmm dst p.1).setRip nr

  -- ⭐⭐⭐ CVTSD2SS (SDM Vol. 2A) — SUB-GROUP B3, the first CONVERSION that rounds under
  -- MXCSR.RC.  The low binary32 lane only; bits 127:32 are preserved; no EFLAGS bit is
  -- written.  ⚠️ NO ALIGNMENT CHECK at the memory form, which reads `m64`.
  | .vcvtsd2ss dst src =>
      let p := vcvtsd2ssLow (mxcsrRC s.mxcsr) (s.getXmm dst) ((s.getXmm src).setWidth 64)
      s.withSimd p.2 fun s => (s.setXmm dst p.1).setRip nr
  | .vcvtsd2ssm dst ea =>
      let p := vcvtsd2ssLow (mxcsrRC s.mxcsr) (s.getXmm dst) (s.readMem .q (ea.addr s nr))
      s.withSimd p.2 fun s => (s.setXmm dst p.1).setRip nr

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

  -- ⭐ D356 — MOVD / MOVQ FROM AND TO MEMORY: `vmovsld`'s and `vmovsst`'s formulas, spelled
  -- `movd`/`movq`. The load ZEROES bits 127:sz (SDM Vol. 2B MOVD/MOVQ; legacy SSE, so the
  -- YMM bits above 127 are untouched, as `setXmm` leaves them). ⛔ x86isa MERGES at `66 0f 6e`
  -- (D93, reached through memory): that is declared per vector, never modelled.
  | .vmovgld sz dst ea =>
      let a := ea.addr s nr
      (s.setXmm dst (((s.readMem sz a).setWidth sz.bits).setWidth 128)).setRip nr
  | .vmovgst sz ea src =>
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

  -- ⭐⭐⭐ P2 BATCH 37 — THE TWO-SOURCE SHUFFLES.  ⚠️ THE DESTINATION IS READ:
  -- `s.getXmm dst` appears as the FIRST argument, and it is not decoration —
  -- lanes 0-1 of the result come from it.  Every other shuffle arm above
  -- overwrites its destination without consulting it.
  | .vshufp k dst src sel =>
      (s.setXmm dst (vshufpApply k (s.getXmm dst) (s.getXmm src) sel)).setRip nr

  -- ⛔ AND THE SAME 16-BYTE `#GP` (D110).  ⚠️ The MEMORY operand is the SOURCE,
  -- so the destination register is still read for lanes 0-1.
  | .vshufpm k dst ea sel =>
      let a := ea.addr s nr
      if !aligned16 a then
        s.halt (.byDesign
          "a Type-4 128-bit memory operand at an address that is not 16-byte aligned (#GP(0))")
      else (s.setXmm dst (vshufpApply k (s.getXmm dst) (s.readMem128 a) sel)).setRip nr

  -- ⭐ D336 (V1b): PSHUFB, PALIGNR, PINSRD/Q, PEXTRD/Q.  x86isa refuses all six;
  -- `hwprobe/` referees them.  ⚠️ PSHUFB and PALIGNR READ THE DESTINATION
  -- (`s.getXmm dst` is an argument); their m128 shapes carry the Type-4 16-byte
  -- `#GP` (D110).  PINSRD/Q's m32/m64 is Type 5 and has no alignment check.
  | .vshufb dst src =>
      (s.setXmm dst (vshufbApply (s.getXmm dst) (s.getXmm src))).setRip nr
  | .vshufbm dst ea =>
      let a := ea.addr s nr
      if !aligned16 a then
        s.halt (.byDesign
          "a Type-4 128-bit memory operand at an address that is not 16-byte aligned (#GP(0))")
      else (s.setXmm dst (vshufbApply (s.getXmm dst) (s.readMem128 a))).setRip nr
  | .valignr dst src imm =>
      (s.setXmm dst (valignrApply (s.getXmm dst) (s.getXmm src) imm)).setRip nr
  | .valignrm dst ea imm =>
      let a := ea.addr s nr
      if !aligned16 a then
        s.halt (.byDesign
          "a Type-4 128-bit memory operand at an address that is not 16-byte aligned (#GP(0))")
      else (s.setXmm dst (valignrApply (s.getXmm dst) (s.readMem128 a) imm)).setRip nr
  | .vinsr sz dst src imm =>
      if src.isImm then s.halt (.illegalOperands "pinsrd/pinsrq with an immediate source")
      else match sz with
      | .d | .q => (s.setXmm dst (vinsrApply sz (s.getXmm dst) (s.readOperand sz nr src) imm)).setRip nr
      | _ => s.halt (.illegalOperands "pinsr at an 8- or 16-bit width (pinsrb/pinsrw are other mnemonics)")
  | .vextr sz dst src imm =>
      match sz with
      | .d | .q => (s.setReg sz dst (vextrApply sz (s.getXmm src) imm)).setRip nr
      | _ => s.halt (.illegalOperands "pextr at an 8- or 16-bit width (pextrb/pextrw are other mnemonics)")

  -- ⭐ D338 (V2): SHA256MSG1, SHA256MSG2, SHA256RNDS2.  x86isa refuses all three;
  -- `hwprobe/` referees them.  ⚠️ ALL THREE READ THE DESTINATION (SRC1), and RNDS2
  -- reads XMM0 as well — read here BEFORE the write, so `dst = .x0` reads the old
  -- value as the SDM's Operation does.  The m128 shape carries the Type-4 16-byte `#GP`.
  | .vsha k dst src =>
      (s.setXmm dst (shaApply k (s.getXmm dst) (s.getXmm src) (s.getXmm .x0))).setRip nr
  | .vsham k dst ea =>
      let a := ea.addr s nr
      if !aligned16 a then
        s.halt (.byDesign
          "a Type-4 128-bit memory operand at an address that is not 16-byte aligned (#GP(0))")
      else (s.setXmm dst (shaApply k (s.getXmm dst) (s.readMem128 a) (s.getXmm .x0))).setRip nr

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
      else
        let b := s.readMem128 a
        s.withSimd (vbinFlags k (s.getXmm dst) b) fun s =>
          (s.setXmm dst (vbinApply k (s.getXmm dst) b)).setRip nr

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
  -- ⭐⭐ THE BIT STRING (D331, reversing D23's decline): a MEMORY base with a
  -- REGISTER offset is not a bit inside the addressed operand.  The offset is a
  -- SIGNED integer of the operand size, and the bit is bit `offset AND 7` of the
  -- byte at `EA + (offset SAR 3)` (SDM Vol. 2A §3.1.1.9 and Table 3-2: bit
  -- `offset MOD 8` of the byte at `BitBase + offset DIV 8`, DIV rounding toward
  -- negative infinity).  ONE BYTE is read and, for BTS/BTR/BTC, written back.
  -- The SDM lets the processor access the operand-size unit that contains it;
  -- that changes which addresses must be accessible and never the result, and
  -- the only access condition this model has is canonicity, checked on the byte
  -- it touches.  ⛔ The `abs` in x86isa's bit number is WRONG for a negative
  -- offset (D331; declared in `knownDivergences`, per state).
  | .bit k sz (.mem ea) (.reg r h8) =>
      let o := s.getReg sz r h8
      let ba := bitStringByte s sz ea r h8 nr
      if !canonical ba then
        s.halt (.unimplemented "non-canonical bit-string byte address (#GP(0) in hardware)")
      else
        let a := s.readMem .b ba
        let n := o.toNat % 8
        let bit := a.getLsbD n
        let res : Val :=
          match k with
          | .bt  => a
          | .bts => Value.trunc .b (a ||| (BitVec.ofNat 64 1 <<< n))
          | .btr => Value.trunc .b (a &&& ~~~(BitVec.ofNat 64 1 <<< n))
          | .btc => Value.trunc .b (a ^^^ (BitVec.ofNat 64 1 <<< n))
        let (pfU, s) := s.undefBit
        let (afU, s) := s.undefBit
        let (sfU, s) := s.undefBit
        let (ofU, s) := s.undefBit
        let s := s.setFlags { s.flags with
          cf := bit, pf := pfU, af := afU, sf := sfU, of := ofU }
        match k with
        | .bt => s.setRip nr
        | _ => (s.writeMem .b ba res).setRip nr
  -- Every other operand pair takes the offset MODULO the operand width, which is
  -- what the SDM specifies for a register destination and for an immediate
  -- offset.
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
  -- ENDBR64 (D347): a NOP on every piece of state this model carries (SDM Vol. 2A p. 3-288).
  | .endbr64 => s.setRip nr

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
  -- ⭐⭐ D346 (2026-10-17): BSF AND BSR AT A ZERO SOURCE LEAVE THE DESTINATION
  -- UNMODIFIED.  SDM 253666-093US Vol. 2A, read at the source: "If the content of
  -- the source operand is zero, the destination operand is unmodified." AMD's APM
  -- says the same, and x86isa writes no register there.  From batch 14 until D346
  -- this arm DREW the destination (D40), on the older SDM's "undefined"; that
  -- reason was the source this model follows, and the source changed.  Writing
  -- nothing is now the stated rule, not an invention.
  --
  -- ⚠️ THE ZERO SOURCE IS REACHABLE, not hypothetical: `adversarial` contains 0,
  -- so every `bsf`/`bsr` vector runs this branch at one pre-state in eleven.
  --
  -- ⚠️ THE FIVE FLAG DRAWS HAPPEN BEFORE THE BRANCH, unconditionally, so that
  -- the flags always read the same five positions of the stream whichever way
  -- the source falls.  ⭐ Since D346 the total is FIVE at every source (the zero
  -- source no longer draws a destination).  Until then it was data-dependent, and
  -- the weaker fact below was the one that mattered: the cursor depends on the
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

  -- ADCX / ADOX (SDM Vol. 2A, ADCX and ADOX), D330.  ADCX: "DEST := DEST + SRC +
  -- CF", "CF is updated based on the result.  OF, SF, ZF, AF and PF flags are
  -- unmodified."  ADOX is the same sentence with OF in both places.
  --
  -- ⭐ THE SUM AND THE CARRY-OUT ARE ADC'S, SHARED RATHER THAN RESTATED
  -- (`Flags.adcResult`, `Flags.adcCF`): the arithmetic is identical and only the
  -- flag that carries it differs.  ⚠️ The carry is read from the INCOMING flags,
  -- exactly as `.bin .adc` reads it.
  --
  -- ⛔ NOTHING IS DRAWN FROM THE UNDEFINED-BIT ORACLE: every flag is either the
  -- one carry or unmodified, so the form is `T-exact`.
  | .adx o sz dst src =>
      match sz with
      | .d | .q =>
          let a := s.getReg sz dst
          let b := s.readOperand sz nr src
          let cin := if o then s.flags.of else s.flags.cf
          let res := Flags.adcResult sz a b cin
          let cout := Flags.adcCF sz a b cin
          let f := if o then { s.flags with of := cout } else { s.flags with cf := cout }
          ((s.setFlags f).setReg sz dst res).setRip nr
      | _ => s.halt (.illegalOperands
          "adcx/adox at an 8- or 16-bit operand size (no encoding exists)")

  -- MULX (SDM Vol. 2B, MULX), D330.  "DEST2 := (SRC1 * SRC2)[OperandSize-1:0];
  -- DEST1 := (SRC1 * SRC2)[2*OperandSize-1:OperandSize]", SRC1 being RDX (EDX at
  -- 32 bits) and DEST2 the VEX.vvvv register.  "Flags Affected: None."
  --
  -- ⚠️ THE ORDER OF THE TWO WRITES IS THE SDM's, AND IT IS OBSERVABLE: when `hi`
  -- and `lo` are the same register the second write wins, and the SDM says the
  -- high half is what that register holds.  ⚠️ Both reads (RDX and `src`) happen
  -- before either write, so a source addressed through a destination reads the
  -- pre-state.  At `.d` both writes zero-extend (SDM Vol. 1 §3.4.1.1).
  | .mulx sz hi lo src =>
      match sz with
      | .d | .q =>
          let b := s.readOperand sz nr src
          let (l, h) := Value.mulPair sz (s.getReg sz .rdx) b
          ((s.setReg sz lo l).setReg sz hi h).setRip nr
      | _ => s.halt (.illegalOperands
          "mulx at an 8- or 16-bit operand size (VEX.W selects 32 or 64 only)")

  -- ══ D334 (W1c): ANDN, BEXTR, BZHI, BLSMSK/BLSR, PDEP/PEXT, RORX, MOVNTI ══
  -- x86isa refuses every one; `hwprobe/` referees them on a processor and
  -- `Tests/AnchorsBmi.lean` pins this model to the same rows.  ⚠️ Every source is
  -- read BEFORE the destination is written, so a source that names the destination
  -- reads the pre-state.  ⚠️ The undefined flags are drawn in a FIXED order — PF,
  -- AF (and SF for BEXTR) — exactly as `.bitcnt .blsi` draws them, so the oracle
  -- cursor depends on the form alone.  At `.d` the register write zero-extends.
  | .andn sz dst src1 src2 =>
      match sz with
      | .d | .q =>
          let res := Value.andn sz (s.getReg sz src1) (s.readOperand sz nr src2)
          let (pfU, s) := s.undefBit
          let (afU, s) := s.undefBit
          ((s.setFlags (Flags.andn sz res pfU afU s.flags)).setReg sz dst res).setRip nr
      | _ => s.halt (.illegalOperands "andn at an 8- or 16-bit operand size (no encoding)")
  | .bextr sz dst src ctl =>
      match sz with
      | .d | .q =>
          let res := Value.bextr sz (s.readOperand sz nr src) (s.getReg sz ctl)
          let (pfU, s) := s.undefBit
          let (afU, s) := s.undefBit
          let (sfU, s) := s.undefBit
          ((s.setFlags (Flags.bextr sz res pfU afU sfU s.flags)).setReg sz dst res).setRip nr
      | _ => s.halt (.illegalOperands "bextr at an 8- or 16-bit operand size (no encoding)")
  | .bzhi sz dst src idx =>
      match sz with
      | .d | .q =>
          let c := s.getReg sz idx
          let res := Value.bzhi sz (s.readOperand sz nr src) c
          let (pfU, s) := s.undefBit
          let (afU, s) := s.undefBit
          ((s.setFlags (Flags.bzhi sz (Value.bzhiIndex c) res pfU afU s.flags)).setReg
            sz dst res).setRip nr
      | _ => s.halt (.illegalOperands "bzhi at an 8- or 16-bit operand size (no encoding)")
  | .blsx m sz dst src =>
      match sz with
      | .d | .q =>
          let a := s.readOperand sz nr src
          let res := if m then Value.blsmsk sz a else Value.blsr sz a
          let (pfU, s) := s.undefBit
          let (afU, s) := s.undefBit
          let f := if m then Flags.blsmsk sz a res pfU afU s.flags
                   else Flags.blsr sz a res pfU afU s.flags
          ((s.setFlags f).setReg sz dst res).setRip nr
      | _ => s.halt (.illegalOperands "blsmsk/blsr at an 8- or 16-bit operand size (no encoding)")
  -- PDEP / PEXT / RORX: "Flags Affected: None", and nothing is drawn.
  | .pbits e sz dst src1 mask =>
      match sz with
      | .d | .q =>
          let v := s.getReg sz src1
          let mk := s.readOperand sz nr mask
          (s.setReg sz dst (if e then Value.pext sz v mk else Value.pdep sz v mk)).setRip nr
      | _ => s.halt (.illegalOperands "pdep/pext at an 8- or 16-bit operand size (no encoding)")
  | .rorx sz dst src imm =>
      match sz with
      | .d | .q => (s.setReg sz dst (Value.rorx sz (s.readOperand sz nr src) imm)).setRip nr
      | _ => s.halt (.illegalOperands "rorx at an 8- or 16-bit operand size (no encoding)")
  -- MOVNTI (SDM Vol. 2B): `DEST := SRC`, a plain store in this model.  The
  -- non-temporal hint and the weak (write-combining) ordering it permits have no
  -- counterpart in a single-threaded state without memory types (D334).
  | .movnti sz dst src =>
      if !dst.isMem then
        s.halt (.illegalOperands "movnti requires a memory destination (0F C3 /r)")
      else match sz with
      | .d | .q => (s.writeOperand sz nr dst (s.getReg sz src)).setRip nr
      | _ => s.halt (.illegalOperands "movnti at an 8- or 16-bit operand size (no encoding)")

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
