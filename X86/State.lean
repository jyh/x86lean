/-
# X86.State — the machine state `Cpu`

Plan v1 §3.1.  What is here and what is deliberately NOT here:

PRESENT AT P0: the sixteen GPRs with their 64/32/16/8 views (and AH/CH/DH/BH),
RIP, the six arithmetic flags plus DF, a total byte-addressed memory, the
adversarial undefined-bit oracle, and a model-state field.

ABSENT AT P0, ON PURPOSE: the XMM/YMM/ZMM register file and MXCSR.  Plan v1
§3.1 lists them and P0's roster is the SCALAR subset, so at P0 they would be
fields that no instruction reads and no test constrains — a phantom that reads
as coverage.  Adding a field to a structure is source-compatible with every
`{ s with … }` update and every `rfl`-shaped characterization lemma already
proven, so deferring costs nothing and claiming costs credibility.  Recorded as
decision D2 in docs/DECISIONS.md and due at P2 with the first SIMD form.

THE MODEL-STATE FIELD (`ms`) follows ACL2 x86isa's discipline: a non-`none`
value means the model has STOPPED and its state below is not to be read as a
machine state.  It is what keeps `step` a TOTAL function without inventing
behaviour for an ill-formed instruction: `step` on a malformed form sets `ms`
and changes nothing else, rather than being partial or fabricating a result.

LANE. Personal lane, public sources only.
-/
import X86.Memory
import X86.Oracle

namespace X86

/-- Why the model stopped.  Not an x86 exception vector: an exception is a
MACHINE event with architected behaviour, and this is a statement that THIS
MODEL declines to say what happens.  Real exceptions arrive with system mode,
which is a v0.x non-goal (plan v1 §1). -/
inductive MsErr where
  /-- The AST held an operand combination no encoding can express (e.g. two
  memory operands), so there is no instruction to give a meaning to. -/
  | illegalOperands (what : String)
  /-- A form outside the covered roster: the `T-absent` fidelity tier. -/
  | unimplemented (what : String)
  /-- ⭐ P1 BATCH 12: THE INSTRUCTION'S MEANING IS TO FAULT, and that is a
  different claim from either of the two above.  `ud2` is not an operand
  combination we cannot express, and it is not a gap in the roster — it is fully
  modelled, and what it is modelled as is #UD.  Filing it under
  `unimplemented` would put a COVERED form in the `T-absent` tier and make the
  fidelity table lie in the one direction the table exists to prevent. -/
  | byDesign (what : String)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The user-level x86-64 machine state. -/
structure Cpu where
  regs : Regs := {}
  rip : BitVec 64 := 0
  flags : Flags := {}
  mem : Mem := {}
  /-- ⭐⭐ P2 ITEM 1: THE FS AND GS SEGMENT BASES.  In 64-bit mode these are the
  only two segment bases the machine still adds (see `X86.Seg`), and they are
  MSR-loaded values — IA32_FS_BASE and IA32_GS_BASE — not descriptor fields.

  ⛔ THEY ARE INPUTS, NOT OUTPUTS, AND THAT IS A DELIBERATE LIMIT ON THE MODEL.
  No instruction in this roster writes either of them: `wrfsbase`/`wrgsbase` and
  `wrmsr` are not modelled, and `arch_prctl` is a system call.  D27 is the rule
  that decides what follows from that — *a state component no instruction writes
  is a constant, and a comparator that watches a constant reports agreement it
  did not test* — so these two fields are deliberately **absent from the
  differential record**.  What is compared is the ADDRESS the base produces:
  the vectors read and write through `%fs:`/`%gs:` into the watched windows, and
  a model with the wrong base (or none) lands somewhere else and differs in the
  window bytes and in the loaded register.  Putting the bases in the record
  instead would have added two fields that agree in every case for ever. -/
  fsBase : BitVec 64 := 0
  gsBase : BitVec 64 := 0
  /-- ⭐⭐⭐ THE VECTOR REGISTER FILE (P2 vector wave, batch 0 — THE HARNESS).

  ⛔ THIS FIELD IS THE ANSWER TO A MEASUREMENT, NOT A GUESS AT WHAT P2 NEEDS.
  The header above says XMM is "ABSENT AT P0, ON PURPOSE … a phantom that reads
  as coverage", and that was right for as long as no vector form was next.  What
  changed is what the oracle-availability run measured: the oracle EXECUTES the
  vector forms, and `x86l-post` reports 16 GPRs, RIP, the flags and two memory
  windows — so a vector form run on both sides would be compared on NONE of its
  results, and an unobserved region reports AGREEMENT rather than "unknown".

  ⚠️ IT IS ONE FIELD AND NOT SIXTEEN, and that is D71 applied in advance: two
  fields on this structure blew three inherited proofs in P2 batch 1 because a
  whole-record `rfl` costs O(fields).  Nested in `Xmms`, every existing record
  proof pays for one more projection rather than sixteen.

  ⚠️ AND NO INSTRUCTION IN THIS ROSTER WRITES IT — so by D27 it is a CONSTANT,
  and a comparator that watches a constant reports agreement it did not test.
  The batch's claim is exactly: the channel exists, both models report it, they
  agree, and a PLANTED difference in it is caught.  Only the last clause has
  teeth, and it is the one the red probe proves. -/
  xmm : Xmms := {}
  oracle : Oracle := Oracle.zero
  ms : Option MsErr := none

namespace Cpu

instance : Inhabited Cpu := ⟨{}⟩

/-- Has the model stopped? -/
def stopped (s : Cpu) : Bool := s.ms.isSome

/-- Stop the model, leaving everything else alone.  Idempotent in the sense that
a second stop does not overwrite the first reason — the FIRST thing that went
wrong is the informative one. -/
def halt (s : Cpu) (e : MsErr) : Cpu :=
  match s.ms with
  | some _ => s
  | none => { s with ms := some e }

@[simp] theorem halt_of_stopped (s : Cpu) (e e' : MsErr) (h : s.ms = some e') :
    s.halt e = s := by simp [halt, h]

/-! ### Register views -/

/-- Read the `sz`-wide view of `r`; `high8` selects AH/CH/DH/BH (bits 8..15),
which is legal only for `rax rcx rdx rbx` and only at `Size.b`. -/
def getReg (s : Cpu) (sz : Size) (r : GPR) (high8 : Bool := false) : Val :=
  if high8 then Value.readHigh8 (s.regs.get r)
  else Value.trunc sz (s.regs.get r)

/-- Write the `sz`-wide view of `r` under the SDM Vol. 1 §3.4.1.1 rules
(32-bit writes zero-extend; 16- and 8-bit writes preserve). -/
def setReg (s : Cpu) (sz : Size) (r : GPR) (v : Val) (high8 : Bool := false) : Cpu :=
  let old := s.regs.get r
  let new := if high8 then Value.writeHigh8 old v else Value.writeView sz old v
  { s with regs := s.regs.set r new }

@[simp] theorem getReg_setReg_same (s : Cpu) (sz : Size) (r : GPR) (v : Val) :
    (s.setReg sz r v).getReg sz r = Value.trunc sz (Value.writeView sz (s.regs.get r) v) := by
  simp [getReg, setReg]

@[simp] theorem getReg_setReg_ne (s : Cpu) (sz sz' : Size) (r r' : GPR) (v : Val)
    (h : r ≠ r') : (s.setReg sz r v).getReg sz' r' = s.getReg sz' r' := by
  simp [getReg, setReg, Regs.get_set_ne _ _ _ _ h]

/-- FRAME (plan v1 §3.5): a register write touches nothing but `regs`. -/
@[simp] theorem setReg_rip (s : Cpu) (sz : Size) (r : GPR) (v : Val) (h8 : Bool) :
    (s.setReg sz r v h8).rip = s.rip := rfl
@[simp] theorem setReg_flags (s : Cpu) (sz : Size) (r : GPR) (v : Val) (h8 : Bool) :
    (s.setReg sz r v h8).flags = s.flags := rfl
@[simp] theorem setReg_mem (s : Cpu) (sz : Size) (r : GPR) (v : Val) (h8 : Bool) :
    (s.setReg sz r v h8).mem = s.mem := rfl
@[simp] theorem setReg_ms (s : Cpu) (sz : Size) (r : GPR) (v : Val) (h8 : Bool) :
    (s.setReg sz r v h8).ms = s.ms := rfl
@[simp] theorem setReg_oracle (s : Cpu) (sz : Size) (r : GPR) (v : Val) (h8 : Bool) :
    (s.setReg sz r v h8).oracle = s.oracle := rfl

/-! ### The vector registers -/

/-- Read one XMM register. -/
def getXmm (s : Cpu) (r : XmmReg) : BitVec 128 := s.xmm.get r

/-- Write one XMM register.  ⚠️ NOTHING IN THIS ROSTER CALLS IT YET — it exists
so the harness's red probe can plant a difference, and so the first vector form
has a place to write.  See the note on `Cpu.xmm`. -/
def setXmm (s : Cpu) (r : XmmReg) (v : BitVec 128) : Cpu :=
  { s with xmm := s.xmm.set r v }

@[simp] theorem setXmm_regs (s : Cpu) (r : XmmReg) (v : BitVec 128) :
    (s.setXmm r v).regs = s.regs := rfl
@[simp] theorem setXmm_rip (s : Cpu) (r : XmmReg) (v : BitVec 128) :
    (s.setXmm r v).rip = s.rip := rfl
@[simp] theorem setXmm_flags (s : Cpu) (r : XmmReg) (v : BitVec 128) :
    (s.setXmm r v).flags = s.flags := rfl
@[simp] theorem setXmm_mem (s : Cpu) (r : XmmReg) (v : BitVec 128) :
    (s.setXmm r v).mem = s.mem := rfl
@[simp] theorem setXmm_ms (s : Cpu) (r : XmmReg) (v : BitVec 128) :
    (s.setXmm r v).ms = s.ms := rfl
@[simp] theorem getXmm_setXmm_same (s : Cpu) (r : XmmReg) (v : BitVec 128) :
    (s.setXmm r v).getXmm r = v := by simp [getXmm, setXmm]

/-! ⭐ AND THE FRAME LEMMAS IN THE OTHER DIRECTION, WRITTEN NOW RATHER THAN WHEN
A PROOF NEEDS THEM.  D71's finding was that `undefVal` shipped without the frame
lemmas its sibling had, and three proofs closed by whole-record `rfl` instead —
which is why two new fields could blow a heartbeat limit.  Every state-mutating
helper this file already has gets its `xmm` lemma here, on the day the field is
added, so no proof ever has to reduce the record to learn that XMM did not move. -/
@[simp] theorem setReg_xmm (s : Cpu) (sz : Size) (r : GPR) (v : Val) (h8 : Bool) :
    (s.setReg sz r v h8).xmm = s.xmm := rfl
/-! ### The segment bases -/

/-- The base a segment override selects.  `none` — no override — is base zero,
which in 64-bit mode is also what CS/DS/ES/SS give (SDM Vol. 3A §3.4.4), so the
absence of an override and an override on a zeroed segment are the same
computation and this function has no third case. -/
def segBase (s : Cpu) : Option Seg → BitVec 64
  | none => 0
  | some .fs => s.fsBase
  | some .gs => s.gsBase

@[simp] theorem segBase_none (s : Cpu) : s.segBase none = 0 := rfl
@[simp] theorem segBase_fs (s : Cpu) : s.segBase (some .fs) = s.fsBase := rfl
@[simp] theorem segBase_gs (s : Cpu) : s.segBase (some .gs) = s.gsBase := rfl

/-! ### Memory access -/

def readMem (s : Cpu) (sz : Size) (a : BitVec 64) : Val := s.mem.readSize sz a

def writeMem (s : Cpu) (sz : Size) (a : BitVec 64) (v : Val) : Cpu :=
  { s with mem := s.mem.writeSize sz a v }

/-! ### ⭐⭐⭐ THE 128-BIT MEMORY PATH — P2 vector wave, batch 3 -/

/-- Read sixteen bytes, little-endian, as TWO 64-bit reads.

⚠️ IT REUSES `readMem` RATHER THAN REACHING INTO `Mem`.  `Mem.readN` tops out at
eight bytes because it returns a `BitVec 64`, so a 128-bit read needs either a
new byte recursion or a composition of the existing one.  The composition is
chosen deliberately: `readMem` is the path every scalar vector in this repository
has exercised since P0, its endianness is settled by 500 roster rows of
differential evidence, and a second byte-recursion beside it would be a place for
the two to disagree — a duplicate born in agreement.

⚠️ AND IT IS TWO SEPARATE 8-BYTE READS, NOT AN ATOMIC ONE.  That is honest: this
model has no atomicity vocabulary for loads (TRUSTBASE.md, "Atomicity is
RECORDED, never verified"), and a 16-byte SSE load is not architecturally atomic
anyway. -/
def readMem128 (s : Cpu) (a : BitVec 64) : BitVec 128 :=
  (((s.readMem .q (a + 8)).setWidth 128) <<< 64) ||| ((s.readMem .q a).setWidth 128)

/-- Write sixteen bytes, little-endian, as two 64-bit writes: low half first. -/
def writeMem128 (s : Cpu) (a : BitVec 64) (v : BitVec 128) : Cpu :=
  ((s.writeMem .q a (v.setWidth 64)).writeMem .q (a + 8) ((v >>> 64).setWidth 64))

/-! ⭐ THE FRAME LEMMAS FOR THE NEW WRITER, ON THE DAY IT IS ADDED — D71's rule,
which this repository has now paid for twice.  A proof must never have to reduce
the whole record to learn that a 128-bit store left the registers alone. -/
@[simp] theorem writeMem128_regs (s : Cpu) (a : BitVec 64) (v : BitVec 128) :
    (s.writeMem128 a v).regs = s.regs := rfl
@[simp] theorem writeMem128_rip (s : Cpu) (a : BitVec 64) (v : BitVec 128) :
    (s.writeMem128 a v).rip = s.rip := rfl
@[simp] theorem writeMem128_flags (s : Cpu) (a : BitVec 64) (v : BitVec 128) :
    (s.writeMem128 a v).flags = s.flags := rfl
@[simp] theorem writeMem128_xmm (s : Cpu) (a : BitVec 64) (v : BitVec 128) :
    (s.writeMem128 a v).xmm = s.xmm := rfl
@[simp] theorem writeMem128_ms (s : Cpu) (a : BitVec 64) (v : BitVec 128) :
    (s.writeMem128 a v).ms = s.ms := rfl
@[simp] theorem setXmm_mem' (s : Cpu) (r : XmmReg) (v : BitVec 128) :
    (s.setXmm r v).mem = s.mem := rfl


@[simp] theorem writeMem_regs (s : Cpu) (sz : Size) (a : BitVec 64) (v : Val) :
    (s.writeMem sz a v).regs = s.regs := rfl
@[simp] theorem writeMem_rip (s : Cpu) (sz : Size) (a : BitVec 64) (v : Val) :
    (s.writeMem sz a v).rip = s.rip := rfl
@[simp] theorem writeMem_flags (s : Cpu) (sz : Size) (a : BitVec 64) (v : Val) :
    (s.writeMem sz a v).flags = s.flags := rfl
@[simp] theorem writeMem_ms (s : Cpu) (sz : Size) (a : BitVec 64) (v : Val) :
    (s.writeMem sz a v).ms = s.ms := rfl
@[simp] theorem writeMem_oracle (s : Cpu) (sz : Size) (a : BitVec 64) (v : Val) :
    (s.writeMem sz a v).oracle = s.oracle := rfl

/-! ### The undefined-bit oracle at the state level

Every SDM "undefined" in this model goes through `undefBit`.  Nothing else in
the semantics may invent a value, and that is checkable: `grep` for `undefBit`
gives the complete list of places this model declines to commit, and that list
is exactly the `undefined` column of the generated coverage table. -/

/-- Draw one undefined bit, advancing the oracle. -/
def undefBit (s : Cpu) : Bool × Cpu :=
  let (b, o) := s.oracle.draw
  (b, { s with oracle := o })

/-- Draw `n` undefined bits as the low `n` bits of a value.

⛔ P1 BATCH 14 IS THE FIRST CALLER, AND IT IS THE FIRST TIME AN ORACLE BIT IS
ALLOWED TO REACH A REGISTER.  `bsf`/`bsr` at a zero source leave the DESTINATION
undefined (SDM Vol. 2A), not merely a flag.  Everything the surrounding
machinery assumed about undefined regions being flags had to be widened to
admit it — deliberately and in one place, `X86.undefinedRegs`, so that an
oracle bit reaching any register NO FORM DECLARES undefined is still the leak it
always was.  See the note there. -/
def undefVal (s : Cpu) (n : Nat) : Val × Cpu :=
  let (v, o) := s.oracle.drawVal n
  (v, { s with oracle := o })

@[simp] theorem undefBit_regs (s : Cpu) : (s.undefBit).2.regs = s.regs := rfl
@[simp] theorem undefBit_rip (s : Cpu) : (s.undefBit).2.rip = s.rip := rfl
@[simp] theorem undefBit_flags (s : Cpu) : (s.undefBit).2.flags = s.flags := rfl
@[simp] theorem undefBit_mem (s : Cpu) : (s.undefBit).2.mem = s.mem := rfl
@[simp] theorem undefBit_ms (s : Cpu) : (s.undefBit).2.ms = s.ms := rfl
@[simp] theorem undefBit_fst (s : Cpu) : (s.undefBit).1 = s.oracle.bits s.oracle.cursor := rfl

/-! ⭐⭐ P2 ITEM 1 ADDED THE FRAME LEMMAS FOR `undefVal`, AND THE REASON IS A
COST FINDING RATHER THAN A NEW THEOREM.

`undefBit` has had these five since P0; `undefVal` — added in P1 batch 14 — never
got them, so the three `bitScanStep` frame proofs in `X86/Theorems.lean` unfolded
it and finished by `rfl`, i.e. by a defeq check over the WHOLE `Cpu` record
eight updates deep.  That worked, with no margin: adding two fields to `Cpu` for
the FS/GS bases — two fields no instruction reads and nothing else in the batch
touches — pushed all three over the 200 000-heartbeat limit at once, before the
batch had added a single instruction.

⇒ 🔑 **THE COST OF A STATE FIELD IS PAID BY EVERY WHOLE-RECORD PROOF, NOT BY THE
FORMS THAT USE IT.**  A `maxHeartbeats` bump on the three would have been the
one-line repair and would have left the next field to find the limit again.
With these, `simp` pushes each projection through symbolically and never builds
the record at all — the proofs no longer scale with the number of fields, which
is the property that was missing, not the margin. -/

@[simp] theorem undefVal_regs (s : Cpu) (n : Nat) : (s.undefVal n).2.regs = s.regs := rfl
@[simp] theorem undefVal_rip (s : Cpu) (n : Nat) : (s.undefVal n).2.rip = s.rip := rfl
@[simp] theorem undefVal_flags (s : Cpu) (n : Nat) : (s.undefVal n).2.flags = s.flags := rfl
@[simp] theorem undefVal_mem (s : Cpu) (n : Nat) : (s.undefVal n).2.mem = s.mem := rfl
@[simp] theorem undefVal_ms (s : Cpu) (n : Nat) : (s.undefVal n).2.ms = s.ms := rfl
@[simp] theorem undefVal_fsBase (s : Cpu) (n : Nat) : (s.undefVal n).2.fsBase = s.fsBase := rfl
@[simp] theorem undefVal_gsBase (s : Cpu) (n : Nat) : (s.undefVal n).2.gsBase = s.gsBase := rfl
@[simp] theorem undefBit_fsBase (s : Cpu) : (s.undefBit).2.fsBase = s.fsBase := rfl
@[simp] theorem undefBit_gsBase (s : Cpu) : (s.undefBit).2.gsBase = s.gsBase := rfl

/-! ### Control flow -/

/-- Advance RIP past an instruction of `len` bytes.  x86 RIP-relative behaviour
is defined against the address of the NEXT instruction (SDM Vol. 2A §2.2.1.6),
so `len` is a datum on every decoded instruction, not a property of its form. -/
def advance (s : Cpu) (len : Nat) : Cpu := { s with rip := s.rip + BitVec.ofNat 64 len }

@[simp] theorem advance_regs (s : Cpu) (n : Nat) : (s.advance n).regs = s.regs := rfl
@[simp] theorem advance_flags (s : Cpu) (n : Nat) : (s.advance n).flags = s.flags := rfl
@[simp] theorem advance_mem (s : Cpu) (n : Nat) : (s.advance n).mem = s.mem := rfl
@[simp] theorem advance_ms (s : Cpu) (n : Nat) : (s.advance n).ms = s.ms := rfl
@[simp] theorem advance_rip (s : Cpu) (n : Nat) :
    (s.advance n).rip = s.rip + BitVec.ofNat 64 n := rfl

/-- Set RIP to an absolute value (JMP/CALL targets, and the return address on
POP into RIP, which this roster does not yet have). -/
def setRip (s : Cpu) (v : BitVec 64) : Cpu := { s with rip := v }

@[simp] theorem setRip_rip (s : Cpu) (v : BitVec 64) : (s.setRip v).rip = v := rfl
@[simp] theorem setRip_regs (s : Cpu) (v : BitVec 64) : (s.setRip v).regs = s.regs := rfl
@[simp] theorem setRip_flags (s : Cpu) (v : BitVec 64) : (s.setRip v).flags = s.flags := rfl
@[simp] theorem setRip_mem (s : Cpu) (v : BitVec 64) : (s.setRip v).mem = s.mem := rfl

/-! ### Flags -/

def setFlags (s : Cpu) (f : Flags) : Cpu := { s with flags := f }

@[simp] theorem setFlags_flags (s : Cpu) (f : Flags) : (s.setFlags f).flags = f := rfl
@[simp] theorem setFlags_regs (s : Cpu) (f : Flags) : (s.setFlags f).regs = s.regs := rfl
@[simp] theorem setFlags_rip (s : Cpu) (f : Flags) : (s.setFlags f).rip = s.rip := rfl
@[simp] theorem setFlags_mem (s : Cpu) (f : Flags) : (s.setFlags f).mem = s.mem := rfl

/-! ### ⭐ THE REST OF THE XMM FRAME, at the end because these helpers are
defined below the register views.  Written on the day the field was added, for
D71's reason: `undefVal` shipped without the frame lemmas its sibling had, and
three proofs closed by whole-record `rfl` instead — which is how two new fields
came to blow a heartbeat limit. -/
@[simp] theorem writeMem_xmm (s : Cpu) (sz : Size) (a : BitVec 64) (v : Val) :
    (s.writeMem sz a v).xmm = s.xmm := rfl
@[simp] theorem setFlags_xmm (s : Cpu) (f : Flags) : (s.setFlags f).xmm = s.xmm := rfl
@[simp] theorem setRip_xmm (s : Cpu) (v : BitVec 64) : (s.setRip v).xmm = s.xmm := rfl
@[simp] theorem advance_xmm (s : Cpu) (n : Nat) : (s.advance n).xmm = s.xmm := rfl
@[simp] theorem undefBit_xmm (s : Cpu) : (s.undefBit).2.xmm = s.xmm := rfl
@[simp] theorem undefVal_xmm (s : Cpu) (n : Nat) : (s.undefVal n).2.xmm = s.xmm := rfl

end Cpu
end X86
