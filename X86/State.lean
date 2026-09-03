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

/-! ### Memory access -/

def readMem (s : Cpu) (sz : Size) (a : BitVec 64) : Val := s.mem.readSize sz a

def writeMem (s : Cpu) (sz : Size) (a : BitVec 64) (v : Val) : Cpu :=
  { s with mem := s.mem.writeSize sz a v }

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

end Cpu
end X86
