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

/-- The effective address of a memory operand.  All arithmetic is `BitVec 64`,
so it wraps at 2^64 exactly as 64-bit-mode address computation does.
`nextRip` is the address of the FOLLOWING instruction, which is what
RIP-relative addressing is defined against (SDM Vol. 2A §2.2.1.6). -/
def Ea.addr (ea : Ea) (s : Cpu) (nextRip : BitVec 64) : Val :=
  if ea.ripRel then nextRip + ea.disp
  else
    let b := match ea.base with | some r => s.regs.get r | none => 0
    let i := match ea.index with | some r => s.regs.get r * ea.scale.toVal | none => 0
    b + i + ea.disp

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

/-- The small-step transition.  A stopped model does not move. -/
def step (i : Instr) (s : Cpu) : Cpu :=
  if s.stopped then s else
  -- the address of the NEXT instruction: what RIP-relative addressing and every
  -- relative branch are defined against.
  let nr : BitVec 64 := s.rip + BitVec.ofNat 64 i.len
  match i.op with

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

  -- LEA (SDM Vol. 2A, LEA): computes the effective address and writes it under
  -- the ordinary register-width rules, so `lea eax, [...]` zero-extends.
  -- "Flags Affected: None."
  | .lea sz dst ea =>
      ((s.setReg sz dst (ea.addr s nr)).setRip nr)

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
