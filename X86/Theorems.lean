/-
# X86.Theorems — one characterization theorem per form, and the frame it carries

Plan v1 §3.5: "record-update predicates per instruction class + one
characterization theorem per form (`step i s = { s with … }`), proven once."

WHY THE `{ s with … }` SHAPE AND NOT A PACK OF PROJECTIONS.  A single equation
says what the instruction DOES and what it LEAVES ALONE in one statement: every
field not named is, by the record-update notation, unchanged.  A pack of
projection lemmas can be INCOMPLETE — it can silently omit the field the
instruction quietly clobbers — and nothing about the pack reveals the omission.
That is the frame problem, and the record-update shape is the standard answer
(Myreen, FMCAD 2012, for machine code; the same discipline at other levels in
the seL4 and CompCert traditions).

⭐ AND IT MAKES THE ORACLE VISIBLE.  Where the SDM leaves a flag undefined, this
model draws an oracle bit, and the `oracle := { … cursor := … + 1 }` component of
these equations is that draw, IN THE THEOREM STATEMENT.  A reader can see from
the statement alone which forms decline to commit and how many bits they spend.

WHAT THEY ARE FOR.  They are the interface a Hoare/separation logic consumes
(plan v1 §3.0): a machine-code triple's step rule is one of these equations plus
a frame condition.  They are also the kernel-cost barrier of plan v1 §3.7 —
downstream proofs rewrite with these instead of unfolding `step`, so no
composite proof re-reduces the twenty-way match.

⛔ AXIOMS.  `rfl`, `simp`, `omega` only.  No `bv_decide`, no `native_decide`.
`Tests/AxiomCheck.lean` asserts the allowlist over the whole library.

LANE. Personal lane, public sources only.
-/
import X86.Semantics

namespace X86

/-- The hypothesis every characterization theorem carries: the model has not
already stopped.  A stopped model does not move (`step_stopped`), so this
restricts which equation applies, not the semantics. -/
abbrev Live (s : Cpu) : Prop := s.ms = none

@[simp] theorem stopped_of_live {s : Cpu} (h : Live s) : s.stopped = false := by
  simp [Cpu.stopped, h]

-- The unfolding set for a concrete form.  Local to this file, so that a
-- downstream proof cannot inherit it and re-unfold `step` by accident: the whole
-- point of the characterization layer is that nothing below it unfolds `step`.
attribute [local simp] Cpu.stopped Cpu.readOperand Cpu.writeOperand Cpu.setReg
  Cpu.setRip Cpu.setFlags Cpu.writeMem Cpu.readMem Cpu.undefBit Oracle.draw
  Cpu.push Cpu.popValue wellFormed2 Operand.isMem

variable {s : Cpu} {len : Nat}

/-! ## MOV — SDM Vol. 2A, MOV.  "Flags Affected: None." -/

theorem step_mov_reg_reg (sz : Size) (r r' : GPR) (h : Live s) :
    step ⟨.mov sz (.reg r) (.reg r'), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView sz (s.regs.get r) (s.getReg sz r')),
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.getReg]

theorem step_mov_reg_imm (sz : Size) (r : GPR) (v : Val) (h : Live s) :
    step ⟨.mov sz (.reg r) (.imm v), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView sz (s.regs.get r) (Value.trunc sz v)),
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h]

theorem step_mov_mem_reg (sz : Size) (ea : Ea) (r : GPR) (h : Live s) :
    step ⟨.mov sz (.mem ea) (.reg r), len⟩ s =
      { s with
        mem := s.mem.writeSize sz (ea.addr s (s.rip + BitVec.ofNat 64 len)) (s.getReg sz r),
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.getReg]

theorem step_mov_reg_mem (sz : Size) (r : GPR) (ea : Ea) (h : Live s) :
    step ⟨.mov sz (.reg r) (.mem ea), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView sz (s.regs.get r)
          (s.mem.readSize sz (ea.addr s (s.rip + BitVec.ofNat 64 len)))),
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h]

/-- TWO MEMORY OPERANDS STOP THE MODEL rather than meaning something.  This is
the totality discipline as a theorem: `step` is total, and its value on a form
no encoding can express is a HALT, not an invention. -/
theorem step_mov_mem_mem (sz : Size) (ea ea' : Ea) (h : Live s) :
    step ⟨.mov sz (.mem ea) (.mem ea'), len⟩ s =
      { s with ms := some (.illegalOperands "mov: two memory operands") } := by
  simp [step, h, Cpu.halt]

/-! ## ADD / SUB — SDM Vol. 2A.  All six status flags set from the result. -/

theorem step_add_reg_reg (sz : Size) (r r' : GPR) (h : Live s) :
    step ⟨.bin .add sz (.reg r) (.reg r'), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView sz (s.regs.get r)
          (Flags.addResult sz (s.getReg sz r) (s.getReg sz r'))),
        flags := Flags.add sz (s.getReg sz r) (s.getReg sz r') s.flags,
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.getReg]

theorem step_sub_reg_reg (sz : Size) (r r' : GPR) (h : Live s) :
    step ⟨.bin .sub sz (.reg r) (.reg r'), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView sz (s.regs.get r)
          (Flags.subResult sz (s.getReg sz r) (s.getReg sz r'))),
        flags := Flags.sub sz (s.getReg sz r) (s.getReg sz r') s.flags,
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.getReg]

/-- CMP writes NO register: it is SUB with the result discarded.  The equation
proves the discard — `regs` is absent from the update. -/
theorem step_cmp_reg_reg (sz : Size) (r r' : GPR) (h : Live s) :
    step ⟨.bin .cmp sz (.reg r) (.reg r'), len⟩ s =
      { s with
        flags := Flags.sub sz (s.getReg sz r) (s.getReg sz r') s.flags,
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h]

/-! ## The logic group — SDM Vol. 2A: OF and CF cleared, SF/ZF/PF from the
result, and **the AF flag is undefined**.  Each of these four equations spends
exactly ONE oracle bit, and the `oracle` component says so. -/

theorem step_and_reg_reg (sz : Size) (r r' : GPR) (h : Live s) :
    step ⟨.bin .and sz (.reg r) (.reg r'), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView sz (s.regs.get r)
          (Value.trunc sz (s.getReg sz r &&& s.getReg sz r'))),
        flags := Flags.logic sz (Value.trunc sz (s.getReg sz r &&& s.getReg sz r'))
          (s.oracle.bits s.oracle.cursor) s.flags,
        oracle := { s.oracle with cursor := s.oracle.cursor + 1 },
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.getReg]

theorem step_or_reg_reg (sz : Size) (r r' : GPR) (h : Live s) :
    step ⟨.bin .or sz (.reg r) (.reg r'), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView sz (s.regs.get r)
          (Value.trunc sz (s.getReg sz r ||| s.getReg sz r'))),
        flags := Flags.logic sz (Value.trunc sz (s.getReg sz r ||| s.getReg sz r'))
          (s.oracle.bits s.oracle.cursor) s.flags,
        oracle := { s.oracle with cursor := s.oracle.cursor + 1 },
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.getReg]

theorem step_xor_reg_reg (sz : Size) (r r' : GPR) (h : Live s) :
    step ⟨.bin .xor sz (.reg r) (.reg r'), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView sz (s.regs.get r)
          (Value.trunc sz (s.getReg sz r ^^^ s.getReg sz r'))),
        flags := Flags.logic sz (Value.trunc sz (s.getReg sz r ^^^ s.getReg sz r'))
          (s.oracle.bits s.oracle.cursor) s.flags,
        oracle := { s.oracle with cursor := s.oracle.cursor + 1 },
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.getReg]

/-- TEST is AND with the result discarded — again, `regs` is absent. -/
theorem step_test_reg_reg (sz : Size) (r r' : GPR) (h : Live s) :
    step ⟨.bin .test sz (.reg r) (.reg r'), len⟩ s =
      { s with
        flags := Flags.logic sz (Value.trunc sz (s.getReg sz r &&& s.getReg sz r'))
          (s.oracle.bits s.oracle.cursor) s.flags,
        oracle := { s.oracle with cursor := s.oracle.cursor + 1 },
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.getReg]

/-! ## P1 BATCH 2 — ADC and SBB: the first forms whose RESULT reads a flag

`p1/roster.tsv` family `xxxxxx-|cf|reg`, 14 forms, 48 K variants.  Same generic
source operand and generic `h8` destination as batch 1 (D10), for the same
reason and with the same limit.

⭐ WHAT IS NEW IN THE STATEMENT, and it is one subterm: `s.flags.cf` appears on
the RIGHT of the equation, inside the result as well as inside the flags.  Every
P0 characterization equation computes its result from operands only; these two
say, in the theorem, that the same instruction on the same operands has two
different results depending on the state it starts in.  Anything reasoning above
this layer has to carry CF, and the equation is where it finds that out.

⚠️ AND THE CARRY IS THE INCOMING ONE.  `s.flags.cf` is read from `s`, not from
the intermediate state after the flags are written — an ADC that read its own
output CF would be a fixpoint, not an instruction, and the equation is what
pins the order down. -/

theorem step_adc_reg_op (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s) :
    step ⟨.bin .adc sz (.reg r h8) o, len⟩ s =
      { s with
        regs := s.regs.set r (if h8
          then Value.writeHigh8 (s.regs.get r)
            (Flags.adcResult sz (s.getReg sz r h8)
              (s.readOperand sz (s.rip + BitVec.ofNat 64 len) o) s.flags.cf)
          else Value.writeView sz (s.regs.get r)
            (Flags.adcResult sz (s.getReg sz r h8)
              (s.readOperand sz (s.rip + BitVec.ofNat 64 len) o) s.flags.cf)),
        flags := Flags.adc sz (s.getReg sz r h8)
          (s.readOperand sz (s.rip + BitVec.ofNat 64 len) o) s.flags.cf s.flags,
        rip := s.rip + BitVec.ofNat 64 len } := by
  cases h8 <;> simp [step, h, Cpu.getReg]

theorem step_sbb_reg_op (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s) :
    step ⟨.bin .sbb sz (.reg r h8) o, len⟩ s =
      { s with
        regs := s.regs.set r (if h8
          then Value.writeHigh8 (s.regs.get r)
            (Flags.sbbResult sz (s.getReg sz r h8)
              (s.readOperand sz (s.rip + BitVec.ofNat 64 len) o) s.flags.cf)
          else Value.writeView sz (s.regs.get r)
            (Flags.sbbResult sz (s.getReg sz r h8)
              (s.readOperand sz (s.rip + BitVec.ofNat 64 len) o) s.flags.cf)),
        flags := Flags.sbb sz (s.getReg sz r h8)
          (s.readOperand sz (s.rip + BitVec.ofNat 64 len) o) s.flags.cf s.flags,
        rip := s.rip + BitVec.ofNat 64 len } := by
  cases h8 <;> simp [step, h, Cpu.getReg]

/-- ⭐ ADC WITH CF CLEAR IS ADD, AND SBB WITH CF CLEAR IS SUB — as an equation,
not as a comment.  This is the theorem that says the new template DEGENERATES to
the old one, which is the strongest single statement available about a
carry-propagating form: if it were wrong, `adc` would be a second, subtly
different adder living beside `add` and the differential run would have to find
the difference one operand at a time. -/
theorem adc_no_carry_is_add (sz : Size) (a b : Val) :
    Flags.adcResult sz a b false = Flags.addResult sz a b := by
  simp [Flags.adcResult, Flags.addResult, Flags.carryVal]

theorem sbb_no_carry_is_sub (sz : Size) (a b : Val) :
    Flags.sbbResult sz a b false = Flags.subResult sz a b := by
  simp [Flags.sbbResult, Flags.subResult, Flags.carryVal]

theorem adc_no_carry_flags_are_add (sz : Size) (a b : Val) (f : Flags) :
    Flags.adc sz a b false f = Flags.add sz a b f := by
  simp [Flags.adc, Flags.add, Flags.adcCF, Flags.addCF, adc_no_carry_is_add]

theorem sbb_no_carry_flags_are_sub (sz : Size) (a b : Val) (f : Flags) :
    Flags.sbb sz a b false f = Flags.sub sz a b f := by
  simp [Flags.sbb, Flags.sub, Flags.sbbCF, Flags.subCF, sbb_no_carry_is_sub]

theorem step_adc_reg_op_mem (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s) :
    (step ⟨.bin .adc sz (.reg r h8) o, len⟩ s).mem = s.mem := by
  rw [step_adc_reg_op sz r h8 o h]

theorem step_sbb_reg_op_mem (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s) :
    (step ⟨.bin .sbb sz (.reg r h8) o, len⟩ s).mem = s.mem := by
  rw [step_sbb_reg_op sz r h8 o h]

/-! ## P1 BATCH 1 — the logic group at EVERY operand shape

`p1/roster.tsv` family `0xuxx0-|-|reg`: AND, OR and XOR writing a register.
Twenty-one forms in K's roster; three equations here, because the destination
being a register is the only thing the equation needs to know.

⭐ ONE THEOREM PER MNEMONIC, NOT ONE PER FORM, AND THE REASON IS THE MODEL'S
SHAPE RATHER THAN A WISH TO WRITE LESS.  The source operand is a VARIABLE `o`,
so a single equation covers `r,r`, `r,imm` and `r,m` at once; the destination
carries a variable `h8`, so it covers AH/CH/DH/BH too.  That is sound here and
only here: `wellFormed2` can only fail when BOTH operands are memory, and this
family's destination is a register, so there is no side condition to discharge
and no case to lose.  The memory-DESTINATION forms are batch 4 of the roster and
they are not covered by these — a register destination and a memory destination
are different equations, and merging them is how a frame condition goes missing.

The `oracle` component is the AF draw, exactly one bit, visible in the statement
(SDM Vol. 2A: AND/OR/XOR clear OF and CF, set SF/ZF/PF from the result, and
leave AF undefined).  K agrees at `0xuxx0-` in `p1/roster.tsv`, read from its
rule text and not from ours: three sources, one reading. -/

theorem step_and_reg_op (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s) :
    step ⟨.bin .and sz (.reg r h8) o, len⟩ s =
      { s with
        regs := s.regs.set r (if h8
          then Value.writeHigh8 (s.regs.get r)
            (Value.trunc sz (s.getReg sz r h8 &&&
              s.readOperand sz (s.rip + BitVec.ofNat 64 len) o))
          else Value.writeView sz (s.regs.get r)
            (Value.trunc sz (s.getReg sz r h8 &&&
              s.readOperand sz (s.rip + BitVec.ofNat 64 len) o))),
        flags := Flags.logic sz
          (Value.trunc sz (s.getReg sz r h8 &&&
            s.readOperand sz (s.rip + BitVec.ofNat 64 len) o))
          (s.oracle.bits s.oracle.cursor) s.flags,
        oracle := { s.oracle with cursor := s.oracle.cursor + 1 },
        rip := s.rip + BitVec.ofNat 64 len } := by
  cases h8 <;> simp [step, h, Cpu.getReg]

theorem step_or_reg_op (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s) :
    step ⟨.bin .or sz (.reg r h8) o, len⟩ s =
      { s with
        regs := s.regs.set r (if h8
          then Value.writeHigh8 (s.regs.get r)
            (Value.trunc sz (s.getReg sz r h8 |||
              s.readOperand sz (s.rip + BitVec.ofNat 64 len) o))
          else Value.writeView sz (s.regs.get r)
            (Value.trunc sz (s.getReg sz r h8 |||
              s.readOperand sz (s.rip + BitVec.ofNat 64 len) o))),
        flags := Flags.logic sz
          (Value.trunc sz (s.getReg sz r h8 |||
            s.readOperand sz (s.rip + BitVec.ofNat 64 len) o))
          (s.oracle.bits s.oracle.cursor) s.flags,
        oracle := { s.oracle with cursor := s.oracle.cursor + 1 },
        rip := s.rip + BitVec.ofNat 64 len } := by
  cases h8 <;> simp [step, h, Cpu.getReg]

theorem step_xor_reg_op (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s) :
    step ⟨.bin .xor sz (.reg r h8) o, len⟩ s =
      { s with
        regs := s.regs.set r (if h8
          then Value.writeHigh8 (s.regs.get r)
            (Value.trunc sz (s.getReg sz r h8 ^^^
              s.readOperand sz (s.rip + BitVec.ofNat 64 len) o))
          else Value.writeView sz (s.regs.get r)
            (Value.trunc sz (s.getReg sz r h8 ^^^
              s.readOperand sz (s.rip + BitVec.ofNat 64 len) o))),
        flags := Flags.logic sz
          (Value.trunc sz (s.getReg sz r h8 ^^^
            s.readOperand sz (s.rip + BitVec.ofNat 64 len) o))
          (s.oracle.bits s.oracle.cursor) s.flags,
        oracle := { s.oracle with cursor := s.oracle.cursor + 1 },
        rip := s.rip + BitVec.ofNat 64 len } := by
  cases h8 <;> simp [step, h, Cpu.getReg]

/-! ### The batch's FRAME (plan v1 §3.5)

⚠️ THIS IS THE HALF THE CHARACTERIZATION EQUATIONS DO NOT STATE OUT LOUD.  An
equation `step i s = { s with … }` says which components change by naming them —
but reading a component's ABSENCE as a guarantee means trusting that the reader
enumerated the record's fields correctly, and a record gains fields.  These say
it positively, for the field a register-destination form must not touch: batch
1 writes NO MEMORY, at any width, through any source operand, including a
source that is itself a memory read. -/

theorem step_and_reg_op_mem (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s) :
    (step ⟨.bin .and sz (.reg r h8) o, len⟩ s).mem = s.mem := by
  rw [step_and_reg_op sz r h8 o h]

theorem step_or_reg_op_mem (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s) :
    (step ⟨.bin .or sz (.reg r h8) o, len⟩ s).mem = s.mem := by
  rw [step_or_reg_op sz r h8 o h]

theorem step_xor_reg_op_mem (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s) :
    (step ⟨.bin .xor sz (.reg r h8) o, len⟩ s).mem = s.mem := by
  rw [step_xor_reg_op sz r h8 o h]

/-! ## INC / DEC / NEG / NOT — SDM Vol. 2A.

INC and DEC do **not** touch CF; that is why they are not `add r, 1` and
`sub r, 1`, and the equations below carry the proof: `Flags.inc` and `Flags.dec`
copy `cf` through from `s.flags`.  NOT touches no flag at all. -/

theorem step_inc_reg (sz : Size) (r : GPR) (h : Live s) :
    step ⟨.un .inc sz (.reg r), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView sz (s.regs.get r)
          (Flags.addResult sz (s.getReg sz r) 1)),
        flags := Flags.inc sz (s.getReg sz r) s.flags,
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.getReg]

theorem step_dec_reg (sz : Size) (r : GPR) (h : Live s) :
    step ⟨.un .dec sz (.reg r), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView sz (s.regs.get r)
          (Flags.subResult sz (s.getReg sz r) 1)),
        flags := Flags.dec sz (s.getReg sz r) s.flags,
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.getReg]

theorem step_neg_reg (sz : Size) (r : GPR) (h : Live s) :
    step ⟨.un .neg sz (.reg r), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView sz (s.regs.get r)
          (Flags.subResult sz 0 (s.getReg sz r))),
        flags := Flags.neg sz (s.getReg sz r) s.flags,
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.getReg]

/-- NOT changes no flag: `flags` is absent from the update. -/
theorem step_not_reg (sz : Size) (r : GPR) (h : Live s) :
    step ⟨.un .not sz (.reg r), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView sz (s.regs.get r)
          (Value.trunc sz (~~~s.getReg sz r))),
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.getReg]

/-! ## SHL / SHR / SAR — SDM Vol. 2A.

TWO equations, because the SDM gives two behaviours: a masked count of zero
affects NO flag, and a non-zero count spends THREE oracle bits (CF, OF, AF, in
that order) whether or not each is undefined at that count.  Fixing the COUNT as
well as the order is what makes the cursor a deterministic function of the
instruction stream, so the harness can replay a run. -/

theorem step_shift_reg_zero (k : ShiftKind) (sz : Size) (r : GPR) (c : BitVec 8)
    (h : Live s) (hc : Flags.shiftCount sz c = 0) :
    step ⟨.shift k sz (.reg r) (.imm8 c), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView sz (s.regs.get r)
          (match k with
           | .shl => Value.trunc sz (s.getReg sz r <<< (0 : Nat))
           | .shr => (Value.trunc sz (s.getReg sz r)) >>> (0 : Nat)
           | .sar => Value.sar sz (s.getReg sz r) 0)),
        rip := s.rip + BitVec.ofNat 64 len } := by
  cases k <;> simp [step, h, hc, Cpu.getReg]

theorem step_shift_reg_nonzero (k : ShiftKind) (sz : Size) (r : GPR) (c : BitVec 8)
    (h : Live s) (hc : Flags.shiftCount sz c ≠ 0) :
    step ⟨.shift k sz (.reg r) (.imm8 c), len⟩ s =
      (let n := Flags.shiftCount sz c
       let a := s.getReg sz r
       let res := match k with
         | .shl => Value.trunc sz (a <<< n)
         | .shr => (Value.trunc sz a) >>> n
         | .sar => Value.sar sz a n
       { s with
         regs := s.regs.set r (Value.writeView sz (s.regs.get r) res),
         flags := Flags.shiftFlags k sz a res n
           (s.oracle.bits s.oracle.cursor)
           (s.oracle.bits (s.oracle.cursor + 1))
           (s.oracle.bits (s.oracle.cursor + 2)) s.flags,
         oracle := { s.oracle with cursor := s.oracle.cursor + 3 },
         rip := s.rip + BitVec.ofNat 64 len }) := by
  cases k <;> simp [step, h, hc, Cpu.getReg] <;> omega

/-! ## LEA — SDM Vol. 2A, LEA.  "Flags Affected: None."  The address is written
under the ordinary register-width rules, so `lea eax, [...]` ZERO-EXTENDS. -/

theorem step_lea (sz : Size) (r : GPR) (ea : Ea) (h : Live s) :
    step ⟨.lea sz r ea, len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView sz (s.regs.get r)
          (ea.addr s (s.rip + BitVec.ofNat 64 len))),
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h]

/-! ## PUSH / POP — SDM Vol. 2A.  "Flags Affected: None." -/

theorem step_push_reg (sz : Size) (r : GPR) (h : Live s) :
    step ⟨.push sz (.reg r), len⟩ s =
      { s with
        mem := s.mem.writeSize sz (s.regs.get .rsp - BitVec.ofNat 64 sz.bytes)
          (s.getReg sz r),
        regs := s.regs.set .rsp (s.regs.get .rsp - BitVec.ofNat 64 sz.bytes),
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.getReg]

/-- POP into a register OTHER than RSP. -/
theorem step_pop_reg (sz : Size) (r : GPR) (h : Live s) (hr : GPR.rsp ≠ r) :
    step ⟨.pop sz (.reg r), len⟩ s =
      { s with
        regs := (s.regs.set .rsp (s.regs.get .rsp + BitVec.ofNat 64 sz.bytes)).set r
          (Value.writeView sz (s.regs.get r) (s.mem.readSize sz (s.regs.get .rsp))),
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Regs.get_set_ne _ _ _ _ hr]

/-- POP into RSP: the LOADED value wins over the increment.  This is the classic
ordering subtlety and it is worth its own theorem, because a model that does the
increment last is wrong here and nowhere else. -/
theorem step_pop_rsp (sz : Size) (h : Live s) :
    step ⟨.pop sz (.reg .rsp), len⟩ s =
      { s with
        regs := s.regs.set .rsp (Value.writeView sz
          (s.regs.get .rsp + BitVec.ofNat 64 sz.bytes)
          (s.mem.readSize sz (s.regs.get .rsp))),
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Regs.set_set_same]

/-! ## JMP / Jcc / CALL — SDM Vol. 2A.  "Flags Affected: None."

⭐ EVERY ONE OF THESE CARRIES A CANONICALITY HYPOTHESIS, and it is not
bookkeeping.  In 64-bit mode a branch to a non-canonical target raises #GP(0)
(SDM Vol. 1 §3.3.7.1 for canonical form; Vol. 2A, JMP/CALL "64-Bit Mode
Exceptions").  The first version of this file had no such hypothesis and the
theorems were all still TRUE OF THE MODEL — the model was simply wrong, and
self-consistently so.  What found it was the differential run against ACL2
x86isa: 80 unexplained disagreements, every one an indirect branch to a
non-canonical address.  The `_noncanonical` companions below are the other half
of each equation, and the reason the hypothesis cannot be quietly dropped. -/

theorem step_jmp_rel (d : Val) (h : Live s) (hc : canonical (s.rip + BitVec.ofNat 64 len + d)) :
    step ⟨.jmp (.rel d), len⟩ s =
      { s with rip := (s.rip + BitVec.ofNat 64 len) + d } := by
  simp [step, h, Cpu.setRipChecked, hc]

theorem step_jmp_indirect_reg (r : GPR) (h : Live s) (hc : canonical (s.getReg .q r)) :
    step ⟨.jmp (.indirect (.reg r)), len⟩ s = { s with rip := s.getReg .q r } := by
  simp [step, h, Cpu.getReg, Cpu.setRipChecked] at hc ⊢
  simp [hc]

/-- A branch this model declines: it HALTS and moves nothing else.  Note what is
absent from the update — `rip` is not written, so a refused jump does not land
anywhere. -/
theorem step_jmp_indirect_noncanonical (r : GPR) (h : Live s)
    (hc : canonical (s.getReg .q r) = false) :
    step ⟨.jmp (.indirect (.reg r)), len⟩ s =
      { s with ms := some (.unimplemented "non-canonical branch target (#GP(0) in hardware)") } := by
  simp [step, h, Cpu.getReg, Cpu.setRipChecked, Cpu.halt] at hc ⊢
  simp [hc, Cpu.halt, h]

/-- Jcc, both arms in one equation: RIP is the taken target or the fall-through,
and NOTHING else moves — in particular the flags the condition read are
untouched.  Only the TAKEN arm can be non-canonical, so the hypothesis is
conditional on the branch being taken. -/
theorem step_jcc (c : Cc) (d : Val) (h : Live s)
    (hc : c.eval s.flags = true → canonical (s.rip + BitVec.ofNat 64 len + d)) :
    step ⟨.jcc c d, len⟩ s =
      { s with rip := if c.eval s.flags then (s.rip + BitVec.ofNat 64 len) + d
                      else s.rip + BitVec.ofNat 64 len } := by
  by_cases he : c.eval s.flags
  · simp [step, h, he, Cpu.setRipChecked, hc he]
  · simp [step, h, he]

theorem step_call_rel (d : Val) (h : Live s)
    (hc : canonical (s.rip + BitVec.ofNat 64 len + d)) :
    step ⟨.call (.rel d), len⟩ s =
      { s with
        mem := s.mem.writeSize .q (s.regs.get .rsp - 8) (s.rip + BitVec.ofNat 64 len),
        regs := s.regs.set .rsp (s.regs.get .rsp - 8),
        rip := (s.rip + BitVec.ofNat 64 len) + d } := by
  simp [step, h, hc]

theorem step_call_indirect_reg (r : GPR) (h : Live s) (hc : canonical (s.getReg .q r)) :
    step ⟨.call (.indirect (.reg r)), len⟩ s =
      { s with
        mem := s.mem.writeSize .q (s.regs.get .rsp - 8) (s.rip + BitVec.ofNat 64 len),
        regs := s.regs.set .rsp (s.regs.get .rsp - 8),
        rip := s.getReg .q r } := by
  simp [step, h, Cpu.getReg] at hc ⊢
  simp [hc]

/-- ⭐ A REFUSED CALL DOES NOT PUSH.  `regs` and `mem` are both absent from the
update, so RSP is untouched and no return address is written.  This is the
ordering the differential run made observable: the first version pushed before
checking, and disagreed with x86isa on `rsp` and on the stack window as well as
on `rip` — three symptoms of one mis-ordering. -/
theorem step_call_indirect_noncanonical (r : GPR) (h : Live s)
    (hc : canonical (s.getReg .q r) = false) :
    step ⟨.call (.indirect (.reg r)), len⟩ s =
      { s with ms := some (.unimplemented "non-canonical branch target (#GP(0) in hardware)") } := by
  simp [step, h, Cpu.getReg, Cpu.halt] at hc ⊢
  simp [hc, Cpu.halt, h]

/-! ## The frame pack

Which forms leave the FLAGS alone, and which leave the ORACLE alone.  These are
corollaries of the equations above — every one is `by simp [the equation]` — but
they are stated because they are what a downstream proof actually needs, and
because a form that quietly spends an oracle bit would break the second group
loudly. -/

@[simp] theorem step_mov_flags (sz : Size) (r r' : GPR) (h : Live s) :
    (step ⟨.mov sz (.reg r) (.reg r'), len⟩ s).flags = s.flags := by
  rw [step_mov_reg_reg sz r r' h]

@[simp] theorem step_lea_flags (sz : Size) (r : GPR) (ea : Ea) (h : Live s) :
    (step ⟨.lea sz r ea, len⟩ s).flags = s.flags := by
  rw [step_lea sz r ea h]

@[simp] theorem step_not_flags (sz : Size) (r : GPR) (h : Live s) :
    (step ⟨.un .not sz (.reg r), len⟩ s).flags = s.flags := by
  rw [step_not_reg sz r h]

@[simp] theorem step_jcc_flags (c : Cc) (d : Val) (h : Live s)
    (hc : c.eval s.flags = true → canonical (s.rip + BitVec.ofNat 64 len + d)) :
    (step ⟨.jcc c d, len⟩ s).flags = s.flags := by
  rw [step_jcc c d h hc]

/-- ADD SPENDS NO ORACLE BIT: every flag it writes is defined.  The contrast
with `step_and_oracle` below is the content. -/
@[simp] theorem step_add_oracle (sz : Size) (r r' : GPR) (h : Live s) :
    (step ⟨.bin .add sz (.reg r) (.reg r'), len⟩ s).oracle = s.oracle := by
  rw [step_add_reg_reg sz r r' h]

/-- AND SPENDS EXACTLY ONE: the SDM leaves AF undefined and this model declines
to invent it. -/
theorem step_and_oracle (sz : Size) (r r' : GPR) (h : Live s) :
    (step ⟨.bin .and sz (.reg r) (.reg r'), len⟩ s).oracle.cursor
      = s.oracle.cursor + 1 := by
  rw [step_and_reg_reg sz r r' h]

/-- INC PRESERVES CF.  The single most-cited difference between `inc` and
`add 1`, as a theorem rather than a comment. -/
theorem step_inc_preserves_cf (sz : Size) (r : GPR) (h : Live s) :
    (step ⟨.un .inc sz (.reg r), len⟩ s).flags.cf = s.flags.cf := by
  rw [step_inc_reg sz r h]; rfl

/-! ## P1 BATCH 10 — the width-changing and two-destination moves

⭐ THE WHOLE BATCH IS ONE FRAME CLAIM: these forms move data and NOTHING ELSE.
No flag, no oracle bit, no memory (`xchg` refuses the shape that would touch
it).  Stating it as equations is what makes "flags affected: none" checkable
rather than a sentence copied out of the manual. -/

/-- MOVZX / MOVSX / MOVSXD: the source is read at `ssz`, extended, and written
at `dsz`.  The two widths are separate arguments of the equation because they
are separate data on the instruction. -/
theorem step_movx (k : MovxKind) (dsz ssz : Size) (r r' : GPR) (h : Live s) :
    step ⟨.movx k dsz ssz r (.reg r'), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView dsz (s.regs.get r)
                  (match k with
                   | .zero => Value.zext ssz (s.getReg ssz r')
                   | .sign => Value.sext ssz (s.getReg ssz r'))),
        rip := s.rip + BitVec.ofNat 64 len } := by
  cases k <;> simp [step, h, Cpu.setReg, Cpu.setRip, Cpu.readOperand, Cpu.getReg]

@[simp] theorem step_movx_flags (k : MovxKind) (dsz ssz : Size) (r r' : GPR) (h : Live s) :
    (step ⟨.movx k dsz ssz r (.reg r'), len⟩ s).flags = s.flags := by
  rw [step_movx k dsz ssz r r' h]

@[simp] theorem step_movx_oracle (k : MovxKind) (dsz ssz : Size) (r r' : GPR) (h : Live s) :
    (step ⟨.movx k dsz ssz r (.reg r'), len⟩ s).oracle = s.oracle := by
  rw [step_movx k dsz ssz r r' h]

@[simp] theorem step_movx_mem (k : MovxKind) (dsz ssz : Size) (r r' : GPR) (h : Live s) :
    (step ⟨.movx k dsz ssz r (.reg r'), len⟩ s).mem = s.mem := by
  rw [step_movx k dsz ssz r r' h]

/-- ⭐ `cqto` WRITES RDX AND LEAVES RAX ALONE.  `regs` is updated at `.rdx` only,
which is the frame claim the `98`/`99` opcode pair turns on: one trio widens the
accumulator, the other fills a register the operands never name. -/
theorem step_cqto (h : Live s) :
    step ⟨.cext .cqo, len⟩ s =
      { s with
        regs := s.regs.set .rdx (if Value.msb .q (s.regs.get .rax) then Size.mask .q else 0),
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.setReg, Cpu.setRip, Value.writeView]

theorem step_cqto_leaves_rax (h : Live s) :
    (step ⟨.cext .cqo, len⟩ s).regs.get .rax = s.regs.get .rax := by
  rw [step_cqto h]; simp [Regs.get_set_ne _ _ _ _ (by decide : GPR.rdx ≠ GPR.rax)]

@[simp] theorem step_cext_flags (k : CextKind) (h : Live s) :
    (step ⟨.cext k, len⟩ s).flags = s.flags := by
  cases k <;> simp [step, h, Cpu.setReg, Cpu.setRip]

@[simp] theorem step_cext_oracle (k : CextKind) (h : Live s) :
    (step ⟨.cext k, len⟩ s).oracle = s.oracle := by
  cases k <;> simp [step, h, Cpu.setReg, Cpu.setRip]

/-- XCHG at two registers: BOTH values are read before either is written, so the
equation names `s.getReg` on both sides and never the intermediate state.  That
is what makes the same-register case a swap of a value with itself rather than a
clobber. -/
theorem step_xchg_reg_reg (sz : Size) (a b : GPR) (h : Live s) :
    step ⟨.xchg sz (.reg a) (.reg b), len⟩ s =
      { s with
        regs := (s.regs.set a (Value.writeView sz (s.regs.get a) (s.getReg sz b))).set b
                  (Value.writeView sz
                    ((s.regs.set a (Value.writeView sz (s.regs.get a) (s.getReg sz b))).get b)
                    (s.getReg sz a)),
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.setReg, Cpu.setRip, Cpu.readOperand, Cpu.writeOperand, Cpu.getReg,
    Operand.isMem, Operand.isImm]

@[simp] theorem step_xchg_flags (sz : Size) (a b : GPR) (h : Live s) :
    (step ⟨.xchg sz (.reg a) (.reg b), len⟩ s).flags = s.flags := by
  rw [step_xchg_reg_reg sz a b h]

@[simp] theorem step_xchg_mem (sz : Size) (a b : GPR) (h : Live s) :
    (step ⟨.xchg sz (.reg a) (.reg b), len⟩ s).mem = s.mem := by
  rw [step_xchg_reg_reg sz a b h]

/-- ⛔ AND THE REFUSED SHAPE IS A THEOREM TOO.  `xchg` with a memory operand sets
`ms` and changes NOTHING else — not the registers, not the memory it declined to
touch.  A refusal that quietly half-executed would be worse than a wrong answer,
because the state it left would look like a state. -/
theorem step_xchg_mem_refuses (sz : Size) (ea : Ea) (r : GPR) (h : Live s) :
    step ⟨.xchg sz (.mem ea) (.reg r), len⟩ s =
      { s with ms := some (.unimplemented "xchg with a memory operand (implicit LOCK)") } := by
  simp [step, h, Cpu.halt, Operand.isMem]

@[simp] theorem step_bswap_flags (sz : Size) (r : GPR) (h : Live s) :
    (step ⟨.bswap sz r, len⟩ s).flags = s.flags := by
  cases sz <;> simp [step, h, Cpu.setReg, Cpu.setRip, Cpu.halt]

/-! ## P1 BATCH 11 — the loop group and the flag-control singles -/

/-- A checked RIP write never touches the registers — whether it lands or
REFUSES.  Needed because `loop`'s counter write-back must be visible on both
paths, and the taken path ends in `setRipChecked`, which may halt. -/
@[simp] theorem setRipChecked_regs (s : Cpu) (v : Val) :
    (s.setRipChecked v).regs = s.regs := by
  cases hc : canonical v <;> cases hm : s.ms <;>
    simp [Cpu.setRipChecked, Cpu.halt, hc, hm]

@[simp] theorem setRipChecked_flags (s : Cpu) (v : Val) :
    (s.setRipChecked v).flags = s.flags := by
  cases hc : canonical v <;> cases hm : s.ms <;>
    simp [Cpu.setRipChecked, Cpu.halt, hc, hm]

@[simp] theorem setRipChecked_mem (s : Cpu) (v : Val) :
    (s.setRipChecked v).mem = s.mem := by
  cases hc : canonical v <;> cases hm : s.ms <;>
    simp [Cpu.setRipChecked, Cpu.halt, hc, hm]

@[simp] theorem setRipChecked_oracle (s : Cpu) (v : Val) :
    (s.setRipChecked v).oracle = s.oracle := by
  cases hc : canonical v <;> cases hm : s.ms <;>
    simp [Cpu.setRipChecked, Cpu.halt, hc, hm]

/-- ⭐ THE FRAME CLAIM THAT IS THE WHOLE POINT OF THE LOOP GROUP: `loop` WRITES
NO FLAG, at either counter width and on either path.  Two of the three loops
READ a flag (ZF) and none of the three writes one — the counter moves, the flags
do not.  Stated over both `addr32` values and all three predicates at once,
because a per-predicate proof would let one case drift. -/
@[simp] theorem step_loop_flags (k : LoopKind) (a32 : Bool) (d : Val) (h : Live s) :
    (step ⟨.loop k a32 d, len⟩ s).flags = s.flags := by
  cases k <;> cases a32 <;>
    simp [step, h, Cpu.setReg, Cpu.setRip] <;> split <;> simp [Cpu.setRip]

@[simp] theorem step_loop_mem (k : LoopKind) (a32 : Bool) (d : Val) (h : Live s) :
    (step ⟨.loop k a32 d, len⟩ s).mem = s.mem := by
  cases k <;> cases a32 <;>
    simp [step, h, Cpu.setReg, Cpu.setRip] <;> split <;> simp [Cpu.setRip]

@[simp] theorem step_loop_oracle (k : LoopKind) (a32 : Bool) (d : Val) (h : Live s) :
    (step ⟨.loop k a32 d, len⟩ s).oracle = s.oracle := by
  cases k <;> cases a32 <;>
    simp [step, h, Cpu.setReg, Cpu.setRip] <;> split <;> simp [Cpu.setRip]

/-- ⭐ THE COUNTER IS WRITTEN ON BOTH PATHS, AND THIS IS THE THEOREM THAT SAYS SO.
Whether or not the branch is taken, RCX ends holding the DECREMENTED counter —
which is the half of `LOOP` that a "if taken, then jump and decrement"
implementation gets wrong, and which no flag or RIP claim can see.

Stated at the 64-bit width, where the write-back is the whole register, so the
equation is an equality of values rather than of write-views. -/
theorem step_loop_q_counter (k : LoopKind) (d : Val) (h : Live s) :
    (step ⟨.loop k false d, len⟩ s).regs.get .rcx = s.regs.get .rcx - 1 := by
  cases k <;>
    simp [step, h, Cpu.setReg, Cpu.setRip, Cpu.getReg, Value.writeView] <;>
    split <;> simp [Cpu.setRip]

/-- ⛔ AND THE FLAG-CONTROL SINGLES CHANGE EXACTLY ONE BIT.  `clc` writes CF and
leaves DF; `cld` writes DF and leaves CF; and NEITHER touches the other five
arithmetic flags.  This is the frame claim that makes "all other flags are
unaffected" (SDM Vol. 2A, CLC/CLD) a checked statement rather than a comment. -/
theorem step_clc (h : Live s) :
    step ⟨.flagop .clc, len⟩ s =
      { s with flags := { s.flags with cf := false },
               rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.setFlags, Cpu.setRip]

theorem step_std (h : Live s) :
    step ⟨.flagop .std, len⟩ s =
      { s with flags := { s.flags with df := true },
               rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.setFlags, Cpu.setRip]

/-- `cld` leaves CF exactly as it found it — the pair of this and
`step_clc_leaves_df` is what says the two instructions are independent, which is
the only thing that could go wrong in a five-case `match` written from one
template. -/
theorem step_cld_leaves_cf (h : Live s) :
    (step ⟨.flagop .cld, len⟩ s).flags.cf = s.flags.cf := by
  simp [step, h, Cpu.setFlags, Cpu.setRip]

theorem step_clc_leaves_df (h : Live s) :
    (step ⟨.flagop .clc, len⟩ s).flags.df = s.flags.df := by
  simp [step, h, Cpu.setFlags, Cpu.setRip]

/-- ⭐ `cmc` IS AN INVOLUTION ON CF, which is the one algebraic fact this group
has and the one a "complement" written as "set" would break. -/
theorem step_cmc_cmc_restores_cf (len2 : Nat) (h : Live s)
    (h' : Live (step ⟨.flagop .cmc, len⟩ s)) :
    (step ⟨.flagop .cmc, len2⟩ (step ⟨.flagop .cmc, len⟩ s)).flags.cf = s.flags.cf := by
  simp [step, h, h', Cpu.setFlags, Cpu.setRip]

@[simp] theorem step_flagop_regs (k : FlagOp) (h : Live s) :
    (step ⟨.flagop k, len⟩ s).regs = s.regs := by
  cases k <;> simp [step, h, Cpu.setFlags, Cpu.setRip]

@[simp] theorem step_flagop_mem (k : FlagOp) (h : Live s) :
    (step ⟨.flagop k, len⟩ s).mem = s.mem := by
  cases k <;> simp [step, h, Cpu.setFlags, Cpu.setRip]

@[simp] theorem step_flagop_oracle (k : FlagOp) (h : Live s) :
    (step ⟨.flagop k, len⟩ s).oracle = s.oracle := by
  cases k <;> simp [step, h, Cpu.setFlags, Cpu.setRip]

/-! ## P1 BATCH 12 — the near-free four -/

/-- ⭐⭐ NOP'S CHARACTERIZATION IS ITS FRAME, AND IT IS QUANTIFIED OVER THE
OPERAND.  Every other form in this file needs a separate lemma per component to
say what it did NOT touch; `nop` is the one whose entire meaning is the frame, so
the statement is a single equation and there is nothing left to say.

⚠️ THE `∀ o` IS THE LOAD-BEARING PART.  It covers `.nop (some (M .rbx))` — the
multi-byte form with a MEMORY operand — and therefore proves that
`nopl (%rbx)` does not read the data window, does not fault on it, and does not
depend on what it holds.  A model that "harmlessly" read the operand and threw
the value away would still be wrong (a read from an unmapped page faults in
hardware), and this equation is what forbids it. -/
theorem step_nop (o : Option Operand) (h : Live s) :
    step ⟨.nop o, len⟩ s = { s with rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.setRip]

/-- ⭐ UD2 HALTS AND DOES NOT ADVANCE RIP.  The second half is the claim that
could go wrong: a fault is not a completed instruction, so the RIP that x86isa
reports is the one the instruction started at.  Everything else is untouched. -/
theorem step_ud2 (h : Live s) :
    step ⟨.ud2, len⟩ s =
      { s with ms := some (.byDesign "ud2: #UD is the instruction's meaning") } := by
  simp [step, h, Cpu.halt]

/-- RET near, taken: RIP becomes the popped value and RSP moves up by eight. -/
theorem step_ret_taken (h : Live s)
    (hc : canonical (s.readMem .q (s.regs.get .rsp)) = true) :
    step ⟨.ret, len⟩ s =
      { s.setReg .q .rsp (s.regs.get .rsp + 8) with
          rip := s.readMem .q (s.regs.get .rsp) } := by
  simp only [Cpu.readMem] at hc ⊢
  simp [step, h, hc, Cpu.setReg]

/-- ⭐⭐ AND ON A REFUSAL, RSP DOES NOT MOVE.  This is the lemma that encodes what
`call`'s first differential run had to be taught: x86isa raises #GP(0) on a
non-canonical target BEFORE committing the stack update, so a `retq` that popped
and then refused would disagree with it on `rsp` as well as on `rip`.  The
disagreement on `rsp` is what makes the ORDER observable rather than an
implementation detail — and it is the reason this is a theorem rather than a
comment beside the `if`. -/
theorem step_ret_refused_frame (h : Live s)
    (hc : canonical (s.readMem .q (s.regs.get .rsp)) = false) :
    (step ⟨.ret, len⟩ s).regs = s.regs
      ∧ (step ⟨.ret, len⟩ s).rip = s.rip
      ∧ (step ⟨.ret, len⟩ s).mem = s.mem := by
  simp only [Cpu.readMem] at hc
  simp [step, h, hc, Cpu.halt]

/-- ⭐ LEAVE IS `mov rsp, rbp` THEN `pop rbp`, AND THE ORDER IS THE INSTRUCTION.
RBP comes from the address RBP ITSELF held — not from the old RSP — so the new
RSP is `RBP + 8`.  A model that popped before moving RSP would read the caller's
stack and leave RSP eight above the OLD one; against a state set where RBP is
zero and the stack pattern is fixed, the two are indistinguishable, which is
exactly why `frameStates` exists. -/
theorem step_leave_rsp (h : Live s) :
    (step ⟨.leave, len⟩ s).regs.get .rsp = s.regs.get .rbp + 8 := by
  simp [step, h, Cpu.setReg, Cpu.setRip, Cpu.popValue, Value.writeView]

theorem step_leave_rbp (h : Live s) :
    (step ⟨.leave, len⟩ s).regs.get .rbp = s.readMem .q (s.regs.get .rbp) := by
  simp [step, h, Cpu.setReg, Cpu.setRip, Cpu.popValue, Cpu.readMem, Value.writeView]

theorem step_leave_rip (h : Live s) :
    (step ⟨.leave, len⟩ s).rip = s.rip + BitVec.ofNat 64 len := by
  simp [step, h, Cpu.setReg, Cpu.setRip, Cpu.popValue]

/-- The two components `leaveq` must NOT touch. -/
@[simp] theorem step_leave_flags (h : Live s) :
    (step ⟨.leave, len⟩ s).flags = s.flags := by
  simp [step, h, Cpu.setReg, Cpu.setRip, Cpu.popValue]

@[simp] theorem step_leave_mem (h : Live s) :
    (step ⟨.leave, len⟩ s).mem = s.mem := by
  simp [step, h, Cpu.setReg, Cpu.setRip, Cpu.popValue]

@[simp] theorem step_nop_flags (o : Option Operand) (h : Live s) :
    (step ⟨.nop o, len⟩ s).flags = s.flags := by
  simp [step, h, Cpu.setRip]

end X86
