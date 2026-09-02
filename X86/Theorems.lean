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

end X86
