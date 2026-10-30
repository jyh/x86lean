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

theorem step_mov_mem_reg (sz : Size) (ea : Ea) (r : GPR) (h : Live s)
    (hl : ea.lock = false) :
    step ⟨.mov sz (.mem ea) (.reg r), len⟩ s =
      { s with
        mem := s.mem.writeSize sz (ea.addr s (s.rip + BitVec.ofNat 64 len)) (s.getReg sz r),
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.getReg, hl]

theorem step_mov_reg_mem (sz : Size) (r : GPR) (ea : Ea) (h : Live s)
    (hl : ea.lock = false) :
    step ⟨.mov sz (.reg r) (.mem ea), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView sz (s.regs.get r)
          (s.mem.readSize sz (ea.addr s (s.rip + BitVec.ofNat 64 len)))),
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, hl]

/-- TWO MEMORY OPERANDS STOP THE MODEL rather than meaning something.  This is
the totality discipline as a theorem: `step` is total, and its value on a form
no encoding can express is a HALT, not an invention. -/
theorem step_mov_mem_mem (sz : Size) (ea ea' : Ea) (h : Live s)
    (hl : ea.lock = false) (hl' : ea'.lock = false) :
    step ⟨.mov sz (.mem ea) (.mem ea'), len⟩ s =
      { s with ms := some (.illegalOperands "mov: two memory operands") } := by
  simp [step, h, Cpu.halt, hl, hl']

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

theorem step_adc_reg_op (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s)
    (hl : o.locked = false) :
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
  cases h8 <;> cases o <;> simp [step, h, Cpu.getReg, hl] <;> simp_all

theorem step_sbb_reg_op (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s)
    (hl : o.locked = false) :
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
  cases h8 <;> cases o <;> simp [step, h, Cpu.getReg, hl] <;> simp_all

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

theorem step_adc_reg_op_mem (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s)
    (hl : o.locked = false) :
    (step ⟨.bin .adc sz (.reg r h8) o, len⟩ s).mem = s.mem := by
  rw [step_adc_reg_op sz r h8 o h hl]

theorem step_sbb_reg_op_mem (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s)
    (hl : o.locked = false) :
    (step ⟨.bin .sbb sz (.reg r h8) o, len⟩ s).mem = s.mem := by
  rw [step_sbb_reg_op sz r h8 o h hl]

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

theorem step_and_reg_op (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s)
    (hl : o.locked = false) :
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
  cases h8 <;> cases o <;> simp [step, h, Cpu.getReg, hl] <;> simp_all

theorem step_or_reg_op (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s)
    (hl : o.locked = false) :
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
  cases h8 <;> cases o <;> simp [step, h, Cpu.getReg, hl] <;> simp_all

theorem step_xor_reg_op (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s)
    (hl : o.locked = false) :
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
  cases h8 <;> cases o <;> simp [step, h, Cpu.getReg, hl] <;> simp_all

/-! ### The batch's FRAME (plan v1 §3.5)

⚠️ THIS IS THE HALF THE CHARACTERIZATION EQUATIONS DO NOT STATE OUT LOUD.  An
equation `step i s = { s with … }` says which components change by naming them —
but reading a component's ABSENCE as a guarantee means trusting that the reader
enumerated the record's fields correctly, and a record gains fields.  These say
it positively, for the field a register-destination form must not touch: batch
1 writes NO MEMORY, at any width, through any source operand, including a
source that is itself a memory read. -/

theorem step_and_reg_op_mem (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s)
    (hl : o.locked = false) :
    (step ⟨.bin .and sz (.reg r h8) o, len⟩ s).mem = s.mem := by
  rw [step_and_reg_op sz r h8 o h hl]

theorem step_or_reg_op_mem (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s)
    (hl : o.locked = false) :
    (step ⟨.bin .or sz (.reg r h8) o, len⟩ s).mem = s.mem := by
  rw [step_or_reg_op sz r h8 o h hl]

theorem step_xor_reg_op_mem (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s)
    (hl : o.locked = false) :
    (step ⟨.bin .xor sz (.reg r h8) o, len⟩ s).mem = s.mem := by
  rw [step_xor_reg_op sz r h8 o h hl]

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
well as the order, once the branch is decided, keeps the cursor after ONE
instruction independent of the oracle's bits (D213; it read "a deterministic
function of the instruction stream" until 2026-09-12, which is false across a
stream). -/

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

/-! ### ⭐⭐ S1 (desk `PE`): THE MEMORY FRAME PACK'S REAL REMAINDER — THREE FORMS, FOUR LEMMAS

v1 §1.6 lists a six-form memory frame pack — movx-load, xor r/m-load, `shr`, `not`, `inc q`,
`test` — as what the CRC-32 proof needs to reason about the image across its loop body.

⛔⛔ THE FIRST CENSUS TAKEN FOR THIS BLOCK WAS WRONG, AND IN THE DIRECTION THAT INVENTS WORK. It
searched `X86/Theorems.lean` alone and reported **18** `_mem` frames; the model library carries
**27**, because NINE of them live in `X86/Program.lean` — `step_dec_reg_mem`, `step_jcc_mem`,
`step_mov_reg_imm_mem`, `step_mov_reg_mem_mem` and `step_inc_reg_mem` among them. The error was
caught by the ELABORATOR, not by the census: `step_inc_reg_mem` had already been declared, so
`inc q` was one of v1 §1.6's six that did NOT need writing.
⇒ 🔑 ***A CENSUS OVER ONE FILE OF A MULTI-FILE LIBRARY IS AN ACCURATE COUNT OF SOMETHING ELSE***,
and a frame pack is exactly the kind of thing that grows wherever the proof that needed it lived.

THREE of the six were already covered and are NOT restated here: `step_xor_reg_op_mem` (general in
its operand, so it already covers the r/m-LOAD form), `step_inc_reg_mem` (`X86/Program.lean`), and
`step_movx_memsrc_mem` (added by S1, above).  The remainder is THREE FORMS — `not`, `test`,
`shr` — and FOUR lemmas, because the shift is stated as a PAIR split on whether its masked
count is zero and a frame proved on one branch alone would be silent about the other.

⚠️ The 27/132 ratio still carries the finding the wrong number was reaching for: `flags` is framed
18 times and `oracle` 7, and **the pack was fitted to the DIFFERENTIAL COMPARATOR'S question rather
than a proof's** — `flags` and `oracle` are what the harness watches per case, while `mem` is what a
SAFETY proof asks about and was framed only where some earlier proof happened to need it.

⚠️ THESE ARE TRIVIALLY TRUE AND THAT IS NOT AN ARGUMENT AGAINST THEM. Each names a REGISTER-form
instruction, so it obviously writes no memory — and without the lemma a proof of the loop body has
to unfold `step` at every one of these instructions, which is precisely what the proof interface
exists to prevent. A frame lemma's value is that the caller never has to look.
-/

@[simp] theorem step_not_reg_mem (sz : Size) (r : GPR) (h : Live s) :
    (step ⟨.un .not sz (.reg r), len⟩ s).mem = s.mem := by
  rw [step_not_reg sz r h]

@[simp] theorem step_test_reg_reg_mem (sz : Size) (r r' : GPR) (h : Live s) :
    (step ⟨.bin .test sz (.reg r) (.reg r'), len⟩ s).mem = s.mem := by
  rw [step_test_reg_reg sz r r' h]

/-- ⚠️ THE SHIFT NEEDS BOTH BRANCHES, because `step_shift_reg_*` is stated as a PAIR split on
whether the masked count is zero — the SDM's "if the count is 0 the flags are unaffected" rule —
and a frame proved on one branch alone would be silent about the other. -/
@[simp] theorem step_shift_reg_zero_mem (k : ShiftKind) (sz : Size) (r : GPR) (c : BitVec 8)
    (h : Live s) (hc : Flags.shiftCount sz c = 0) :
    (step ⟨.shift k sz (.reg r) (.imm8 c), len⟩ s).mem = s.mem := by
  rw [step_shift_reg_zero k sz r c h hc]

@[simp] theorem step_shift_reg_nonzero_mem (k : ShiftKind) (sz : Size) (r : GPR) (c : BitVec 8)
    (h : Live s) (hc : Flags.shiftCount sz c ≠ 0) :
    (step ⟨.shift k sz (.reg r) (.imm8 c), len⟩ s).mem = s.mem := by
  rw [step_shift_reg_nonzero k sz r c h hc]

/-! ## LEA — SDM Vol. 2A, LEA.  "Flags Affected: None."  The address is written
under the ordinary register-width rules, so `lea eax, [...]` ZERO-EXTENDS.

⭐⭐ P2 ITEM 1 CHANGED THIS THEOREM'S STATEMENT, AND THE CHANGE IS THE CLAIM.
It said `ea.addr` and now says `ea.offset`: LEA writes the EFFECTIVE ADDRESS,
with no segment base added (SDM Vol. 2A, LEA).  Before this batch the two were
the same function and the distinction could not be stated; `step_lea_ignores_seg`
below is the half that a reader cannot get from the shape of this one. -/

theorem step_lea (sz : Size) (r : GPR) (ea : Ea) (h : Live s)
    (hl : ea.lock = false) :
    step ⟨.lea sz r ea, len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView sz (s.regs.get r)
          (ea.offset s (s.rip + BitVec.ofNat 64 len))),
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, hl]

/-- ⭐⭐ A SEGMENT PREFIX ON A `lea` IS INERT — stated positively, over ALL
segments and ALL states, because the differential run can only ever sample it.
`{ ea with seg := g }` and `ea` are the same instruction to LEA. -/
theorem step_lea_ignores_seg (sz : Size) (r : GPR) (ea : Ea) (g g' : Option Seg)
    (hl : ea.lock = false) :
    step ⟨.lea sz r { ea with seg := g }, len⟩ s = step ⟨.lea sz r { ea with seg := g' }, len⟩ s := by
  by_cases h : Live s
  · rw [step_lea sz r { ea with seg := g } h hl, step_lea sz r { ea with seg := g' } h hl]
    simp only [Ea.offset_set_seg]
  · simp only [Live] at h
    cases hm : s.ms with
    | none => exact absurd hm h
    | some _ => simp [step, Cpu.stopped, hm]

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

/-! ### ⭐⭐⭐ THE PACKED (SIMD) FORMS — P2 vector wave, batch 2 -/

/-- Any of the four 128-bit moves between registers: XMM and RIP move, and
NOTHING ELSE.  ⭐ STATED OVER THE KIND rather than over each mnemonic, which is
what makes `vmov_kind_irrelevant` a corollary rather than a second proof. -/
theorem step_vmov (k : VMovKind) (d s' : XmmReg) (h : Live s) :
    step ⟨.vmov k d s', len⟩ s =
      { s with xmm := s.xmm.set d (s.getXmm s'),
               rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.setXmm, Cpu.setRip, Cpu.getXmm]

/-- The packed binary operations: DEST := DEST op SRC, in XMM only.
⚠️ D266: every kind but `minps`/`maxps`, which also raise MXCSR flags (below). -/
theorem step_vbin (k : VBinKind) (d s' : XmmReg) (h : Live s) (hk : k.isMinMax = false) :
    step ⟨.vbin k d s', len⟩ s =
      { s with xmm := s.xmm.set d (vbinApply k (s.getXmm d) (s.getXmm s')),
               rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, hk, vbinFlags, Cpu.setXmm, Cpu.setRip, Cpu.getXmm]

/-- ⭐ D266: `minps`/`maxps` write XMM and RIP as every packed kind does, AND OR their
exception flags into MXCSR, when every flag they raise is masked. -/
theorem step_vbin_minmax (k : VBinKind) (d s' : XmmReg) (h : Live s)
    (hm : (vbinFlags k (s.getXmm d) (s.getXmm s') &&& ~~~(s.mxcsr >>> 7) &&& 63#32) = 0#32) :
    step ⟨.vbin k d s', len⟩ s =
      { s with xmm := s.xmm.set d (vbinApply k (s.getXmm d) (s.getXmm s')),
               rip := s.rip + BitVec.ofNat 64 len,
               mxcsr := s.mxcsr ||| vbinFlags k (s.getXmm d) (s.getXmm s') } := by
  simp [step, h, Cpu.withSimd, hm, Cpu.setXmm, Cpu.setRip]
  rfl

/-- ⭐ NO PACKED FORM TOUCHES A FLAG.  "Flags Affected: None" is on every SDM
entry in this group, and the easiest way to get a packed operation wrong is to
reach for `BinKind`'s flag machinery by analogy — so the absence is asserted
rather than assumed. -/
@[simp] theorem step_vbin_flags (k : VBinKind) (d s' : XmmReg) (h : Live s) :
    (step ⟨.vbin k d s', len⟩ s).flags = s.flags := by
  by_cases hc : (vbinFlags k (s.getXmm d) (s.getXmm s') &&& ~~~(s.mxcsr >>> 7) &&& 63#32) = 0#32
    <;> simp [step, h, hc, Cpu.withSimd, Cpu.halt, Cpu.setXmm, Cpu.setRip]

@[simp] theorem step_vmov_flags (k : VMovKind) (d s' : XmmReg) (h : Live s) :
    (step ⟨.vmov k d s', len⟩ s).flags = s.flags := by
  rw [step_vmov k d s' h]

/-! ### ⭐⭐⭐ MOVD / MOVQ across the register files — P2 vector wave, batch 5 -/

/-- ⭐⭐ WRITING AN XMM REGISTER FROM A GPR **CLEARS** THE BITS ABOVE THE WRITTEN
WIDTH.  `movd %ecx,%xmm0` leaves bits 127:32 zero; it does not merge.

⛔ AND THIS THEOREM IS THE ONLY THING IN THE REPOSITORY THAT CHECKS IT, BECAUSE
THE ORACLE IS WRONG HERE.  ACL2 x86isa merges — measured, 81 of 86 and 78 of 86
unexplained `spec` disagreements on the two into-XMM vectors, which is why those
vectors are not in the table (D93).

⚠️ It is NOT this model's word against x86isa's. **K's semantics, vendored and
public, give `movd r32 -> xmm` as `concatenateMInt(mi(96, 0), …)`** — ninety-six
zero bits and then the datum — and `movq r64 -> xmm` as `mi(64, 0)` the same way;
SDM Vol. 2B says `DEST[127:32] <- 0`. Two independent public models and the manual
agree with this model. -/
theorem vmovg_to_xmm_zeroes_upper (sz : Size) (x : XmmReg) (r : GPR) (h : Live s) :
    (step ⟨.vmovg true sz x r, len⟩ s).getXmm x = (s.getReg sz r).setWidth 128 := by
  simp [step, h, Cpu.setXmm, Cpu.setRip, Cpu.getXmm, Op.lockIllegal, Op.anyLocked,
        Op.lockable]

/-- ⭐ `movq %xmm1,%xmm0` moves the low quadword and ZEROES the upper one — it is
not `movdqa` at a narrower width.  ⭐ x86isa gets THIS one right, so it is
differentially validated as well as proved; the defect is directional. -/
theorem vmovq_zeroes_upper (d s' : XmmReg) (h : Live s) :
    (step ⟨.vmovq d s', len⟩ s).getXmm d = ((s.getXmm s').setWidth 64).setWidth 128 := by
  simp [step, h, Cpu.setXmm, Cpu.setRip, Cpu.getXmm, Op.lockIllegal, Op.anyLocked,
        Op.lockable]

/-! ### ⭐⭐⭐ MOVSS / MOVSD — the merge and the zero — P2 vector wave, batch 11 -/

/-- ⭐⭐ FROM A REGISTER, THE UPPER BITS ARE **PRESERVED**.

This is the only XMM write in this model that keeps any of its destination.
`vmov` fills all 128 bits, `vbin` computes all 128, and `vmovg`/`vmovq` CLEAR
what they do not write — so "the upper bits survive" is the claim most likely to
be written wrong by analogy with the five forms that came before it, and it is
stated here rather than left to the differential.

⚠️ STATED AS AN EQUALITY ON THE HIGH BITS SPECIFICALLY, not as an equality on the
whole register, because the whole-register form is just `step`'s definition read
back and would hold for a model that merged the WRONG WAY round. `getLsbD` above
the lane must equal the DESTINATION's old bit — naming which operand survives. -/
theorem vmovs_preserves_upper (sz : Size) (d s' : XmmReg) (h : Live s)
    (i : Nat) (hi : sz.bits ≤ i) :
    ((step ⟨.vmovs sz d s', len⟩ s).getXmm d).getLsbD i = (s.getXmm d).getLsbD i := by
  have hn : sz.bits + (i - sz.bits) = i := Nat.add_sub_cancel' hi
  simp [step, h, Cpu.setXmm, Cpu.setRip, Cpu.getXmm, Cpu.stopped, Op.lockIllegal,
        Op.anyLocked, Op.lockable, hn, Nat.not_lt.mpr hi]
  -- ⚠️ THE INDEX ABOVE THE REGISTER is not a vacuous case to wave through: both
  -- sides are `false` there, and saying so is what lets the theorem be stated for
  -- EVERY `i` rather than only for `i < 128` — a hypothesis a caller would then
  -- have to carry.
  rcases Nat.lt_or_ge i 128 with h1 | h1
  · simp [h1]
  · simp [Nat.not_lt.mpr h1, BitVec.getLsbD_of_ge _ _ h1]

/-- ⭐ AND THE LOW LANE COMES FROM THE SOURCE — the other half, without which the
theorem above is satisfied by an instruction that does nothing at all. -/
theorem vmovs_low_from_src (sz : Size) (d s' : XmmReg) (h : Live s)
    (i : Nat) (hi : i < sz.bits) :
    ((step ⟨.vmovs sz d s', len⟩ s).getXmm d).getLsbD i = (s.getXmm s').getLsbD i := by
  have h128 : i < 128 := by cases sz <;> simp [Size.bits] at hi <;> omega
  simp [step, h, Cpu.setXmm, Cpu.setRip, Cpu.getXmm, Cpu.stopped, Op.lockIllegal,
        Op.anyLocked, Op.lockable, hi, h128]

/-- ⭐⭐ FROM MEMORY, THE UPPER BITS ARE **CLEARED** — the same mnemonic, the
other rule.  ⛔ THIS AND THE THEOREM ABOVE ARE THE BATCH: two claims that cannot
both be true of one function, about instructions a disassembler prints with the
same name. -/
theorem vmovsld_zeroes_upper (sz : Size) (d : XmmReg) (ea : Ea) (h : Live s)
    (hl : ea.lock = false) :
    (step ⟨.vmovsld sz d ea, len⟩ s).getXmm d =
      ((s.readMem sz (ea.addr s (s.rip + BitVec.ofNat 64 len))).setWidth sz.bits).setWidth 128 := by
  simp [step, h, hl, Cpu.setXmm, Cpu.setRip, Cpu.getXmm, Op.lockIllegal, Op.anyLocked,
        Op.lockable]

/-- ⭐ D356 — `movd`/`movq` FROM MEMORY CLEAR bits 127:sz (SDM Vol. 2B MOVD/MOVQ), at both
widths. ⛔ x86isa MERGES at `66 0f 6e` (D93's defect through memory); this theorem is the
model's side of that declared divergence, stated so it cannot drift by a refactor. -/
theorem vmovgld_zeroes_upper (sz : Size) (d : XmmReg) (ea : Ea) (h : Live s)
    (hl : ea.lock = false) :
    (step ⟨.vmovgld sz d ea, len⟩ s).getXmm d =
      ((s.readMem sz (ea.addr s (s.rip + BitVec.ofNat 64 len))).setWidth sz.bits).setWidth 128 := by
  simp [step, h, hl, Cpu.setXmm, Cpu.setRip, Cpu.getXmm, Op.lockIllegal, Op.anyLocked,
        Op.lockable]

/-- ⭐ D356 — A `movd`/`movq` STORE WRITES NO GENERAL REGISTER and NO FLAG. -/
@[simp] theorem step_vmovgst_regs (sz : Size) (ea : Ea) (x : XmmReg) (h : Live s)
    (hl : ea.lock = false) :
    (step ⟨.vmovgst sz ea x, len⟩ s).regs = s.regs := by
  simp [step, h, hl, Cpu.setRip, Op.lockIllegal, Op.anyLocked, Op.lockable]

@[simp] theorem step_vmovgst_flags (sz : Size) (ea : Ea) (x : XmmReg) (h : Live s)
    (hl : ea.lock = false) :
    (step ⟨.vmovgst sz ea x, len⟩ s).flags = s.flags := by
  simp [step, h, hl, Cpu.setRip, Op.lockIllegal, Op.anyLocked, Op.lockable]

/-- ⭐ D357 — `withSimd` leaves the general registers alone whenever its continuation does, on both of
its branches (the #XM halt and the continuation). -/
theorem withSimd_regs (s : Cpu) (fl : BitVec 32) (k : Cpu → Cpu) (hk : ∀ t, (k t).regs = t.regs) :
    (s.withSimd fl k).regs = s.regs := by
  unfold Cpu.withSimd
  split
  · unfold Cpu.halt; split <;> rfl
  · exact hk _

/-- ⭐ D357 — A COMIS/UCOMIS WITH A MEMORY SOURCE WRITES NO GENERAL REGISTER. -/
@[simp] theorem step_vcomism_regs (o : Bool) (sz : Size) (d : XmmReg) (ea : Ea) (h : Live s)
    (hl : ea.lock = false) :
    (step ⟨.vcomism o sz d ea, len⟩ s).regs = s.regs := by
  simp [step, h, hl, Op.lockIllegal, Op.anyLocked, Op.lockable]
  exact withSimd_regs _ _ _ (fun _ => rfl)

/-- ⭐ NO SCALAR MOVE TOUCHES A FLAG (SDM Vol. 2B, MOVSS/MOVSD: "Flags Affected:
None"), stated for the same reason `step_vbin_flags` is. -/
@[simp] theorem step_vmovs_flags (sz : Size) (d s' : XmmReg) (h : Live s) :
    (step ⟨.vmovs sz d s', len⟩ s).flags = s.flags := by
  simp [step, h, Cpu.setXmm, Cpu.setRip, Op.lockIllegal, Op.anyLocked, Op.lockable]

/-- ⭐ AND NO SCALAR MOVE BETWEEN REGISTERS TOUCHES MEMORY OR A GPR — the frame. -/
@[simp] theorem step_vmovs_regs (sz : Size) (d s' : XmmReg) (h : Live s) :
    (step ⟨.vmovs sz d s', len⟩ s).regs = s.regs := by
  simp [step, h, Cpu.setXmm, Cpu.setRip, Op.lockIllegal, Op.anyLocked, Op.lockable]

@[simp] theorem step_vmovs_mem (sz : Size) (d s' : XmmReg) (h : Live s) :
    (step ⟨.vmovs sz d s', len⟩ s).mem = s.mem := by
  simp [step, h, Cpu.setXmm, Cpu.setRip, Op.lockIllegal, Op.anyLocked, Op.lockable]

/-! ### The vector MEMORY forms — P2 vector wave, batch 3 -/

/-- An ALIGNED vector load: XMM and RIP move, nothing else. -/
theorem step_vload_aligned (k : VMovKind) (d : XmmReg) (ea : Ea) (h : Live s)
    (hl : ea.lock = false)
    (hA : aligned16 (ea.addr s (s.rip + BitVec.ofNat 64 len)) = true) :
    step ⟨.vload k d ea, len⟩ s =
      { s with xmm := s.xmm.set d (s.readMem128 (ea.addr s (s.rip + BitVec.ofNat 64 len))),
               rip := s.rip + BitVec.ofNat 64 len } := by
  cases k <;> simp [step, h, hl, hA, Cpu.setXmm, Cpu.setRip, Op.lockIllegal,
                    Op.anyLocked, Op.lockable, VMovKind.aligned]

/-- ⭐⭐ AN UNALIGNED `movdqa` FAULTS — the rule that makes `aligned` mean
something, stated where a kernel can check it.

⛔ AND IT IS ASSERTED HERE **BECAUSE THE DIFFERENTIAL CANNOT ASSERT IT AT THIS
FORM.** Measured, by executing `movdqa 8(%rbx),%xmm0` at an unaligned address
with CR4.OSFXSR set: the oracle EXECUTES it, at all 88 pre-states. A vector for
this form would therefore put a ONE-SIDED REFUSAL into every pre-state, which
`classify` correctly calls the `refusal` class and counts UNEXPLAINED — a red run
about a model that is right.

⛔⛔ **THIS PARAGRAPH USED TO SAY "ACL2 x86isa DOES NOT IMPLEMENT THE ALIGNMENT
CHECK", AND THAT SENTENCE IS FALSE ABOUT THE ORACLE** (P2 batch 14, D110). It is
true of `movdqa`, which is what was measured. x86isa implements the 16-byte #GP
in exactly one file of its tree — `logical.lisp`, the legacy `pand`/`por`/`pxor`
— and REFUSES `pand 8(%rbx),%xmm0` at all 88 pre-states in the same run in which
it executes this form and `psrlw` and `pshufd` at the same address. One exception
class (SDM Table 2-21, Type 4), three answers.
⇒ 🔑 **THE ORACLE'S ALIGNMENT BEHAVIOUR IS A PROPERTY OF THE FILE THAT IMPLEMENTS
THE INSTRUCTION, NOT OF THE INSTRUCTION'S CLASS** — so "the oracle does not check
alignment" is not a fact that generalises from one form, and the sentence that
generalised it was the one telling the next reader not to look.

⇒ This rule still has no second source AT THIS FORM: it rests on the SDM
(Vol. 2B, MOVDQA) and on this theorem, and TRUSTBASE.md says so in as many words.
⭐ But the CLASS now has a measured route to differential validation — `vbin` at a
memory operand, where the oracle does check — and that is a priced next batch
rather than a wish. D91, amended by D110. -/
theorem vload_unaligned_faults (k : VMovKind) (d : XmmReg) (ea : Ea) (h : Live s)
    (hl : ea.lock = false) (hk : k.aligned = true)
    (hU : aligned16 (ea.addr s (s.rip + BitVec.ofNat 64 len)) = false) :
    (step ⟨.vload k d ea, len⟩ s).stopped = true := by
  simp [step, h, hl, hU, hk, Cpu.halt, Cpu.stopped, Op.lockIllegal, Op.anyLocked,
        Op.lockable]

theorem vstore_unaligned_faults (k : VMovKind) (r : XmmReg) (ea : Ea) (h : Live s)
    (hl : ea.lock = false) (hk : k.aligned = true)
    (hU : aligned16 (ea.addr s (s.rip + BitVec.ofNat 64 len)) = false) :
    (step ⟨.vstore k ea r, len⟩ s).stopped = true := by
  simp [step, h, hl, hU, hk, Cpu.halt, Cpu.stopped, Op.lockIllegal, Op.anyLocked,
        Op.lockable]

/-- ⭐ AND `movdqu` DOES NOT FAULT AT THE SAME ADDRESS — the other half of the
claim, and the one that says `aligned` is doing the discriminating rather than
the address being rejected by something else. -/
theorem vload_unaligned_movdqu_runs (k : VMovKind) (d : XmmReg) (ea : Ea) (h : Live s)
    (hl : ea.lock = false) (hk : k.aligned = false) :
    (step ⟨.vload k d ea, len⟩ s).stopped = false := by
  simp [step, h, hl, hk, Cpu.setXmm, Cpu.setRip, Cpu.stopped, Op.lockIllegal,
        Op.anyLocked, Op.lockable]

/-- ⭐ AND NO PACKED FORM TOUCHES A GENERAL-PURPOSE REGISTER OR MEMORY — the
frame, stated in the direction a downstream proof needs it. -/
@[simp] theorem step_vbin_regs (k : VBinKind) (d s' : XmmReg) (h : Live s) :
    (step ⟨.vbin k d s', len⟩ s).regs = s.regs := by
  by_cases hc : (vbinFlags k (s.getXmm d) (s.getXmm s') &&& ~~~(s.mxcsr >>> 7) &&& 63#32) = 0#32
    <;> simp [step, h, hc, Cpu.withSimd, Cpu.halt, Cpu.setXmm, Cpu.setRip]

@[simp] theorem step_vbin_mem (k : VBinKind) (d s' : XmmReg) (h : Live s) :
    (step ⟨.vbin k d s', len⟩ s).mem = s.mem := by
  by_cases hc : (vbinFlags k (s.getXmm d) (s.getXmm s') &&& ~~~(s.mxcsr >>> 7) &&& 63#32) = 0#32
    <;> simp [step, h, hc, Cpu.withSimd, Cpu.halt, Cpu.setXmm, Cpu.setRip]

@[simp] theorem step_mov_flags (sz : Size) (r r' : GPR) (h : Live s) :
    (step ⟨.mov sz (.reg r) (.reg r'), len⟩ s).flags = s.flags := by
  rw [step_mov_reg_reg sz r r' h]

@[simp] theorem step_lea_flags (sz : Size) (r : GPR) (ea : Ea) (h : Live s)
    (hl : ea.lock = false) :
    (step ⟨.lea sz r ea, len⟩ s).flags = s.flags := by
  rw [step_lea sz r ea h hl]

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

/-! ### ⭐⭐ S1 (desk `PE`): MOVZX/MOVSX AT A **MEMORY** SOURCE, WHICH THE ROUTINE ACTUALLY USES

`step_movx` above is stated for a REGISTER source only (`.reg r'`), and v1 §1.6 named that as the
first missing piece of the CRC-32 proof's interface: the routine's table walk begins
`movzbl (%rsi,%rcx), %ecx` — a BYTE LOAD, extended, into the index. Without this equation a proof
of that instruction has to unfold `step` itself, which is exactly what the proof interface exists
to stop.

⚠️ THE ADDRESS CARRIES `nextRip`, AND THAT IS NOT DECORATION: `Ea.addr` reads it for a RIP-relative
operand (`X86/Semantics.lean:52`), so the effect of a load genuinely depends on the instruction's
own length. Stating it with a bare `ea.addr s s.rip` would be false for every `ripRel` source and
would typecheck.

⛔⛔ AND `ea.lock = false` IS A REAL PRECONDITION, NOT BOILERPLATE — THE FIRST DRAFT OMITTED IT AND
WAS FALSE. `Op.lockIllegal` is `anyLocked && !lockable`, and `movx`'s destination is a REGISTER, so
`movx` is not on the SDM's lockable list: a `lock` prefix on this form is #UD and `step` halts.
Without the hypothesis the goal that survives is exactly

    ⊢ ea.lock = true → s.halt (MsErr.byDesign "lock prefix on a form the SDM does not permit it on
      (#UD)") = { regs := … }

⇒ 🔑 ***THE OMISSION IS INVISIBLE IN THE STATEMENT AND LOUD IN THE PROOF*** — the equation reads
perfectly well without it, and only elaboration knows the guard is there. It is the same shape as
`step_ret_taken`'s `canonical [rsp]` side condition, which v1 §1.6 records for the same reason:
*without it the theorem is FALSE*. This is red-first evidence obtained the honest way — the arm
failed before the hypothesis existed, not after a mutation.
-/

/-- MOVZX / MOVSX / MOVSXD from MEMORY: the source is read at `ssz` from the effective address,
extended, and written at `dsz`. -/
theorem step_movx_memsrc (k : MovxKind) (dsz ssz : Size) (r : GPR) (ea : Ea) (h : Live s)
    (hlk : ea.lock = false) :
    step ⟨.movx k dsz ssz r (.mem ea), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView dsz (s.regs.get r)
                  (match k with
                   | .zero => Value.zext ssz (s.readMem ssz (ea.addr s (s.rip + BitVec.ofNat 64 len)))
                   | .sign => Value.sext ssz (s.readMem ssz (ea.addr s (s.rip + BitVec.ofNat 64 len))))),
        rip := s.rip + BitVec.ofNat 64 len } := by
  cases k <;> simp [step, h, hlk, Cpu.setReg, Cpu.setRip, Cpu.readOperand, Cpu.getReg,
    Operand.locked]

/-- …and its FRAME: a load writes no flag. -/
@[simp] theorem step_movx_memsrc_flags (k : MovxKind) (dsz ssz : Size) (r : GPR) (ea : Ea)
    (h : Live s) (hlk : ea.lock = false) :
    (step ⟨.movx k dsz ssz r (.mem ea), len⟩ s).flags = s.flags := by
  rw [step_movx_memsrc k dsz ssz r ea h hlk]

/-- …draws no oracle bit. -/
@[simp] theorem step_movx_memsrc_oracle (k : MovxKind) (dsz ssz : Size) (r : GPR) (ea : Ea)
    (h : Live s) (hlk : ea.lock = false) :
    (step ⟨.movx k dsz ssz r (.mem ea), len⟩ s).oracle = s.oracle := by
  rw [step_movx_memsrc k dsz ssz r ea h hlk]

/-- …and, being a LOAD, leaves memory entirely alone.  This is the half the frame pack needs and
the half a reader is most likely to assume rather than check. -/
@[simp] theorem step_movx_memsrc_mem (k : MovxKind) (dsz ssz : Size) (r : GPR) (ea : Ea)
    (h : Live s) (hlk : ea.lock = false) :
    (step ⟨.movx k dsz ssz r (.mem ea), len⟩ s).mem = s.mem := by
  rw [step_movx_memsrc k dsz ssz r ea h hlk]

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

/-- ⭐⭐ P2 ITEM 2 REPLACED A REFUSAL THEOREM WITH A BEHAVIOUR ONE, and the
replacement is the batch's whole claim about `xchg`.

This declaration used to read `step_xchg_mem_refuses` and assert that `xchg` at
memory sets `ms` and changes nothing else — D25's decline, stated so that a
refusal could not quietly half-execute.  The decline was about ATOMICITY, and
`Ea.lock` is the vocabulary it lacked, so the form now EXECUTES: it swaps, and
the atomicity is recorded rather than verified (`TRUSTBASE.md`).

⛔ THE OLD THEOREM IS DELETED RATHER THAN KEPT WITH A HYPOTHESIS, because there
is no state left in which it holds — and a refusal theorem that can no longer
fire is exactly the kind of green that describes a model nobody runs. -/
theorem step_xchg_mem_reg (sz : Size) (ea : Ea) (r : GPR) (h : Live s) :
    step ⟨.xchg sz (.mem ea) (.reg r), len⟩ s =
      (((s.writeOperand sz (s.rip + BitVec.ofNat 64 len) (.mem ea) (s.getReg sz r)).writeOperand
          sz (s.rip + BitVec.ofNat 64 len) (.reg r)
          (s.readOperand sz (s.rip + BitVec.ofNat 64 len) (.mem ea))).setRip
        (s.rip + BitVec.ofNat 64 len)) := by
  simp [step, h, Cpu.getReg, Operand.isMem, Operand.isImm, wellFormed2]

@[simp] theorem step_bswap_flags (sz : Size) (r : GPR) (h : Live s) :
    (step ⟨.bswap sz r, len⟩ s).flags = s.flags := by
  cases sz <;> simp [step, h, Cpu.setReg, Cpu.setRip, Cpu.halt]

/-! ## P1 BATCH 10 — the loop group and the flag-control singles -/

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
theorem step_nop (o : Option Operand) (h : Live s)
    (hl : (o.map Operand.locked).getD false = false) :
    step ⟨.nop o, len⟩ s = { s with rip := s.rip + BitVec.ofNat 64 len } := by
  cases o with
  | none => simp [step, h, Cpu.setRip]
  | some x => cases x <;> simp_all [step, h, Cpu.setRip]

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

@[simp] theorem step_nop_flags (o : Option Operand) (h : Live s)
    (hl : (o.map Operand.locked).getD false = false) :
    (step ⟨.nop o, len⟩ s).flags = s.flags := by
  cases o with
  | none => simp [step, h, Cpu.setRip]
  | some x => cases x <;> simp_all [step, h, Cpu.setRip]

/-- V8a (D347): ENDBR64 is a NOP on this model's state — the SDM's "This opcode is a NOP when CET indirect
branch tracking is not enabled" applied to a model that carries no CET state.  Only RIP moves. -/
theorem step_endbr64 (h : Live s) :
    step ⟨.endbr64, len⟩ s = { s with rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.setRip]

@[simp] theorem step_endbr64_flags (h : Live s) :
    (step ⟨.endbr64, len⟩ s).flags = s.flags := by
  simp [step, h, Cpu.setRip]

/-! ## P1 BATCH 14 — the bit-counting group

⭐ THE THEOREMS THAT EARN THEIR KEEP HERE ARE THE ONES ABOUT THE THREE ZF RULES.
The group's results are ordinary computations and a differential run checks them
against the oracle case by case; what a run over a fixed vector table CANNOT
check is that ZF reads the SOURCE for `bsf`/`bsr`/`popcnt` and the DESTINATION
for `lzcnt`/`tzcnt`, because those two questions have the same answer for every
source except the ones where the count comes out zero.  Stated as theorems they
are claims about ALL states. -/

section BitCnt
variable {sz : Size} {dst : GPR} {src : Operand}

/-! ### The shared BSF/BSR body, framed once

`bitScanStep` branches on the source, and BOTH branches write the destination
and RIP and touch nothing else.  Framing it here once means the six `step`
theorems below never have to see that branch. -/

@[simp] theorem bitScanStep_mem (rev : Bool) (a : Val) (nr : BitVec 64) :
    (bitScanStep rev sz dst a nr s).mem = s.mem := by
  -- ⭐ P2 ITEM 1: `simp` with the FRAME LEMMAS, not `rfl` over the record.  See
  -- the note on `undefVal_regs` in `X86/State.lean`: unfolding and closing by
  -- `rfl` made this proof's cost scale with the number of fields in `Cpu`, and
  -- two new fields blew the heartbeat limit on it.
  simp only [bitScanStep, Cpu.setFlags]
  split <;> simp

@[simp] theorem bitScanStep_rip (rev : Bool) (a : Val) (nr : BitVec 64) :
    (bitScanStep rev sz dst a nr s).rip = nr := by
  -- ⭐ P2 ITEM 1: `simp` with the FRAME LEMMAS, not `rfl` over the record.  See
  -- the note on `undefVal_regs` in `X86/State.lean`: unfolding and closing by
  -- `rfl` made this proof's cost scale with the number of fields in `Cpu`, and
  -- two new fields blew the heartbeat limit on it.
  simp only [bitScanStep, Cpu.setFlags]
  split <;> simp

/-- ⭐ ZF IS SET FROM THE SOURCE IN BOTH BRANCHES — including the branch where
the DESTINATION is undefined.  That is the whole of what `bsf`/`bsr` promise
about their flags at a zero source, and it holds whatever the oracle says. -/
@[simp] theorem bitScanStep_zf (rev : Bool) (a : Val) (nr : BitVec 64) :
    (bitScanStep rev sz dst a nr s).flags.zf = Value.isZero sz a := by
  simp only [bitScanStep, Cpu.setFlags, Flags.bitScan]
  split <;> simp [Flags.bitScan]

/-! ### The three ZF rules, which are three different questions -/

/-- BSF sets ZF from the SOURCE (SDM Vol. 2A: "ZF ← (SRC = 0)"). -/
theorem step_bsf_zf (h : Live s) (he : bitcntEncodable .bsf sz = true)
    (hl : src.locked = false) :
    (step ⟨.bitcnt .bsf sz dst src, len⟩ s).flags.zf =
      Value.isZero sz (s.readOperand sz (s.rip + BitVec.ofNat 64 len) src) := by
  cases src <;> simp_all only [Operand.locked] <;>
  simp only [step, Cpu.stopped, Op.lockIllegal, Op.eas, opOperands, Op.lockable,
    List.filterMap_cons, List.filterMap_nil, List.any_nil, List.any_cons, List.append_nil,
    Bool.or_false, Bool.false_and, Bool.and_false, Bool.not_false,
    Bool.false_eq_true, if_false, h, Option.isSome_none, Bool.false_eq_true, if_false, he,
    Bool.not_true, if_false, bitScanStep_zf] <;> simp_all

theorem step_bsr_zf (h : Live s) (he : bitcntEncodable .bsr sz = true)
    (hl : src.locked = false) :
    (step ⟨.bitcnt .bsr sz dst src, len⟩ s).flags.zf =
      Value.isZero sz (s.readOperand sz (s.rip + BitVec.ofNat 64 len) src) := by
  cases src <;> simp_all only [Operand.locked] <;>
  simp only [step, Cpu.stopped, Op.lockIllegal, Op.eas, opOperands, Op.lockable,
    List.filterMap_cons, List.filterMap_nil, List.any_nil, List.any_cons, List.append_nil,
    Bool.or_false, Bool.false_and, Bool.and_false, Bool.not_false,
    Bool.false_eq_true, if_false, h, Option.isSome_none, Bool.false_eq_true, if_false, he,
    Bool.not_true, if_false, bitScanStep_zf] <;> simp_all

/-- ⭐ LZCNT AND TZCNT SET ZF FROM THE DESTINATION, WHICH IS A DIFFERENT
QUESTION.  `lzcntq` of a source whose top bit is set writes 0 and sets ZF though
the source is not zero; a model that copied `bsr`'s rule is wrong on exactly
those states, and this is the theorem that says so about all of them. -/
theorem step_lzcnt_zf (h : Live s) (he : bitcntEncodable .lzcnt sz = true)
    (hl : src.locked = false) :
    (step ⟨.bitcnt .lzcnt sz dst src, len⟩ s).flags.zf =
      Value.isZero sz
        (BitVec.ofNat 64
          (Value.clz sz (s.readOperand sz (s.rip + BitVec.ofNat 64 len) src))) := by
  cases src <;> simp_all [step, h, he, Flags.bitCount]

theorem step_tzcnt_zf (h : Live s) (he : bitcntEncodable .tzcnt sz = true)
    (hl : src.locked = false) :
    (step ⟨.bitcnt .tzcnt sz dst src, len⟩ s).flags.zf =
      Value.isZero sz
        (BitVec.ofNat 64
          (Value.ctz sz (s.readOperand sz (s.rip + BitVec.ofNat 64 len) src))) := by
  cases src <;> simp_all [step, h, he, Flags.bitCount]

/-- And LZCNT sets CF when the SOURCE is zero. -/
theorem step_lzcnt_cf (h : Live s) (he : bitcntEncodable .lzcnt sz = true)
    (hl : src.locked = false) :
    (step ⟨.bitcnt .lzcnt sz dst src, len⟩ s).flags.cf =
      Value.isZero sz (s.readOperand sz (s.rip + BitVec.ofNat 64 len) src) := by
  cases src <;> simp_all [step, h, he, Flags.bitCount]

/-- ⛔ AND BLSI SETS CF THE OTHER WAY UP — set when the source is NON-zero
(SDM Vol. 2A, BLSI: "IF SRC = 0 THEN CF ← 0 ELSE CF ← 1").  Two instructions in
one batch whose CF asks the same question and answers it oppositely; a model
that shared one rule between them is wrong on every state for one of the two. -/
theorem step_blsi_cf (h : Live s) (he : bitcntEncodable .blsi sz = true)
    (hl : src.locked = false) :
    (step ⟨.bitcnt .blsi sz dst src, len⟩ s).flags.cf =
      !(Value.isZero sz (s.readOperand sz (s.rip + BitVec.ofNat 64 len) src)) := by
  cases src <;> simp_all [step, h, he, Flags.blsi]

/-- POPCNT clears OF, SF, AF, CF and PF unconditionally — the one member of the
group that leaves nothing undefined. -/
theorem step_popcnt_clears (h : Live s) (he : bitcntEncodable .popcnt sz = true)
    (hl : src.locked = false) :
    (step ⟨.bitcnt .popcnt sz dst src, len⟩ s).flags.cf = false
    ∧ (step ⟨.bitcnt .popcnt sz dst src, len⟩ s).flags.of = false
    ∧ (step ⟨.bitcnt .popcnt sz dst src, len⟩ s).flags.sf = false
    ∧ (step ⟨.bitcnt .popcnt sz dst src, len⟩ s).flags.af = false
    ∧ (step ⟨.bitcnt .popcnt sz dst src, len⟩ s).flags.pf = false := by
  cases src <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [step, h, he, Flags.popcnt]

/-- ⭐ NONE OF THE SIX WRITES MEMORY.  Their memory operand is always the SOURCE,
which is what the coverage table's shapes column claims by NOT spelling any of
them `m(...)` — and `isMemDestVector`'s `.bitcnt` case says the same thing one
layer down.  Three statements of one fact, and this is the one with a proof. -/
@[simp] theorem step_bitcnt_mem (k : BitCntKind) (h : Live s) :
    (step ⟨.bitcnt k sz dst src, len⟩ s).mem = s.mem := by
  simp only [step, Cpu.stopped, h, Option.isSome_none, Bool.false_eq_true, if_false]
  -- ⭐ P2 ITEM 2: the lock guard's HALT branch preserves memory too, so this
  -- claim needs no hypothesis — only a case for the branch.
  split
  · cases hm : s.ms <;> simp [Cpu.halt, hm]
  · split
    · simp [Cpu.halt, h]
    · cases k <;> simp

/-- And a form the model DECLINES changes nothing but `ms` — `blsi` at 16 bits
and any of the six at 8 bits have no encoding, and refusing is not the same as
answering zero. -/
theorem step_bitcnt_declined (k : BitCntKind) (h : Live s)
    (he : bitcntEncodable k sz = false) :
    (step ⟨.bitcnt k sz dst src, len⟩ s).regs = s.regs
    ∧ (step ⟨.bitcnt k sz dst src, len⟩ s).rip = s.rip
    ∧ (step ⟨.bitcnt k sz dst src, len⟩ s).flags = s.flags := by
  refine ⟨?_, ?_, ?_⟩ <;> cases src <;> simp [step, h, he, Cpu.halt] <;> split <;> simp

end BitCnt

/-! ## P1 BATCH 15 — the string group

⭐ WHAT THESE CAN AND CANNOT SAY.  A characterization theorem states that `step`
equals a record update; it cannot state that the update is the RIGHT one.  For
this group the differential run against x86isa is what checks the VALUES, and
what is worth proving here is the FRAME — which components each form touches —
because the frame is where the group's five members actually differ from one
another, and where a copy-and-edit mistake between them would land. -/
section StringOps
variable {sz : Size} {len : Nat} {s : Cpu}

/-- ⭐ MOVS, STOS AND LODS WRITE NO FLAG.  "Flags Affected: None" for all three,
and this is the statement that separates them from `cmps`/`scas`, which are the
same shape of instruction and write six.  ⚠️ The three are proved TOGETHER
rather than one at a time on purpose: the risk in this group is not that one
member is wrong in isolation, it is that one member was written by editing
another and kept a line it should have dropped. -/
@[simp] theorem step_strop_movs_flags (h : Live s) :
    (step ⟨.strop .movs sz, len⟩ s).flags = s.flags := by
  simp [step, stringIter, Cpu.stopped, h]

@[simp] theorem step_strop_stos_flags (h : Live s) :
    (step ⟨.strop .stos sz, len⟩ s).flags = s.flags := by
  simp [step, stringIter, Cpu.stopped, h]

@[simp] theorem step_strop_lods_flags (h : Live s) :
    (step ⟨.strop .lods sz, len⟩ s).flags = s.flags := by
  simp [step, stringIter, Cpu.stopped, h]

/-- ⭐ CMPS AND SCAS WRITE NO MEMORY.  They are the two members whose coverage
row CLAIMS a memory destination (`m,m` and `m,acc`) while writing nothing — the
`cmp`/`test` case — so this theorem is the proof of the half of that claim a
reader is most likely to doubt. -/
@[simp] theorem step_strop_cmps_mem (h : Live s) :
    (step ⟨.strop .cmps sz, len⟩ s).mem = s.mem := by
  simp [step, stringIter, Cpu.stopped, h]

@[simp] theorem step_strop_scas_mem (h : Live s) :
    (step ⟨.strop .scas sz, len⟩ s).mem = s.mem := by
  simp [step, stringIter, Cpu.stopped, h]

/-- ⭐ LODS DOES NOT TOUCH RDI, AND STOS AND SCAS DO NOT TOUCH RSI.  Which
pointer each form advances is the single most confusable fact in the group —
the names differ by one letter — and `wrongScasUsesRsi` is the planted defect
that says the differential can see it.  This says the model has it right by
construction rather than by agreement. -/
theorem step_strop_lods_rdi (h : Live s) :
    (step ⟨.strop .lods sz, len⟩ s).regs.get .rdi = s.regs.get .rdi := by
  simp [step, stringIter, Cpu.stopped, h, Cpu.setReg, Cpu.setRip, Regs.get_set_ne]

theorem step_strop_stos_rsi (h : Live s) :
    (step ⟨.strop .stos sz, len⟩ s).regs.get .rsi = s.regs.get .rsi := by
  simp [step, stringIter, Cpu.stopped, h, Cpu.setReg, Cpu.setRip, Regs.get_set_ne]

theorem step_strop_scas_rsi (h : Live s) :
    (step ⟨.strop .scas sz, len⟩ s).regs.get .rsi = s.regs.get .rsi := by
  simp [step, stringIter, Cpu.stopped, h, Cpu.setReg, Cpu.setRip, Regs.get_set_ne]

end StringOps

/-! ### P1 BATCH 16 — the repeat prefixes -/
section RepStringOps
variable {r : RepPrefix} {k : StringOp} {sz : Size} {len : Nat} {s : Cpu}

/-- A prefix this model does not claim HALTS rather than guessing.  `repApplies`
is a roster partition and every pair it rejects assembles, so the decline has to
be visible in the semantics and not only in the coverage table. -/
theorem step_repstrop_declined (h : Live s) (hp : repApplies r k = false) :
    (step ⟨.repstrop r k sz, len⟩ s).stopped = true := by
  simp [step, Cpu.stopped, Cpu.halt, h, hp] at *

/-- ⭐ RCX = 0 ON ENTRY: THE INSTRUCTION IS A FALL-THROUGH AND NOTHING ELSE.
No memory access, no flag write, no pointer move — and RCX itself is NOT
decremented, so it does not wrap to all-ones.  Stated over the WHOLE record
rather than field by field, because "changes nothing" is the claim and a
field-by-field version would be a list somebody has to keep complete. -/
theorem step_repstrop_rcx_zero (h : Live s) (hp : repApplies r k = true)
    (h0 : s.regs.get .rcx = 0) :
    step ⟨.repstrop r k sz, len⟩ s
      = { s with rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, Cpu.stopped, Cpu.setRip, h, hp, h0]

/-- ⭐⭐ THE BATCH'S FINDING, AS A THEOREM: `rep` ON A NON-ZERO COUNT LEAVES RIP
WHERE IT FOUND IT — including on the step that drives the count to zero.

`RepPrefix.terminates .rep` is constantly `false`, so this needs no hypothesis
about the count's VALUE beyond its being non-zero: `rep movs` with RCX = 1 ends
with RCX = 0 and RIP still at the instruction, and it is the NEXT step, finding
the count already zero, that falls through.  A model that advanced on the
decrement reaching zero contradicts this theorem at exactly one value of RCX,
and `wrongRepAdvanceOnCountZero` is that model. -/
theorem step_rep_rip_unmoved (h : Live s) (hp : repApplies .rep k = true)
    (h0 : ¬ (s.regs.get .rcx = 0)) :
    (step ⟨.repstrop .rep k sz, len⟩ s).rip = s.rip := by
  simp only [step, Cpu.stopped, h, hp, if_false, Bool.not_true, if_neg h0,
    beq_iff_eq, Bool.false_eq_true, RepPrefix.terminates, Cpu.setRip, Cpu.setReg]
  simp

/-- The count is decremented by one, as a FULL 64-BIT write.  `rep movsb`
decrements the whole of RCX, not its low byte — the pointer-width defect of
batch 15 (D43) in the one register batch 15 did not update. -/
theorem step_repstrop_decrements_rcx (h : Live s) (hp : repApplies r k = true)
    (h0 : ¬ (s.regs.get .rcx = 0)) :
    (step ⟨.repstrop r k sz, len⟩ s).regs.get .rcx = s.regs.get .rcx - 1 := by
  -- ⚠️ ALL FIVE KINDS, not the three that move two pointers.  A first draft
  -- carried `k ≠ .lods` and `k ≠ .scas` hypotheses that nothing in the
  -- statement needs — `stringIter` never writes RCX for any kind — and
  -- `simp_all` discharged those two cases FROM THE CONTRADICTION rather than
  -- from the semantics.  The theorem was green and silent about two fifths of
  -- the group it names.
  cases k <;> simp_all [step, Cpu.stopped, Cpu.setRip, Cpu.setReg, stringIter,
    Regs.get_set_ne]

/-- ⭐⭐ THE PREFIX CHANGES LOOP CONTROL AND NOTHING ELSE — the theorem that
audits the `stringIter` refactor rather than trusting it.

On a non-zero count, the prefixed form leaves the SAME memory and the SAME flags
as the unprefixed one.  If the shared iteration had been copied instead of
factored and the two copies drifted, this is the statement that would fail; a
script that diffed the two bodies would not have been evidence anybody could
re-run. -/
theorem step_repstrop_iterates_like_strop (h : Live s) (hp : repApplies r k = true)
    (h0 : ¬ (s.regs.get .rcx = 0)) :
    (step ⟨.repstrop r k sz, len⟩ s).mem = (step ⟨.strop k sz, len⟩ s).mem
  ∧ (step ⟨.repstrop r k sz, len⟩ s).flags = (step ⟨.strop k sz, len⟩ s).flags := by
  constructor <;>
    (simp only [step, Cpu.stopped, h, hp, if_false, Bool.not_true, if_neg h0,
      beq_iff_eq, Bool.false_eq_true, Cpu.setRip, Cpu.setReg]; simp)

end RepStringOps

/-! ## P1 BATCH 17 — the multiply-divide group

⭐ THE STATEMENTS HERE ARE ABOUT THE FAULT AND THE FRAME, NOT ABOUT THE
ARITHMETIC.  A theorem saying `mul` computes the product would restate
`Value.mulPair`, which is the definition; what is worth holding is what the
definitions do NOT say — that a division's refusal is exactly the SDM's two
conditions, that a refusal writes nothing at all, and that the pair really is
`AH:AL` at one width and `RDX:RAX` at the other three.  Those are the claims a
plausible wrong model contradicts. -/

section MulDiv
variable {k : MulDivKind} {sz : Size} {src : Operand} {len : Nat} {s s' : Cpu}

/-- ⭐⭐ THE FAULT LAW: a `div` refuses EXACTLY when `Value.divPairU` has no
answer, and an `idiv` exactly when `Value.divPairS` has none.  Nothing else can
stop these forms.

⚠️ THIS IS THE THEOREM `wrongDivNoQuotientOverflow` CONTRADICTS, and it is
stated as an `↔` on purpose: an implication in either direction alone would be
satisfied by a model that refuses too often or too rarely, and this batch's
measurement says the too-often direction is the one nothing else would catch. -/
theorem step_div_refuses_iff (h : Live s) (hl : src.locked = false) :
    (step ⟨.muldiv .div sz src, len⟩ s).stopped = true
      ↔ Value.divPairU sz (s.mdHi sz) (s.getReg sz .rax)
          (s.readOperand sz (s.rip + BitVec.ofNat 64 len) src) = none := by
  -- ⭐ P2 ITEM 2: the lock guard is discharged FIRST, as a `have`, so the proof
  -- below is the one this theorem always had.  Rewriting the guard away before
  -- the case analysis keeps the two concerns separate.
  have hlk : (Op.muldiv .div sz src).lockIllegal = false := by
    cases src <;> simp_all [Operand.locked]
  simp only [step, Cpu.stopped, h, hlk, if_false, Bool.not_true]
  cases hd : Value.divPairU sz (s.mdHi sz) (s.getReg sz .rax)
      (s.readOperand sz (s.rip + BitVec.ofNat 64 len) src) <;> cases sz <;>
    simp_all [Cpu.halt, Cpu.setRip, Cpu.setFlags, Cpu.setMdPair, Cpu.setReg, Cpu.undefBit]

theorem step_idiv_refuses_iff (h : Live s) (hl : src.locked = false) :
    (step ⟨.muldiv .idiv sz src, len⟩ s).stopped = true
      ↔ Value.divPairS sz (s.mdHi sz) (s.getReg sz .rax)
          (s.readOperand sz (s.rip + BitVec.ofNat 64 len) src) = none := by
  -- ⭐ P2 ITEM 2: the lock guard is discharged FIRST, as a `have`, so the proof
  -- below is the one this theorem always had.  Rewriting the guard away before
  -- the case analysis keeps the two concerns separate.
  have hlk : (Op.muldiv .idiv sz src).lockIllegal = false := by
    cases src <;> simp_all [Operand.locked]
  simp only [step, Cpu.stopped, h, hlk, if_false, Bool.not_true]
  cases hd : Value.divPairS sz (s.mdHi sz) (s.getReg sz .rax)
      (s.readOperand sz (s.rip + BitVec.ofNat 64 len) src) <;> cases sz <;>
    simp_all [Cpu.halt, Cpu.setRip, Cpu.setFlags, Cpu.setMdPair, Cpu.setReg, Cpu.undefBit]

/-- ⭐⭐ A REFUSED DIVISION CHANGES NOTHING BUT `ms` — stated over the WHOLE
record, as batch 16's `step_repstrop_rcx_zero` is, because "writes nothing" is
the claim and a field-by-field version is a list somebody has to keep complete.

⚠️ IT IS ALSO THE PROPERTY THE DIFFERENTIAL RUN DEPENDS ON.  x86isa's post-state
on a #DE has RAX, RDX, RIP and the flags exactly as it found them — measured, in
the 656-case probe — so a model that faulted after committing a partial write
would disagree with the oracle in a field the comparator reads. -/
theorem step_div_refused_frame (h : Live s) (hl : src.locked = false)
    (hd : Value.divPairU sz (s.mdHi sz) (s.getReg sz .rax)
            (s.readOperand sz (s.rip + BitVec.ofNat 64 len) src) = none) :
    step ⟨.muldiv .div sz src, len⟩ s
      = { s with ms := some (.byDesign "div: #DE is the instruction's meaning at this divisor") } := by
  have hlk : ∀ k, (Op.muldiv k sz src).lockIllegal = false := by
    intro k; cases src <;> simp_all [Operand.locked]
  cases src <;> simp_all [step, Cpu.stopped, Cpu.halt, Live, Operand.locked]

theorem step_idiv_refused_frame (h : Live s) (hl : src.locked = false)
    (hd : Value.divPairS sz (s.mdHi sz) (s.getReg sz .rax)
            (s.readOperand sz (s.rip + BitVec.ofNat 64 len) src) = none) :
    step ⟨.muldiv .idiv sz src, len⟩ s
      = { s with ms := some (.byDesign "idiv: #DE is the instruction's meaning at this divisor") } := by
  have hlk : ∀ k, (Op.muldiv k sz src).lockIllegal = false := by
    intro k; cases src <;> simp_all [Operand.locked]
  cases src <;> simp_all [step, Cpu.stopped, Cpu.halt, Live, Operand.locked]

/-- ⭐ THE PAIR IS `AH:AL` AT `.b` AND LEAVES RDX ALONE — the claim
`wrongMulBytePairInRdx` contradicts, and the one sentence of the SDM's
destination table that a uniform implementation gets wrong. -/
theorem setMdPair_b_leaves_rdx (s : Cpu) (lo hi : Val) :
    (s.setMdPair .b lo hi).regs.get .rdx = s.regs.get .rdx := by
  simp [Cpu.setMdPair, Cpu.setReg, Regs.get_set_ne]

/-- …and at every other width the high half IS RDX, so the two halves of the
previous theorem's claim are both stated rather than one being left to a
reader. -/
theorem setMdPair_wide_writes_rdx (s : Cpu) (sz : Size) (lo hi : Val) (hs : sz ≠ .b) :
    (s.setMdPair sz lo hi).getReg sz .rdx
      = Value.trunc sz (Value.writeView sz (s.regs.get .rdx) hi) := by
  cases sz <;> simp_all [Cpu.setMdPair, Cpu.setReg, Cpu.getReg, Regs.get_set_ne]

/-- ⛔ IMUL's TWO- AND THREE-OPERAND FORMS DO NOT EXIST AT `.b`, and `step` says
so rather than answering for bytes no encoding can carry — the same statement
batch 14 makes about the bit-counting group's missing widths. -/
theorem step_imulr_b_refuses (h : Live s) (dst : GPR) (imm : Option Val) :
    (step ⟨.imulr .b dst src imm, len⟩ s).stopped = true := by
  have he : imulrEncodable .b = false := by decide
  -- ⭐ P2 ITEM 2: TRUE IN BOTH BRANCHES OF THE LOCK GUARD, and it needs no
  -- hypothesis for that reason — a locked operand halts too, with a different
  -- `ms`, and this theorem is about `stopped` rather than about the reason.
  cases src <;> simp [step, Cpu.stopped, h, he, Cpu.halt] <;> split <;> simp

/-- ⭐ THE THREE-OPERAND FORM DOES NOT READ ITS DESTINATION: overwriting the
destination register with an arbitrary value does not change the answer.

⚠️ THE PERTURBATION IS NAMED IN THE STATEMENT rather than left as "two states
that happen to agree elsewhere", so the theorem says what a reader would test by
hand.  It is exactly what `wrongImul3ReadsDest` breaks — and no single example
could show it, because that model agrees with this one wherever the destination
already holds the source. -/
theorem step_imul3_ignores_dest (h : Live s) (dst rs : GPR) (hne : dst ≠ rs)
    (im v : Val) (hsz : sz ≠ .b) :
    (step ⟨.imulr sz dst (.reg rs) (some im), len⟩ (s.setReg .q dst v)).getReg sz dst
      = (step ⟨.imulr sz dst (.reg rs) (some im), len⟩ s).getReg sz dst := by
  have he : imulrEncodable sz = true := by
    cases sz <;> first | exact absurd rfl hsz | decide
  have hl : Live (s.setReg .q dst v) := by simpa [Live, Cpu.setReg] using h
  cases sz <;> simp_all [step, Cpu.stopped, imulrEncodable, Cpu.setRip,
    Cpu.setFlags, Cpu.setReg, Cpu.getReg, Cpu.readOperand, Cpu.undefBit,
    Regs.get_set_ne _ _ _ _ hne, Value.trunc_writeView]
  <;> rw [Regs.get_set_ne _ _ _ _ hne]

end MulDiv

/-! ## P1 BATCH 18 — CMPXCHG, XADD and the double-precision shifts

⭐ THE FIRST THEOREM HERE IS A CORRECTION, NOT A CHARACTERIZATION.  The SDM's
CMPXCHG pseudo-code writes `DEST := TEMP` on the unequal branch; this model
wrote it, and eighty differential cases at `.d` said no.  `step_cmpxchg_unequal_
leaves_dest` is the repaired claim in the form a reader can check without running
anything: on the unequal branch the destination register keeps ALL SIXTY-FOUR of
its bits.  See docs/DECISIONS.md D53. -/
section Batch18
variable {sz : Size} {r rs : GPR} {len : Nat} {s : Cpu}

/-- ⛔⛔ D53, AS A THEOREM.  A `DEST := DEST` on a 32-bit register destination is
not the no-op it reads as — a 32-bit register write zero-extends — so "the model
leaves it alone" is a claim with observable content and belongs here rather than
in a comment. -/
theorem step_cmpxchg_unequal_leaves_dest (h : Live s) (hne : r ≠ .rax)
    (hu : Value.trunc sz (s.regs.get .rax) ≠ Value.trunc sz (s.regs.get r)) :
    (step ⟨.cmpxchg sz (.reg r) rs, len⟩ s).regs.get r = s.regs.get r := by
  simp [step, h, Cpu.getReg, Operand.isImm, if_neg hu,
    Regs.get_set_ne _ _ _ _ (Ne.symm hne)]

/-- …and the accumulator DOES move on that branch, so the theorem above is a
statement about which half of the SDM's else-branch is real rather than a claim
that the branch does nothing. -/
theorem step_cmpxchg_unequal_writes_acc (h : Live s) (hne : r ≠ .rax)
    (hu : Value.trunc sz (s.regs.get .rax) ≠ Value.trunc sz (s.regs.get r)) :
    (step ⟨.cmpxchg sz (.reg r) rs, len⟩ s).regs.get .rax
      = Value.writeView sz (s.regs.get .rax) (s.getReg sz r) := by
  simp [step, h, Cpu.getReg, Operand.isImm, if_neg hu]

/-- THE EQUAL BRANCH: the destination takes the SOURCE, and the accumulator is
left alone — the mirror image of the two above. -/
theorem step_cmpxchg_equal (h : Live s) (hne : r ≠ .rax)
    (he : Value.trunc sz (s.regs.get .rax) = Value.trunc sz (s.regs.get r)) :
    (step ⟨.cmpxchg sz (.reg r) rs, len⟩ s).regs
      = s.regs.set r (Value.writeView sz (s.regs.get r) (s.getReg sz rs)) := by
  simp [step, h, Cpu.getReg, Operand.isImm, if_pos he]

/-- ⭐ XADD WRITES BOTH OPERANDS, and the SOURCE takes the destination's ORIGINAL
value.  Stated as the whole register file so that "both" is visible rather than
split across two theorems that could each be true of a model that wrote one. -/
theorem step_xadd_reg_reg (h : Live s) :
    step ⟨.xadd sz (.reg r) rs, len⟩ s =
      (let a := s.getReg sz r
       let b := s.getReg sz rs
       let s1 := s.setFlags (Flags.add sz a b s.flags)
       let s2 := s1.setReg sz rs a
       { s2 with
         regs := s2.regs.set r (Value.writeView sz (s2.regs.get r)
           (Flags.addResult sz a b)),
         rip := s.rip + BitVec.ofNat 64 len }) := by
  simp [step, h, Cpu.getReg, Operand.isImm, Cpu.setFlags, Cpu.setReg, Cpu.setRip]

/-- ⛔ SHLD/SHRD HAVE NO 8-BIT ENCODING, and `step` says so rather than answering
for bytes no opcode can carry — batch 14's statement about the bit-counting
group's missing widths, and batch 17's about `imul`'s, in a third place. -/
theorem step_dshift_b_refuses (k : DShiftKind) (dst : Operand) (amt : ShiftAmt)
    (h : Live s) :
    (step ⟨.dshift k .b dst rs amt, len⟩ s).stopped = true := by
  have he : dshiftEncodable .b = false := by decide
  cases dst <;> simp [step, h, he, Cpu.halt] <;> split <;> simp

/-- ⛔⛔ D52, AS A THEOREM: the ONE combination this model declines to answer for,
stated as a refusal that changes nothing else.  A 16-bit memory destination with
a masked count above 16 would place an undefined value in MEMORY, and
`X86.undefinedLeaked` has no declaration channel for that.  ⚠️ The hypothesis is
on the masked count and not on the immediate, because CL reaches the same branch
in thirty-five of the harness's eighty-two pre-states. -/
theorem step_dshift_mem_undefined_refuses (k : DShiftKind) (ea : Ea) (c : BitVec 8)
    (h : Live s) (hc : 16 < Flags.shiftCount .w c) (hl : ea.lock = false) :
    step ⟨.dshift k .w (.mem ea) rs (.imm8 c), len⟩ s =
      { s with ms := some (.unimplemented
          "shld/shrd: an undefined RESULT in memory (16-bit operand, count > 16)") } := by
  have he : dshiftEncodable .w = true := by decide
  have hm : dshiftMemUndefined .w true (Flags.shiftCount .w c) = true := by
    simp [dshiftMemUndefined, Size.bits]; omega
  simp [step, h, he, hm, hl, Cpu.halt, Operand.isImm, Operand.isMem]

/-- ⭐⭐ A COUNT OF ZERO TOUCHES NO FLAG — AND STILL WRITES THE DESTINATION.  D54:
the SDM says "IF COUNT = 0 THEN no operation", and both public executable models
disagree with it, K's rule for this case carrying the comment `// Intel Bug`.
The write is invisible at `.b`, `.w` and `.q` and is a ZERO-EXTENSION at `.d`,
which is where fifty-one differential cases found it.

⚠️ THE STATEMENT IS ABOUT A REGISTER because that is where the write is
observable: `Value.writeView` is the whole content of the theorem, and at `.d` it
clears bits 63:32. -/
theorem step_dshift_zero_count (k : DShiftKind) (c : BitVec 8)
    (h : Live s) (hsz : sz ≠ .b) (hc : Flags.shiftCount sz c = 0) :
    step ⟨.dshift k sz (.reg r) rs (.imm8 c), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView sz (s.regs.get r) (s.getReg sz r)),
        rip := s.rip + BitVec.ofNat 64 len } := by
  have he : dshiftEncodable sz = true := by
    cases sz <;> first | exact absurd rfl hsz | decide
  simp_all [step, dshiftEncodable, dshiftMemUndefined, Cpu.getReg, Operand.isImm,
    Operand.isMem]

/-- ⭐ AT A COUNT EQUAL TO THE OPERAND SIZE THE ANSWER IS THE SOURCE, and the
count can only equal the operand size at `.w`, where a five-bit mask allows 16.
It is the boundary the vector `shld_ri16_w` exists for: one below it is an
ordinary shift, one above it the SDM stops defining the result. -/
theorem dshiftRes_shld_full_width (a b : Val) :
    Flags.dshiftRes .shld .w a b 16 = Value.trunc .w b := by
  simp only [Flags.dshiftRes, Size.bits, Nat.sub_self, BitVec.ushiftRight_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [Value.trunc, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  by_cases hi : i < 16
  · have hlo : i < (Size.w).bits := by simpa [Size.bits] using hi
    simp [hi, Size.mask_getLsbD_low .w i hlo]
  · have hhi : (Size.w).bits ≤ i := by simp [Size.bits]; omega
    simp [Size.mask_getLsbD_high .w i hhi]

end Batch18

/-! ## P2 VECTOR WAVE, BATCH 14 — the permute group, and the alignment rule it
shares with the packed shifts.

⛔ **THE THREE THEOREMS BELOW ARE THE ONLY GATE ON A RULE NO VECTOR CAN REACH.**
The differential cannot test an unaligned `pshufd`, `pshuflw`, `pshufhw` or
`psrlw`: the oracle executes all of them (measured, 88 of 88, in the same run in
which it refuses `pand` at the identical address). So the `#GP` branch these
forms carry is checked by the kernel here or by nothing at all — which is
precisely the shape D91 gave `vload`, arriving a second time at a group whose
prose had claimed the opposite. -/
namespace Batch14

variable {s : Cpu} {len : Nat}

/-- ⭐⭐ AN UNALIGNED PERMUTE FAULTS. -/
theorem vshufm_unaligned_faults (k : VShufKind) (d : XmmReg) (ea : Ea) (sel : BitVec 8)
    (h : Live s) (hl : ea.lock = false)
    (hU : aligned16 (ea.addr s (s.rip + BitVec.ofNat 64 len)) = false) :
    (step ⟨.vshufm k d ea sel, len⟩ s).stopped = true := by
  simp [step, h, hl, hU, Cpu.halt, Cpu.stopped, Op.lockIllegal, Op.anyLocked,
        Op.lockable]

/-- ⭐ AND IT RUNS AT AN ALIGNED ONE — the other half, without which "it faults"
is indistinguishable from "it always faults". -/
theorem vshufm_aligned_runs (k : VShufKind) (d : XmmReg) (ea : Ea) (sel : BitVec 8)
    (h : Live s) (hl : ea.lock = false)
    (hA : aligned16 (ea.addr s (s.rip + BitVec.ofNat 64 len)) = true) :
    (step ⟨.vshufm k d ea sel, len⟩ s).stopped = false := by
  simp [step, h, hl, hA, Cpu.setXmm, Cpu.setRip, Cpu.stopped, Op.lockIllegal,
        Op.anyLocked, Op.lockable]

/-- ⭐⭐⭐ AND THE SAME RULE AT THE PACKED SHIFTS' MEMORY FORM — **the theorem
that would have failed before this batch**, because `Op.vshiftm` had no `#GP`
branch and a comment saying its absence was the rule.

⚠️ The `vshiftEncodable` hypothesis is not decoration: at an unencodable pair the
arm halts for a DIFFERENT reason (`illegalOperands`), so a theorem without it
would be true for the wrong reason on two of its twelve cases and would go on
holding if the alignment branch were deleted. -/
theorem vshiftm_unaligned_faults (op : VShiftOp) (w : VShiftW) (d : XmmReg) (ea : Ea)
    (h : Live s) (hl : ea.lock = false) (he : vshiftEncodable op w = true)
    (hU : aligned16 (ea.addr s (s.rip + BitVec.ofNat 64 len)) = false) :
    (step ⟨.vshiftm op w d ea, len⟩ s).stopped = true := by
  simp [step, h, hl, he, hU, Cpu.halt, Cpu.stopped, Op.lockIllegal, Op.anyLocked,
        Op.lockable]

theorem vshiftm_aligned_runs (op : VShiftOp) (w : VShiftW) (d : XmmReg) (ea : Ea)
    (h : Live s) (hl : ea.lock = false) (he : vshiftEncodable op w = true)
    (hA : aligned16 (ea.addr s (s.rip + BitVec.ofNat 64 len)) = true) :
    (step ⟨.vshiftm op w d ea, len⟩ s).stopped = false := by
  simp [step, h, hl, he, hA, Cpu.setXmm, Cpu.setRip, Cpu.stopped, Op.lockIllegal,
        Op.anyLocked, Op.lockable]

/-- ⭐⭐ THE DESTINATION IS NOT READ — stated as an EXACT step characterisation,
so the claim is visible in the theorem's own shape: the right-hand side names
`s.xmm.get r` and never mentions `d`'s old value at all.

⛔ It is a theorem rather than a vector because the vectors cannot say it. A model
that permuted the destination IN PLACE agrees with this one on every vector whose
destination already holds its source — the register-field mistake batch 5 paid
for once, arriving here in its operand form. `pshufd_x2x3` is the vector that
makes the two differ; this is the statement of what it is testing. -/
theorem vshuf_reads_only_the_source (k : VShufKind) (d r : XmmReg) (sel : BitVec 8)
    (h : Live s) :
    step ⟨.vshuf k d r sel, len⟩ s =
      { s with xmm := s.xmm.set d (vshufApply k (s.xmm.get r) sel),
               rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.setXmm, Cpu.setRip, Cpu.getXmm, Op.lockIllegal,
        Op.anyLocked, Op.lockable]

end Batch14

/-! ## P2 VECTOR WAVE, BATCH 15 — the packed binary group at a memory source, and
the first alignment claim in this repository a RUN can check. -/
namespace Batch15

variable {s : Cpu} {len : Nat}

/-- ⭐⭐ AN UNALIGNED PACKED BINARY OPERATION FAULTS.

⭐⭐⭐ **AND UNLIKE `vload_unaligned_faults` (D91) AND `vshufm_unaligned_faults`
(D110), THIS ONE IS NOT ALONE.** For `k = .and`, `.or`, `.xor` the oracle refuses
the same address — x86isa implements the 16-byte `#GP` in `logical.lisp`, and
only there — so `pand_m_unal`, `por_m_unal` and `pxor_m_unal` are vectors in which
BOTH models refuse, `bothRefused` reports agreement, and the rule is carried by a
RUN as well as by this theorem.

⛔⛔ **AND THAT SENTENCE'S SECOND HALF WAS TRUE WHEN WRITTEN AND IS NOT NOW.** It
went on: *"at the other sixteen kinds it is theorem-only, and the split is a fact
about x86isa's source tree rather than a judgement."* Both clauses read as a
reason not to look again — and the fact about the source tree is larger than the
three the sentence names. `logical.lisp`'s function is
`x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM`: ONE body, serving
TWELVE mnemonics, with the `:memory-address-is-not-16-byte-aligned` branch inside
it — read in the body, not off its doc comment. P2 batch 34 claims the other nine,
so the run-backed set is twelve of twenty-eight kinds, not three of nineteen.
⚠️ Only two more vectors were added for it, not nine: both sides share their rule
(this theorem is generic in `k`; ACL2's is one function), so the extra seven would
be one test wearing seven names. What varies is the DISPATCH, whose live dimension
is the mandatory prefix — hence one prefixed and one bare.
🔑 A justification for an exclusion outlives the condition that made it true.
[[feedback-a-justification-outlives-its-condition]] -/
theorem vbinm_unaligned_faults (k : VBinKind) (d : XmmReg) (ea : Ea) (h : Live s)
    (hl : ea.lock = false)
    (hU : aligned16 (ea.addr s (s.rip + BitVec.ofNat 64 len)) = false) :
    (step ⟨.vbinm k d ea, len⟩ s).stopped = true := by
  simp [step, h, hl, hU, Cpu.halt, Cpu.stopped, Op.lockIllegal, Op.anyLocked,
        Op.lockable]

theorem vbinm_aligned_runs (k : VBinKind) (d : XmmReg) (ea : Ea) (h : Live s)
    (hl : ea.lock = false) (hk : k.isMinMax = false)
    (hA : aligned16 (ea.addr s (s.rip + BitVec.ofNat 64 len)) = true) :
    (step ⟨.vbinm k d ea, len⟩ s).stopped = false := by
  simp [step, h, hl, hA, hk, vbinFlags, Cpu.setXmm, Cpu.setRip, Cpu.stopped, Op.lockIllegal,
        Op.anyLocked, Op.lockable]

/-- ⭐⭐ THE MEMORY SHAPE IS THE REGISTER SHAPE'S FUNCTION WITH ITS SECOND OPERAND
LOADED — stated so that the two shapes cannot drift into different arithmetic.

⚠️ The operand ORDER is the content: `dst` is the first argument and the memory
value the second, which for the eleven commuting operations is invisible and for
`psub*` and the eight unpacks is the whole answer. -/
theorem vbinm_is_vbin_with_a_loaded_operand (k : VBinKind) (d : XmmReg) (ea : Ea)
    (h : Live s) (hl : ea.lock = false) (hk : k.isMinMax = false)
    (hA : aligned16 (ea.addr s (s.rip + BitVec.ofNat 64 len)) = true) :
    (step ⟨.vbinm k d ea, len⟩ s).xmm.get d
      = vbinApply k (s.xmm.get d) (s.readMem128 (ea.addr s (s.rip + BitVec.ofNat 64 len))) := by
  simp [step, h, hl, hA, hk, vbinFlags, Cpu.setXmm, Cpu.setRip, Cpu.getXmm, Op.lockIllegal,
        Op.anyLocked, Op.lockable]

end Batch15

/-! ## P2 BATCH 34 — the bitwise complement

The batch's whole semantic content is one asymmetry, so it is stated here as
theorems rather than left to a comment and a differential score. -/
namespace Batch34

variable {s : Cpu} {len : Nat}

/-- ⛔⛔ `ANDN` COMPLEMENTS ITS DESTINATION, NOT ITS SOURCE — the rule, as an
equation the kernel checks rather than a sentence in a docstring.

⚠️ Stated for all three spellings at once, which is itself the claim that they
are one function: `pandn`, `andnps` and `andnpd` differ in their bytes and in
nothing else. -/
@[simp] theorem vbinApply_andn (a b : BitVec 128) :
    vbinApply .andn a b = (~~~a) &&& b ∧
    vbinApply .andnps a b = (~~~a) &&& b ∧
    vbinApply .andnpd a b = (~~~a) &&& b := by
  refine ⟨rfl, rfl, rfl⟩

/-- ⭐⭐ AND THE SWAPPED MODEL IS A DIFFERENT FUNCTION — a WITNESS, not an
appeal to plausibility.

⚠️ This is the theorem the differential score cannot give: an arm's count says
how often two models happened to disagree on the pre-states that exist, which is
a joint fact about the model and the table
([[feedback-a-wrong-models-score-is-a-joint-fact]]). This says they differ at
all, once, for reasons no pre-state table can affect. -/
theorem andn_is_not_its_operand_swap :
    ∃ a b : BitVec 128, (~~~a) &&& b ≠ a &&& (~~~b) := by
  exact ⟨0, 1, by decide⟩

/-- ⭐⭐ AND SO IS THE `NAND` READING, for the same reason and with its own
witness. ⚠️ The two wrong models are not each other: they coincide only where
`a = b`, and `xmmPattern` puts no such pre-state in the table — which is why both
are planted, and why the reason is stated as an equation here rather than as a
claim about how often each fires. -/
theorem andn_is_not_nand :
    ∃ a b : BitVec 128, (~~~a) &&& b ≠ ~~~(a &&& b) := by
  exact ⟨0, 0, by decide⟩

/-- ⭐ THE SIX ALIAS SPELLINGS ARE THEIR INTEGER SIBLINGS, EXACTLY.

⛔ THIS IS THE BATCH'S OTHER CLAIM AND IT IS THE ONE A READER SHOULD DOUBT: nine
new kinds, and six of them are asserted to be operations the model already had.
If that is false the coverage table publishes six wrong rows, and no differential
vector would say so — each spelling is tested only against the oracle, never
against its sibling. So it is a theorem. -/
@[simp] theorem bitwise_aliases_are_their_integer_siblings (a b : BitVec 128) :
    vbinApply .andps a b = vbinApply .and a b ∧
    vbinApply .andpd a b = vbinApply .and a b ∧
    vbinApply .orps  a b = vbinApply .or  a b ∧
    vbinApply .orpd  a b = vbinApply .or  a b ∧
    vbinApply .xorps a b = vbinApply .xor a b ∧
    vbinApply .xorpd a b = vbinApply .xor a b := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚠️ AND THE NINE ARE NINE, not one under nine names: the mnemonics a
disassembler prints are distinct, which is what makes them nine roster rows.
⛔ The SEMANTICS being shared is not the same claim as the SPELLING being shared,
and this repository counts rows by what is printed. -/
theorem bitwise_complement_mnemonics_are_distinct :
    ([VBinKind.andn, .andnps, .andnpd, .andps, .andpd,
      .orps, .orpd, .xorps, .xorpd].map VBinKind.mnemonic).eraseDups.length = 9 := by
  decide

/-! ### ⭐⭐ P2 BATCH 37 — THE FOUR UNPACK SPELLINGS

The batch-19/batch-34 claim in its fourth instance, and the one a reader should
doubt: four new kinds, all four asserted to be operations the model already had.
If that is false the coverage table publishes four wrong rows, and **no
differential vector would say so** — each spelling is tested only against the
oracle, never against its sibling, so a model decoding `0f 14` as `punpckldq`
scores identically on every case in the table.  The bytes are held apart by
`scripts/check_encodings.py`; the semantics is held together here. -/

/-- ⛔⛔ DECIDED ON K'S LEAF SEQUENCE, AND ITS TEXT SAYS OTHERWISE FOR TWO OF THE
FOUR.  Whitespace-normalised, `unpcklpd`/`punpcklqdq` and `unpckhpd`/`punpckhqdq`
are byte-identical (207 chars) while `unpcklps`/`punpckldq` and
`unpckhps`/`punpckhdq` differ at char 122 of 345 — pure re-association of
`concatenateMInt`, which is associative on bit strings.  ⇒ a byte comparison over
the four reports *two spellings, two new semantics*, a self-consistent wrong
design with a ready-made `ps`/`pd` explanation.  Under the leaf normal form all
four agree and three controls differ.  ⭐ LLVM's disassembler agrees
independently of K, printing one operand comment for each pair. -/
@[simp] theorem unpack_aliases_are_their_integer_siblings (a b : BitVec 128) :
    vbinApply .unpcklps a b = vbinApply .unpckld a b ∧
    vbinApply .unpckhps a b = vbinApply .unpckhd a b ∧
    vbinApply .unpcklpd a b = vbinApply .unpcklq a b ∧
    vbinApply .unpckhpd a b = vbinApply .unpckhq a b := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- ⚠️ AND THE FOUR ARE FOUR SPELLINGS OF FOUR DISTINCT OPERATIONS, not one under
four names.  ⛔ THIS IS THE ARM THE PREVIOUS THEOREM CANNOT PROVIDE: routing every
new kind to a SINGLE sibling would satisfy `unpack_aliases_...` for whichever one
it named, and this refuses it — the four siblings are pairwise different
functions, so a mis-routed spelling lands on a sibling that disagrees.

⛔⛔ THE WITNESS IS CHOSEN, AND THE OBVIOUS ONE IS SILENT ON THE LAST CONJUNCT.
This was first written with `⟨0, 1, …⟩`, which satisfies the first THREE and makes
the fourth FALSE: `1` lies entirely in the LOW half, so `unpckhd` and `unpckhq`
both read nothing but zeros and AGREE.  Had the theorem been written with only the
three conjuncts that passed — a natural thing to do — it would have been green and
blind to exactly the pair a mis-routed `unpckhps`/`unpckhpd` lands on.
⇒ 🔑 a witness drawn from the same half of the space as everything else is silent
in the dimension the claim is about.  Every lane here is distinct and non-zero in
BOTH halves, so all four operations give four different answers, and the
destination-first order is visible too.
[[feedback-a-control-can-share-the-blind-spot]] -/
theorem unpack_siblings_are_pairwise_distinct :
    ∃ a b : BitVec 128,
      vbinApply .unpckld a b ≠ vbinApply .unpcklq a b ∧
      vbinApply .unpckld a b ≠ vbinApply .unpckhd a b ∧
      vbinApply .unpcklq a b ≠ vbinApply .unpckhq a b ∧
      vbinApply .unpckhd a b ≠ vbinApply .unpckhq a b := by
  refine ⟨0x000000A4000000A3000000A2000000A1, 0x000000B4000000B3000000B2000000B1,
    by decide, by decide, by decide, by decide⟩

/-- ⚠️ The four spellings are four roster rows, which is a claim about what a
disassembler PRINTS and not about the semantics shared above. -/
theorem unpack_spelling_mnemonics_are_distinct :
    ([VBinKind.unpcklps, .unpckhps, .unpcklpd, .unpckhpd,
      .unpckld, .unpckhd, .unpcklq, .unpckhq].map VBinKind.mnemonic).eraseDups.length = 8 := by
  decide

end Batch34

/-! ## D330 (W1b) — ADCX, ADOX and MULX

⭐ THE CONTENT OF ALL THREE IS WHAT THEY DO **NOT** WRITE.  ADCX writes CF and no
other flag, ADOX writes OF and no other flag, and MULX writes no flag at all
(SDM Vol. 2A ADCX, ADOX; Vol. 2B MULX).  A model that routed `adcx` through
`.bin .adc` would compute the same sum and write six flags; these theorems are
the statements that separate the two, and they are equations a reader can check
without running anything.

⚠️ MULX HAS NO DIFFERENTIAL PARTNER: ACL2 x86isa refuses it at every pre-state
(`scripts/oracle_availability.py`).  Its numbers are checked against a PROCESSOR
by `hwprobe/` and pinned in `Tests/Anchors.lean`; these theorems state its frame. -/
section W1b
variable {sz : Size} {len : Nat} {s : Cpu}

/-- ADCX, register source: the sum is ADC's, and the flags are the incoming flags
with CF — and only CF — replaced by the carry out. -/
theorem step_adcx_reg (h : Live s) (dst rs : GPR) (hsz : sz = .d ∨ sz = .q) :
    step ⟨.adx false sz dst (.reg rs), len⟩ s =
      ((s.setFlags { s.flags with
          cf := Flags.adcCF sz (s.getReg sz dst) (s.getReg sz rs) s.flags.cf }).setReg sz dst
        (Flags.adcResult sz (s.getReg sz dst) (s.getReg sz rs) s.flags.cf)).setRip
        (s.rip + BitVec.ofNat 64 len) := by
  rcases hsz with rfl | rfl <;> simp [step, h]

/-- ADOX, register source: the same sum, carried through OF instead. -/
theorem step_adox_reg (h : Live s) (dst rs : GPR) (hsz : sz = .d ∨ sz = .q) :
    step ⟨.adx true sz dst (.reg rs), len⟩ s =
      ((s.setFlags { s.flags with
          of := Flags.adcCF sz (s.getReg sz dst) (s.getReg sz rs) s.flags.of }).setReg sz dst
        (Flags.adcResult sz (s.getReg sz dst) (s.getReg sz rs) s.flags.of)).setRip
        (s.rip + BitVec.ofNat 64 len) := by
  rcases hsz with rfl | rfl <;> simp [step, h]

/-- ⭐ ADCX LEAVES OF, SF, ZF, AF AND PF EXACTLY AS IT FOUND THEM — the half of
the SDM's flag sentence that ADC does not share. -/
theorem step_adcx_keeps_other_flags (h : Live s) (dst rs : GPR) (hsz : sz = .d ∨ sz = .q) :
    let f := (step ⟨.adx false sz dst (.reg rs), len⟩ s).flags
    f.of = s.flags.of ∧ f.sf = s.flags.sf ∧ f.zf = s.flags.zf
      ∧ f.af = s.flags.af ∧ f.pf = s.flags.pf := by
  rw [step_adcx_reg h dst rs hsz]; simp

/-- ⭐ ADOX LEAVES CF, SF, ZF, AF AND PF EXACTLY AS IT FOUND THEM — including CF,
which is the flag a reader expects an add-with-carry to touch. -/
theorem step_adox_keeps_other_flags (h : Live s) (dst rs : GPR) (hsz : sz = .d ∨ sz = .q) :
    let f := (step ⟨.adx true sz dst (.reg rs), len⟩ s).flags
    f.cf = s.flags.cf ∧ f.sf = s.flags.sf ∧ f.zf = s.flags.zf
      ∧ f.af = s.flags.af ∧ f.pf = s.flags.pf := by
  rw [step_adox_reg h dst rs hsz]; simp

/-- ADCX/ADOX spend no oracle bit: every flag is either the carry or unmodified. -/
@[simp] theorem step_adx_oracle (o : Bool) (h : Live s) (dst rs : GPR) (hsz : sz = .d ∨ sz = .q) :
    (step ⟨.adx o sz dst (.reg rs), len⟩ s).oracle = s.oracle := by
  cases o
  · rw [step_adcx_reg h dst rs hsz]; simp
  · rw [step_adox_reg h dst rs hsz]; simp

/-- MULX, register source: RDX times the source, the low half written to `lo`
FIRST and the high half to `hi` SECOND (the SDM's order), and nothing else. -/
theorem step_mulx_reg (h : Live s) (hi lo rs : GPR) (hsz : sz = .d ∨ sz = .q) :
    step ⟨.mulx sz hi lo (.reg rs), len⟩ s =
      (let p := Value.mulPair sz (s.getReg sz .rdx) (s.getReg sz rs)
       ((s.setReg sz lo p.1).setReg sz hi p.2).setRip (s.rip + BitVec.ofNat 64 len)) := by
  rcases hsz with rfl | rfl <;> simp [step, h]

/-- ⭐ "FLAGS AFFECTED: NONE", as an equation. -/
@[simp] theorem step_mulx_flags (h : Live s) (hi lo rs : GPR) (hsz : sz = .d ∨ sz = .q) :
    (step ⟨.mulx sz hi lo (.reg rs), len⟩ s).flags = s.flags := by
  rw [step_mulx_reg h hi lo rs hsz]; simp

@[simp] theorem step_mulx_oracle (h : Live s) (hi lo rs : GPR) (hsz : sz = .d ∨ sz = .q) :
    (step ⟨.mulx sz hi lo (.reg rs), len⟩ s).oracle = s.oracle := by
  rw [step_mulx_reg h hi lo rs hsz]; simp

/-- ⭐⭐ THE SAME-DESTINATION CASE: when both destinations name one register, it
holds the HIGH half (SDM Vol. 2B, MULX: DEST2 is written before DEST1). -/
theorem step_mulx_same_dest_is_high (h : Live s) (r rs : GPR) (hsz : sz = .d ∨ sz = .q) :
    (step ⟨.mulx sz r r (.reg rs), len⟩ s).getReg sz r
      = Value.trunc sz (Value.mulPair sz (s.getReg sz .rdx) (s.getReg sz rs)).2 := by
  rw [step_mulx_reg h r r rs hsz]
  rcases hsz with rfl | rfl <;> simp [Cpu.getReg, Value.trunc_writeView]

/-- ⛔ NEITHER FORM EXISTS AT 8 OR 16 BITS, and `step` refuses rather than
answering for bytes no encoding can carry. -/
theorem step_adx_narrow_refuses (o : Bool) (dst : GPR) (src : Operand) (h : Live s)
    (hsz : sz = .b ∨ sz = .w) :
    (step ⟨.adx o sz dst src, len⟩ s).stopped = true := by
  rcases hsz with rfl | rfl <;> cases src <;> simp [step, h, Cpu.halt] <;> split <;> simp

theorem step_mulx_narrow_refuses (hi lo : GPR) (src : Operand) (h : Live s)
    (hsz : sz = .b ∨ sz = .w) :
    (step ⟨.mulx sz hi lo src, len⟩ s).stopped = true := by
  rcases hsz with rfl | rfl <;> cases src <;> simp [step, h, Cpu.halt] <;> split <;> simp

end W1b

/-! ## D334 (W1c) — ANDN, BEXTR, BZHI, BLSMSK, BLSR, PDEP, PEXT, RORX, MOVNTI

⚠️ NONE OF THESE HAS A DIFFERENTIAL PARTNER: ACL2 x86isa refuses every one
(`scripts/oracle_availability.py`).  Their numbers are checked against a PROCESSOR
by `hwprobe/` and pinned in `Tests/AnchorsBmi.lean`; these theorems state the frame
and the flag rules the SDM gives, as equations. -/
section W1c
variable {sz : Size} {len : Nat} {s : Cpu}

/-- ANDN, register sources: `(NOT src1) AND src2`, PF then AF from the oracle. -/
theorem step_andn_reg (h : Live s) (dst r1 r2 : GPR) (hsz : sz = .d ∨ sz = .q) :
    step ⟨.andn sz dst r1 (.reg r2), len⟩ s =
      (let res := Value.andn sz (s.getReg sz r1) (s.getReg sz r2)
       let (pfU, s1) := s.undefBit
       let (afU, s2) := s1.undefBit
       ((s2.setFlags (Flags.andn sz res pfU afU s2.flags)).setReg sz dst res).setRip
         (s.rip + BitVec.ofNat 64 len)) := by
  rcases hsz with rfl | rfl <;> simp [step, h]

/-- ⭐ ANDN CLEARS CF AND OF, whatever they were. -/
theorem step_andn_cf_of (h : Live s) (dst r1 r2 : GPR) (hsz : sz = .d ∨ sz = .q) :
    let f := (step ⟨.andn sz dst r1 (.reg r2), len⟩ s).flags
    f.cf = false ∧ f.of = false := by
  rw [step_andn_reg h dst r1 r2 hsz]; simp [Flags.andn]

/-- ⭐ BLSMSK CLEARS ZF UNCONDITIONALLY and sets CF exactly at a zero source
(SDM Vol. 2A, BLSMSK: `ZF := 0`). -/
theorem step_blsmsk_flags (h : Live s) (dst rs : GPR) (hsz : sz = .d ∨ sz = .q) :
    let f := (step ⟨.blsx true sz dst (.reg rs), len⟩ s).flags
    f.zf = false ∧ f.of = false ∧ f.cf = Value.isZero sz (s.getReg sz rs) := by
  rcases hsz with rfl | rfl <;> simp [step, h, Flags.blsmsk]

/-- BLSR: ZF from the result, CF exactly at a zero source, OF cleared. -/
theorem step_blsr_flags (h : Live s) (dst rs : GPR) (hsz : sz = .d ∨ sz = .q) :
    let f := (step ⟨.blsx false sz dst (.reg rs), len⟩ s).flags
    f.zf = Value.isZero sz (Value.blsr sz (s.getReg sz rs)) ∧ f.of = false
      ∧ f.cf = Value.isZero sz (s.getReg sz rs) := by
  rcases hsz with rfl | rfl <;> simp [step, h, Flags.blsr]

/-- BEXTR: ZF from the result; CF and OF cleared. -/
theorem step_bextr_flags (h : Live s) (dst rs rc : GPR) (hsz : sz = .d ∨ sz = .q) :
    let f := (step ⟨.bextr sz dst (.reg rs) rc, len⟩ s).flags
    f.zf = Value.isZero sz (Value.bextr sz (s.getReg sz rs) (s.getReg sz rc))
      ∧ f.cf = false ∧ f.of = false := by
  rcases hsz with rfl | rfl <;> simp [step, h, Flags.bextr]

/-- ⭐ BEXTR AT A START OF 64 OR MORE EXTRACTS NOTHING — the 512-bit zero-extension
in the SDM's operation supplies only zeros there. -/
theorem bextr_start_past (v ctl : Val) (hs : 64 ≤ ctl.toNat % 256) :
    Value.bextr sz v ctl = 0 := by
  have h0 : Value.trunc sz v >>> (ctl.toNat % 256) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight]
    apply Nat.shiftRight_eq_zero
    exact Nat.lt_of_lt_of_le (BitVec.isLt _) (Nat.pow_le_pow_right (by decide) hs)
  simp only [Value.bextr, h0]
  split <;> simp

/-- ⭐ BZHI's CF READS THE INDEX, NOT THE SOURCE: it is set exactly when the
control's low byte exceeds width − 1. -/
theorem step_bzhi_cf (h : Live s) (dst rs ri : GPR) (hsz : sz = .d ∨ sz = .q) :
    (step ⟨.bzhi sz dst (.reg rs) ri, len⟩ s).flags.cf
      = decide (sz.bits - 1 < Value.bzhiIndex (s.getReg sz ri)) := by
  rcases hsz with rfl | rfl <;> simp [step, h, Flags.bzhi]

/-- ⭐ BZHI AT AN INDEX OF THE WIDTH OR MORE CLEARS NOTHING (the SDM's Operation;
D334 records the prose that reads otherwise). -/
theorem bzhi_index_past (v ctl : Val) (hn : sz.bits ≤ Value.bzhiIndex ctl) :
    Value.bzhi sz v ctl = Value.trunc sz v := by
  simp [Value.bzhi, Nat.not_lt.mpr hn]

/-- ⭐ PDEP AND PEXT: "FLAGS AFFECTED: NONE", and no oracle bit is spent. -/
@[simp] theorem step_pbits_flags (e : Bool) (h : Live s) (dst r1 rm : GPR) (hsz : sz = .d ∨ sz = .q) :
    (step ⟨.pbits e sz dst r1 (.reg rm), len⟩ s).flags = s.flags
      ∧ (step ⟨.pbits e sz dst r1 (.reg rm), len⟩ s).oracle = s.oracle := by
  rcases hsz with rfl | rfl <;> simp [step, h]

/-- ⭐ RORX: "FLAGS AFFECTED: NONE" — unlike ROR, at every count. -/
@[simp] theorem step_rorx_flags (h : Live s) (dst rs : GPR) (imm : Val) (hsz : sz = .d ∨ sz = .q) :
    (step ⟨.rorx sz dst (.reg rs) imm, len⟩ s).flags = s.flags
      ∧ (step ⟨.rorx sz dst (.reg rs) imm, len⟩ s).oracle = s.oracle := by
  rcases hsz with rfl | rfl <;> simp [step, h]

/-- RORX, register source: the rotated source, and nothing else. -/
theorem step_rorx_reg (h : Live s) (dst rs : GPR) (imm : Val) (hsz : sz = .d ∨ sz = .q) :
    step ⟨.rorx sz dst (.reg rs) imm, len⟩ s =
      (s.setReg sz dst (Value.rorx sz (s.getReg sz rs) imm)).setRip (s.rip + BitVec.ofNat 64 len) := by
  rcases hsz with rfl | rfl <;> simp [step, h]

/-- ⭐ MOVNTI IS A PLAIN STORE IN THIS MODEL: the source written at the operand
width to the memory destination, no flag, no oracle bit (D334: the non-temporal
hint and its weak ordering are outside a single-threaded state). -/
theorem step_movnti (h : Live s) (ea : Ea) (hl : ea.lock = false) (rs : GPR)
    (hsz : sz = .d ∨ sz = .q) :
    step ⟨.movnti sz (.mem ea) rs, len⟩ s =
      (s.writeOperand sz (s.rip + BitVec.ofNat 64 len) (.mem ea) (s.getReg sz rs)).setRip
        (s.rip + BitVec.ofNat 64 len) := by
  rcases hsz with rfl | rfl <;> simp [step, h, hl, Operand.isMem]

/-- ⛔ NO W1c FORM EXISTS AT 8 OR 16 BITS (VEX.W, or MOVNTI's REX.W, selects 32 or
64 only), and `step` refuses rather than answering for an encoding that is not. -/
theorem step_andn_narrow_refuses (dst r1 : GPR) (src : Operand) (h : Live s)
    (hsz : sz = .b ∨ sz = .w) :
    (step ⟨.andn sz dst r1 src, len⟩ s).stopped = true := by
  rcases hsz with rfl | rfl <;> cases src <;> simp [step, h, Cpu.halt] <;> split <;> simp

theorem step_rorx_narrow_refuses (dst : GPR) (src : Operand) (imm : Val) (h : Live s)
    (hsz : sz = .b ∨ sz = .w) :
    (step ⟨.rorx sz dst src imm, len⟩ s).stopped = true := by
  rcases hsz with rfl | rfl <;> cases src <;> simp [step, h, Cpu.halt] <;> split <;> simp

/-- ⛔ MOVNTI TO A REGISTER HAS NO ENCODING (`0F C3` takes a memory r/m only). -/
theorem step_movnti_reg_refuses (r rs : GPR) (h8 : Bool) (h : Live s) :
    (step ⟨.movnti sz (.reg r h8) rs, len⟩ s).stopped = true := by
  simp [step, h, Cpu.halt, Operand.isMem] <;> split <;> simp

end W1c

/-! ## D336 (V1b) — PSHUFB, PALIGNR, PINSRD/Q, PEXTRD/Q

⚠️ No differential partner: ACL2 x86isa refuses all six
(`scripts/oracle_availability.py`).  Their numbers are checked against a PROCESSOR
by `hwprobe/` and pinned in `Tests/AnchorsShuf.lean`; these theorems state the frame
and the rules' edge cases as equations. -/
section V1b
variable {sz : Size} {len : Nat} {s : Cpu}

/-- PSHUFB between registers: the destination's ORIGINAL value shuffled by the
source's control bytes; no flag, no oracle bit, no GPR written. -/
theorem step_vshufb (h : Live s) (d x : XmmReg) :
    step ⟨.vshufb d x, len⟩ s =
      (s.setXmm d (vshufbApply (s.getXmm d) (s.getXmm x))).setRip (s.rip + BitVec.ofNat 64 len) := by
  simp [step, h, Op.lockIllegal, Op.anyLocked, Op.lockable]

/-- ⭐ A CONTROL BYTE WITH BIT 7 SET ZEROES ITS LANE, whatever the data: an
all-`0x80` control returns zero. -/
theorem vshufb_all_high (a : BitVec 128) :
    vshufbApply a 0x80808080808080808080808080808080 = 0 := by
  have hm : (128#8).msb = true := by decide
  simp [vshufbApply, vshufbAux, hm]

/-- ⛔⭐ AN UNALIGNED PSHUFB m128 FAULTS (Exception Type 4, D110). -/
theorem vshufbm_unaligned_faults (d : XmmReg) (ea : Ea) (h : Live s) (hl : ea.lock = false)
    (hU : aligned16 (ea.addr s (s.rip + BitVec.ofNat 64 len)) = false) :
    (step ⟨.vshufbm d ea, len⟩ s).stopped = true := by
  simp [step, h, hl, hU, Cpu.halt, Cpu.stopped, Op.lockIllegal, Op.anyLocked, Op.lockable]

/-- PALIGNR between registers. -/
theorem step_valignr (h : Live s) (d x : XmmReg) (imm : BitVec 8) :
    step ⟨.valignr d x imm, len⟩ s =
      (s.setXmm d (valignrApply (s.getXmm d) (s.getXmm x) imm)).setRip
        (s.rip + BitVec.ofNat 64 len) := by
  simp [step, h, Op.lockIllegal, Op.anyLocked, Op.lockable]

/-- ⭐ PALIGNR AT A SHIFT OF 32 BYTES OR MORE RETURNS ZERO — the whole 256-bit
concatenation has been shifted out (SDM Vol. 2B, PALIGNR). -/
theorem valignr_past (a b : BitVec 128) (imm : BitVec 8) (h : 31 < imm.toNat) :
    valignrApply a b imm = 0 := by
  simp [valignrApply, h]

/-- ⭐ AND AT ZERO IT RETURNS THE SOURCE (the sixteen-byte case, which returns the
destination, is pinned by the silicon rows in `Tests/AnchorsShuf.lean`). -/
theorem valignr_zero (a b : BitVec 128) : valignrApply a b 0 = b := by
  simp [valignrApply]

/-- ⛔⭐ AN UNALIGNED PALIGNR m128 FAULTS (Exception Type 4, D110). -/
theorem valignrm_unaligned_faults (d : XmmReg) (ea : Ea) (imm : BitVec 8) (h : Live s)
    (hl : ea.lock = false) (hU : aligned16 (ea.addr s (s.rip + BitVec.ofNat 64 len)) = false) :
    (step ⟨.valignrm d ea imm, len⟩ s).stopped = true := by
  simp [step, h, hl, hU, Cpu.halt, Cpu.stopped, Op.lockIllegal, Op.anyLocked, Op.lockable]

/-- PINSRD/PINSRQ from a register: the lane replaced, nothing else written. -/
theorem step_vinsr_reg (h : Live s) (d : XmmReg) (r : GPR) (imm : BitVec 8)
    (hsz : sz = .d ∨ sz = .q) :
    step ⟨.vinsr sz d (.reg r) imm, len⟩ s =
      (s.setXmm d (vinsrApply sz (s.getXmm d) (s.getReg sz r) imm)).setRip
        (s.rip + BitVec.ofNat 64 len) := by
  rcases hsz with rfl | rfl <;>
    simp [step, h, Op.lockIllegal, Op.anyLocked, Op.lockable, Operand.isImm,
      Cpu.readOperand]

/-- ⭐ ONLY `imm[1:0]` SELECTS AT 32 BITS AND `imm[0]` AT 64: the imm8 bits above
are ignored (SDM Vol. 2B, PINSRD/PINSRQ and PEXTRD/PEXTRQ). -/
theorem vlaneSel_d (imm : BitVec 8) : vlaneSel .d imm = imm.toNat % 4 := rfl
theorem vlaneSel_q (imm : BitVec 8) : vlaneSel .q imm = imm.toNat % 2 := rfl

/-- PEXTRD/PEXTRQ to a register: an ordinary GPR write of the selected lane (at
`.d` it zero-extends, by `setReg`), nothing else written. -/
theorem step_vextr (h : Live s) (r : GPR) (x : XmmReg) (imm : BitVec 8)
    (hsz : sz = .d ∨ sz = .q) :
    step ⟨.vextr sz (.reg r) x imm, len⟩ s =
      (s.setReg sz r (vextrApply sz (s.getXmm x) imm)).setRip (s.rip + BitVec.ofNat 64 len) := by
  rcases hsz with rfl | rfl <;>
    simp [step, h, Op.lockIllegal, Op.anyLocked, Op.lockable, Operand.isImm, Cpu.writeOperand]

/-- D362: PEXTRD/PEXTRQ to memory, an unlocked operand: the selected lane is
written at the operand's address at width `sz`, and nothing else is written. -/
theorem step_vextr_mem (h : Live s) (ea : Ea) (x : XmmReg) (imm : BitVec 8)
    (hl : ea.lock = false) (hsz : sz = .d ∨ sz = .q) :
    step ⟨.vextr sz (.mem ea) x imm, len⟩ s =
      (s.writeMem sz (ea.addr s (s.rip + BitVec.ofNat 64 len)) (vextrApply sz (s.getXmm x) imm)).setRip
        (s.rip + BitVec.ofNat 64 len) := by
  rcases hsz with rfl | rfl <;>
    simp [step, h, hl, Op.lockIllegal, Op.anyLocked, Op.lockable, Operand.isImm, Cpu.writeOperand]

/-- ⛔ NO FLAG: PSHUFB, PALIGNR, PINSR* and PEXTR* leave RFLAGS as they found it. -/
theorem step_vextr_flags (h : Live s) (r : GPR) (x : XmmReg) (imm : BitVec 8)
    (hsz : sz = .d ∨ sz = .q) :
    (step ⟨.vextr sz (.reg r) x imm, len⟩ s).flags = s.flags := by
  rw [step_vextr h r x imm hsz]; simp

/-- ⛔ PINSR*/PEXTR* AT 8 OR 16 BITS ARE OTHER MNEMONICS, and `step` refuses them. -/
theorem step_vextr_narrow_refuses (r : GPR) (x : XmmReg) (imm : BitVec 8) (h : Live s)
    (hsz : sz = .b ∨ sz = .w) :
    (step ⟨.vextr sz (.reg r) x imm, len⟩ s).stopped = true := by
  rcases hsz with rfl | rfl <;> simp [step, h, Cpu.halt, Cpu.stopped, Op.lockIllegal,
    Op.anyLocked, Op.lockable, Operand.isImm]

end V1b

/-! ## D335 (V1a) — the packed-integer arithmetic x86isa refuses

⚠️ NONE OF THESE HAS A DIFFERENTIAL PARTNER: ACL2 x86isa refuses all eleven
(`scripts/oracle_availability.py`).  Their numbers are checked against a PROCESSOR by
`hwprobe/` (`mk_simda_rows.py`) and pinned in `Tests/AnchorsSimd.lean`.  The FRAME is
already stated for every `VBinKind` — `step_vbin` (XMM and RIP only), `step_vbin_flags`
(no flag), `vbinm_unaligned_faults` (the 16-byte `#GP`) — and applies to these kinds
because none is min/max (the first theorem below).  The rest state, as equations, the
edge cases the SDM names in words. -/
section V1a

/-- The eleven kinds are not min/max, so `step_vbin` and `vbinm_aligned_runs` apply. -/
theorem v1a_kinds_not_minmax :
    [VBinKind.maddwd, .maddubsw, .mullw, .mulhrsw, .muludq, .addsw, .subusw, .subusb,
      .maxsw, .sadbw, .packssdw].all (fun k => !k.isMinMax) = true := by decide

/-- ⭐ PMADDWD WRAPS, ONCE: all four words 8000H give 80000000H (the SDM's one wrap). -/
theorem maddwd_wraps_at_min : vmaddwdLane 0x80008000 0x80008000 = 0x80000000 := by decide

/-- ⭐ PMULHRSW's ONE OVERFLOW: 8000H × 8000H rounds to 8000H, not +32768. -/
theorem mulhrsw_min_min : vmulhrswLane 0x8000 0x8000 = 0x8000 := by decide

/-- ⛔ PMADDUBSW IS ASYMMETRIC: the destination byte FFH is 255 (unsigned) and the
source byte FFH is −1 (signed), so swapping the operands changes the word. -/
theorem maddubsw_asymmetric :
    vmaddubswLane 0x00FF 0x0001 = 0x00FF ∧ vmaddubswLane 0x0001 0x00FF = 0xFFFF := by decide

/-- PMADDUBSW saturates at both ends: 2 × 255 × 127 to 7FFFH and 2 × 255 × (−128) to 8000H. -/
theorem maddubsw_saturates :
    vmaddubswLane 0xFFFF 0x7F7F = 0x7FFF ∧ vmaddubswLane 0xFFFF 0x8080 = 0x8000 := by decide

/-- SaturateToSignedWord, below and above. -/
theorem ssatW_low {v : BitVec 32} (h : v.slt 0xFFFF8000 = true) : ssatW v = 0x8000 := by
  rw [ssatW, if_pos h]

theorem ssatW_high {v : BitVec 32} (hl : v.slt 0xFFFF8000 = false)
    (h : (0x00007FFF : BitVec 32).slt v = true) : ssatW v = 0x7FFF := by
  rw [ssatW, if_neg (by rw [hl]; exact Bool.false_ne_true), if_pos h]

/-- ⭐ PSADBW's quadword holds the sum in its low word and ZERO above it: the
largest sum, eight differences of 255, is 7F8H. -/
theorem sad_max : vsadLane 0xFFFFFFFFFFFFFFFF 0 = 0x7F8 := by decide

end V1a

/-! ⭐ D373 — `pminsw`, `pmulhw`, `pmulhuw`, `pavgb`: four more kinds with no
differential partner (x86isa refuses all four), checked on silicon by
`hwprobe/mk_simda_rows.py --set-b` and pinned in `Tests/AnchorsSimdB.lean`.  The frame
theorems above apply for the same reason as D335's: none is min/max. -/
section D373

theorem d373_kinds_not_minmax :
    [VBinKind.minsw, .mulhw, .mulhuw, .avgb].all (fun k => !k.isMinMax) = true := by decide

/-- ⛔ PMINSW IS SIGNED: 8000H (−32768) is below 7FFFH, where an unsigned minimum
would keep 7FFFH. -/
theorem minsw_signed :
    vbinApply .minsw 0x80008000800080008000800080008000 0x7FFF7FFF7FFF7FFF7FFF7FFF7FFF7FFF
      = 0x80008000800080008000800080008000 := by decide

/-- ⭐ THE TWO HIGH HALVES DIFFER ONLY IN SIGNEDNESS: FFFFH × FFFFH is 1 signed
(high word 0) and FFFE0001H unsigned (high word FFFEH). -/
theorem mulhw_mulhuw_ones :
    vbinApply .mulhw 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF = 0 ∧
    vbinApply .mulhuw 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
      = 0xFFFEFFFEFFFEFFFEFFFEFFFEFFFEFFFE := by decide

/-- ⭐ PAVGB ROUNDS UP AND DOES NOT WRAP: FFH and FFH average to FFH, 0 and 1 to 1. -/
theorem avgb_rounds_up :
    vbinApply .avgb 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
      = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF ∧
    vbinApply .avgb 0 0x01010101010101010101010101010101
      = 0x01010101010101010101010101010101 := by decide

end D373

/-! ## D338 (V2) — SHA256MSG1, SHA256MSG2, SHA256RNDS2 (SHA-NI, legacy SSE)

⚠️ NONE OF THESE HAS A DIFFERENTIAL PARTNER: ACL2 x86isa refuses all three
(`scripts/oracle_availability.py`, D338 prediction 1).  Their numbers are checked
against a PROCESSOR by `hwprobe/` (`mk_sha_rows.py`, whose known-answer rows come from a
textbook FIPS 180-4 SHA-256) and pinned in `Tests/AnchorsSha.lean`.  The theorems
below state the frame, the Type-4 fault, WHICH DWORDS EACH RULE READS (the SDM's
Operation in words, here as equations), the σ boundaries, and FIPS 180-4's "abc"
block through the message and round rules. -/
section V2
variable {len : Nat} {s : Cpu}

/-- SHA256MSG1/MSG2/RNDS2 between registers: SRC1 is the destination's ORIGINAL value
and XMM0 is read before the write; no flag, no oracle bit, no GPR written. -/
theorem step_vsha (h : Live s) (k : ShaKind) (d x : XmmReg) :
    step ⟨.vsha k d x, len⟩ s =
      (s.setXmm d (shaApply k (s.getXmm d) (s.getXmm x) (s.getXmm .x0))).setRip
        (s.rip + BitVec.ofNat 64 len) := by
  simp [step, h, Op.lockIllegal, Op.anyLocked, Op.lockable]

/-- ⛔ NO FLAG: "Flags Affected: None" for all three. -/
theorem step_vsha_flags (h : Live s) (k : ShaKind) (d x : XmmReg) :
    (step ⟨.vsha k d x, len⟩ s).flags = s.flags := by
  rw [step_vsha h k d x]; simp

/-- ⛔⭐ AN UNALIGNED SHA m128 FAULTS (Exception Type 4, D110). -/
theorem vsham_unaligned_faults (k : ShaKind) (d : XmmReg) (ea : Ea) (h : Live s) (hl : ea.lock = false)
    (hU : aligned16 (ea.addr s (s.rip + BitVec.ofNat 64 len)) = false) :
    (step ⟨.vsham k d ea, len⟩ s).stopped = true := by
  simp [step, h, hl, hU, Cpu.halt, Cpu.stopped, Op.lockIllegal, Op.anyLocked, Op.lockable]

/-- And an ALIGNED one is the register rule with SRC2 read from memory. -/
theorem step_vsham_aligned (k : ShaKind) (d : XmmReg) (ea : Ea) (h : Live s) (hl : ea.lock = false)
    (hA : aligned16 (ea.addr s (s.rip + BitVec.ofNat 64 len)) = true) :
    step ⟨.vsham k d ea, len⟩ s =
      (s.setXmm d (shaApply k (s.getXmm d) (s.readMem128 (ea.addr s (s.rip + BitVec.ofNat 64 len)))
        (s.getXmm .x0))).setRip (s.rip + BitVec.ofNat 64 len) := by
  simp [step, h, hl, hA, Op.lockIllegal, Op.anyLocked, Op.lockable]

/-- ⭐ SHA256MSG1 READS ONLY SRC2's LOW DWORD (W4): two SRC2s that agree there give the
same result, whatever their other 96 bits. -/
theorem sha256msg1_reads_src2_low (a b b' x : BitVec 128) (h : shaD b 0 = shaD b' 0) :
    shaApply .msg1 a b x = shaApply .msg1 a b' x := by
  simp [shaApply, h]

/-- ⭐ SHA256MSG2 READS ONLY SRC2's HIGH TWO DWORDS (W14, W15). -/
theorem sha256msg2_reads_src2_high (a b b' x : BitVec 128) (h2 : shaD b 2 = shaD b' 2)
    (h3 : shaD b 3 = shaD b' 3) :
    shaApply .msg2 a b x = shaApply .msg2 a b' x := by
  simp [shaApply, h2, h3]

/-- ⭐ SHA256RNDS2 READS ONLY XMM0's LOW QUADWORD (WK0, WK1). -/
theorem sha256rnds2_reads_xmm0_low (a b x x' : BitVec 128) (h0 : shaD x 0 = shaD x' 0)
    (h1 : shaD x 1 = shaD x' 1) :
    shaApply .rnds2 a b x = shaApply .rnds2 a b x' := by
  simp [shaApply, h0, h1]

/-- ⭐ THE TWO MESSAGE KINDS DO NOT READ XMM0 AT ALL. -/
theorem sha_msg_ignores_xmm0 (k : ShaKind) (hk : k ≠ .rnds2) (a b x x' : BitVec 128) :
    shaApply k a b x = shaApply k a b x' := by
  cases k <;> simp_all [shaApply]

/-- σ0 and σ1 at bit 0 — the rotates wrap it to bits 25 and 14 (σ0) and 15 and 13 (σ1);
the shifts drop it — and σ0 at bit 3, the first bit `SHR 3` keeps. -/
theorem shaSig0_bit0 : shaSig0 1 = 0x02004000 := by decide
theorem shaSig1_bit0 : shaSig1 1 = 0x0000A000 := by decide
theorem shaSig0_bit3 : shaSig0 8 = 0x10020001 := by decide

/-- ⭐ FIPS 180-4's "abc" block through SHA256MSG2: SRC1 = W[i] + σ0(W[i+1]) + W[i+9]
(here W0 alone, every other of W1..W12 is zero), SRC2 = W12..W15 (W15 = 18H, the bit
length), gives W16..W19 = 61626380H, 000F0000H, 7DA86405H, 600003C6H — the values of the
textbook schedule (`hwprobe/mk_sha_rows.py`'s KAT, checked against the FIPS digest). -/
theorem sha256msg2_abc :
    shaApply .msg2 0x00000000000000000000000061626380 0x00000018000000000000000000000000 0 =
      0x600003c67da86405000f000061626380 := by decide

/-- ⭐ AND ROUNDS 0–1 FROM H0 THROUGH SHA256RNDS2: ABEF = 6A09E667 BB67AE85 510E527F
9B05688C, CDGH = 3C6EF372 A54FF53A 1F83D9AB 5BE0CD19, WK = K0+W0, K1+W1 — and the
result is the textbook's (a, b, e, f) after round 1. -/
theorem sha256rnds2_abc_r01 :
    shaApply .rnds2 0x3c6ef372a54ff53a1f83d9ab5be0cd19 0x6a09e667bb67ae85510e527f9b05688c
      0x000000000000000071374491a3ec9318 = 0x5a6ad9ad5d6aebcd78ce7989fa2a4622 := by decide

end V2

end X86
