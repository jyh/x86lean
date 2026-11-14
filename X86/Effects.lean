/-
# X86.Effects — the instruction library a compiler lowers to (vir's C3 (a), STATUS-paris row 64)

vir's compiler object (`object-COMPILER/OBJECT-COMPILER.md` at vir a5edcc7, §3) asks x86lean for effect
equations in the `{ s with … }` form for: mov (sizes 8 and 64), movzx byte loads, lea, add, sub, and, or,
xor, shl, shr, cmp, test, jcc, jmp, call, ret, imul and setcc. Every one of those mnemonics has a row in
`docs/COVERAGE.md`, so this file adds PROOFS only and no differential work.

`X86/Theorems.lean` already proves most of the list. This file adds the ones it lacks (the census, by statement
shape, at master a370c1c):
- `stepP_of_at`: the lift from `step` to `stepP` at a fetched address, so a block proof needs one lemma rather
  than one lifted copy per form (`Program.lean` carries five such copies);
- `step_add_reg_op` (add r,imm · r,m · r,r with the high-8 destination); only `add r,r` existed;
- `step_test_reg_op` (test r,imm · r,m); only `test r,r` existed;
- `step_imulr` (imul r,r · r,m · r,r,imm · r,m,imm); only a refusal and a frame lemma existed;
- `step_setcc_reg` and `step_setcc_mem`; nothing existed.

⚠️ IMUL IS T-FRAME: SF, ZF, AF and PF are undefined after it (SDM Vol. 2A IMUL) and the model draws all four from
the undefined-bit oracle. The equation states those four draws, so a proof that branches on one of those flags
after an imul has to carry an oracle bit, and a compiler that wants a defined flag must not read one there.

LANE. Personal lane, public sources only. Every theorem here rests on the three standard axioms at most (the axiom
gate enumerates this module through `X86.lean`).
-/
import X86.Theorems
import X86.Program

namespace X86

variable {s : Cpu} {len : Nat}

-- The same local simp set `X86/Theorems.lean` declares (its line 47): `Live s` is `s.ms = none`, and the guard
-- in `step` reads `s.stopped`, so `stopped` must unfold for `h` to close the halted branch.
attribute [local simp] Cpu.stopped Cpu.readOperand Cpu.writeOperand Cpu.setReg

/-- **THE LIFT.** A live state whose `rip` fetches `i` steps by `step i`. A block proof composes per-instruction
equations through this one lemma. -/
theorem stepP_of_at {p : Program} {i : Instr} (hs : s.stopped = false) (hi : p.at? s.rip = some i) :
    stepP p s = step i s := by
  simp only [Cpu.stopped] at hs
  simp [stepP, hs, hi]

/-- **ADD r, op** (SDM Vol. 2A ADD): the `adc_reg_op` equation with no incoming carry. -/
theorem step_add_reg_op (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s)
    (hl : o.locked = false) :
    step ⟨.bin .add sz (.reg r h8) o, len⟩ s =
      { s with
        regs := s.regs.set r (if h8
          then Value.writeHigh8 (s.regs.get r)
            (Flags.addResult sz (s.getReg sz r h8)
              (s.readOperand sz (s.rip + BitVec.ofNat 64 len) o))
          else Value.writeView sz (s.regs.get r)
            (Flags.addResult sz (s.getReg sz r h8)
              (s.readOperand sz (s.rip + BitVec.ofNat 64 len) o))),
        flags := Flags.add sz (s.getReg sz r h8)
          (s.readOperand sz (s.rip + BitVec.ofNat 64 len) o) s.flags,
        rip := s.rip + BitVec.ofNat 64 len } := by
  cases h8 <;> cases o <;>
    simp [step, h, Cpu.getReg, hl, wellFormed2, Operand.isMem, Cpu.setFlags, Cpu.setRip] <;> simp_all

/-- **TEST r, op** (SDM Vol. 2A TEST): the flags of the AND, no register written, AF drawn (T-frame). -/
theorem step_test_reg_op (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s)
    (hl : o.locked = false) :
    step ⟨.bin .test sz (.reg r h8) o, len⟩ s =
      { s with
        flags := Flags.logic sz
          (Value.trunc sz (s.getReg sz r h8 &&&
            s.readOperand sz (s.rip + BitVec.ofNat 64 len) o))
          (s.oracle.bits s.oracle.cursor) s.flags,
        oracle := { s.oracle with cursor := s.oracle.cursor + 1 },
        rip := s.rip + BitVec.ofNat 64 len } := by
  cases h8 <;> cases o <;>
    simp [step, h, Cpu.getReg, hl, wellFormed2, Operand.isMem, Cpu.setFlags, Cpu.setRip, Cpu.undefBit,
      Oracle.draw] <;> simp_all

/-- **SETcc r8** (SDM Vol. 2A SETcc): the low byte of `r` is 1 when the condition holds and 0 otherwise. -/
theorem step_setcc_reg (c : Cc) (r : GPR) (h : Live s) :
    step ⟨.setcc c (.reg r), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView .b (s.regs.get r) (if c.eval s.flags then 1 else 0)),
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.writeOperand, Cpu.setReg, Cpu.setRip]

/-- **SETcc m8** (SDM Vol. 2A SETcc): one byte written at the effective address. -/
theorem step_setcc_mem (c : Cc) (ea : Ea) (h : Live s) (hl : ea.lock = false) :
    step ⟨.setcc c (.mem ea), len⟩ s =
      { s with
        mem := s.mem.writeSize .b (ea.addr s (s.rip + BitVec.ofNat 64 len)) (if c.eval s.flags then 1 else 0),
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, hl, Cpu.writeOperand, Cpu.writeMem, Cpu.setRip]

/-- **IMUL r, op[, imm]** (SDM Vol. 2A IMUL, the two- and three-operand forms, w/l/q): the low half of the
signed product into `dst`; CF = OF = the overflow; SF, ZF, AF, PF the four oracle draws, in that order. -/
theorem step_imulr (sz : Size) (dst : GPR) (src : Operand) (imm : Option Val) (h : Live s)
    (henc : imulrEncodable sz = true) (hl : src.locked = false) :
    step ⟨.imulr sz dst src imm, len⟩ s =
      let b := s.readOperand sz (s.rip + BitVec.ofNat 64 len) src
      let x := match imm with | none => s.getReg sz dst | some _ => b
      let y := match imm with | none => b | some i => Value.trunc sz i
      let c := s.oracle.cursor
      { s with
        regs := s.regs.set dst (Value.writeView sz (s.regs.get dst) (Value.imulPair sz x y).1),
        flags := Flags.mulFlags (Value.imulOverflow sz x y)
          (s.oracle.bits c) (s.oracle.bits (c + 1)) (s.oracle.bits (c + 2)) (s.oracle.bits (c + 3)) s.flags,
        oracle := { s.oracle with cursor := c + 4 },
        rip := s.rip + BitVec.ofNat 64 len } := by
  cases imm <;> cases src <;> simp_all [step, Cpu.undefBit, Oracle.draw, Cpu.setFlags, Cpu.setReg,
    Cpu.setRip, Nat.add_assoc]

end X86
