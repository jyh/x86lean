/-
# Router.Steps — the effect equations the repaired router needs that x86lean's `X86/Theorems.lean` does not carry,
and the fetch/step plumbing for a ∀-state run of `repaired`. Written private; published 2026-11-01 (SPIKE-PLAN.md).

The x86lean pack has `cmp`/`sub` only for reg,reg. The router uses reg,imm (`cmpq $24,%rsi`, `subq $24,%rsi`,
`cmpl $M,%eax`), mem,imm (`cmpl $0,cell`, `subl $1,cell`) and the bit-string `bt` (mem, reg). Each is proved the
way the pack proves its own (`simp [step, h]`), in the same `{ s with … }` shape.
-/
import Router.Repaired

namespace Router
open X86

variable {s : Cpu} {len : Nat}

theorem step_cmp_reg_imm (sz : Size) (r : GPR) (v : Val) (h : Live s) :
    step ⟨.bin .cmp sz (.reg r) (.imm v), len⟩ s =
      { s with
        flags := Flags.sub sz (s.getReg sz r) (Value.trunc sz v) s.flags,
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, stopped_of_live h, wellFormed2, Operand.isMem, Cpu.readOperand, Cpu.setFlags, Cpu.setRip]

theorem step_sub_reg_imm (sz : Size) (r : GPR) (v : Val) (h : Live s) :
    step ⟨.bin .sub sz (.reg r) (.imm v), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView sz (s.regs.get r)
          (Flags.subResult sz (s.getReg sz r) (Value.trunc sz v))),
        flags := Flags.sub sz (s.getReg sz r) (Value.trunc sz v) s.flags,
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, stopped_of_live h, wellFormed2, Operand.isMem, Cpu.readOperand, Cpu.writeOperand, Cpu.setFlags, Cpu.setRip, Cpu.setReg, Cpu.getReg]

theorem step_cmp_mem_imm (sz : Size) (ea : Ea) (v : Val) (h : Live s) (hl : ea.lock = false) :
    step ⟨.bin .cmp sz (.mem ea) (.imm v), len⟩ s =
      { s with
        flags := Flags.sub sz (s.mem.readSize sz (ea.addr s (s.rip + BitVec.ofNat 64 len))) (Value.trunc sz v) s.flags,
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, stopped_of_live h, hl, wellFormed2, Operand.isMem, Cpu.readOperand, Cpu.readMem, Cpu.setFlags, Cpu.setRip]

theorem step_sub_mem_imm (sz : Size) (ea : Ea) (v : Val) (h : Live s) (hl : ea.lock = false) :
    step ⟨.bin .sub sz (.mem ea) (.imm v), len⟩ s =
      { s with
        mem := s.mem.writeSize sz (ea.addr s (s.rip + BitVec.ofNat 64 len))
          (Flags.subResult sz (s.mem.readSize sz (ea.addr s (s.rip + BitVec.ofNat 64 len))) (Value.trunc sz v)),
        flags := Flags.sub sz (s.mem.readSize sz (ea.addr s (s.rip + BitVec.ofNat 64 len))) (Value.trunc sz v) s.flags,
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, stopped_of_live h, hl, wellFormed2, Operand.isMem, Cpu.readOperand, Cpu.writeOperand, Cpu.readMem, Cpu.writeMem, Cpu.setFlags, Cpu.setRip] <;> rfl

/-- One program step from a live state at a defined address is that instruction's `step`. -/
theorem stepP_at {p : Program} {i : Instr} (h : Live s) (hat : p.at? s.rip = some i) :
    stepP p s = step i s := by
  simp [stepP, stopped_of_live h, hat]

/-- One program step from a live state at an UNDEFINED address stops the model and moves nothing else. -/
theorem stepP_off {p : Program} (h : Live s) (hat : p.at? s.rip = none) :
    stepP p s = s.halt (.outsideProgram "no instruction at RIP") := by
  simp [stepP, stopped_of_live h, hat]

/-- The step at a known address, with the address supplied as an equation so `at?` reduces on a literal. -/
theorem stepP_eq {p : Program} {i : Instr} {a : BitVec 64} (h : Live s) (hrip : s.rip = a)
    (hat : p.at? a = some i) : stepP p s = step i s := by
  simp [stepP, stopped_of_live h, hrip, hat]

theorem stepP_eq_off {p : Program} {a : BitVec 64} (h : Live s) (hrip : s.rip = a) (hat : p.at? a = none) :
    stepP p s = s.halt (.outsideProgram "no instruction at RIP") := by
  simp [stepP, stopped_of_live h, hrip, hat]

end Router
