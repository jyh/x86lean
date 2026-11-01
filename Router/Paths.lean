/-
# Router.Paths — the repaired router's MACHINE-LEVEL exit relation, ∀ states (O95 step 3, layer 1).
PRIVATE (SPIKE-PLAN.md).

Each instruction address gets one lemma stating what `stepP repaired` does there, as PROJECTION facts (liveness,
rip, memory, flags, registers). A path is those lemmas chained over named intermediate states, so no proof ever
reduces a nested record. The five paths are the five exits: drop_truncated (3 steps), drop_unauthorized by the
magic (6) or by the ACL bit (11), drop_rate_limited (13), and emit_slice (17).
-/
import Router.Steps

namespace Router
open X86

/-! ## The quantities the router reads, named from the START state. -/
def W (s : Cpu) (k : BitVec 64) : Val := s.mem.readSize .d (s.regs.get .rdi + k)
def sender (s : Cpu) : Val := Value.trunc .d (W s 4)
def topic (s : Cpu) : Val := Value.trunc .d (W s 8)
def cellA (s : Cpu) : BitVec 64 := s.regs.get .rdx + sender s * 4 + 0x3000
def aclByteA (s : Cpu) : BitVec 64 := (0x301d + sender s * 8) + (Value.sext .q (topic s)).sshiftRight 3
def aclBit (s : Cpu) : Bool := (s.mem.readSize .b (aclByteA s)).getLsbD ((topic s).toNat % 8)
def tok (s : Cpu) : Val := s.mem.readSize .d (cellA s)

/-! ## Condition-code bridges for `cmp` (the pack carries `.b`/`.ae` only). Definitional. -/
@[simp] theorem cc_ne_of_sub (sz : Size) (a b : Val) (f : Flags) :
    Cc.eval .ne (Flags.sub sz a b f) = !Value.isZero sz (Flags.subResult sz a b) := rfl
@[simp] theorem cc_le_of_sub (sz : Size) (a b : Val) (f : Flags) :
    Cc.eval .le (Flags.sub sz a b f) =
      (Value.isZero sz (Flags.subResult sz a b) ||
        (Value.msb sz (Flags.subResult sz a b) != Flags.subOF sz a b (Flags.subResult sz a b))) := rfl

variable {s : Cpu}

/-! ## The sixteen addresses, and the stop. -/
theorem A1000 (h : Live s) (hrip : s.rip = 0x1000) :
    Live (stepP repaired s) ∧ (stepP repaired s).rip = 0x1004 ∧ (stepP repaired s).mem = s.mem ∧
    (stepP repaired s).regs = s.regs ∧
    (stepP repaired s).flags = Flags.sub .q (s.regs.get .rsi) 24 s.flags := by
  rw [stepP_eq h hrip rfl, step_cmp_reg_imm _ _ _ h]
  simp [hrip, h, Cpu.getReg]

theorem jcc_at {a : BitVec 64} {c : Cc} {d : Val} {l : Nat} {tk nt : BitVec 64} (h : Live s)
    (hrip : s.rip = a) (hat : repaired.at? a = some ⟨.jcc c d, l⟩)
    (htk : a + BitVec.ofNat 64 l + d = tk) (hnt : a + BitVec.ofNat 64 l = nt) (hc : canonical tk = true) :
    Live (stepP repaired s) ∧
    (stepP repaired s).rip = (if c.eval s.flags then tk else nt) ∧ (stepP repaired s).mem = s.mem ∧
    (stepP repaired s).regs = s.regs ∧ (stepP repaired s).flags = s.flags := by
  subst htk hnt
  rw [stepP_eq h hrip hat, step_jcc _ _ h (by intro _; rw [hrip]; exact hc)]
  simp [hrip, h]

theorem A1006 (h : Live s) (hrip : s.rip = 0x1006) :
    Live (stepP repaired s) ∧ (stepP repaired s).rip = 0x1008 ∧ (stepP repaired s).mem = s.mem ∧
    (stepP repaired s).flags = s.flags ∧
    (stepP repaired s).regs = s.regs.set .rax (Value.trunc .d (s.mem.readSize .d (s.regs.get .rdi))) := by
  rw [stepP_eq h hrip rfl, step_mov_reg_mem _ _ _ h rfl]
  simp [hrip, h, Ea.addr, Ea.offset, Value.writeView]

theorem A1008 (h : Live s) (hrip : s.rip = 0x1008) :
    Live (stepP repaired s) ∧ (stepP repaired s).rip = 0x100d ∧ (stepP repaired s).mem = s.mem ∧
    (stepP repaired s).regs = s.regs ∧
    (stepP repaired s).flags = Flags.sub .d (Value.trunc .d (s.regs.get .rax)) (Value.trunc .d 0x4D534731) s.flags := by
  rw [stepP_eq h hrip rfl, step_cmp_reg_imm _ _ _ h]
  simp [hrip, h, Cpu.getReg]

theorem A100f (h : Live s) (hrip : s.rip = 0x100f) :
    Live (stepP repaired s) ∧ (stepP repaired s).rip = 0x1012 ∧ (stepP repaired s).mem = s.mem ∧
    (stepP repaired s).flags = s.flags ∧
    (stepP repaired s).regs = s.regs.set .rcx (Value.trunc .d (s.mem.readSize .d (s.regs.get .rdi + 4))) := by
  rw [stepP_eq h hrip rfl, step_mov_reg_mem _ _ _ h rfl]
  simp [hrip, h, Ea.addr, Ea.offset, Value.writeView]

theorem A1012 (h : Live s) (hrip : s.rip = 0x1012) :
    Live (stepP repaired s) ∧ (stepP repaired s).rip = 0x1016 ∧ (stepP repaired s).mem = s.mem ∧
    (stepP repaired s).flags = s.flags ∧
    (stepP repaired s).regs = s.regs.set .r8 (Value.trunc .d (s.mem.readSize .d (s.regs.get .rdi + 8))) := by
  rw [stepP_eq h hrip rfl, step_mov_reg_mem _ _ _ h rfl]
  simp [hrip, h, Ea.addr, Ea.offset, Value.writeView]

theorem A1016 (h : Live s) (hrip : s.rip = 0x1016) :
    Live (stepP repaired s) ∧ (stepP repaired s).rip = 0x101d ∧ (stepP repaired s).mem = s.mem ∧
    (stepP repaired s).flags = s.flags ∧ (stepP repaired s).regs = s.regs.set .r9 0x301d := by
  rw [stepP_eq h hrip rfl, step_lea _ _ _ h rfl]
  simp [hrip, h, Ea.offset, Value.writeView]

/-- `bt %r8, 0(%r9,%rcx,8)`: CF is the bit, nothing else the router reads moves. The canonicality of the
bit-string byte address is a hypothesis (the model halts on a non-canonical one). -/
theorem A101d (h : Live s) (hrip : s.rip = 0x101d)
    (hcan : canonical (bitStringByte s .q { base := some .r9, index := some .rcx, scale := .s8 } .r8 false 0x1022)
      = true) :
    Live (stepP repaired s) ∧ (stepP repaired s).rip = 0x1022 ∧ (stepP repaired s).mem = s.mem ∧
    (stepP repaired s).regs = s.regs ∧
    (stepP repaired s).flags.cf =
      (s.mem.readSize .b (bitStringByte s .q { base := some .r9, index := some .rcx, scale := .s8 } .r8 false 0x1022)).getLsbD
        ((s.getReg .q .r8).toNat % 8) := by
  have hc' := hcan
  simp only [show (0x1022 : BitVec 64) = 4130#64 from rfl] at hc'
  rw [stepP_eq h hrip rfl]
  simp [step, stopped_of_live h, hrip, Cpu.readMem, Cpu.setFlags, Cpu.setRip, Cpu.undefBit, h] at hc' ⊢
  simp [hc', Cpu.halt]

theorem A1024 (h : Live s) (hrip : s.rip = 0x1024) :
    Live (stepP repaired s) ∧ (stepP repaired s).rip = 0x102c ∧ (stepP repaired s).mem = s.mem ∧
    (stepP repaired s).regs = s.regs ∧
    (stepP repaired s).flags = Flags.sub .d
      (s.mem.readSize .d (s.regs.get .rdx + s.regs.get .rcx * 4 + 0x3000)) (Value.trunc .d 0) s.flags := by
  rw [stepP_eq h hrip rfl, step_cmp_mem_imm _ _ _ h rfl]
  simp [hrip, h, Ea.addr, Ea.offset, Scale.toVal]

theorem A102e (h : Live s) (hrip : s.rip = 0x102e) :
    Live (stepP repaired s) ∧ (stepP repaired s).rip = 0x1036 ∧ (stepP repaired s).regs = s.regs ∧
    (stepP repaired s).mem = s.mem.writeSize .d (s.regs.get .rdx + s.regs.get .rcx * 4 + 0x3000)
      (Flags.subResult .d (s.mem.readSize .d (s.regs.get .rdx + s.regs.get .rcx * 4 + 0x3000)) (Value.trunc .d 1)) := by
  rw [stepP_eq h hrip rfl, step_sub_mem_imm _ _ _ h rfl]
  simp [hrip, h, Ea.addr, Ea.offset, Scale.toVal]

theorem A1036 (h : Live s) (hrip : s.rip = 0x1036) :
    Live (stepP repaired s) ∧ (stepP repaired s).rip = 0x103a ∧ (stepP repaired s).mem = s.mem ∧
    (stepP repaired s).regs = s.regs.set .rax (s.regs.get .rdi + 24) := by
  rw [stepP_eq h hrip rfl, step_lea _ _ _ h rfl]
  simp [hrip, h, Ea.offset, Value.writeView]

theorem A103a (h : Live s) (hrip : s.rip = 0x103a) :
    Live (stepP repaired s) ∧ (stepP repaired s).rip = 0x103e ∧ (stepP repaired s).mem = s.mem ∧
    (stepP repaired s).regs = s.regs.set .rsi (s.regs.get .rsi - 24) := by
  rw [stepP_eq h hrip rfl, step_sub_reg_imm _ _ _ h]
  simp [hrip, h, Cpu.getReg, Value.writeView, Flags.subResult]

theorem A103e (h : Live s) (hrip : s.rip = 0x103e) :
    Live (stepP repaired s) ∧ (stepP repaired s).rip = 0x1043 ∧ (stepP repaired s).mem = s.mem ∧
    (stepP repaired s).regs = s.regs := by
  rw [stepP_eq h hrip rfl, step_jmp_rel _ h (by rw [hrip]; decide)]
  simp [hrip, h]

/-- At an exit label the program defines nothing, so the next step STOPS, moving nothing the relation reads. -/
theorem Aoff {a : BitVec 64} (h : Live s) (hrip : s.rip = a) (hat : repaired.at? a = none) :
    (stepP repaired s).stopped = true ∧ (stepP repaired s).rip = a ∧ (stepP repaired s).mem = s.mem ∧
    (stepP repaired s).regs = s.regs := by
  rw [stepP_eq_off h hrip hat]
  simp [Cpu.halt, h, Cpu.stopped, hrip]

/-! ## The five paths. -/

theorem path_truncated (h : Live s) (hrip : s.rip = 0x1000) (hlt : (s.regs.get .rsi).toNat < 24) :
    (runP repaired 3 s).stopped = true ∧ (runP repaired 3 s).rip = 0x1040 ∧ (runP repaired 3 s).mem = s.mem := by
  simp only [runP_succ, runP_zero]
  obtain ⟨l1, r1, m1, g1, f1⟩ := A1000 h hrip
  obtain ⟨l2, r2, m2, g2, f2⟩ := jcc_at (tk := 0x1040) (nt := 0x1006) l1 r1 rfl rfl rfl (by decide)
  have hb : Cc.eval .b (stepP repaired s).flags = true := by
    rw [f1, cc_b_of_sub]; simpa [Value.uval] using hlt
  rw [hb] at r2; simp only [if_true] at r2
  obtain ⟨t1, t2, t3, -⟩ := Aoff l2 r2 rfl
  exact ⟨t1, t2, by rw [t3, m2, m1]⟩

end Router
