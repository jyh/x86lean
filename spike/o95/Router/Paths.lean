/-
# Router.Paths — the repaired router's MACHINE-LEVEL exit relation, ∀ states (O95 step 3, layer 1).
Written private; published 2026-11-01 (SPIKE-PLAN.md).

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


/-! The shared prefix of the four later paths: past the length guard, `rax` loaded, the magic compared. -/
theorem prefix_magic (h : Live s) (hrip : s.rip = 0x1000) (hge : ¬ (s.regs.get .rsi).toNat < 24) :
    Live (runP repaired 5 s) ∧ (runP repaired 5 s).mem = s.mem ∧
    (runP repaired 5 s).rip = (if Cc.eval .ne (Flags.sub .d (Value.trunc .d (s.mem.readSize .d (s.regs.get .rdi)))
                (Value.trunc .d 0x4D534731) s.flags) then 0x1041 else 0x100f) ∧
    (runP repaired 5 s).regs = s.regs.set .rax (Value.trunc .d (s.mem.readSize .d (s.regs.get .rdi))) := by
  simp only [runP_succ, runP_zero]
  obtain ⟨l1, r1, m1, g1, f1⟩ := A1000 h hrip
  obtain ⟨l2, r2, m2, g2, f2⟩ := jcc_at (tk := 0x1040) (nt := 0x1006) l1 r1 rfl rfl rfl (by decide)
  have hb : Cc.eval .b (stepP repaired s).flags = false := by
    rw [f1, cc_b_of_sub]; simpa [Value.uval] using hge
  rw [hb] at r2; simp only [Bool.false_eq_true, if_false] at r2
  obtain ⟨l3, r3, m3, f3, g3⟩ := A1006 l2 r2
  obtain ⟨l4, r4, m4, g4, f4⟩ := A1008 l3 r3
  obtain ⟨l5, r5, m5, g5, f5⟩ := jcc_at (tk := 0x1041) (nt := 0x100f) l4 r4 rfl rfl rfl (by decide)
  refine ⟨l5, by rw [m5, m4, m3, m2, m1], ?_, by rw [g5, g4, g3, m2, m1, g2, g1]⟩
  rw [r5, f4, g3, Regs.get_set_same, m2, m1, g2, g1, cc_ne_of_sub, cc_ne_of_sub, Value.trunc_trunc]

theorem path_unauth_magic (h : Live s) (hrip : s.rip = 0x1000) (hge : ¬ (s.regs.get .rsi).toNat < 24)
    (hm : Cc.eval .ne (Flags.sub .d (Value.trunc .d (s.mem.readSize .d (s.regs.get .rdi)))
            (Value.trunc .d 0x4D534731) s.flags) = true) :
    (runP repaired 6 s).stopped = true ∧ (runP repaired 6 s).rip = 0x1041 ∧ (runP repaired 6 s).mem = s.mem := by
  obtain ⟨l5, m5, r5, -⟩ := prefix_magic h hrip hge
  simp only [runP_succ, runP_zero] at l5 m5 r5 ⊢
  rw [hm] at r5; simp only [if_true] at r5
  obtain ⟨t1, t2, t3, -⟩ := Aoff l5 r5 rfl
  exact ⟨t1, t2, by rw [t3, m5]⟩

/-- The middle: past the magic, `rcx`/`r8`/`r9` loaded, the ACL bit tested. -/
theorem prefix_acl (h : Live s) (hrip : s.rip = 0x1000) (hge : ¬ (s.regs.get .rsi).toNat < 24)
    (hm : Cc.eval .ne (Flags.sub .d (Value.trunc .d (s.mem.readSize .d (s.regs.get .rdi)))
            (Value.trunc .d 0x4D534731) s.flags) = false)
    (hcan : canonical (aclByteA s) = true) :
    Live (runP repaired 10 s) ∧ (runP repaired 10 s).mem = s.mem ∧
    (runP repaired 10 s).rip = (if aclBit s then 0x1024 else 0x1041) ∧
    (runP repaired 10 s).regs = ((((s.regs.set .rax (Value.trunc .d (s.mem.readSize .d (s.regs.get .rdi)))).set .rcx (sender s)).set
      .r8 (topic s)).set .r9 0x301d) := by
  obtain ⟨l5, m5, r5, g5⟩ := prefix_magic h hrip hge
  simp only [runP_succ, runP_zero] at l5 m5 r5 g5 ⊢
  rw [hm] at r5; simp only [Bool.false_eq_true, if_false] at r5
  obtain ⟨l6, r6, m6, f6, g6⟩ := A100f l5 r5
  obtain ⟨l7, r7, m7, f7, g7⟩ := A1012 l6 r6
  obtain ⟨l8, r8, m8, f8, g8⟩ := A1016 l7 r7
  have hregs8 : (stepP repaired (stepP repaired (stepP repaired (runP repaired 5 s)))).regs =
      ((((s.regs.set .rax (Value.trunc .d (s.mem.readSize .d (s.regs.get .rdi)))).set .rcx (sender s)).set
        .r8 (topic s)).set .r9 0x301d) := by
    simp only [runP_succ, runP_zero]
    rw [g8, g7, g6, g5, m6, m5]
    simp [sender, topic, W, Regs.get_set_ne]
  simp only [runP_succ, runP_zero] at hregs8
  have hba : bitStringByte (stepP repaired (stepP repaired (stepP repaired (runP repaired 5 s)))) .q
      { base := some .r9, index := some .rcx, scale := .s8 } .r8 false 0x1022 = aclByteA s := by
    simp only [runP_succ, runP_zero]
    simp [bitStringByte, Ea.addr, Ea.offset, Scale.toVal, Cpu.getReg, hregs8, aclByteA, Regs.get_set_ne]
  simp only [runP_succ, runP_zero] at hba
  obtain ⟨l9, r9, m9, g9, f9⟩ := A101d l8 r8 (by rw [hba]; exact hcan)
  obtain ⟨l10, r10, m10, g10, f10⟩ := jcc_at (tk := 0x1041) (nt := 0x1024) l9 r9 rfl rfl rfl (by decide)
  have hcf : Cc.eval .ae (stepP repaired (stepP repaired (stepP repaired (stepP repaired
      (stepP repaired (stepP repaired (stepP repaired (stepP repaired (stepP repaired s))))))))).flags = !aclBit s := by
    simp only [Cc.eval, f9, hba, m8, m7, m6, m5, aclBit, Cpu.getReg, hregs8]
    simp [Regs.get_set_ne]
  refine ⟨l10, by rw [m10, m9, m8, m7, m6, m5], ?_, by rw [g10, g9, hregs8]⟩
  rw [r10, hcf]
  cases aclBit s <;> rfl

theorem path_unauth_acl (h : Live s) (hrip : s.rip = 0x1000) (hge : ¬ (s.regs.get .rsi).toNat < 24)
    (hm : Cc.eval .ne (Flags.sub .d (Value.trunc .d (s.mem.readSize .d (s.regs.get .rdi)))
            (Value.trunc .d 0x4D534731) s.flags) = false)
    (hcan : canonical (aclByteA s) = true) (hacl : aclBit s = false) :
    (runP repaired 11 s).stopped = true ∧ (runP repaired 11 s).rip = 0x1041 ∧ (runP repaired 11 s).mem = s.mem := by
  obtain ⟨l10, m10, r10, -⟩ := prefix_acl h hrip hge hm hcan
  simp only [runP_succ, runP_zero] at l10 m10 r10 ⊢
  rw [hacl] at r10; simp only [Bool.false_eq_true, if_false] at r10
  obtain ⟨t1, t2, t3, -⟩ := Aoff l10 r10 rfl
  exact ⟨t1, t2, by rw [t3, m10]⟩

/-- The bucket test: `cmpl $0, cell` then `jle drop_rate_limited`. -/
theorem prefix_rate (h : Live s) (hrip : s.rip = 0x1000) (hge : ¬ (s.regs.get .rsi).toNat < 24)
    (hm : Cc.eval .ne (Flags.sub .d (Value.trunc .d (s.mem.readSize .d (s.regs.get .rdi)))
            (Value.trunc .d 0x4D534731) s.flags) = false)
    (hcan : canonical (aclByteA s) = true) (hacl : aclBit s = true) :
    Live (runP repaired 12 s) ∧ (runP repaired 12 s).mem = s.mem ∧
    (runP repaired 12 s).rip = (if Cc.eval .le (Flags.sub .d (tok s) (Value.trunc .d 0) s.flags) then 0x1042 else 0x102e) ∧
    (runP repaired 12 s).regs = ((((s.regs.set .rax (Value.trunc .d (s.mem.readSize .d (s.regs.get .rdi)))).set .rcx (sender s)).set
      .r8 (topic s)).set .r9 0x301d) := by
  obtain ⟨l10, m10, r10, g10⟩ := prefix_acl h hrip hge hm hcan
  simp only [runP_succ, runP_zero] at l10 m10 r10 g10 ⊢
  rw [hacl] at r10; simp only [if_true] at r10
  obtain ⟨l11, r11, m11, g11, f11⟩ := A1024 l10 r10
  obtain ⟨l12, r12, m12, g12, f12⟩ := jcc_at (tk := 0x1042) (nt := 0x102e) l11 r11 rfl rfl rfl (by decide)
  refine ⟨l12, by rw [m12, m11, m10], ?_, by rw [g12, g11, g10]⟩
  rw [r12, f11, cc_le_of_sub, cc_le_of_sub, m10, g10]
  simp [tok, cellA, sender, W, Regs.get_set_ne]

theorem path_rate_limited (h : Live s) (hrip : s.rip = 0x1000) (hge : ¬ (s.regs.get .rsi).toNat < 24)
    (hm : Cc.eval .ne (Flags.sub .d (Value.trunc .d (s.mem.readSize .d (s.regs.get .rdi)))
            (Value.trunc .d 0x4D534731) s.flags) = false)
    (hcan : canonical (aclByteA s) = true) (hacl : aclBit s = true)
    (hle : Cc.eval .le (Flags.sub .d (tok s) (Value.trunc .d 0) s.flags) = true) :
    (runP repaired 13 s).stopped = true ∧ (runP repaired 13 s).rip = 0x1042 ∧ (runP repaired 13 s).mem = s.mem := by
  obtain ⟨l12, m12, r12, -⟩ := prefix_rate h hrip hge hm hcan hacl
  simp only [runP_succ, runP_zero] at l12 m12 r12 ⊢
  rw [hle] at r12; simp only [if_true] at r12
  obtain ⟨t1, t2, t3, -⟩ := Aoff l12 r12 rfl
  exact ⟨t1, t2, by rw [t3, m12]⟩

/-- emit_slice: I6's OK exit — rax = b0 + 24, rsi = len − 24, rdx kept, memory = one cell written. -/
theorem path_ok (h : Live s) (hrip : s.rip = 0x1000) (hge : ¬ (s.regs.get .rsi).toNat < 24)
    (hm : Cc.eval .ne (Flags.sub .d (Value.trunc .d (s.mem.readSize .d (s.regs.get .rdi)))
            (Value.trunc .d 0x4D534731) s.flags) = false)
    (hcan : canonical (aclByteA s) = true) (hacl : aclBit s = true)
    (hle : Cc.eval .le (Flags.sub .d (tok s) (Value.trunc .d 0) s.flags) = false) :
    let t := runP repaired 17 s
    t.stopped = true ∧ t.rip = 0x1043 ∧ t.regs.get .rax = s.regs.get .rdi + 24 ∧
    t.regs.get .rsi = s.regs.get .rsi - 24 ∧ t.regs.get .rdx = s.regs.get .rdx ∧
    t.mem = s.mem.writeSize .d (cellA s) (Flags.subResult .d (tok s) (Value.trunc .d 1)) := by
  intro t
  obtain ⟨l12, m12, r12, g12⟩ := prefix_rate h hrip hge hm hcan hacl
  simp only [t, runP_succ, runP_zero] at l12 m12 r12 g12 ⊢
  rw [hle] at r12; simp only [Bool.false_eq_true, if_false] at r12
  obtain ⟨l13, r13, g13, m13⟩ := A102e l12 r12
  obtain ⟨l14, r14, m14, g14⟩ := A1036 l13 r13
  obtain ⟨l15, r15, m15, g15⟩ := A103a l14 r14
  obtain ⟨l16, r16, m16, g16⟩ := A103e l15 r15
  obtain ⟨t1, t2, t3, t4⟩ := Aoff l16 r16 rfl
  refine ⟨t1, t2, ?_, ?_, ?_, ?_⟩
  · rw [t4, g16, g15, g14, g13, g12]; simp [Regs.get_set_ne]
  · rw [t4, g16, g15, g14, g13, g12]; simp [Regs.get_set_ne]
  · rw [t4, g16, g15, g14, g13, g12]; simp [Regs.get_set_ne]
  · rw [t3, m16, m15, m14, m13, g12, m12]
    simp [tok, cellA, sender, W, Regs.get_set_ne]

end Router
