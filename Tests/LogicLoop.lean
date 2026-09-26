/-
# Tests.LogicLoop — R-LOOP: a loop whose pass is four steps or five (D304, moved here by D311)

Its own module because the ms delta gate refused the step that put it inside `Tests.Logic`
(27.0 → 88.6 ms against a 6.3 ms step budget): a new module is judged once against a ceiling measured
on its own machine, and the refusal is a design hint that one test module should not grow per witness.

LANE. Personal lane, public sources only.
-/
import Tests.Logic

namespace Tests.Logic
open X86

/-! ## R-LOOP — a body whose LENGTH depends on the data (`docs/P2-LOGIC-DESIGN.md` §4.1)

```
  0x1000:  L: cmp  rax, rbx      ; 3 bytes
  0x1003:     jae  SKIP          ; 2 bytes, rel8 = +3   (0x1005 + 3 = 0x1008)
  0x1005:     inc  rax           ; 3 bytes
  0x1008:  SKIP: dec rcx         ; 3 bytes
  0x100B:     jne  L             ; 2 bytes, rel8 = -13  (0x100D - 13 = 0x1000)
  0x100D:  (outside the program — the exit)
```
A pass is FOUR steps when `jae` is taken and FIVE when it is not. `rax` climbs toward `rbx` on the
untaken arm, so ONE run mixes both lengths, and how many of each depends on the data. R1's `7 * n` shape cannot state this loop; `Spec.loop` needs no count. -/

def clampLoop : Program := { code := [
  (0x1000, ⟨.bin .cmp .q (.reg .rax) (.reg .rbx), 3⟩),
  (0x1003, ⟨.jcc .ae (BitVec.ofInt 64 3), 2⟩),
  (0x1005, ⟨.un .inc .q (.reg .rax), 3⟩),
  (0x1008, ⟨.un .dec .q (.reg .rcx), 3⟩),
  (0x100B, ⟨.jcc .ne (BitVec.ofInt 64 (-13)), 2⟩)] }

def CHead (s u : Cpu) : Prop := u.ms = none ∧ u.rip = 0x1000 ∧ u.mem = s.mem
def CDone (s t : Cpu) : Prop :=
  t.stopped = true ∧ t.rip = 0x100D ∧ t.regs.get .rcx = 0 ∧ t.mem = s.mem

/-- The conditional half: from the head, SOME number of steps (two or three — the proof never says
which to its caller) reaches `SKIP` with `rcx` and memory untouched. -/
theorem to_skip (u : Cpu) (hms : u.ms = none) (hrip : u.rip = 0x1000) :
    ∃ k, let m := runP clampLoop k u
      m.ms = none ∧ m.rip = 0x1008 ∧ m.regs.get .rcx = u.regs.get .rcx ∧ m.mem = u.mem := by
  have hst : ¬ u.stopped = true := by simp [Cpu.stopped, hms]
  have e1 : stepP clampLoop u = { u with
      flags := Flags.sub .q (u.getReg .q .rax) (u.getReg .q .rbx) u.flags,
      rip := 0x1003 } := by
    rw [stepP_at hst (by rw [hrip]; rfl), step_cmp_reg_reg .q .rax .rbx hms, hrip]; rfl
  generalize hu1 : ({ u with
      flags := Flags.sub .q (u.getReg .q .rax) (u.getReg .q .rbx) u.flags,
      rip := 0x1003 } : Cpu) = u1 at e1
  have h1ms : u1.ms = none := by rw [← hu1]; exact hms
  have h1st : ¬ u1.stopped = true := by simp [Cpu.stopped, h1ms]
  have h1rip : u1.rip = 0x1003 := by rw [← hu1]
  have e2 := stepP_at h1st (show clampLoop.at? u1.rip = _ by rw [h1rip]; rfl)
  rw [step_jcc .ae _ h1ms (fun _ => by rw [h1rip]; decide), h1rip] at e2
  by_cases hc : Cc.eval .ae u1.flags = true
  · -- taken: two steps
    refine ⟨2, ?_⟩
    simp only [runP_succ, runP_zero, e1, e2, if_pos hc]
    refine ⟨h1ms, by decide, ?_, ?_⟩ <;> rw [← hu1]
  · -- not taken: `inc rax`, three steps
    rw [if_neg hc] at e2
    have hu2ms : ({ u1 with rip := 0x1003 + BitVec.ofNat 64 2 } : Cpu).ms = none := h1ms
    have hu2st : ¬ ({ u1 with rip := 0x1003 + BitVec.ofNat 64 2 } : Cpu).stopped = true := by
      simp [Cpu.stopped, h1ms]
    have e3 := stepP_at hu2st (by rfl : clampLoop.at? (0x1003 + BitVec.ofNat 64 2) = _)
    rw [step_inc_reg .q .rax hu2ms] at e3
    refine ⟨3, ?_⟩
    simp only [runP_succ, runP_zero, e1, e2, e3]
    refine ⟨h1ms, by decide, ?_, ?_⟩
    · show (u1.regs.set .rax _).get .rcx = _
      rw [Regs.get_set_ne _ _ _ _ (by decide), ← hu1]
    · rw [← hu1]

/-- The state after `dec rcx` at `SKIP`. -/
def cAfterDec (m : Cpu) : Cpu :=
  { m with regs := m.regs.set .rcx (m.regs.get .rcx - 1),
           flags := Flags.dec .q (m.regs.get .rcx) m.flags,
           rip := 0x100B }

/-- The state after `jne L`: back at the head if the decremented counter is non-zero. -/
def cAfterJne (m : Cpu) : Cpu :=
  { cAfterDec m with rip := if m.regs.get .rcx - 1 = 0 then 0x100D else 0x1000 }

theorem cstep_dec (m : Cpu) (hms : m.ms = none) (hrip : m.rip = 0x1008) :
    stepP clampLoop m = cAfterDec m := by
  have hst : ¬ m.stopped = true := by simp [Cpu.stopped, hms]
  rw [stepP_at hst (by rw [hrip]; rfl), step_dec_reg .q .rcx hms]
  simp [cAfterDec, hrip, Value.writeView, Flags.subResult, Cpu.getReg]

theorem cstep_jne (m : Cpu) (hms : m.ms = none) :
    stepP clampLoop (cAfterDec m) = cAfterJne m := by
  have hms' : (cAfterDec m).ms = none := hms
  have hst : ¬ (cAfterDec m).stopped = true := by simp [Cpu.stopped, hms']
  have hrip : (cAfterDec m).rip = 0x100B := rfl
  rw [stepP_at hst (by rfl), step_jcc .ne _ hms' (fun _ => by rw [hrip]; decide)]
  have hc : Cc.eval .ne (cAfterDec m).flags = !(m.regs.get .rcx - 1 == 0) := by
    show Cc.eval .ne (Flags.dec .q (m.regs.get .rcx) m.flags) = _
    rw [cc_ne_of_dec]; simp [Value.isZero, Flags.subResult]
  simp only [cAfterJne]
  congr 1
  rw [hc, hrip]
  by_cases h : m.regs.get .rcx - 1 = 0
  · rw [if_pos h, h]; decide
  · rw [if_neg h, beq_false_of_ne h]; decide

theorem cstep_exit (m : Cpu) (hms : m.ms = none) (h : m.regs.get .rcx - 1 = 0) :
    stepP clampLoop (cAfterJne m) = (cAfterJne m).halt (.outsideProgram "no instruction at RIP") := by
  have hst : ¬ (cAfterJne m).stopped = true := by simp [Cpu.stopped, cAfterJne, cAfterDec, hms]
  have hrip : (cAfterJne m).rip = 0x100D := if_pos h
  exact stepP_off hst (by rw [hrip]; rfl)

theorem cAfterJne_rcx (m : Cpu) : (cAfterJne m).regs.get .rcx = m.regs.get .rcx - 1 := by
  show (m.regs.set .rcx (m.regs.get .rcx - 1)).get .rcx = _
  exact Regs.get_set_same _ _ _

/-- ⭐⭐⭐ **R-LOOP's WITNESS.** From EVERY live state at `L` the loop reaches its exit with
`rcx = 0` and memory unchanged — though each pass is four steps or five according to `rax` and
`rbx`, and the proof never learns which. The body's fuel is `k + 2` or `k + 3`, where `k` is
whatever `to_skip` returned. -/
theorem clampLoop_terminates :
    Spec clampLoop (fun s => s.ms = none ∧ s.rip = 0x1000) CDone := by
  refine Spec.loop CHead (fun u => (u.regs.get .rcx - 1).toNat) ?_ ?_
  · rintro s ⟨h1, h2⟩; exact ⟨h1, h2, rfl⟩
  · rintro s u _ ⟨hms, hrip, hmem⟩
    obtain ⟨k, hkms, hkrip, hkrcx, hkmem⟩ := to_skip u hms hrip
    generalize hm : runP clampLoop k u = m at hkms hkrip hkrcx hkmem
    by_cases hc : m.regs.get .rcx - 1 = 0
    · refine ⟨k + 3, Or.inl ?_⟩
      rw [runP_add, hm]
      simp only [runP_succ, runP_zero, cstep_dec m hkms hkrip, cstep_jne m hkms,
        cstep_exit m hkms hc]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [Cpu.halt, Cpu.stopped, cAfterJne, cAfterDec, hkms]
      · rw [halt_rip]; exact if_pos hc
      · rw [halt_regs, cAfterJne_rcx]; exact hc
      · rw [halt_mem]; exact hkmem.trans hmem
    · refine ⟨k + 2, Or.inr ⟨?_, ?_⟩⟩
      · rw [runP_add, hm]
        simp only [runP_succ, runP_zero, cstep_dec m hkms hkrip, cstep_jne m hkms]
        exact ⟨hkms, if_neg hc, hkmem.trans hmem⟩
      · rw [runP_add, hm]
        simp only [runP_succ, runP_zero, cstep_dec m hkms hkrip, cstep_jne m hkms]
        rw [cAfterJne_rcx, hkrcx]
        exact toNat_pred_lt _ (hkrcx ▸ hc)

/-! ### R-LOOP's nonvacuity: BOTH body lengths really occur in one run

`rax = 0`, `rbx = 1`, `rcx = 2`: the first pass does not take `jae` (0 < 1) and increments `rax`; the
second takes it (1 ≥ 1). So the concrete run mixes a 5-step and a 4-step pass: 5 + 4 = 9 steps, plus the
halting one — and one step earlier it has not stopped. (Two passes, not four: D311 moved this section to
its own module and halved the control, whose `decide` runs were half of `Tests.Logic`'s kernel time.) -/

def cstart : Cpu :=
  Cpu.setReg (Cpu.setReg (Cpu.setReg { rip := 0x1000 } .q .rax 0) .q .rbx 1) .q .rcx 2

theorem cstart_meets_pre : cstart.ms = none ∧ cstart.rip = 0x1000 := by decide

theorem cstart_run_is_done : CDone cstart (runP clampLoop 10 cstart) :=
  ⟨by decide, by decide, by decide, rfl⟩

theorem cstart_not_done_early : (runP clampLoop 9 cstart).stopped = false := by decide

/-- …and `inc rax` ran exactly once: the not-taken arm was really exercised, and so was the taken
one (a run of only 5-step passes would stop at 11, not 10). -/
theorem cstart_took_both_arms : (runP clampLoop 10 cstart).regs.get .rax = 1 := by decide

end Tests.Logic
