/-
# Tests.Logic — the program logic's first witness: a loop that TERMINATES, for every count

`X86/Logic.lean`'s `Spec` is a total-correctness judgment. This file proves, through `Spec.loop`,
a statement no theorem in this repository could state before it: a counted loop entered with an
ARBITRARY 64-bit count reaches its exit, with the counter at zero and memory untouched.

`Tests/Program.lean`'s countdown shows termination only by `decide` at one start state and one
fuel (`runP_exits`, fuel 8, count 3). Here the count is universally quantified — **including 0**,
where `dec` wraps to 2^64 − 1 and the loop runs 2^64 passes — and no step count appears: the
variant `(rcx − 1).toNat` carries the whole termination argument.

LANE. Personal lane, public sources only.
-/
import X86

namespace Tests.Logic
open X86

/-! ## The routine

```
  0x1000:  L: dec rcx       ; 3 bytes (REX.W FF /1)
  0x1003:     jne L         ; 2 bytes, rel8 = -5  (next_rip 0x1005, 0x1005-5 = 0x1000)
  0x1005:  (outside the program — the routine's exit)
```
-/

def countdownN : Program := { code := [
  (0x1000, ⟨.un .dec .q (.reg .rcx), 3⟩),
  (0x1003, ⟨.jcc .ne (BitVec.ofInt 64 (-5)), 2⟩)] }

/-- The loop head, related to the start: live, at `L`, memory as the start left it. -/
def AtHead (s u : Cpu) : Prop := u.ms = none ∧ u.rip = 0x1000 ∧ u.mem = s.mem

/-- The exit, related to the start: stopped at the exit address, the counter at zero, and
memory exactly the start's. -/
def Done (s t : Cpu) : Prop :=
  t.stopped = true ∧ t.rip = 0x1005 ∧ t.regs.get .rcx = 0 ∧ t.mem = s.mem

/-- The state after `dec rcx` at the head. -/
def afterDec (u : Cpu) : Cpu :=
  { u with regs := u.regs.set .rcx (u.regs.get .rcx - 1),
           flags := Flags.dec .q (u.regs.get .rcx) u.flags,
           rip := 0x1003 }

/-- The state after `jne L`: back at the head if the decremented counter is non-zero. -/
def afterJne (u : Cpu) : Cpu :=
  { afterDec u with rip := if u.regs.get .rcx - 1 = 0 then 0x1005 else 0x1000 }

theorem step1 (u : Cpu) (hms : u.ms = none) (hrip : u.rip = 0x1000) :
    stepP countdownN u = afterDec u := by
  have hst : ¬ u.stopped = true := by simp [Cpu.stopped, hms]
  rw [stepP_at hst (by rw [hrip]; rfl), step_dec_reg .q .rcx hms]
  simp [afterDec, hrip, Value.writeView, Flags.subResult, Cpu.getReg]

theorem step2 (u : Cpu) (hms : u.ms = none) :
    stepP countdownN (afterDec u) = afterJne u := by
  have hms' : (afterDec u).ms = none := hms
  have hst : ¬ (afterDec u).stopped = true := by simp [Cpu.stopped, hms']
  have hrip : (afterDec u).rip = 0x1003 := rfl
  rw [stepP_at hst (by rfl), step_jcc .ne _ hms' (fun _ => by rw [hrip]; decide)]
  have hc : Cc.eval .ne (afterDec u).flags = !(u.regs.get .rcx - 1 == 0) := by
    show Cc.eval .ne (Flags.dec .q (u.regs.get .rcx) u.flags) = _
    rw [cc_ne_of_dec]; simp [Value.isZero, Flags.subResult]
  simp only [afterJne]
  congr 1
  rw [hc, hrip]
  by_cases h : u.regs.get .rcx - 1 = 0
  · rw [if_pos h, h]; decide
  · rw [if_neg h, beq_false_of_ne h]; decide

theorem step3 (u : Cpu) (hms : u.ms = none) (h : u.regs.get .rcx - 1 = 0) :
    stepP countdownN (afterJne u) = (afterJne u).halt (.outsideProgram "no instruction at RIP") := by
  have hst : ¬ (afterJne u).stopped = true := by simp [Cpu.stopped, afterJne, afterDec, hms]
  have hrip : (afterJne u).rip = 0x1005 := if_pos h
  exact stepP_off hst (by rw [hrip]; rfl)

/-- The counter after a pass is one lower — `Regs.get_set_same`, read through `afterJne`. -/
theorem afterJne_rcx (u : Cpu) : (afterJne u).regs.get .rcx = u.regs.get .rcx - 1 := by
  show (u.regs.set .rcx (u.regs.get .rcx - 1)).get .rcx = _
  exact Regs.get_set_same _ _ _

/-- One pass of the body from the head: taken, back at the head one lower; or fallen through,
and the third step halts at the exit. -/
theorem pass (s u : Cpu) (h : AtHead s u) :
    (u.regs.get .rcx - 1 ≠ 0 →
      AtHead s (runP countdownN 2 u) ∧ (runP countdownN 2 u).regs.get .rcx = u.regs.get .rcx - 1)
    ∧ (u.regs.get .rcx - 1 = 0 → Done s (runP countdownN 3 u)) := by
  obtain ⟨hms, hrip, hmem⟩ := h
  refine ⟨fun hne => ?_, fun heq => ?_⟩
  · simp only [runP_succ, runP_zero, step1 u hms hrip, step2 u hms]
    exact ⟨⟨hms, if_neg hne, hmem⟩, afterJne_rcx u⟩
  · simp only [runP_succ, runP_zero, step1 u hms hrip, step2 u hms, step3 u hms heq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Cpu.halt, Cpu.stopped, afterJne, afterDec, hms]
    · rw [halt_rip]; exact if_pos heq
    · rw [halt_regs, afterJne_rcx]; exact heq
    · rw [halt_mem]; exact hmem

/-- The variant falls: a non-zero `y` has `(y - 1).toNat < y.toNat`, wrap-free. -/
theorem toNat_pred_lt (y : BitVec 64) (hy : y ≠ 0) : (y - 1).toNat < y.toNat := by
  have h0 : y.toNat ≠ 0 := fun h => hy (BitVec.eq_of_toNat_eq (by simpa using h))
  have hlt := y.isLt
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_sub, h1]
  simp only [Nat.reducePow] at *
  omega

/-- ⭐⭐⭐ **THE WITNESS.** From EVERY live state at `L` — every count, every register file, every
memory — the loop reaches its exit with `rcx = 0` and memory unchanged. Proved by `Spec.loop`
with the variant `(rcx − 1).toNat`; no fuel is named. -/
theorem countdownN_terminates :
    Spec countdownN (fun s => s.ms = none ∧ s.rip = 0x1000) Done := by
  refine Spec.loop AtHead (fun u => (u.regs.get .rcx - 1).toNat) ?_ ?_
  · rintro s ⟨h1, h2⟩; exact ⟨h1, h2, rfl⟩
  · intro s u _ hI
    obtain ⟨hgo, hdone⟩ := pass s u hI
    by_cases hc : u.regs.get .rcx - 1 = 0
    · exact ⟨3, Or.inl (hdone hc)⟩
    · obtain ⟨hI', hr⟩ := hgo hc
      exact ⟨2, Or.inr ⟨hI', by simp only [hr]; exact toNat_pred_lt _ hc⟩⟩

/-! ## ⭐ NONVACUITY — the precondition is met, and the machine really does what `Done` says

⛔ A total-correctness theorem with an unsatisfiable precondition is vacuously true and no build
reports it. These pin a concrete start state that meets the precondition and a concrete run
that reaches exactly the state `Done` describes — computed by the kernel, independently of
`Spec.loop`. -/

def start3 : Cpu := Cpu.setReg { rip := 0x1000 } .q .rcx 3

/-- The precondition is satisfiable. -/
theorem start3_meets_pre : start3.ms = none ∧ start3.rip = 0x1000 := by decide

/-- Three passes of two steps plus the halting third: fuel 7 reaches `Done`. -/
theorem start3_run_is_done : Done start3 (runP countdownN 7 start3) :=
  ⟨by decide, by decide, by decide, rfl⟩

/-- …and one step earlier it had NOT stopped — so `Done` describes a run that did the work, not
a machine that halted at once. -/
theorem start3_not_done_early : (runP countdownN 6 start3).stopped = false := by decide

end Tests.Logic
