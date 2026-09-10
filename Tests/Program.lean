/-
# Tests.Program — the P2 proof interface, worked end to end on a routine with a LOOP

Council 2026-09-10 ruling ⑧: *"the proof interface that makes a twenty-instruction
routine provable in tens of lines, not thousands."*  This file is the measurement
of that claim on the first routine, and the nonvacuity evidence that the routine
it is about really executes.

⛔ **WHY THE NONVACUITY SECTION IS NOT OPTIONAL HERE.** A safety theorem of the
form "for all fuel `n`, nothing bad happens" is TRUE AND WORTHLESS about a
program that halts on step one — and the whole reason this file exists is that
the previous driver silently did the wrong thing.  So the trace is pinned by
kernel-checked theorems BEFORE the safety theorem is believed:
`X86.run` gives ONE pass and `X86.runP` gives THREE.

LANE. Personal lane, public sources only.
-/
import X86

namespace Tests
open X86

/-! ## The routine

```
  0x1000:  mov  ecx, 3      ; 5 bytes
  0x1005:  L: dec ecx       ; 2 bytes
  0x1007:  jne  L           ; 2 bytes, rel8 = -4  (next_rip 0x1009, 0x1009-4 = 0x1005)
  0x1009:  (outside the program — the routine's exit)
```
-/

def countdown : Program := { code := [
  (0x1000, ⟨.mov .d (.reg .rcx) (.imm 3), 5⟩),
  (0x1005, ⟨.un .dec .d (.reg .rcx), 2⟩),
  (0x1007, ⟨.jcc .ne (BitVec.ofInt 64 (-4)), 2⟩)] }

def start : Cpu := { rip := 0x1000 }

/-! ## ⭐⭐⭐ NONVACUITY — the loop LOOPS, and the old driver did not

These are the two numbers from the measurement that opened `X86/Program.lean`,
frozen as theorems so a regression in `stepP` cannot quietly restore the old
behaviour while the safety theorem above stays green. -/

/-- ⛔ THE OLD DRIVER: `run` folds the list and takes ONE pass — `ecx = 2`. -/
theorem run_fold_does_not_loop :
    ((run [⟨.mov .d (.reg .rcx) (.imm 3), 5⟩, ⟨.un .dec .d (.reg .rcx), 2⟩,
           ⟨.jcc .ne (BitVec.ofInt 64 (-4)), 2⟩] start).regs.get .rcx) = 2 := by
  decide

/-- ✅ THE PROGRAM-INDEXED RELATION: three passes — `ecx = 0`. -/
theorem runP_loops : ((runP countdown 7 start).regs.get .rcx) = 0 := by decide

/-- The branch is taken at step 3: `rip` goes BACK to `L`.  This is the single
step the fold could not take, stated on its own so a failure names the step. -/
theorem runP_branches_backward : (runP countdown 3 start).rip = 0x1005 := by decide

/-- The routine EXITS: `rip` leaves the code and the model stops.  This is what
makes "for all `n`" a claim about a finished routine rather than a running one. -/
theorem runP_exits : (runP countdown 8 start).stopped = true := by decide

/-- …and stays exited, so more fuel adds nothing.  ⭐ NOTE THE PROOF: this is
`runP_stopped` applied, not a computation — so it holds for **every** `k`,
where a `decide` could only ever have pinned one number. -/
theorem runP_exit_is_stable (k : Nat) :
    runP countdown k (runP countdown 8 start) = runP countdown 8 start :=
  runP_stopped countdown k _ runP_exits

/-! ## ⭐⭐⭐ THE SAFETY THEOREM — thirteen lines, a loop, all fuel, all start states

The property is a FRAME claim ("this routine writes no memory"), so it goes to
the frame tier and mentions no label and no branch.  Note what is quantified:
**every** start state `s`, **every** amount of fuel `n`. -/

theorem countdown_writes_no_memory (n : Nat) (s : Cpu) :
    (runP countdown n s).mem = s.mem := by
  refine runP_invariant_instrs countdown (fun t => t.mem = s.mem) ?_ ?_ n s rfl
  · intro t e ht; unfold Cpu.halt; split <;> exact ht
  · intro b i t hb ht
    by_cases hl : Live t
    · simp only [countdown, List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq] at hb
      rcases hb with ⟨_, h⟩|⟨_, h⟩|⟨_, h⟩ <;> subst h
      · rw [step_mov_reg_imm_mem _ _ _ hl]; exact ht
      · rw [step_dec_reg_mem _ _ hl]; exact ht
      · rw [step_jcc_mem _ _ hl]; exact ht
    · rw [step_stopped]; exact ht
      simpa [Cpu.stopped, Live, Option.isSome_iff_ne_none] using hl

/-- ⚠️ AND THE CONTROL THAT STOPS THE ABOVE BEING VACUOUS BY CONSTRUCTION: the
routine's run really does move the machine, so "memory is unchanged" is a claim
about seven executed instructions and not about a machine that never started. -/
theorem countdown_really_ran : (runP countdown 7 start).rip ≠ start.rip := by decide

end Tests
