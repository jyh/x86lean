/-
# Tests.LogicKit — the composition kit, exercised (D307)

Its own module by D311's rule (one test module per witness family): a new unit is judged once against a
ceiling measured on its own machine, instead of as a delta against `Tests.Logic`'s budget.

LANE. Personal lane, public sources only.
-/
import Tests.LogicLoop

namespace Tests.Logic
open X86

/-! ### The composition kit, exercised (D307)

A step-invariant fact (the frame tier's kind: preserved by every step, no footprint) proved per step, joined to the termination proof by `with_invariant`, and
two total specs joined by `Total.and` — the shape `CorrectFor`'s post needs. -/

/-- One step of `countdownN` never touches `rbx`: `dec rcx` writes only `rcx`, `jne` writes no register,
and halting writes none. Proved at EVERY state, with no label and no `rip` case analysis. -/
theorem countdownN_step_rbx (u : Cpu) : (stepP countdownN u).regs.get .rbx = u.regs.get .rbx := by
  unfold stepP
  split
  · rfl
  · rename_i hst
    cases hf : countdownN.at? u.rip with
    | none => simp only [halt_regs]
    | some i =>
      obtain ⟨b, hb⟩ := Program.at?_mem hf
      simp only [countdownN, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hb
      have hl : Live u := live_of_not_stopped hst
      rcases hb with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · simp only [step_dec_reg .q .rcx hl]
        exact Regs.get_set_ne _ _ _ _ (by decide)
      · simp only [step, hl, Cpu.setRipChecked, Cpu.setRip, Cpu.halt, Cpu.stopped,
          Option.isSome_none, Bool.false_eq_true, if_false, Op.lockIllegal]
        split
        · rfl
        · split
          · split <;> rfl
          · rfl

/-- `with_invariant`: the loop's termination proof, with `rbx` carried along as a step invariant. -/
theorem countdownN_keeps_rbx :
    Spec.Total countdownN (fun s => s.ms = none ∧ s.rip = 0x1000)
      (fun s t => t.regs.get .rbx = s.regs.get .rbx) :=
  Spec.conseq (fun _ h => h) (fun _ _ _ ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩)
    (Spec.with_invariant (fun s u => u.regs.get .rbx = s.regs.get .rbx) (fun _ _ => rfl)
      (fun _ u _ h => (countdownN_step_rbx u).trans h) countdownN_total)

/-- `Total.and`: the functional-and-reason post and the `rbx` invariant post, proved apart, joined. -/
theorem countdownN_total_with_frame :
    Spec.Total countdownN (fun s => s.ms = none ∧ s.rip = 0x1000)
      (fun s t => (t.regs.get .rcx = 0 ∧ t.mem = s.mem
          ∧ t.ms = some (.outsideProgram "no instruction at RIP"))
        ∧ t.regs.get .rbx = s.regs.get .rbx) :=
  Spec.Total.and countdownN_total countdownN_keeps_rbx

/-- ⛔ **THE CONTROL: `and` IS FALSE FOR A BARE `Spec`.** "The machine is at its start" and "the machine
has moved" are each eventually reached (fuel 0, fuel 1), and never at once. So `Total.and`'s restriction
is load-bearing, not caution. -/
theorem spec_and_is_false :
    Spec countdownN (fun s => s = start3) (fun s t => t = s)
    ∧ Spec countdownN (fun s => s = start3) (fun s t => t ≠ s)
    ∧ ¬ Spec countdownN (fun s => s = start3) (fun s t => t = s ∧ t ≠ s) := by
  refine ⟨Spec.skip (fun _ _ => rfl), fun s hs => ⟨1, ?_⟩, fun h => ?_⟩
  · subst hs; exact fun h => absurd (congrArg Cpu.rip h) (by decide)
  · obtain ⟨_, h1, h2⟩ := h start3 rfl
    exact h2 h1

/-- `seq` and `step`, exercised in the tree (the census's last two zeros, D307): from the head, the
conditional prefix (`to_skip`, restated as a `Spec`) and then ONE `step` (the `dec`) reach `jne` with
the counter one lower and memory untouched. -/
theorem clampLoop_to_jne :
    Spec clampLoop (fun s => s.ms = none ∧ s.rip = 0x1000)
      (fun s t => t.ms = none ∧ t.rip = 0x100B ∧ t.regs.get .rcx = s.regs.get .rcx - 1
        ∧ t.mem = s.mem) := by
  refine Spec.seq (R := fun s m => m.ms = none ∧ m.rip = 0x1008
      ∧ m.regs.get .rcx = s.regs.get .rcx ∧ m.mem = s.mem) ?_ ?_
  · rintro s ⟨hms, hrip⟩
    obtain ⟨k, h⟩ := to_skip s hms hrip
    exact ⟨k, h⟩
  · intro s _
    refine Spec.step fun m ⟨hms, hrip, hrcx, hmem⟩ => ?_
    rw [cstep_dec m hms hrip]
    refine ⟨hms, rfl, ?_, hmem⟩
    rw [← hrcx]
    show (m.regs.set .rcx (m.regs.get .rcx - 1)).get .rcx = _
    exact Regs.get_set_same _ _ _

end Tests.Logic
