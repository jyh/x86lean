/-
# Tests.Logic — the program logic's first witness: a loop that TERMINATES, for every count

`X86/Logic.lean`'s `Spec` is an eventually-reaches judgment, and total correctness exactly when its post
implies `stopped` (`Spec.Total`). This file proves, through `Spec.loop`,
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

/-- The exit, related to the start: stopped at the exit address, the counter at zero, memory
exactly the start's — and stopped for the RIGHT REASON, by leaving the program (D306: a fault is also
`stopped`, so `stopped` alone does not say the routine finished). -/
def Done (s t : Cpu) : Prop :=
  t.stopped = true ∧ t.rip = 0x1005 ∧ t.regs.get .rcx = 0 ∧ t.mem = s.mem
  ∧ t.ms = some (.outsideProgram "no instruction at RIP")

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
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [Cpu.halt, Cpu.stopped, afterJne, afterDec, hms]
    · rw [halt_rip]; exact if_pos heq
    · rw [halt_regs, afterJne_rcx]; exact heq
    · rw [halt_mem]; exact hmem
    · simp [Cpu.halt, afterJne, afterDec, hms]

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

/-! ### The judgment's other rules, exercised in the tree (D305; census 3b of math's refuter pass read
`loop` as the ONLY rule any theorem here used) -/

/-- `Spec.Total` by `conseq`: `Done` already carries `stopped`, so the witness is total correctness
and not merely an eventually-reaches claim — and its post states the halt REASON, as the design doc's
§4a says a `Total` post in this logic does. -/
theorem countdownN_total :
    Spec.Total countdownN (fun s => s.ms = none ∧ s.rip = 0x1000)
      (fun s t => t.regs.get .rcx = 0 ∧ t.mem = s.mem
        ∧ t.ms = some (.outsideProgram "no instruction at RIP")) :=
  Spec.conseq (fun _ h => h) (fun _ _ _ ⟨h1, _, h3, h4, h5⟩ => ⟨h1, h3, h4, h5⟩) countdownN_terminates

/-- `Spec.reach`: the end state is a RUN of the program from the start, which is what a relational
or two-run corollary needs and `Spec` alone forgets. -/
theorem countdownN_reaches_a_run :
    Spec countdownN (fun s => s.ms = none ∧ s.rip = 0x1000)
      (fun s t => Done s t ∧ ∃ n, t = runP countdownN n s) :=
  Spec.reach countdownN_terminates

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
  ⟨by decide, by decide, by decide, rfl, rfl⟩

/-- …and one step earlier it had NOT stopped — so `Done` describes a run that did the work, not
a machine that halted at once. -/
theorem start3_not_done_early : (runP countdownN 6 start3).stopped = false := by decide

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

`rax = 0`, `rbx = 2`, `rcx = 4`: the first two passes do not take `jae` (0 < 2, then 1 < 2) and
increment `rax`; the last two take it (2 ≥ 2). So the concrete run mixes 5-step and 4-step passes:
5 + 5 + 4 + 4 = 18 steps, plus the halting one — and one step earlier it has not stopped. -/

def cstart : Cpu :=
  Cpu.setReg (Cpu.setReg (Cpu.setReg { rip := 0x1000 } .q .rax 0) .q .rbx 2) .q .rcx 4

theorem cstart_meets_pre : cstart.ms = none ∧ cstart.rip = 0x1000 := by decide

theorem cstart_run_is_done : CDone cstart (runP clampLoop 19 cstart) :=
  ⟨by decide, by decide, by decide, rfl⟩

theorem cstart_not_done_early : (runP clampLoop 18 cstart).stopped = false := by decide

/-- …and `inc rax` ran exactly twice: the not-taken arm was really exercised, and so was the taken
one (a run of only 5-step passes would stop at 21, not 19). -/
theorem cstart_took_both_arms : (runP clampLoop 19 cstart).regs.get .rax = 2 := by decide

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

/-! ### The composition kit, exercised (D307)

A FRAME fact proved per step in the frame tier, joined to the termination proof by `with_invariant`, and
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

/-- `with_invariant`: the loop's termination proof, with `rbx` carried along by the frame tier. -/
theorem countdownN_keeps_rbx :
    Spec.Total countdownN (fun s => s.ms = none ∧ s.rip = 0x1000)
      (fun s t => t.regs.get .rbx = s.regs.get .rbx) :=
  Spec.conseq (fun _ h => h) (fun _ _ _ ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩)
    (Spec.with_invariant (fun s u => u.regs.get .rbx = s.regs.get .rbx) (fun _ _ => rfl)
      (fun _ u _ h => (countdownN_step_rbx u).trans h) countdownN_total)

/-- `Total.and`: the functional-and-reason post and the frame post, proved apart, joined. -/
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

end Tests.Logic
