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

/-! # ⚖️ PROBLEM 1 OF FIVE — the `memset`-style fill, and the target it MISSED

`docs/P2-PROOF-INTERFACE.md` names five problems that SIZE this interface. This is the
first, and the first real memory-safety property in the campaign: **the routine writes
only inside its destination buffer**, for every amount of fuel and every initial memory.

## ⛔⛔ THE RESULT REFUTES MY OWN SIZING, AND THAT IS THE POINT OF THE EXERCISE

The Captain's criterion is *"tens of lines, not thousands."* The countdown above — a
FRAME property, no labels — cost **14**. This one cost:
```
  the routine                                6 lines
  the invariant                             14
  the preservation proof                   152      ⇐ against a target of "tens"
     of which LABEL-DISPATCH boilerplate     64  (42%)
     everything else                         88
  the safety theorem itself                  5
```
⇒ 🔑 ***THE FRAME TIER HITS THE TARGET AND THE LABELLED TIER DOES NOT — AND THE GAP IS
NOT THE SAFETY ARGUMENT.*** 42% of the proof is mechanically deriving *"at this `rip`
the instruction is X"* and reducing the invariant's `if`-chain to this label's arm: the
same twenty lines five times, differing only in a literal.
⚠️ **AND REMOVING ALL OF IT STILL LEAVES 88.** The dispatch is the largest single
component and it is not the whole gap — stated so the next head does not build a
dispatch tactic expecting "tens" and find 88 lines waiting.

📌 **WHAT TO BUILD NEXT, MEASURED RATHER THAN GUESSED:** a label-dispatch combinator —
given a `Program` over concrete addresses, produce `at? L = some I` and the reduced
invariant arm per label — removes ~64 lines here and about as many from every later
problem, because the cost is **per label, not per property**.
⚠️ **NOT CLAIMED: that 152 is the floor.** This is a first proof by the head that had
just built the interface. A second attempt with the dispatch factored out is the
experiment, and it has not been run.

## WHY THIS PROBLEM NEEDED THE LABELLED TIER AT ALL
It was SIZED as a frame-tier problem and is not one. The frame tier requires every
instruction to preserve the invariant **from any state satisfying it**, and `mov rcx, 4`
does not: it re-establishes the pointer/counter relation the loop body maintains, so from
an arbitrary mid-loop state it breaks the invariant. ⇒ **This routine's safety genuinely
depends on WHERE the machine is, and no frame-shaped invariant can express that.**

⚠️ **`dec rcx` RATHER THAN `dec ecx`, DELIBERATELY.** Both are real x86; the 32-bit
spelling adds `Value.writeView` zero-extension reasoning orthogonal to the memory-safety
content, inflating the line count with something this exercise is not measuring. -/

/-- The routine, at 0x1000:
```
  0x1000  mov  rcx, 4        (7)
  0x1007  L: mov [rdi], al   (2)
  0x1009  inc  rdi           (3)
  0x100C  dec  rcx           (3)
  0x100F  jne  L             (2)   next = 0x1011, disp = 0x1007-0x1011 = -10
  0x1011  (exit — outside the program)
```
-/
def fill : Program := { code := [
  (0x1000, ⟨.mov .q (.reg .rcx) (.imm 4), 7⟩),
  (0x1007, ⟨.mov .b (.mem { base := some .rdi }) (.reg .rax), 2⟩),
  (0x1009, ⟨.un .inc .q (.reg .rdi), 3⟩),
  (0x100C, ⟨.un .dec .q (.reg .rcx), 3⟩),
  (0x100F, ⟨.jcc .ne (BitVec.ofInt 64 (-10)), 2⟩)] }

def entry (d0 : BitVec 64) (m0 : Mem) : Cpu :=
  { rip := 0x1000, mem := m0, regs := Regs.set default .rdi d0 }

/-- The per-label invariant. -/
def FillInv (d0 : BitVec 64) (m0 : Mem) (a : BitVec 64) (s : Cpu) : Prop :=
  AgreeOutside (Region d0 4) m0 s.mem ∧
  (if a = 0x1000 then s.regs.get .rdi = d0
   else if a = 0x1007 ∨ a = 0x1009 then
     ∃ k : Nat, k < 4 ∧ s.regs.get .rdi = d0 + BitVec.ofNat 64 k
                      ∧ s.regs.get .rcx = BitVec.ofNat 64 (4 - k)
   else if a = 0x100C then
     ∃ k : Nat, k < 4 ∧ s.regs.get .rdi = d0 + BitVec.ofNat 64 (k+1)
                      ∧ s.regs.get .rcx = BitVec.ofNat 64 (4 - k)
   else if a = 0x100F then
     ∃ k : Nat, k < 4 ∧ s.regs.get .rdi = d0 + BitVec.ofNat 64 (k+1)
                      ∧ s.regs.get .rcx = BitVec.ofNat 64 (3 - k)
                      ∧ s.flags.zf = decide (k = 3)
   else True)

theorem fill_entry (d0 : BitVec 64) (m0 : Mem) : FillInv d0 m0 (entry d0 m0).rip (entry d0 m0) := by
  constructor
  · intro a _; rfl
  · simp [entry, Regs.get, Regs.set]

set_option maxHeartbeats 1000000 in
theorem fill_preserves (d0 : BitVec 64) (m0 : Mem) (s : Cpu)
    (h : FillInv d0 m0 s.rip s) : FillInv d0 m0 (stepP fill s).rip (stepP fill s) := by
  by_cases hst : s.stopped = true
  · rw [stepP_stopped fill s hst]; exact h
  have hl : Live s := live_of_not_stopped hst
  by_cases e0 : s.rip = 0x1000
  · obtain ⟨ha, hr⟩ := h
    rw [e0] at hr
    simp only [if_pos rfl] at hr
    have hat : fill.at? s.rip = some ⟨.mov .q (.reg .rcx) (.imm 4), 7⟩ := by
      rw [e0]; rfl
    have hstep : stepP fill s = step ⟨.mov .q (.reg .rcx) (.imm 4), 7⟩ s := by
      simp [stepP, hst, hat]
    simp only [if_true] at hr
    rw [hstep, step_mov_reg_imm .q .rcx 4 hl]
    have hrip : s.rip + BitVec.ofNat 64 7 = (0x1007 : BitVec 64) := by rw [e0]; rfl
    refine ⟨ha, ?_⟩
    rw [hrip]
    simp only [show ((0x1007 : BitVec 64) = 0x1000) = False from by decide, if_false,
      show (((0x1007 : BitVec 64) = 0x1007) ∨ ((0x1007 : BitVec 64) = 0x1009)) = True from by decide,
      if_true]
    exact ⟨0, by decide, by simpa using hr, by simp⟩
  by_cases e1 : s.rip = 0x1007
  · obtain ⟨ha, hr⟩ := h
    rw [e1] at hr
    simp only [show ((0x1007 : BitVec 64) = 0x1000) = False from by decide, if_false,
      show (((0x1007 : BitVec 64) = 0x1007) ∨ ((0x1007 : BitVec 64) = 0x1009)) = True from by decide,
      if_true] at hr
    obtain ⟨k, hk, hd, hc⟩ := hr
    have hat : fill.at? s.rip
        = some ⟨.mov .b (.mem { base := some .rdi }) (.reg .rax), 2⟩ := by rw [e1]; rfl
    have hstep : stepP fill s = step ⟨.mov .b (.mem { base := some .rdi }) (.reg .rax), 2⟩ s := by
      simp [stepP, hst, hat]
    rw [hstep, step_mov_mem_reg .b { base := some .rdi } .rax hl rfl]
    have hrip : s.rip + BitVec.ofNat 64 2 = (0x1009 : BitVec 64) := by rw [e1]; rfl
    have haddr : (({ base := some .rdi } : Ea)).addr s (s.rip + BitVec.ofNat 64 2)
        = s.regs.get .rdi := by simp [Ea.addr, Ea.offset]
    refine ⟨?_, ?_⟩
    · simp only [haddr, Mem.writeSize, Mem.writeN, Size.bytes]
      exact agreeOutside_write ha ⟨k, hk, hd⟩
    · rw [hrip]
      simp only [show ((0x1009 : BitVec 64) = 0x1000) = False from by decide, if_false,
        show (((0x1009 : BitVec 64) = 0x1007) ∨ ((0x1009 : BitVec 64) = 0x1009)) = True from by decide,
        if_true]
      exact ⟨k, hk, hd, hc⟩
  by_cases e2 : s.rip = 0x1009
  · obtain ⟨ha, hr⟩ := h
    rw [e2] at hr
    simp only [show ((0x1009 : BitVec 64) = 0x1000) = False from by decide, if_false,
      show (((0x1009 : BitVec 64) = 0x1007) ∨ ((0x1009 : BitVec 64) = 0x1009)) = True from by decide,
      if_true] at hr
    obtain ⟨k, hk, hd, hc⟩ := hr
    have hat : fill.at? s.rip = some ⟨.un .inc .q (.reg .rdi), 3⟩ := by rw [e2]; rfl
    have hstep : stepP fill s = step ⟨.un .inc .q (.reg .rdi), 3⟩ s := by
      simp [stepP, hst, hat]
    rw [hstep, step_inc_reg .q .rdi hl]
    have hrip : s.rip + BitVec.ofNat 64 3 = (0x100C : BitVec 64) := by rw [e2]; rfl
    refine ⟨ha, ?_⟩
    rw [hrip]
    simp only [show ((0x100C : BitVec 64) = 0x1000) = False from by decide, if_false,
      show (((0x100C : BitVec 64) = 0x1007) ∨ ((0x100C : BitVec 64) = 0x1009)) = False from by decide,
      show ((0x100C : BitVec 64) = 0x100C) = True from by decide, if_true]
    refine ⟨k, hk, ?_, ?_⟩
    · simp only [Regs.get_set_same, Value.writeView_q, Flags.addResult, Cpu.getReg,
        Value.trunc_q, hd, Bool.false_eq_true, if_false]
      rw [ofNat_succ_64, BitVec.add_assoc]
    · rw [Regs.get_set_ne _ _ _ _ (by decide)]; exact hc
  by_cases e3 : s.rip = 0x100C
  · obtain ⟨ha, hr⟩ := h
    rw [e3] at hr
    simp only [show ((0x100C : BitVec 64) = 0x1000) = False from by decide, if_false,
      show (((0x100C : BitVec 64) = 0x1007) ∨ ((0x100C : BitVec 64) = 0x1009)) = False from by decide,
      show ((0x100C : BitVec 64) = 0x100C) = True from by decide, if_true] at hr
    obtain ⟨k, hk, hd, hc⟩ := hr
    have hat : fill.at? s.rip = some ⟨.un .dec .q (.reg .rcx), 3⟩ := by rw [e3]; rfl
    have hstep : stepP fill s = step ⟨.un .dec .q (.reg .rcx), 3⟩ s := by
      simp [stepP, hst, hat]
    rw [hstep, step_dec_reg .q .rcx hl]
    have hrip : s.rip + BitVec.ofNat 64 3 = (0x100F : BitVec 64) := by rw [e3]; rfl
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    refine ⟨ha, ?_⟩
    rw [hrip]
    simp only [show ((0x100F : BitVec 64) = 0x1000) = False from by decide, if_false,
      show (((0x100F : BitVec 64) = 0x1007) ∨ ((0x100F : BitVec 64) = 0x1009)) = False from by decide,
      show ((0x100F : BitVec 64) = 0x100C) = False from by decide,
      show ((0x100F : BitVec 64) = 0x100F) = True from by decide, if_true]
    refine ⟨k, hk, ?_, ?_, ?_⟩
    · rw [Regs.get_set_ne _ _ _ _ (by decide)]; exact hd
    · simp only [Regs.get_set_same, Value.writeView_q, Flags.subResult, Cpu.getReg,
        Value.trunc_q, hc, Bool.false_eq_true, if_false]
      rcases hk4 with rfl|rfl|rfl|rfl <;> decide
    · simp only [Flags.dec, Flags.fromResult, Cpu.getReg, Value.trunc_q, hc,
        Bool.false_eq_true, if_false]
      rcases hk4 with rfl|rfl|rfl|rfl <;> decide
  by_cases e4 : s.rip = 0x100F
  · obtain ⟨ha, hr⟩ := h
    rw [e4] at hr
    simp only [show ((0x100F : BitVec 64) = 0x1000) = False from by decide, if_false,
      show (((0x100F : BitVec 64) = 0x1007) ∨ ((0x100F : BitVec 64) = 0x1009)) = False from by decide,
      show ((0x100F : BitVec 64) = 0x100C) = False from by decide,
      show ((0x100F : BitVec 64) = 0x100F) = True from by decide, if_true] at hr
    obtain ⟨k, hk, hd, hc, hz⟩ := hr
    have hat : fill.at? s.rip = some ⟨.jcc .ne (BitVec.ofInt 64 (-10)), 2⟩ := by rw [e4]; rfl
    have hstep : stepP fill s = step ⟨.jcc .ne (BitVec.ofInt 64 (-10)), 2⟩ s := by
      simp [stepP, hst, hat]
    have hcanon : Cc.eval .ne s.flags = true →
        canonical (s.rip + BitVec.ofNat 64 2 + BitVec.ofInt 64 (-10)) := by
      intro _; rw [e4]; decide
    rw [hstep, step_jcc .ne (BitVec.ofInt 64 (-10)) hl hcanon]
    refine ⟨ha, ?_⟩
    by_cases hzf : s.flags.zf = true
    · -- ZF set: the loop is done, the branch falls through to 0x1011, outside the program
      have hnb : Cc.eval .ne s.flags = false := by simp [Cc.eval, hzf]
      have hrip : s.rip + BitVec.ofNat 64 2 = (0x1011 : BitVec 64) := by rw [e4]; rfl
      simp only [hnb, if_false, hrip]
      trivial
    · -- ZF clear: the branch is TAKEN back to the loop head, and k+1 is still in range
      have hzf' : s.flags.zf = false := by
        cases hb : s.flags.zf with
        | true => exact absurd hb hzf
        | false => rfl
      have hb : Cc.eval .ne s.flags = true := by simp [Cc.eval, hzf']
      have hk3 : k < 3 := by
        rw [hzf'] at hz
        have : ¬ (k = 3) := by
          intro hh; rw [hh] at hz; simp at hz
        omega
      have hrip : s.rip + BitVec.ofNat 64 2 + BitVec.ofInt 64 (-10) = (0x1007 : BitVec 64) := by
        rw [e4]; rfl
      simp only [hb, if_true, hrip]
      simp only [show ((0x1007 : BitVec 64) = 0x1000) = False from by decide, if_false,
        show (((0x1007 : BitVec 64) = 0x1007) ∨ ((0x1007 : BitVec 64) = 0x1009)) = True from by decide,
        if_true]
      exact ⟨k + 1, by omega, hd, by rw [hc]; congr 1; omega⟩
  -- not a label at all: the program has no instruction here, so the model halts
  have hnone : fill.at? s.rip = none := by
    have f0 : ((0x1000 : BitVec 64) == s.rip) = false := by
      simp only [beq_eq_false_iff_ne]; exact fun hh => e0 hh.symm
    have f1 : ((0x1007 : BitVec 64) == s.rip) = false := by
      simp only [beq_eq_false_iff_ne]; exact fun hh => e1 hh.symm
    have f2 : ((0x1009 : BitVec 64) == s.rip) = false := by
      simp only [beq_eq_false_iff_ne]; exact fun hh => e2 hh.symm
    have f3 : ((0x100C : BitVec 64) == s.rip) = false := by
      simp only [beq_eq_false_iff_ne]; exact fun hh => e3 hh.symm
    have f4 : ((0x100F : BitVec 64) == s.rip) = false := by
      simp only [beq_eq_false_iff_ne]; exact fun hh => e4 hh.symm
    simp only [Program.at?, fill, List.find?, f0, f1, f2, f3, f4, Option.map_none]
  have hstep : stepP fill s = s.halt (.outsideProgram "no instruction at RIP") := by
    simp [stepP, hst, hnone]
  rw [hstep]
  unfold FillInv at h ⊢
  simpa only [halt_mem, halt_rip, halt_regs, halt_flags] using h

/-- ⭐⭐⭐ MEMORY SAFETY: the fill routine writes ONLY inside its destination
buffer — for every amount of fuel, and for every initial memory. -/
theorem fill_writes_only_in_buffer (d0 : BitVec 64) (m0 : Mem) (n : Nat) :
    AgreeOutside (Region d0 4) m0 (runP fill n (entry d0 m0)).mem :=
  (runP_labels fill (FillInv d0 m0) (fun s hs => fill_preserves d0 m0 s hs) n (entry d0 m0)
    (fill_entry d0 m0)).1

-- ⭐ NONVACUITY: the theorem is about a routine that really runs and really writes.
-- ⛔ THE MEMORY IS SEEDED WITH SENTINELS, NOT LEFT EMPTY. On the zero background a
-- "the neighbour is still 0" control cannot tell PRESERVED from NEVER-WRITTEN — it
-- would pass against a model whose stores all vanished.
def seeded : Mem := { bytes := [(0x1FFF, 0x5A), (0x2004, 0x5A)] }
def s0 : Cpu := entry 0x2000 seeded
theorem fill_really_wrote : ((runP fill 20 (Cpu.setReg s0 .q .rax 0xAB)).mem.read 0x2000) = 0xAB := by
  decide
theorem fill_wrote_the_last_byte :
    ((runP fill 20 (Cpu.setReg s0 .q .rax 0xAB)).mem.read 0x2003) = 0xAB := by decide
theorem fill_left_the_right_neighbour_alone :
    ((runP fill 20 (Cpu.setReg s0 .q .rax 0xAB)).mem.read 0x2004) = 0x5A := by decide
theorem fill_left_the_left_neighbour_alone :
    ((runP fill 20 (Cpu.setReg s0 .q .rax 0xAB)).mem.read 0x1FFF) = 0x5A := by decide

-- ⭐⭐ AND THE BOUND IS TIGHT: it really does write the FOURTH byte, so the theorem's
-- region cannot be narrowed to three without becoming false. A safety bound that is
-- loose is satisfied by a routine that writes less than it claims.
theorem fill_bound_is_tight :
    ¬ AgreeOutside (Region 0x2000 3) seeded
        (runP fill 20 (Cpu.setReg s0 .q .rax 0xAB)).mem := by
  intro hcon
  have h3 : ¬ Region (0x2000 : BitVec 64) 3 0x2003 := by
    rintro ⟨i, hi, he⟩
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl|rfl|rfl <;> simp at he
  have := hcon 0x2003 h3
  revert this
  decide

end Tests
