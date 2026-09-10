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

/-! # ⚖️ PROBLEM 1 OF FIVE — the `memset` fill: proven, and it MEASURED what to build next

`docs/P2-PROOF-INTERFACE.md` names five problems that SIZE this interface. This is the first,
and the first real memory-safety property in the campaign: **the routine writes only inside its
destination buffer**, ∀ fuel, ∀ initial memory, on the three standard axioms.

## ⛔ IT IS NOT A FRAME-TIER PROBLEM, AND THE DESIGN DOC SAID IT WAS
The frame tier needs every instruction to preserve the invariant **from ANY state satisfying
it**, and `mov rcx, 4` does not: it *re-establishes* the pointer/counter relation the loop body
maintains, so from an arbitrary mid-loop state it breaks it. ⇒ **This routine's safety genuinely
depends on WHERE the machine is.** The two-tier split is sound; **the assignment of a problem to
a tier was not, and writing the proof is what found out.**

## ⭐⭐⭐ THE MEASUREMENT, PRE-REGISTERED AND THEN CONFIRMED
The first proof was **152 lines, 64 of them (42%) label dispatch** — and that split was recorded
*before* anything was built, together with the warning that removing all of it **would still
leave 88**. The combinators went into `X86/Program.lean`; the proof was re-run:
```
  first proof .................................. 152 lines   ≈ 25 / label
  + stepP_at / stepP_off / atTable .............  88          ≈ 12 / label   ⇐ the 64 predicted
  + runP_code (dispatch done ONCE, once proved)   67          ≈ 9.6 / label
  invariant (one `Loop` for four arms) ......... 14 → 10
```
⇒ 🔑 ***THE PREDICTION HELD TO THE LINE, INCLUDING ITS OWN WARNING*** — which is the only reason
the 42% win cannot be read as reaching the target.

## ⛔⛔ AND THE TARGET IS STILL MISSED, FOR THE CASE THE CAPTAIN ACTUALLY NAMED
His criterion is a **twenty-instruction routine**. This routine has FIVE labels. Decomposed:
```
  lines ≈ 19 fixed + ~9.6 per LABEL         (measured: blocks of 4, 7, 8, 12, 17)
     5 labels →   67
    10 labels →  115
    20 labels →  211        ⛔ not "tens of lines"
```
⇒ 🔑 ***THE COST IS LINEAR IN LABELS, AND LEMMA ENGINEERING IS ASYMPTOTING NEAR ~9-10 LINES
EACH.*** Three measured points — 25, then 12, then 9.6 — and the prediction written before the
third round, *"a second round would move it less"*, held: the constant fell **13**, then **2.4**.
⛔ **THAT SETTLES THE FEASIBILITY QUESTION FOR A LEMMA LIBRARY.** Reaching "tens" at twenty
instructions needs ~2-3 lines per label. **No arrangement of lemmas gets there from 9.6 — it
needs a TACTIC or a VC generator**, and that is now named on evidence rather than on taste.
⚠️ **NOT CLAIMED:** that ~12 is the floor for a lemma-based approach, or that the extrapolation
holds exactly — it is linear in the four blocks measured, and a routine with harder branch
structure would cost more per label, not less.

⚠️ **`dec rcx` RATHER THAN `dec ecx`, DELIBERATELY.** Both are real x86; the 32-bit spelling adds
zero-extension reasoning orthogonal to the memory-safety content. -/

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

/-- The loop assertion: the pointer has advanced `k` and the counter holds the rest. -/
def Loop (d0 : BitVec 64) (o c : Nat) (s : Cpu) : Prop :=
  ∃ k : Nat, k < 4 ∧ s.regs.get .rdi = d0 + BitVec.ofNat 64 (k + o)
           ∧ s.regs.get .rcx = BitVec.ofNat 64 (c - k)
           ∧ (c = 3 → s.flags.zf = decide (k = 3))

def FillInv (d0 : BitVec 64) (m0 : Mem) (a : BitVec 64) (s : Cpu) : Prop :=
  AgreeOutside (Region d0 4) m0 s.mem ∧ atTable
    [(0x1000, fun s => s.regs.get .rdi = d0),
     (0x1007, Loop d0 0 4), (0x1009, Loop d0 0 4),
     (0x100C, Loop d0 1 4), (0x100F, Loop d0 1 3)] a s

set_option maxHeartbeats 1000000 in
theorem fill_safe (d0 : BitVec 64) (m0 : Mem) (n : Nat) :
    AgreeOutside (Region d0 4) m0 (runP fill n (entry d0 m0)).mem :=
  (runP_code fill (FillInv d0 m0)
    (fun s e hl h => by
      have hh : s.halt e = { s with ms := some e } := by simp only [Cpu.halt, hl]
      rw [hh]
      exact ⟨h.1, atTable_of_congr (by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl|rfl|rfl|rfl|rfl <;> exact id) h.2⟩)
    (by
      intro a i s hmem hrip hl hI
      simp only [fill, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      obtain ⟨ha, hr⟩ := hI
      rcases hmem with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · rw [step_mov_reg_imm .q .rcx 4 hl, hrip]
        have hr0 : s.regs.get .rdi = d0 := hr
        exact ⟨ha, show Loop d0 0 4 _ from ⟨0, by decide, by simpa using hr0, by simp, by simp⟩⟩
      · obtain ⟨k, hk, hd, hc, _⟩ := (hr : Loop d0 0 4 s)
        rw [step_mov_mem_reg .b { base := some .rdi } .rax hl rfl,
            show s.rip + BitVec.ofNat 64 2 = (0x1009 : BitVec 64) by rw [hrip]; rfl]
        refine ⟨?_, show Loop d0 0 4 _ from ⟨k, hk, hd, hc, by simp⟩⟩
        simp only [Ea.addr, show (({ base := some .rdi } : Ea)).offset s (0x1009 : BitVec 64)
          = s.regs.get .rdi by simp [Ea.offset], Mem.writeSize, Mem.writeN, Size.bytes]
        exact agreeOutside_write ha ⟨k, hk, by simpa using hd⟩
      · obtain ⟨k, hk, hd, hc, _⟩ := (hr : Loop d0 0 4 s)
        rw [step_inc_reg .q .rdi hl, hrip]
        refine ⟨ha, show Loop d0 1 4 _ from ⟨k, hk, ?_,
          by rw [Regs.get_set_ne _ _ _ _ (by decide)]; exact hc, by simp⟩⟩
        regcalc [Flags.addResult, hd, Nat.add_zero]
        rw [ofNat_succ_64, BitVec.add_assoc]
      · obtain ⟨k, hk, hd, hc, _⟩ := (hr : Loop d0 1 4 s)
        have h4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
        rw [step_dec_reg .q .rcx hl, hrip]
        refine ⟨ha, show Loop d0 1 3 _ from ⟨k, hk,
          by rw [Regs.get_set_ne _ _ _ _ (by decide)]; exact hd, ?_, fun _ => ?_⟩⟩
        · regcalc [Flags.subResult, hc]
          rcases h4 with rfl|rfl|rfl|rfl <;> decide
        · regcalc [Flags.dec, Flags.fromResult, hc]
          rcases h4 with rfl|rfl|rfl|rfl <;> decide
      · obtain ⟨k, hk, hd, hc, hz⟩ := (hr : Loop d0 1 3 s)
        have hzf := hz rfl
        rw [step_jcc .ne (BitVec.ofInt 64 (-10)) hl (by intro _; rw [hrip]; decide)]
        by_cases hb : s.flags.zf = true
        · rw [show Cc.eval .ne s.flags = false by simp [Cc.eval, hb], if_neg (by simp), hrip]
          exact ⟨ha, trivial⟩
        · have hbf : s.flags.zf = false := by
            cases hq : s.flags.zf with | true => exact absurd hq hb | false => rfl
          have hk3 : k < 3 := by
            rw [hbf] at hzf
            have : ¬ (k = 3) := fun hh => by rw [hh] at hzf; simp at hzf
            omega
          rw [if_pos (by simp [Cc.eval, hbf]), hrip]
          exact ⟨ha, show Loop d0 0 4 _ from
            ⟨k + 1, by omega, by simpa using hd, by rw [hc]; congr 1; omega, by simp⟩⟩)
    n (entry d0 m0) ⟨fun _ _ => rfl, show (entry d0 m0).regs.get .rdi = d0 by
      simp [entry, Regs.get, Regs.set]⟩).1

/-- The name the rest of the campaign cites. -/
theorem fill_writes_only_in_buffer (d0 : BitVec 64) (m0 : Mem) (n : Nat) :
    AgreeOutside (Region d0 4) m0 (runP fill n (entry d0 m0)).mem := fill_safe d0 m0 n

-- ⭐ NONVACUITY, SEEDED RATHER THAN EMPTY. On a zero background a "the neighbour is
-- still 0" control cannot tell PRESERVED from NEVER-WRITTEN: it would pass against a
-- model whose stores all vanished.
def seeded : Mem := { bytes := [(0x1FFF, 0x5A), (0x2004, 0x5A)] }
def s0 : Cpu := entry 0x2000 seeded
def ran : Cpu := runP fill 20 (Cpu.setReg s0 .q .rax 0xAB)

theorem fill_really_wrote : ran.mem.read 0x2000 = 0xAB := by decide
theorem fill_wrote_the_last_byte : ran.mem.read 0x2003 = 0xAB := by decide
theorem fill_left_the_right_neighbour_alone : ran.mem.read 0x2004 = 0x5A := by decide
theorem fill_left_the_left_neighbour_alone : ran.mem.read 0x1FFF = 0x5A := by decide
theorem fill_exits : ran.stopped = true := by decide

/-- ⭐⭐ AND THE BOUND IS TIGHT: it really writes the FOURTH byte, so the theorem's region
cannot be narrowed to three without becoming false. **A safety bound that is loose is
satisfied by a routine that writes less than it claims.** -/
theorem fill_bound_is_tight :
    ¬ AgreeOutside (Region 0x2000 3) seeded ran.mem := by
  intro hcon
  have h3 : ¬ Region (0x2000 : BitVec 64) 3 0x2003 := by
    rintro ⟨i, hi, he⟩
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl|rfl|rfl <;> simp at he
  have := hcon 0x2003 h3
  revert this
  decide

end Tests
