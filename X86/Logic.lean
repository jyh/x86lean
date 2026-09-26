/-
# X86.Logic — a Hoare-style program logic over `runP`, proved sound by construction

O38 (the Captain, 2026-09-10): *"we will want to write a paper for the x86 semantics — including
small-step operational semantics + ~hoare logic"*; 2026-09-11: *"two papers probably"*. Paper 1 is
the validated semantics; this file is the spine of paper 2. Design, arms and what refutes it:
`docs/P2-LOGIC-DESIGN.md` (D303).

## The judgment

`Spec p P Q` — from every state satisfying `P`, SOME amount of fuel reaches a state `t` with
`Q s t`. It is an EVENTUALLY-REACHES judgment — **total correctness exactly when `Q` implies
`t.stopped`** (`Spec.Total` below) — and its postcondition is a RELATION between the start
state and the end state, because the statements this campaign actually proves are relational:
`CorrectFor` (the x86 SaltBench PoC) asks for `AgreeOutside … s.mem t.mem`, `CalleeSaved s t` and
`t.rsp = s.rsp + 8`, and none of those can be said about `t` alone without ghost variables.

⚠️ **IT IS NOT "TOTAL CORRECTNESS" BY ITSELF, AND THIS HEADER SAID IT WAS until D305** (math's refuter
pass, W1, driven: a `Spec` whose post omits `stopped` holds of a program that never stops). The
judgment is kept as it is because `seq` and `loop` need LIVE midpoints; totality is a property of the
post, and `Spec.Total` names it.

⛔ **WHY EVENTUALLY AND NOT PARTIAL.** `runP_invariant` already IS the partial/safety half: it quantifies
over EVERY fuel. What the campaign could not state before this file is REACHING an exit — the PoC's
`∃ n, (runP prog n s).stopped ∧ … = ret`. R1's hand proof reached it by counting steps exactly
(`7 * n` per loop), which works only for a loop body of fixed length. `Spec.loop` below needs no
step count at all, only a variant.

## Soundness

⚖️ **SHALLOW, SO SOUNDNESS IS EVERY RULE BEING A KERNEL-CHECKED THEOREM ABOUT `runP`.** There is no
derivation relation beside the semantics, so there is no second system whose agreement with the
first must be proved — the same argument `X86/Program.lean` makes for `atLabels`, one level up.
The deep-embedding arm (an inductive `Derives` with a soundness theorem) is named in the design
doc as the arm a REFLECTIVE verification-condition generator would need, and is not built.

LANE. Personal lane, public sources only. Every theorem here rests on the three standard axioms at
most (the axiom gate enumerates this module through `X86.lean`).
-/
import X86.Program

namespace X86

/-- **THE JUDGMENT.** From every `P`-state, some fuel reaches a state related to the start by `Q`. -/
def Spec (p : Program) (P : Cpu → Prop) (Q : Cpu → Cpu → Prop) : Prop :=
  ∀ s, P s → ∃ n, Q s (runP p n s)

namespace Spec

variable {p : Program} {P P' : Cpu → Prop} {Q Q' R : Cpu → Cpu → Prop}

/-- **SKIP.** Zero fuel: the postcondition already holds of the start state. -/
theorem skip (h : ∀ s, P s → Q s s) : Spec p P Q :=
  fun s hs => ⟨0, h s hs⟩

/-- **STEP.** One fuel: the postcondition holds after one program step. -/
theorem step (h : ∀ s, P s → Q s (stepP p s)) : Spec p P Q :=
  fun s hs => ⟨1, h s hs⟩

/-- **CONSEQUENCE.** Strengthen the pre, weaken the post — the post may use the pre. -/
theorem conseq (hP : ∀ s, P' s → P s) (hQ : ∀ s t, P' s → Q s t → Q' s t)
    (h : Spec p P Q) : Spec p P' Q' := by
  intro s hs
  obtain ⟨n, hn⟩ := h s (hP s hs)
  exact ⟨n, hQ s _ hs hn⟩

/-- **SEQUENCE.** Run to a midpoint `u` related to the start by `R`, then from `u` onward to `Q`.
The second premise is indexed by the START state `s`, so the final post can relate the end to
the start — which is what a relational post needs and a unary sequencing rule cannot give.
Its proof is `runP_add`, and nothing else. -/
theorem seq (h1 : Spec p P R) (h2 : ∀ s, P s → Spec p (R s) (fun _ t => Q s t)) :
    Spec p P Q := by
  intro s hs
  obtain ⟨n₁, h₁⟩ := h1 s hs
  obtain ⟨n₂, h₂⟩ := h2 s hs _ h₁
  exact ⟨n₁ + n₂, by rw [runP_add]; exact h₂⟩

/-- **LOOP, by a variant.** `I s u` is an invariant relating the start `s` to a loop-head state
`u`; from every such `u` some fuel either finishes (`Q`) or returns to the invariant with a
strictly smaller variant. No step count appears anywhere — a body whose length depends on the
data (a taken or untaken inner branch) costs nothing extra.

⛔ The variant is a `Nat`, so the rule is sound by well-founded induction on `v u` and needs no
termination measure on the program itself. -/
theorem loop (I : Cpu → Cpu → Prop) (v : Cpu → Nat)
    (hinit : ∀ s, P s → I s s)
    (hbody : ∀ s u, P s → I s u →
      ∃ n, Q s (runP p n u) ∨ (I s (runP p n u) ∧ v (runP p n u) < v u)) :
    Spec p P Q := by
  intro s hs
  -- ordinary induction on a strict BOUND of the variant, which is strong induction without a
  -- library lemma for it
  suffices H : ∀ k u, v u < k → I s u → ∃ n, Q s (runP p n u) from
    H _ s (Nat.lt_succ_self _) (hinit s hs)
  intro k
  induction k with
  | zero => intro u hk; exact absurd hk (Nat.not_lt_zero _)
  | succ k ih =>
    intro u hk hI
    obtain ⟨n, hn | ⟨hI', hv⟩⟩ := hbody s u hs hI
    · exact ⟨n, hn⟩
    · obtain ⟨m, hm⟩ := ih _ (by omega) hI'
      exact ⟨n + m, by rw [runP_add]; exact hm⟩

/-- **REACH.** A post may remember that its end state IS a run of the program from the start.
`Spec` forgets `t = runP p n s`, so without this `conseq` cannot lift a post into one that talks
about the run itself — a relational or two-run post (D305; math's refuter pass, R3, where a
read-safety corollary could not close without it). -/
theorem reach (h : Spec p P Q) : Spec p P (fun s t => Q s t ∧ ∃ n, t = runP p n s) := by
  intro s hs
  obtain ⟨n, hn⟩ := h s hs
  exact ⟨n, hn, n, rfl⟩

/-- **TOTAL.** The instance of the judgment that is total correctness: the reached state has
STOPPED. A `Spec` alone is not this (see the header). -/
abbrev Total (p : Program) (P : Cpu → Prop) (Q : Cpu → Cpu → Prop) : Prop :=
  Spec p P (fun s t => t.stopped = true ∧ Q s t)

/-- A stopped end state is the UNIQUE one: every longer run stops at the same state, so a `Total`
witness names the run's result and not merely a state the run passed through. -/
theorem stopped_witness_unique {s : Cpu} {n m : Nat} (hn : (runP p n s).stopped = true)
    (hm : (runP p m s).stopped = true) : runP p n s = runP p m s := by
  rcases Nat.le_total n m with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [runP_add, runP_stopped p k _ hn]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [runP_add, runP_stopped p k _ hm]

/-! ### The composition kit (D307) — how a CRC-shaped post is assembled from separate proofs

`CorrectFor`'s post is a conjunction of a FUNCTIONAL fact (`rax = spec msg`), a TERMINATION fact (stopped at
`ret`) and FRAME facts (`AgreeOutside`, `CalleeSaved`). These two rules let each be proved where it is
cheapest: frames in the frame tier, the rest through `loop`. -/

/-- **INVARIANT.** A relation `J s ·` preserved by EVERY program step rides along any `Spec`: the frame
tier's `runP_invariant`, joined to the judgment. No step count and no label appear in `hstep`. -/
theorem with_invariant (J : Cpu → Cpu → Prop) (hinit : ∀ s, P s → J s s)
    (hstep : ∀ s u, P s → J s u → J s (stepP p u)) (h : Spec p P Q) :
    Spec p P (fun s t => Q s t ∧ J s t) := by
  intro s hs
  obtain ⟨n, hn⟩ := h s hs
  exact ⟨n, hn, runP_invariant p (J s) (fun u hu => hstep s u hs hu) n s (hinit s hs)⟩

/-- **AND, for TOTAL specs.** Two total specs of one program conjoin, because a stopped end state is the
run's UNIQUE result (`stopped_witness_unique`) — so the two proofs name the SAME state.
⛔ It is FALSE for a bare `Spec`: `Tests.Logic.spec_and_is_false` exhibits two eventually-reaches posts
that each hold and never hold together. -/
theorem Total.and {Q₁ Q₂ : Cpu → Cpu → Prop} (h₁ : Total p P Q₁) (h₂ : Total p P Q₂) :
    Total p P (fun s t => Q₁ s t ∧ Q₂ s t) := by
  intro s hs
  obtain ⟨n, hn, hq₁⟩ := h₁ s hs
  obtain ⟨m, hm, hq₂⟩ := h₂ s hs
  refine ⟨n, hn, hq₁, ?_⟩
  rw [stopped_witness_unique hn hm]
  exact hq₂

end Spec

/-- **STOPPED IS FINAL** — a lemma about `runP`, NOT a rule of the judgment: a proof that reaches a
halt may overshoot freely. (It sat in the rule table as `Spec.runP_final` until D305, with a
docstring calling it "lifted to the judgment", which it never was — math's refuter pass, W2.) -/
theorem runP_final {p : Program} {s : Cpu} (n m : Nat) (h : (runP p n s).stopped = true) :
    runP p (n + m) s = runP p n s := by
  rw [runP_add, runP_stopped p m _ h]



/-! ## R-READ — read safety as a TWO-RUN property, stated over the UNCHANGED `runP` (D308)

Paper 1 §6 records that *"a scan reads only inside its buffer"* cannot be stated as a single-run
invariant: a load leaves no trace in the state. The honest form is non-interference over two runs whose
memories agree on the region `R`. **Math's refuter pass (R3, 2026-09-26) drove two forms**: a lockstep
all-fuel one, which is a SECOND judgment beside `Spec`, and the TERMINAL one below, which is an
INSTANCE of `Spec` whose post nests a second `Spec`. This file takes the terminal form, so there is still
one judgment; the lockstep form is named in the design doc and not built. The definitions are ported
from that drive, whose Lean the helm ruled public-safe. -/

/-- Two memories agree on the region `R`. -/
def AgreeOnMem (R : BitVec 64 → Prop) (m m' : Mem) : Prop := ∀ a, R a → m.read a = m'.read a

/-- Two states differ at most in memory: every register, flag, `rip`, the oracle and `ms` equal. -/
def SameExceptMem (s₁ s₂ : Cpu) : Prop := ∃ m, s₂ = { s₁ with mem := m }

/-- The end memories may differ only where BOTH runs left their own start byte alone — a cell either
run wrote must hold the same byte in both (the write-then-read-back case). -/
def MemRel (s₁ s₂ t₁ t₂ : Cpu) : Prop :=
  ∀ a, t₁.mem.read a = t₂.mem.read a ∨ (t₁.mem.read a = s₁.mem.read a ∧ t₂.mem.read a = s₂.mem.read a)

/-- **READS ONLY `R`, terminal form.** Every `P`-run stops, and a second `P`-run from a state that differs
only in memory, agreeing on `R`, stops in a state that differs from the first's only in memory, and only
where neither run wrote. -/
def ReadsOnly (p : Program) (R : BitVec 64 → Prop) (P : Cpu → Prop) : Prop :=
  Spec p P (fun s₁ t₁ => t₁.stopped = true ∧
    ∀ s₂, P s₂ → SameExceptMem s₁ s₂ → AgreeOnMem R s₁.mem s₂.mem →
      Spec p (fun u => u = s₂)
        (fun _ t₂ => t₂.stopped = true ∧ SameExceptMem t₁ t₂ ∧ MemRel s₁ s₂ t₁ t₂))

end X86
