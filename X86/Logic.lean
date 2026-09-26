/-
# X86.Logic — a Hoare-style program logic over `runP`, proved sound by construction

O38 (the Captain, 2026-09-10): *"we will want to write a paper for the x86 semantics — including
small-step operational semantics + ~hoare logic"*; 2026-09-11: *"two papers probably"*. Paper 1 is
the validated semantics; this file is the spine of paper 2. Design, arms and what refutes it:
`docs/P2-LOGIC-DESIGN.md` (D303).

## The judgment

`Spec p P Q` — from every state satisfying `P`, SOME amount of fuel reaches a state `t` with
`Q s t`. It is a TOTAL-correctness triple, and its postcondition is a RELATION between the start
state and the end state, because the statements this campaign actually proves are relational:
`CorrectFor` (the x86 SaltBench PoC) asks for `AgreeOutside … s.mem t.mem`, `CalleeSaved s t` and
`t.rsp = s.rsp + 8`, and none of those can be said about `t` alone without ghost variables.

⛔ **WHY TOTAL AND NOT PARTIAL.** `runP_invariant` already IS the partial/safety half: it quantifies
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

/-- **STOPPED IS FINAL.** A post that holds of a stopped state holds for any further fuel, so a
proof that reaches a halt may overshoot freely. `runP_stopped`, lifted to the judgment. -/
theorem runP_final {s : Cpu} (n m : Nat) (h : (runP p n s).stopped = true) :
    runP p (n + m) s = runP p n s := by
  rw [runP_add, runP_stopped p m _ h]

end Spec

end X86
