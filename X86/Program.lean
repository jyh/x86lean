/-
# X86.Program — the PROGRAM-INDEXED execution relation, and the proof interface over it

**Council 2026-09-10, ruling ⑧, the Captain's words:** *"a semantics sufficient
for proving safety properties (at least)"* — *"the proof interface that makes a
twenty-instruction routine provable in tens of lines, not thousands."*

## ⛔⛔ WHY THIS FILE EXISTS: `run` COULD NOT EXPRESS A LOOP, AND SAID SO IN NO WAY

`X86.run` is `List.foldl step` over a list of decoded instructions.  The branch
forms are modelled correctly — `jcc` evaluates its condition and calls
`setRipChecked` — but the DRIVER never reads `rip` back, so it takes the next
list element regardless.  Measured at the object 2026-09-10, on the three
instructions `mov ecx,3` / `L: dec ecx` / `jne L`:

```
  ecx after run [mov, dec, jne]   = 2      (0 if the loop had run; 2 is ONE pass)
  rip after the same             = 0x1005  (= L: the branch WAS taken)
  ms.isSome                      = false   (the model did NOT stop)
```

⇒ 🔑 ***THE BRANCH IS TAKEN IN THE SEMANTICS AND IGNORED BY THE DRIVER, AND THE
RESULT IS A WELL-FORMED `Cpu` WITH `ms = none`.*** It does not fault, refuse, or
flag; it returns the straight-line answer, which is a perfectly good answer to a
question nobody asked.  That is the shape this campaign has recorded repeatedly
under [[a tool has no concept of "not applicable"]]: an instrument that ANSWERS
where it should REFUSE.

⚠️ **`run` IS NOT THEREBY WRONG AND IS NOT REPLACED.** It is the shape the
differential harness drives (one decoded instruction, or a short straight-line
list, against ACL2 x86isa) and it is correct for that.  What it is not is an
execution relation over a PROGRAM, and no safety property of a routine with a
taken branch can even be STATED through it.  Both files stay.

## THE DESIGN DECISION THIS FILE RECORDS (docs/P2-PROOF-INTERFACE.md, D190)

The council named two design questions as this seat's first.  On (a) —
*a logic over labelled basic blocks, or an inductive invariant over the
reachable-state relation* — the measured answer is that **they are the same
theorem seen from two sides, and the fork is not between them but over WHO PAYS
THE INDUCTION.**  `runP_invariant` below does the reachability induction ONCE,
in four lines, for every program and every property.  `atLabels` is then a
DEFINITIONAL abbreviation — `I s.rip s` — that makes the user's obligation
per-label without introducing a second logic, a VC generator, or a soundness
gap.  A labelled-block logic built as its own layer would need its own soundness
theorem against exactly this relation; building the relation first makes that
theorem `rfl`.

⛔ **THE COST IS NAMED, NOT HIDDEN:** this gives no procedure-modular frame rule.
A routine that CALLS another routine must, today, be reasoned about as one
program.  That is the right bill for five leaf routines and the wrong one for a
call graph; see the doc's "what this defers".

LANE. Personal lane, public sources only.  No mathlib (D1); Lean core only.
-/
import X86.Theorems

namespace X86

/-! ## The program

⚠️ **THE REPRESENTATION MIRRORS `Mem` ON PURPOSE, AND FOR THE SAME REASON.**
`X86.Mem` is a TOTAL function in the semantics with a finite association list as
its representation, because the differential harness has to enumerate it.  A
program has the same two needs — a total `at?` for the theorems, an enumerable
list for any future harness that ships one — so it gets the same shape and the
same seam.  A later swap to a tree or an array leaves every proof below
untouched. -/
structure Program where
  /-- The instruction at each address it defines, most-recent-first. -/
  code : List (BitVec 64 × Instr) := []
  deriving Repr, Inhabited

namespace Program

/-- The instruction at `a`, if this program defines one. -/
def at? (p : Program) (a : BitVec 64) : Option Instr :=
  (p.code.find? (fun q => q.1 == a)).map (·.2)

/-- Does the program define an instruction at `a`? -/
def Defined (p : Program) (a : BitVec 64) : Prop := (p.at? a).isSome = true

@[simp] theorem at?_empty (a : BitVec 64) : (({} : Program)).at? a = none := rfl

end Program

/-! ## The program-indexed small step

The one difference from `X86.step`: the instruction is FETCHED AT `rip` rather
than handed in.  Everything else — the stopped check, the semantics, the flags,
the oracle draws — is `step` unchanged.  This is deliberately a thin wrapper and
not a second semantics: a second semantics would need a theorem saying the two
agree, and the theorem would be the only thing keeping them honest. -/

/-- One step of `p` from `s`: fetch at `rip`, then `step`.

**Running off the code STOPS the model** (`MsErr.outsideProgram`), which is how a
routine returns here.  Because `step_stopped` pins a stopped state, "the routine
has finished" is stable under more fuel — the property that makes a fuel-indexed
run usable for a proof about a routine whose length you do not want to count. -/
def stepP (p : Program) (s : Cpu) : Cpu :=
  if s.stopped then s else
  match p.at? s.rip with
  | some i => step i s
  | none => s.halt (.outsideProgram "no instruction at RIP")

/-- Run `n` steps of `p`.  Fuel, not a partial function: the model is total and
stays total, and a `Nat` bound is what lets the invariant principle below be an
ordinary induction with no well-founded recursion and no termination side
condition. -/
def runP (p : Program) : Nat → Cpu → Cpu
  | 0, s => s
  | n + 1, s => runP p n (stepP p s)

@[simp] theorem runP_zero (p : Program) (s : Cpu) : runP p 0 s = s := rfl

@[simp] theorem runP_succ (p : Program) (n : Nat) (s : Cpu) :
    runP p (n + 1) s = runP p n (stepP p s) := rfl

/-- A stopped model does not move, program or no program.  The `stepP` half of
`step_stopped`, and what makes a finished routine stay finished. -/
@[simp] theorem stepP_stopped (p : Program) (s : Cpu) (h : s.stopped = true) :
    stepP p s = s := by simp [stepP, h]

/-- …and therefore for any amount of fuel. -/
@[simp] theorem runP_stopped (p : Program) (n : Nat) (s : Cpu) (h : s.stopped = true) :
    runP p n s = s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [runP, stepP_stopped p s h, ih s h]

/-! ## ⭐⭐⭐ THE INVARIANT PRINCIPLE — the whole proof interface, proved once

This is the "inductive invariant over the reachable-state relation" arm of the
council's design question (a), and it is four lines.  Every proof about every
program in this repository goes through it, so the induction over execution is
paid exactly once, here, rather than once per routine. -/

/-- If `I` survives one program step, it survives any number of them. -/
theorem runP_invariant (p : Program) (I : Cpu → Prop)
    (hstep : ∀ s, I s → I (stepP p s)) :
    ∀ (n : Nat) (s : Cpu), I s → I (runP p n s) := by
  intro n
  induction n with
  | zero => intro s h; exact h
  | succ n ih => intro s h; exact ih _ (hstep s h)

/-- A safety property is an invariant plus an implication: if `I` is preserved
and `I` implies `Good`, then every state the routine can reach is `Good`. -/
theorem runP_safe (p : Program) (I Good : Cpu → Prop)
    (hstep : ∀ s, I s → I (stepP p s)) (himp : ∀ s, I s → Good s)
    (n : Nat) (s : Cpu) (h0 : I s) : Good (runP p n s) :=
  himp _ (runP_invariant p I hstep n s h0)

/-! ## ⭐⭐⭐ THE FRAME TIER — an invariant with NO control-flow reasoning at all

⭐ **THE MEASUREMENT THAT PUT THIS TIER HERE.** The first proof written against
`runP_invariant` alone got stuck in the obvious place: to know what
`p.at? s.rip` returns you must know `s.rip`, so even *"this routine writes no
memory"* — a property with nothing whatever to do with control flow — was
dragging in a case analysis over every label.

⇒ 🔑 ***A PROPERTY PRESERVED BY EVERY INSTRUCTION OF A PROGRAM IS AN INVARIANT
OF THAT PROGRAM, AND KNOWING WHICH INSTRUCTION IS NEXT IS IRRELEVANT TO IT.***
That is most of what "safety" means for a leaf routine — a frame claim: this
register is untouched, this memory region is untouched, the model never stops.
This tier discharges those with **no labels, no invariant per program point, and
no reasoning about branches**, which is where the "tens of lines, not thousands"
target is actually won.

⚠️ **IT IS STRICTLY WEAKER AND THAT IS THE TRADE.** It cannot prove anything
that depends on WHERE you are — "rdi is inside the buffer" is true at the loop
head and false nowhere else expressible without the label. Those go to
`runP_labels` below. **Two tiers, and the user picks by whether the property
mentions the program counter.** -/

/-- An instruction fetched from `p` is one of `p`'s instructions. -/
theorem Program.at?_mem {p : Program} {a : BitVec 64} {i : Instr}
    (h : p.at? a = some i) : ∃ b, (b, i) ∈ p.code := by
  unfold Program.at? at h
  cases hf : p.code.find? (fun q => q.1 == a) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some q =>
      rw [hf] at h
      simp only [Option.map_some] at h
      obtain ⟨b, j⟩ := q
      cases h
      exact ⟨b, List.mem_of_find?_eq_some hf⟩

/-- ⭐ THE FRAME-TIER PRINCIPLE: a property preserved by every instruction the
program contains, and by halting, is preserved by the whole run — with no
reference to `rip` anywhere in the obligation. -/
theorem runP_invariant_instrs (p : Program) (I : Cpu → Prop)
    (hhalt : ∀ s e, I s → I (s.halt e))
    (hinstr : ∀ b i s, (b, i) ∈ p.code → I s → I (step i s)) :
    ∀ (n : Nat) (s : Cpu), I s → I (runP p n s) := by
  refine runP_invariant p I (fun s hs => ?_)
  unfold stepP
  split
  · exact hs
  · cases hf : p.at? s.rip with
    | none => simpa [hf] using hhalt s _ hs
    | some i =>
        obtain ⟨b, hb⟩ := Program.at?_mem hf
        simpa [hf] using hinstr b i s hb hs

/-! ## ⭐⭐ THE LABELLED-BLOCK INTERFACE — arm (a)'s other side, as an abbreviation

`atLabels I` is `fun s => I s.rip s`: an assertion attached to each ADDRESS,
which is what a label IS in a machine-code program.  ⛔ **IT IS A DEFINITION AND
NOT A NEW LOGIC**, so `runP_labels` below is `runP_invariant` applied — the two
arms of design question (a) are related by `rfl`, and there is no soundness
theorem to owe because there is no second system.

**How the user writes an invariant.** For a routine with labels `L0 L1 L2`,
`I a s` is a `match a with | L0 => … | L1 => … | _ => True`-shaped function.
The `_ => True` arm is what makes the obligation FINITE: every address outside
the routine carries the trivial assertion, so the VC there is discharged by
`trivial` and the user writes one case per label, not one per address. -/

/-- An address-indexed assertion, read at the current `rip`. -/
def atLabels (I : BitVec 64 → Cpu → Prop) (s : Cpu) : Prop := I s.rip s

/-- The labelled-block principle.  Note the proof: the labelled form IS the
invariant form, so this is application and not translation. -/
theorem runP_labels (p : Program) (I : BitVec 64 → Cpu → Prop)
    (hstep : ∀ s, I s.rip s → I (stepP p s).rip (stepP p s)) :
    ∀ (n : Nat) (s : Cpu), I s.rip s → I (runP p n s).rip (runP p n s) :=
  runP_invariant p (atLabels I) hstep

/-! ## ⛔⛔ THE MEMORY FRAME LEMMAS THE FRAME PACK DOES NOT CARRY

**FOUND BY WRITING THE PROOF, NOT BY READING THE LIBRARY.** The first safety
theorem attempted against this interface — *"this routine never writes memory"*,
about a three-instruction countdown loop — could not be finished, because none
of its three forms has a `.mem` frame lemma.

**MEASURED at the object 2026-09-10:**
```
  step_ effect theorems in X86/Theorems.lean ....  92 forms
  carrying a `.flags` frame lemma ...............  17
  carrying a `.mem`   frame lemma ...............  17   ← and NOT these three
```
⇒ 🔑 ***THE FRAME PACK WAS BUILT FOR THE DIFFERENTIAL HARNESS, AND IT FRAMES
WHAT THE COMPARATOR WATCHES.*** Flags and the oracle cursor are what a
differential run can disagree about, so those are the frames that got written.
A MEMORY-SAFETY proof needs the frame nobody had needed yet. The pack is not
wrong; it is complete for the question it was built for, and this is a different
question. **No blame and no rewrite — 75 forms are simply unstated.**

⚠️ **THESE THREE ARE HERE AND NOT IN `X86/Theorems.lean` DELIBERATELY.** That
module is the kernel-cost barrier (plan v1 §3.7) and carries per-declaration
ceilings; three lemmas added to the P2 interface cost nothing there, and the
question of whether all 75 belong in the pack is a sizing decision for the five
problems, not a thing to answer by reflex. **Filed, with its number, rather than
churned.** -/

theorem step_mov_reg_imm_mem (sz : Size) (r : GPR) (v : Val) {s : Cpu} {len : Nat}
    (h : Live s) : (step ⟨.mov sz (.reg r) (.imm v), len⟩ s).mem = s.mem := by
  rw [step_mov_reg_imm sz r v h]

theorem step_dec_reg_mem (sz : Size) (r : GPR) {s : Cpu} {len : Nat} (h : Live s) :
    (step ⟨.un .dec sz (.reg r), len⟩ s).mem = s.mem := by
  rw [step_dec_reg sz r h]

/-- ⭐ NOTE WHAT THIS ONE DOES **NOT** ASSUME: `step_jcc` carries a canonicality
hypothesis, because the equation for the branch depends on whether the target is
canonical.  The MEMORY frame does not — a non-canonical target halts the model,
and halting leaves memory alone — so this lemma is stated with no side
condition at all and is usable at a branch whose target the caller has not
characterised. **A frame is often provable under weaker hypotheses than the
equation it comes from, and taking the equation's hypotheses by habit would
have put a canonicality obligation into every memory-safety proof in the
campaign.** -/
theorem step_jcc_mem (c : Cc) (d : Val) {s : Cpu} {len : Nat} (h : Live s) :
    (step ⟨.jcc c d, len⟩ s).mem = s.mem := by
  simp only [step, h, Cpu.setRipChecked, Cpu.setRip, Cpu.halt, Cpu.stopped,
    Option.isSome_none, Bool.false_eq_true, if_false, Op.lockIllegal]
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

/-! ## ⭐⭐ MEMORY SAFETY BY REGIONS — the council's design question (b)

The council asked: explicit region invariants, or separation logic.  **The model
decides it, not taste.** `X86.Mem.read` is TOTAL — every one of the 2^64
addresses is defined, with an implicit zero background — and that is a recorded,
argued design decision (the differential harness must enumerate a memory to ship
it to ACL2 x86isa).  Separation logic's `P * Q` means *the heap SPLITS into two
disjoint parts*, and **a total memory has nothing to split**: doing separation
logic here means first adding a footprint or permission structure to `Cpu.mem`,
which changes the type that **52 of this library's 298 theorems** state
something about, and every load/store arm of `step`.

⇒ **Regions cost nothing new and reuse what is already proven.** `Mem.span` is
already "the addresses this access touches", and `Mem.readN_congr` is already
the frame lemma — *a read of `n` bytes is determined by the bytes in its own
span*.  What is missing is only the vocabulary below.

⛔ **WHAT THIS DEFERS, SAID NOW RATHER THAN DISCOVERED LATER:** regions give no
FRAME RULE, so a proof does not automatically forget the memory it does not
touch — the user carries `AgreeOutside` explicitly.  For five leaf routines that
is a small, honest cost.  At a call graph it is the wrong bill, and that is the
condition under which this decision should be reopened, stated as a condition
rather than as a worry. -/

/-- The addresses `[base, base + len)`, as a predicate. -/
def Region (base : BitVec 64) (len : Nat) (a : BitVec 64) : Prop :=
  ∃ i, i < len ∧ a = base + BitVec.ofNat 64 i

/-- Two memories that agree everywhere OUTSIDE `R`.  This is the frame
assertion: "the routine wrote only inside `R`". -/
def AgreeOutside (R : BitVec 64 → Prop) (m m' : Mem) : Prop :=
  ∀ a, ¬ R a → m.read a = m'.read a

/-- `AgreeOutside` is reflexive — a step that writes nothing frames trivially. -/
@[simp] theorem agreeOutside_rfl (R : BitVec 64 → Prop) (m : Mem) :
    AgreeOutside R m m := fun _ _ => rfl

/-- …and transitive, which is what makes it compose along a run. -/
theorem agreeOutside_trans {R : BitVec 64 → Prop} {m₁ m₂ m₃ : Mem}
    (h₁ : AgreeOutside R m₁ m₂) (h₂ : AgreeOutside R m₂ m₃) :
    AgreeOutside R m₁ m₃ := fun a ha => (h₁ a ha).trans (h₂ a ha)

/-- ⭐ THE COMPOSITION RULE THE FIVE PROBLEMS NEED: if a routine wrote only
inside `R`, then anything a DISJOINT region `R'` holds is unchanged — so a
caller's buffer survives a callee's scribbling, provided the two are disjoint.
This is what separation logic's frame rule buys, stated for two named regions
instead of for an arbitrary heap split. -/
theorem read_of_agreeOutside_disjoint {R R' : BitVec 64 → Prop} {m m' : Mem}
    (hfr : AgreeOutside R m m') (hdisj : ∀ a, R' a → ¬ R a)
    (a : BitVec 64) (ha : R' a) : m.read a = m'.read a :=
  hfr a (hdisj a ha)

/-- The same, lifted to a multi-byte read: a whole `sz`-wide operand inside a
disjoint region reads unchanged.  Proved through `Mem.readN_congr`, the frame
lemma the memory model already carried. -/
theorem readSize_of_agreeOutside_disjoint {R R' : BitVec 64 → Prop} {m m' : Mem}
    (hfr : AgreeOutside R m m') (hdisj : ∀ a, R' a → ¬ R a)
    (sz : Size) (a : BitVec 64)
    (hin : ∀ i, i < sz.bytes → R' (a + BitVec.ofNat 64 i)) :
    m.readSize sz a = m'.readSize sz a :=
  Mem.readN_congr m m' a sz.bytes
    (fun i hi => hfr _ (hdisj _ (hin i hi)))

/-! ## ⭐⭐ THE VOCABULARY PROBLEM 1 NEEDED, AND DID NOT FIND HERE

Every lemma below was written while proving `Tests.fill_writes_only_in_buffer` — the
`memset`-style fill, problem 1 of the five — and every one is general.  They are here
rather than in that test because **the second problem will need all seven**, and
discovering them one at a time in each proof is how a "proof interface" turns out to be
a pile of per-proof scaffolding.

⚠️ **`agreeOutside_write` IS THE ONE THAT MATTERS**: it is the whole memory-safety
argument for a store — *a write inside the region preserves the frame* — and the region
vocabulary shipped without it, which is exactly the gap the sizing exercise existed to
find. -/

/-- A write INSIDE the region preserves the frame. -/
theorem agreeOutside_write {R : BitVec 64 → Prop} {m0 m : Mem} (h : AgreeOutside R m0 m)
    {a : BitVec 64} {v : BitVec 8} (hin : R a) : AgreeOutside R m0 (m.write a v) := by
  intro x hx
  have hne : x ≠ a := fun hh => hx (hh ▸ hin)
  rw [Mem.read_write_ne _ _ _ _ hne]
  exact h x hx

@[simp] theorem halt_mem (s : Cpu) (e : MsErr) : (s.halt e).mem = s.mem := by
  unfold Cpu.halt; split <;> rfl

@[simp] theorem halt_rip (s : Cpu) (e : MsErr) : (s.halt e).rip = s.rip := by
  unfold Cpu.halt; split <;> rfl

@[simp] theorem halt_regs (s : Cpu) (e : MsErr) : (s.halt e).regs = s.regs := by
  unfold Cpu.halt; split <;> rfl

@[simp] theorem halt_flags (s : Cpu) (e : MsErr) : (s.halt e).flags = s.flags := by
  unfold Cpu.halt; split <;> rfl

theorem ofNat_succ_64 (k : Nat) :
    BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, Nat.add_mod]

theorem live_of_not_stopped {s : Cpu} (h : ¬ s.stopped = true) : Live s := by
  unfold Cpu.stopped at h
  cases hm : s.ms with
  | none => exact hm
  | some e => rw [hm] at h; simp at h

/-! ## ⭐⭐⭐ THE LABEL-DISPATCH COMBINATORS — built because problem 1 MEASURED their absence

Problem 1's first proof was **152 lines, 64 of them (42%) label-dispatch boilerplate**: the same
twenty lines five times, deriving *"at this `rip` the instruction is X"* and reducing the
invariant to this label's arm. **The number was measured, then these three were written, then
the proof was re-run: 152 → 88 — exactly the 64 predicted.**

⇒ 🔑 ***THE PREDICTION WAS PRE-REGISTERED AND CONFIRMED TO THE LINE***, including its warning
that removing the dispatch **still leaves 88** — so the win could not be read as reaching the
target. `Tests/Program.lean` carries what 88 does and does not buy.

⚠️ **`atTable` DOES MOST OF THE WORK.** An invariant written as a nested `if`-chain over
addresses needs a `show (0x1007 = 0x1000) = False from by decide` at every label at every use
site; written as a TABLE it reduces at a concrete label **by `rfl`**. Same information — the
difference is whether the reduction is free. -/

/-- Dispatch: at a defined address, `stepP` is `step` of the instruction there. -/
theorem stepP_at {p : Program} {s : Cpu} {i : Instr}
    (hst : ¬ s.stopped = true) (h : p.at? s.rip = some i) : stepP p s = step i s := by
  simp [stepP, hst, h]

/-- Dispatch: off the program, `stepP` halts. -/
theorem stepP_off {p : Program} {s : Cpu}
    (hst : ¬ s.stopped = true) (h : p.at? s.rip = none) :
    stepP p s = s.halt (.outsideProgram "no instruction at RIP") := by
  simp [stepP, hst, h]

/-- ⭐ THE INVARIANT AS A TABLE rather than an `if`-chain: a per-label assertion with
`True` off the table.  At a CONCRETE label this reduces by `rfl`, where an `if`-chain
needed a `show (0x1007 = 0x1000) = False from by decide` per label per use site. -/
def atTable (tbl : List (BitVec 64 × (Cpu → Prop))) (a : BitVec 64) (s : Cpu) : Prop :=
  match tbl.find? (fun q => q.1 == a) with
  | some q => q.2 s
  | none => True

/-! ## ⭐⭐⭐ `runP_code` — THE DISPATCH DONE ONCE, AND THE THIRD POINT ON A MEASURED CURVE

Problem 1's preservation proof has now been written three ways, and the per-label cost is the
number that matters, because **the cost is linear in labels**:
```
  naive (if-chain invariant, by_cases per label) ....  152 lines   ≈ 25 / label
  + stepP_at / stepP_off / atTable ..................   88         ≈ 12 / label
  + runP_code (this) ................................   67         ≈  9.6 / label
```
⇒ 🔑 ***LEMMA ENGINEERING IS ASYMPTOTING NEAR ~9-10 LINES PER LABEL***, and the prediction that
*"a second round would move it less"* was written before this round and held: the constant fell
13 then 2.4.

⛔ **THAT SETTLES THE COMMISSION'S FEASIBILITY QUESTION.** The Captain's target is a
TWENTY-instruction routine in "tens of lines". At 9.6/label that is **~211 lines**, and reaching
"tens" needs ~2-3 per label. **No lemma library gets there from here — it needs a tactic or a VC
generator.** Named on evidence rather than on taste.

**What `runP_code` removes, versus what the user still writes.** Gone entirely: the `by_cases` on
`rip`, the `at? L = some i` derivation, the `stepP` unfolding, and **the whole off-program case**.
What remains is one `rcases` over the code list — which substitutes each address and instruction
concretely — and then, per label, the effect theorem and the invariant arm. **That residue is the
real content, and it is why the curve is flattening.** -/

/-- The instruction fetched at `a` sits AT `a` in the code list. -/
theorem at?_mem_at {p : Program} {a : BitVec 64} {i : Instr}
    (h : p.at? a = some i) : (a, i) ∈ p.code := by
  unfold Program.at? at h
  cases hf : p.code.find? (fun q => q.1 == a) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some q =>
      rw [hf] at h
      simp only [Option.map_some] at h
      have hq : (q.1 == a) = true := List.find?_some (p := fun r : BitVec 64 × Instr => r.1 == a) hf
      have : q.1 = a := by simpa using hq
      obtain ⟨b, j⟩ := q
      cases h
      simp only at this
      cases this
      exact List.mem_of_find?_eq_some hf

/-- Transport a table assertion to another state, entry by entry.  The per-entry
obligation is what makes this sound: a general `q.2 s → q.2 t` is false, and for a
CONCRETE table each entry is discharged by `id` whenever it reads only fields the two
states share. -/
theorem atTable_of_congr {tbl : List (BitVec 64 × (Cpu → Prop))} {a : BitVec 64} {s t : Cpu}
    (hs : ∀ q ∈ tbl, q.2 s → q.2 t) (h : atTable tbl a s) : atTable tbl a t := by
  unfold atTable at h ⊢
  cases hf : tbl.find? (fun q => q.1 == a) with
  | none => trivial
  | some q =>
      rw [hf] at h
      exact hs q (List.mem_of_find?_eq_some hf) h

/-- ⭐⭐⭐ THE DISPATCH, DONE ONCE. To preserve `I` it is enough to preserve it across
each instruction the program CONTAINS, knowing the address it sits at — so the user
never writes a `by_cases` on `rip`, never derives `at? L = some I`, and never handles
the off-program case at all. -/
theorem runP_code (p : Program) (I : BitVec 64 → Cpu → Prop)
    (hhalt : ∀ (s : Cpu) (e : MsErr), Live s → I s.rip s → I s.rip (s.halt e))
    (hstep : ∀ (a : BitVec 64) (i : Instr) (s : Cpu), (a, i) ∈ p.code → s.rip = a →
       Live s → I a s → I (step i s).rip (step i s)) :
    ∀ (n : Nat) (s : Cpu), I s.rip s → I (runP p n s).rip (runP p n s) := by
  refine runP_labels p I (fun s hs => ?_)
  by_cases hst : s.stopped = true
  · rw [stepP_stopped p s hst]; exact hs
  have hl : Live s := by
    unfold Cpu.stopped at hst
    cases hm : s.ms with
    | none => exact hm
    | some e => rw [hm] at hst; simp at hst
  cases hf : p.at? s.rip with
  | none =>
      rw [stepP_off hst hf, halt_rip]
      exact hhalt s _ hl hs
  | some i =>
      rw [stepP_at hst hf]
      exact hstep s.rip i s (at?_mem_at hf) rfl hl hs

end X86
