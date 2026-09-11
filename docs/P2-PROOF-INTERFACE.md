# The P2 proof interface — the two design decisions, answered by building them

**Commissioned:** council 2026-09-10, ruling ⑧. The Captain's words:
*"a semantics sufficient for proving safety properties (at least)"* ·
***"the proof interface that makes a twenty-instruction routine provable in tens of
lines, not thousands"*** · *"keep everything strictly public"* · *"Yes, paris in
parallel now."*

**Owner:** paris. **Derivation:** `docs/DECISIONS.md` D190.
**Artifacts:** `X86/Program.lean` (the interface) · `Tests/Program.lean` (worked, with
its nonvacuity).

> ⚠️ **A NAME COLLISION, SAID FIRST BECAUSE IT WILL OTHERWISE BE READ WRONG.**
> "P2" already names **the vector campaign** in `docs/QUEUE.md` (33 batches, live).
> The council's "P2" is the *phase deliverable* — this proof interface. **Two
> different things, one token**, and this repo has already been bitten by a gate
> named by a literal when `P1` became `P2`. Nothing here is named `P2` in code:
> the module is `X86.Program`, after what it is.

---

## ⛔⛔ THE FINDING THAT CAME BEFORE EITHER DESIGN QUESTION

Neither arm of either question was answerable, because **there was no execution
relation over a program to state them against.**

`X86.run` is `List.foldl step` over a list of decoded instructions. The branch
forms are modelled correctly — `jcc` evaluates its condition and calls
`setRipChecked` — but **the driver never reads `rip` back.** Measured at the
object, on `mov ecx,3` / `L: dec ecx` / `jne L`:

```
  ecx after run [mov, dec, jne]   = 2        (0 if it had looped; 2 is ONE pass)
  rip after the same              = 0x1005   (= L — the branch WAS taken)
  ms.isSome                       = false    (the model did NOT stop)
```

⇒ 🔑 ***THE BRANCH IS TAKEN IN THE SEMANTICS AND IGNORED BY THE DRIVER, AND THE
RESULT IS A WELL-FORMED `Cpu` WITH `ms = none`.*** It does not fault, refuse or
flag. It returns the straight-line answer — a perfectly good answer to a question
nobody asked. **No safety property of a routine with a taken branch could even be
STATED**, and nothing in the tree said so.

⚠️ **`run` IS NOT WRONG AND IS NOT REPLACED.** It is the shape the differential
harness drives against ACL2 x86isa, and it is correct for that. Both stay.

---

## (a) UNSTRUCTURED CONTROL FLOW — labelled blocks, or inductive reachability?

**ANSWER: the fork is not between them. They are one theorem seen from two sides,
and the real question is WHO PAYS THE INDUCTION.**

`runP_invariant` does the induction over execution **once**, in four lines, for
every program and every property. `atLabels I` is then the *definition*
`fun s => I s.rip s` — an assertion attached to each address, which is what a
label IS in machine code — and `runP_labels` is `runP_invariant` **applied**:

```lean
theorem runP_labels (p : Program) (I : BitVec 64 → Cpu → Prop)
    (hstep : ∀ s, I s.rip s → I (stepP p s).rip (stepP p s)) :
    ∀ (n : Nat) (s : Cpu), I s.rip s → I (runP p n s).rip (runP p n s) :=
  runP_invariant p (atLabels I) hstep
```

⇒ **There is no second logic, so there is no soundness theorem to owe and no gap
to audit.** A labelled-block logic built as its own layer would need a soundness
proof against exactly this relation; building the relation first makes that proof
`rfl`. **That is the whole argument for this order of work.**

### ⭐⭐ AND THE TIER THE MEASUREMENT ADDED, WHICH IS WHERE THE TARGET IS WON

The first proof written against `runP_invariant` alone got stuck immediately: to
know what `p.at? s.rip` returns you must know `s.rip`, so even *"this routine
writes no memory"* — a property with **nothing to do with control flow** — was
dragging in a case analysis over every label.

⇒ 🔑 ***A PROPERTY PRESERVED BY EVERY INSTRUCTION OF A PROGRAM IS AN INVARIANT OF
THAT PROGRAM, AND WHICH INSTRUCTION COMES NEXT IS IRRELEVANT TO IT.***

`runP_invariant_instrs` discharges those with **no labels, no per-point invariant,
and no branch reasoning at all** — and frame claims are most of what "safety"
means for a leaf routine. **Two tiers, and the user picks by one question: does
the property mention the program counter?**

| tier | obligation | use it for |
|---|---|---|
| `runP_invariant_instrs` | one per **instruction** of the program | frames: this memory / register / region is untouched; the model never stops |
| `runP_labels` | one per **label** | anything positional: "rdi is inside the buffer", loop bounds, post-conditions |
| `runP_invariant` | one, raw | the primitive both are built from |

---

## (b) MEMORY-SAFETY COMPOSITION — region invariants, or separation logic?

**ANSWER: regions. And the model decides it, not taste.**

`X86.Mem.read` is **TOTAL** — all 2^64 addresses defined, implicit zero background
— and that is a recorded, argued decision: the differential harness must
*enumerate* a memory to ship it to ACL2 x86isa. Separation logic's `P * Q` means
*the heap SPLITS into two disjoint parts*, and **a total memory has nothing to
split.** Doing separation logic here means first adding a footprint or permission
structure to `Cpu.mem`, which changes the type that **52 of the library's 298
theorems** state something about, plus every load/store arm of `step`.

**Regions cost nothing new and reuse what is already proven:** `Mem.span` is
already *"the addresses this access touches"*, and `Mem.readN_congr` is already
the frame lemma — *a read of `n` bytes is determined by the bytes in its own span*.
Only the vocabulary was missing: `Region`, `AgreeOutside`, and the disjointness
rule that lets a caller's buffer survive a callee's stores.

⛔ **WHAT THIS DEFERS, STATED AS A CONDITION RATHER THAN A WORRY.** Regions give no
procedure-modular frame rule: the user carries `AgreeOutside` explicitly, and a
routine that CALLS another must be reasoned about as one program. **For five leaf
routines that is a small, honest cost. At a call graph it is the wrong bill** —
and *that* is the condition under which this decision should be reopened, not a
change of taste.

---

## ⭐⭐⭐ THE TARGET, MEASURED

The Captain's criterion is a line count, so it is reported as one. `Tests/Program.lean`:

```
  the routine (3 instructions, WITH A LOOP)      5 lines of definition
  the safety theorem, all fuel, all start states  14 lines   ← "tens, not thousands"
     (2 of statement + 12 of proof; counted, not estimated — I first wrote 13)
  its nonvacuity (5 theorems, kernel-checked)     5 lines
```

The safety theorem is `∀ n s, (runP countdown n s).mem = s.mem` — quantified over
**every** start state and **every** amount of fuel, about a routine that really
loops.

⛔⛔ **THE NONVACUITY IS PART OF THE DELIVERABLE, NOT A COURTESY.** A theorem
"for all fuel, nothing bad happens" is TRUE AND WORTHLESS about a program that
halts on step one — and the entire reason this file exists is that the previous
driver silently did the wrong thing. So the trace is pinned by theorems *before*
the safety claim is believed, and **both were driven RED first**: claiming `run`
gives 3 fails, and claiming `runP` gives the fold's answer of 2 fails.

```
  step:  0     1      2      3      4      5      6      7      8
  rip:   1000  1005   1007   1005   1007   1005   1007   1009   1009
  ecx:   0     3      2      2      1      1      0      0      0   halted
                             ↑ the branch the fold could not take
```

---

## THE FIVE PROBLEMS THAT SIZE THIS (proposed; GS depends on them)

Named now because the council reshaped **GS** to *~5 x86 problems … depending on
your P2 interface*, and a hand-off that discovers its own sizing on the day stalls.

| # | routine | safety property | exercises |
|---|---|---|---|
| 1 | `memset`-style fill | every store lands inside the destination buffer | ✅ **BUILT** — regions, loop, **labelled tier** (see below; the "frame tier" in this cell was wrong) |
| 2 | `memcpy`-style copy | writes only `dst`; `src` unchanged | region **disjointness**, composition |
| 3 | `strlen`-style scan | reads stay inside the buffer; writes nothing | read-safety, frame tier |
| 4 | guarded array store | if the bounds check passes, the store is in range | **labelled** tier — positional |
| 5 | prologue / epilogue | push/pop balance; the caller's frame above RSP untouched | stack regions, the call/ret shape |

Between them they use both tiers, both halves of (b), and the branch-dependent
case that the frame tier deliberately cannot reach.

## ⛔ WHAT IS OWED NEXT, WITH ITS NUMBER

1. **The memory frame pack is 17 of 92 forms.** The frame pack frames `flags` (17)
   and `oracle` (6) because **those are what the differential comparator watches** —
   it was built for the harness's question, and memory safety is a different one.
   The three lemmas problem 1 needs are in `X86/Program.lean`; **75 forms are
   unstated**, and whether all of them belong in the pack is a sizing decision
   against the five problems, not a reflex.
2. **No `runP_add`** (`runP p (m+n) = runP p n ∘ runP p m`), which is what lets a
   proof be composed out of per-block runs. Cheap; not yet needed.
3. **Termination is not addressed and is not on the P2 path.** These are SAFETY
   properties: "for all fuel" says nothing about the routine finishing. Saying so
   here stops it being claimed later.

---

## ⚖️ PROBLEM 1 IS BUILT, AND IT REFUTES THIS DOCUMENT TWICE

`Tests/Program.lean`, `fill_writes_only_in_buffer`: *the routine writes only inside its
destination buffer*, ∀ fuel, ∀ initial memory. Axioms: the three standard ones.

### ⛔ REFUTATION 1 — it is NOT a frame-tier problem, and this document said it was
The table above sized problem 1 as "frame tier". **It cannot be.** The frame tier requires
every instruction to preserve the invariant *from any state satisfying it*, and
`mov rcx, 4` does not: it re-establishes the pointer/counter relation the loop body
maintains, so from an arbitrary mid-loop state it breaks the invariant. ⇒ **The safety of
this routine genuinely depends on WHERE the machine is.** The two-tier split is sound; my
assignment of this problem to a tier was not, and it took writing the proof to find out
[[feedback-inherited-diagnosis-is-a-hypothesis]].

### ⛔⛔ REFUTATION 2 — THE TARGET IS MISSED, AND BY MORE THAN A LITTLE
```
  countdown (FRAME tier, no labels) .......   14 lines   ✅ "tens"
  fill      (LABELLED tier, real safety) ..  152 lines   ⛔ against a target of "tens"
     of which LABEL-DISPATCH boilerplate ..   64  (42%)
     everything else ......................   88
```
⇒ 🔑 ***THE FRAME TIER HITS THE CAPTAIN'S CRITERION AND THE LABELLED TIER DOES NOT, AND
THE GAP IS NOT THE SAFETY ARGUMENT.*** 42% is mechanically deriving *"at this `rip` the
instruction is X"* and reducing the invariant's `if`-chain to this label's arm — the same
twenty lines five times, differing only in a literal.
⚠️ **Removing ALL of it still leaves 88**, so a dispatch tactic alone does not reach
"tens". Said here so the next head does not build one expecting it to.
⚠️ **NOT claimed: that 152 is the floor.** First proof, by the head that had just built
the interface, dispatch not yet factored. The re-run is the experiment and has not been done.

### ⇒ WHAT THIS BUYS: THE NEXT BUILD IS NAMED BY A MEASUREMENT
A **label-dispatch combinator** — given a `Program` over concrete addresses, produce
`at? L = some I` and the reduced invariant arm per label — removes ~64 lines here and
about as many from every later problem, because **the cost is per LABEL, not per
property**. That is the highest-value next item, and it is now sized rather than guessed.

### 📌 AND SEVEN LEMMAS THE INTERFACE SHIPPED WITHOUT
All seven are now in `X86/Program.lean`. The one that matters is **`agreeOutside_write`**
— *a write inside the region preserves the frame* — which **is** the memory-safety
argument for a store, and the region vocabulary shipped without it. ⇒ **Exactly the gap
the sizing exercise existed to find**, and an argument for building problem 2 before
declaring the vocabulary complete.

---

## ⭐⭐⭐ THE DISPATCH COMBINATORS WERE BUILT, AND THE PREDICTION HELD TO THE LINE

The section above named the next build from a measurement — *"a label-dispatch combinator …
removes ~64 lines here"* — and warned in the same breath that **removing all of it still leaves
88**. Both were then tested:
```
  problem 1, first proof ....................... 152 lines
  problem 1, after `stepP_at` / `stepP_off` / `atTable` ...  88     ⇐ the 64, exactly
  its invariant (one `Loop` for four label arms) ......  14 → 10
```
⇒ 🔑 ***A PRE-REGISTERED PREDICTION THAT CARRIED ITS OWN CEILING.*** The 42% win is real and it
is not progress toward the target, because the prediction said so before it was measured — which
is the only thing that stops a large improvement being read as arrival
[[feedback-a-pass-at-97-percent-is-not-headroom]].

⚠️ **`atTable` is the one that did the work**, and the reason is worth keeping: an invariant
written as a nested `if`-chain over addresses needs a `show (0x1007 = 0x1000) = False from by
decide` at every label at every use site; the SAME invariant written as a table reduces at a
concrete label **by `rfl`**. Same information — the difference is whether the reduction is free.

## ⛔⛔ AND THE TARGET IS STILL MISSED FOR THE CASE THE CAPTAIN NAMED
His criterion is a **twenty-instruction routine**. Problem 1 has FIVE labels. Decomposed at the
object (per-label blocks measured at 6, 11, 10, 14 lines):
```
  lines ≈ 37 fixed + ~12 per LABEL
      5 labels →  ~98
     10 labels → ~157
     20 labels → ~277        ⛔ not "tens of lines"
```
⇒ 🔑 ***THE COST IS LINEAR IN LABELS AT ~12 LINES EACH, SO THE TWENTY-INSTRUCTION CASE IS ~280
LINES.*** Better lemmas cannot close that: they moved the constant from ~25 to ~12, and a second
round would move it less. **Reaching "tens" at twenty instructions needs the per-label constant
near ZERO — a TACTIC that discharges a label, not more lemmas.**
⚠️ **NOT CLAIMED:** that ~12 is the floor for a lemma-based approach, or that the extrapolation
is exact. It is linear in four measured blocks, and a routine with harder branch structure would
cost MORE per label, not less.

### ⇒ THE HONEST STATE OF THE COMMISSION
The interface **meets** the criterion for frame-shaped safety properties (14 lines, and the
countdown has a loop). It **does not** meet it for position-dependent ones at the size the
Captain named, and the gap is now a measured constant with a named remedy rather than an
impression. **That is what sizing by five problems was for, and it took one problem to find it.**

---

## ⭐⭐⭐ THIRD POINT ON THE CURVE — `runP_code`, AND THE FEASIBILITY QUESTION IS SETTLED

The dispatch was then done **once**, in a lemma proved for every program and every invariant
(`X86.runP_code`): it absorbs the `by_cases` on `rip`, the `at? L = some i` derivation, the
`stepP` unfolding, and **the entire off-program case**. Problem 1 was re-proved through it.
```
  naive (if-chain invariant, by_cases per label) ....  152 lines   ≈ 25   / label
  + stepP_at / stepP_off / atTable ..................   88         ≈ 12   / label
  + runP_code .......................................   67         ≈  9.6 / label
```
⇒ 🔑 ***THE CONSTANT FELL 13, THEN 2.4 — AND "a second round would move it less" WAS WRITTEN
BEFORE THE SECOND ROUND.*** Two pre-registered predictions, both held: the 64-line saving to the
line, and the flattening.

### ⛔⛔ THE ANSWER TO THE COMMISSION'S FEASIBILITY QUESTION
At **9.6 lines per label**, the Captain's **twenty-instruction** routine is **~211 lines**.
"Tens of lines" needs ~2-3 per label.
⇒ **NO LEMMA LIBRARY REACHES THE TARGET FROM HERE.** The residue after `runP_code` is one
`rcases` over the code list plus, per label, the effect theorem and the invariant arm — **that
residue is the real content**, which is exactly why the curve is flattening and why more lemmas
will not move it. **The target needs a TACTIC that discharges a label, or a VC generator.**
⚠️ **NOT CLAIMED:** that 9.6 is a proven floor. It is three points and a shape. A fourth round of
lemma work is the cheap way to falsify this, and it should be run before anyone commits to
building a tactic.

### ⇒ WHAT THIS MEANS FOR THE COMMISSION, PLAINLY
The interface **meets** the criterion for **frame-shaped** properties (14 lines, with a loop). For
**position-dependent** ones it is ~9.6 × labels, so it meets the criterion at ~5 instructions and
misses it at 20. **The deliverable is honest and incomplete, and the gap is now a measured
constant with a named remedy** — which is more useful than a number that flattered it.



---

## ⭐⭐ ROUND 4 (2026-09-10) — PRE-REGISTERED, CONFIRMED ON ALL FOUR FIGURES, AND IT CORRECTS THIS DOCUMENT'S OWN CONCLUSION

Run because the previous bank named it as the cheap way to FALSIFY the 9.6 floor *"before anyone
commits to building a tactic."* The prediction and its refutation threshold were written down
**before any code was touched**:
```
  predicted   6–10 lines removed · 57–61 total · 7.4–8.4 /label · constant falls 1.2–2.2 (< 2.4)
  REFUTATION THRESHOLD, declared in advance:  ≤ 45 lines (≈5.2 /label)
  measured    10 lines removed  · 57 total   · 7.6 /label      · constant fell 2.0
```
**All four held; the refutation threshold was not reached.** Four points now: **25 → 12 → 9.6 → 7.6.**

### ⛔ AND THE HONEST READING WEAKENS THIS DOCUMENT'S ASYMPTOTE ARGUMENT
The falls are **13.0, then 2.4, then 2.0.** This document said *"lemma engineering is asymptoting
near ~9-10 lines each"* on two falls, where 13.0 → 2.4 looked like rapid decay. **A third fall of
2.0 says the decay STALLED rather than continued** — after the first big win the rounds are running
at roughly a constant ~2/round, and at that rate 7.6 → ~2.5 is two or three more rounds, which is
**not obviously infeasible.**
⇒ 🔑 ***THE ROUND-OVER-ROUND DECAY ARGUMENT IS WEAKER THAN THIS DOCUMENT CLAIMED. What still carries
the conclusion is the RESIDUE ARGUMENT, and it is the one that was pre-registered:*** every label
must still (i) unpack the invariant, (ii) name its effect theorem, (iii) re-establish the invariant
with its arithmetic — **≥4 lines/label of CONTENT**, so ≥ 19 + 4×20 = **99 lines at twenty
instructions**, still not "tens". The ceiling does the work here, not the curve.

### ⭐ AND WHERE ROUND 4'S WIN CAME FROM IS ITSELF THE ARGUMENT FOR A TACTIC
**Not one new lemma was added.** The 10 lines came from:
* **7 lines** — deleting `show s.rip + BitVec.ofNat 64 N = (LABEL) by rw [hrip]; rfl` at 4 of 5
  labels and both jcc arms. **Defeq already handled it**; the `show` was pure ceremony. (Block 2
  keeps its explicit form: there the rip also feeds the effective-address computation, so the
  blanket rewrite changes a second site.)
* **3 lines** — `regcalc`, a **MACRO**, replacing a six-way `simp only` unfolding repeated at three
  sites with differing `Flags.*` lemmas.
⇒ ***THE REPETITION THAT REMAINS IS IN THE TACTIC SCRIPT, NOT IN THE MATHEMATICS.*** There was no
proposition to state — only a normalisation to re-run, which is why a macro captured it and a lemma
could not. **That is evidence for the tactic/VC-generator conclusion arriving from a new direction:
the thing that paid this round was tactic-shaped work.**


---

## ⭐⭐⭐ PROBLEM 2 (`memcpy`) — THE LINEARITY CLAIM TESTED AT A SECOND LABEL COUNT

Everything above extrapolates `19 fixed + ~7.6 per LABEL` **from one routine with five labels.**
A model fitted at a single point and extrapolated four-fold is an argument, not a measurement.
`memcpy` has **seven** labels, and a structurally harder invariant — TWO pointers advancing at
different points in the loop body, so the assertion carries a separate offset for each.

```
  model from `fill` (5 labels):  19 + 7.6 x 7  ⇒  PREDICTED 72 lines
  measured on `memcpy` (7):                       ACTUAL    76 lines   (8.1 / label)
  blocks: 4 · 7 · 7 · 7 · 7 · 10 · 19            error: +5.6%
```
⇒ 🔑 ***THE LINEARITY HOLDS ACROSS ROUTINES AND LABEL COUNTS, TO WITHIN 6%.*** The twenty-label
extrapolation now rests on two points at different counts rather than one, and the per-label
constant came out **slightly HIGHER** (8.1 vs 7.6), which is the direction a harder invariant
predicts — so the model is, if anything, optimistic.
⇒ **At twenty labels: `19 + 8.1×20` = ~181 lines.** The conclusion is unchanged and is now
supported by an independent routine: **no lemma library reaches "tens of lines"; it needs a tactic
or a VC generator.**

### ⭐ AND THE INTERFACE ITSELF CAME OUT WELL — THE SECOND ROUTINE COST ONE AUTHORING PASS
`memcpy_safe` **went through on the first build attempt.** That is worth separating from the line
count, because the two say different things:
* **The interface WORKS for transfer.** `runP_code`, `atTable`, `agreeOutside_write`, `stepP_at`
  and round 4's `regcalc` carried over to a new routine with no new library lemmas and no
  fighting. The structure of `fill`'s proof was reusable line for line.
* **And it still misses the Captain's criterion**, which is about LINES at twenty instructions,
  not about author effort.
⚠️ **A first-attempt pass is a suspect, and it was investigated rather than believed** — see the
nonvacuity theorems: the routine runs to completion (`rcx = 0`, `rip = 0x2016`, stopped), the bytes
**actually move** (`0xAA 0xBB 0xCC 0xDD` arrive at the destination from a SEEDED source, because a
zero background cannot tell COPIED from NEVER-WRITTEN), and the four-byte bound is **TIGHT**.
Axioms: `memcpy_safe` on exactly `[propext, Classical.choice, Quot.sound]`.


---

## ⭐⭐⭐ PROBLEM 3 — THE FRAME TIER PRICED, AND THE HALF THAT IS **NOT STATABLE**

Problem 3 is the `strlen`-style scan: *"reads stay inside the buffer; writes nothing."* **Its two
halves land in completely different places, and that is the finding.**

### 1. ✅ "WRITES NOTHING" IS THE FRAME TIER, AND HERE THE CAPTAIN'S CRITERION IS MET
`Tests.scan_writes_no_memory`, ∀ fuel ∀ start state, **no label and no branch reasoning.**
```
  countdown_writes_no_memory   3 instructions   14 lines
  scan_writes_no_memory        4 instructions   14 lines
```
⛔ **THOSE EQUAL NUMBERS ARE A COINCIDENCE AND MUST NOT BE READ AS "CONSTANT IN INSTRUCTIONS".**
`countdown`'s `simp only [...]` wraps onto TWO lines where `scan`'s fits on one, which exactly
cancels `scan`'s extra `rcases` arm and `rw`. **The real cost is ONE LINE PER INSTRUCTION** — one
alternative and one `rw` — on a fixed base of ~11.
⇒ **At twenty instructions ≈ 31 lines.** Against the labelled tier's ~181. ⇒ 🔑 ***THE TIER, NOT
THE LEMMA LIBRARY, IS WHAT DECIDES WHETHER THE TARGET IS MET*** — 1 line/instruction versus 8.1
lines/label is a factor of eight, and no amount of lemma engineering moved the labelled tier by
that much across four rounds.

### 2. ⛔⛔ "READS STAY INSIDE THE BUFFER" IS NOT STATABLE AS A SINGLE-RUN INVARIANT
`X86.Mem.read` is **TOTAL** — every one of the 2^64 addresses is defined. **A read outside the
buffer has no observable consequence**: no fault, no trap, nothing the state records. The new
`step_mov_reg_mem_mem` says it in one line — *a load's memory frame holds with no constraint on the
effective address, however wild.*
⇒ 🔑 ***THE MODEL RECORDS WHAT WAS WRITTEN AND NOWHERE RECORDS WHAT WAS READ, SO READ-SAFETY IS
INVISIBLE TO EVERY INVARIANT OVER ONE RUN.***

**The honest formulation is NON-INTERFERENCE (2-safety):** *the run's result depends only on the
bytes inside the buffer* — i.e. two initial memories agreeing on the buffer produce agreeing runs.
That is expressible with the existing `AgreeOutside` vocabulary, **but it quantifies over TWO RUNS**,
and every combinator this interface has is single-run:
```
  runP_invariant · runP_safe · runP_invariant_instrs · runP_labels · runP_code
      all of shape   ∀ n s, I s → I (runP p n s)
  relational lemmas in the library:  Mem.readN_congr only — one READ, not one RUN
```
⇒ ⛔ **PROBLEM 3 NEEDS A SHAPE THE INTERFACE DOES NOT HAVE** (a `runP_congr`: if two states agree on
everything the program reads, their runs agree). **This is a sizing finding, not a gap to patch by
reflex** — and it is a direct consequence of decision (b)'s own premise: *the same totality that
made separation logic pointless also makes read-safety unobservable in a single run.*

### 3. 📌 AND THE FRAME PACK WAS FITTED TO THE FIRST ROUTINE THAT NEEDED IT
The memory-frame lemmas shipped were `step_mov_reg_imm_mem`, `step_dec_reg_mem`, `step_jcc_mem` —
**exactly `countdown`'s three instructions.** The scan needed a LOAD and an `inc`, and both were
missing; `step_mov_reg_mem_mem` and `step_inc_reg_mem` are added here, two lines each.
⇒ **Third instance of the same shape in two days** (`agreeOutside_write`, `region_disjoint_of_le`,
now these): **a library grown one proof at a time contains exactly what the last proof needed.**


---

## 📐 PROBLEM 5 — A FEASIBILITY PROBE, NOT A PROOF (2026-09-10)

⚠️ **LABELLED AS A PROBE.** Nothing is built. This sizes problem 5 the way the problem-3 probe sized
read-safety, so the five-problem table GS depends on is not discovering its own shape on the day.

### ✅ THE MODEL SUPPORTS IT
`push`/`pop` are in the AST (`X86/Syntax.lean`) and the semantics (`X86/Semantics.lean:181-187`:
push decrements `rsp` by `sz.bytes` then writes; pop reads then increments), with effect theorems
`step_push_reg`, `step_pop_reg` and — separately — **`step_pop_rsp`**, because popping INTO `rsp`
is its own case.

### ⛔ BUT ITS REGION IS A HALF-LINE, AND `Region` ONLY BUILDS INTERVALS
*"The caller's frame above RSP is untouched"* is a frame claim whose region is **`{a | rsp₀ ≤ a}`** —
unbounded — where `fill` and `memcpy` both used **`Region base len`**, a bounded interval.
```
  AgreeOutside (R : BitVec 64 → Prop)          ✅ takes ANY predicate — the half-line is expressible
  agreeOutside_write  {R : BitVec 64 → Prop}   ✅ generic in R — a push's write reuses it unchanged
  region_disjoint_of_le                        ⛔ stated for TWO `Region`s — does NOT reach a half-line
```
⇒ **The frame half transfers for free; the DISJOINTNESS half does not.** Problem 5 needs a
containment/disjointness rule for a half-line — *"everything the routine writes is strictly below
`rsp₀`"* — which is a fourth instance of the pattern already recorded three times: `agreeOutside_write`,
`region_disjoint_of_le`, the load/`inc` frame lemmas, and now this.
⚠️ **And the same wraparound trap applies, with more force**: `rsp₀ ≤ a` is a `BitVec 64` comparison,
and a stack near address 0 wraps. `region_wrap_defeats_order` is the witness that this is not
pedantry — the analogous no-wrap hypothesis will be load-bearing here too.

### ⇒ THE FIVE-PROBLEM TABLE, AS MEASURED RATHER THAN PROPOSED
| # | tier | status |
|---|---|---|
| 1 `fill` | **labelled** (the doc said frame; the proof refuted it) | ✅ built · 57 lines / 7.6 per label |
| 2 `memcpy` | labelled | ✅ built · 76 lines / 8.1 per label · **linearity confirmed at a 2nd count** |
| 3 `scan` | **frame** for "writes nothing"; **2-safety** for "reads in bounds" | ✅ half built (~1 line/instr) · ⛔ half **NOT STATABLE** single-run |
| 4 guarded store | labelled, positional | ⬜ not started |
| 5 prologue/epilogue | frame, but over a **HALF-LINE** region | ⬜ probed only — needs a half-line disjointness rule |
⇒ 🔑 ***THREE OF THE FIVE TURNED OUT TO SIT IN A DIFFERENT TIER OR SHAPE THAN THE TABLE ORIGINALLY
ASSIGNED THEM*** — 1 (frame→labelled), 3 (half of it not a single-run property at all), 5 (interval →
half-line). **The tier assignment is a hypothesis about a problem, and writing the proof is what tests
it.**
