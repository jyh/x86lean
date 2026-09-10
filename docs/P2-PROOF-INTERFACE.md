# The P2 proof interface — the two design decisions, answered by building them

**Commissioned:** council 2026-09-10, ruling ⑧. The Captain's words:
*"a semantics sufficient for proving safety properties (at least)"* ·
***"the proof interface that makes a twenty-instruction routine provable in tens of
lines, not thousands"*** · *"keep everything strictly public"* · *"Yes, paris in
parallel now."*

**Owner:** paris. **Derivation:** `docs/DECISIONS.md` D190.
**Artifacts:** `X86/Program.lean` (the interface) · `Tests/Program.lean` (worked, with
its nonvacuity) .

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
  the safety theorem, all fuel, all start states  13 lines   ← "tens, not thousands"
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
| 1 | `memset`-style fill | every store lands inside the destination buffer | regions, loop, frame tier |
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
