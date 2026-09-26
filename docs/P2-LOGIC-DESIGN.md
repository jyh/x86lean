# P2-LOGIC — the program logic over `runP` (paper 2's spine), design freeze v0

D303. O38, the Captain's words: 2026-09-10 *"we will want to write a paper for the x86 semantics —
including small-step operational semantics + ~hoare logic"*; 2026-09-11 *"two papers probably"*.
Council 2026-09-12 ruled framing (c): **the Hoare logic is paper 2's headline claim**
(`docs/TACAS-PRICING.md` §2.1). Paper 1's §6 ends: *"a program logic proved sound over this
semantics … the subject of later work."* This file starts that work.

Status: **v0, author's freeze. No non-author refuter pass yet — owed before any executor consumes
it** (the `KQ`/`PE` design-block rule). The core it describes is on branch `paris/logic-core`.

## 1. What the logic must prove, read from the object

The one statement this campaign already owes with a loop in it is the x86 SaltBench PoC's
`Crc32X86Interface.CorrectFor` (the interface file on `saltbench-systems`, not vendored here):

```
∀ msg buf ret s, s.ms = none → Hyps prog K image msg entry buf ret s →
  ∃ n, let t := runP prog n s
    t.stopped ∧ t.rip = ret ∧ t.rax32 = spec msg
    ∧ AgreeOutside (StackBand K s.rsp) s.mem t.mem ∧ CalleeSaved s t ∧ t.rsp = s.rsp + 8
```

Two facts decide the judgment:

1. **CorrectFor is TOTAL correctness** — `∃ n`, reaching an exit that has STOPPED. The judgment built for
   it, `Spec`, is **EVENTUALLY-REACHES**, and total correctness exactly when its post implies `t.stopped`
   (`Spec.Total`). (This line called `Spec` itself total until the refuter pass, W1, and again in its
   first repair until the fresh read, A1.) `runP_invariant` (every fuel) is the
   partial/safety half and cannot state it.
2. **Its postcondition is a RELATION between start and end** — `AgreeOutside … s.mem t.mem`,
   `CalleeSaved s t`, `t.rsp = s.rsp + 8`. A unary post needs ghost variables for every one of these.

R1's hand proof of that statement (withheld, `paris/x86-r1`) pays for its loop by counting steps
exactly — `runP prog (7 * n)` — which works only because the loop body is straight-line and of fixed
length. **A body with an inner branch has no fixed step count, and that proof shape does not
extend to it.**

## 2. The judgment (built)

```lean
def Spec (p : Program) (P : Cpu → Prop) (Q : Cpu → Cpu → Prop) : Prop :=
  ∀ s, P s → ∃ n, Q s (runP p n s)
```

Rules, each a theorem about `runP` (`X86/Logic.lean`):

| rule | premise(s) | proof rests on |
|---|---|---|
| `skip` | `P s → Q s s` | fuel 0 |
| `step` | `P s → Q s (stepP p s)` | fuel 1 |
| `conseq` | pre stronger, post weaker (the post may use the pre) | — |
| `seq` | `Spec p P R`, and `∀ s, P s → Spec p (R s) (Q s ·)` | `runP_add` |
| `loop` | invariant `I s u`, variant `v : Cpu → Nat`; from each `I`-state some fuel finishes (`Q`) or returns to `I` with `v` smaller | induction on a bound of `v`, `runP_add` |
| `reach` | none: the post may remember `∃ n, t = runP p n s` | fuel of the witness (D305) |
| `Total` | an abbreviation: `Spec` whose post carries `t.stopped` | — |

`runP_final` (a stopped state is final under more fuel) is a lemma about `runP`, **not a rule** — it
sat in this table until D305 (W2). `stopped_witness_unique` beside `Total`: a stopped end state is the
run's unique result.

⚖️ **Soundness is by construction (a shallow embedding).** The rules are kernel-checked theorems
about the semantics itself, so there is no second system to relate to the first — the argument
`docs/P2-PROOF-INTERFACE.md` (a) makes for `atLabels`, one level up.

## 3. The arms, and the one taken

**(S) SHALLOW — TAKEN.** Judgment = a `Prop` over `runP`; rules = theorems. Cheapest; soundness
free; every existing lemma (`runP_invariant`, the frame tier, `AgreeOutside`, the region lemmas)
composes with it unchanged.

**(D) DEEP — named, not built.** An inductive derivation relation `Derives p P c Q` over code
fragments with a soundness theorem `Derives → Spec`. Buys: a REFLECTIVE verification-condition
generator (a `decide`-able checker over a derivation) and a proof system a paper can present as an
object. Costs: a soundness proof and a second place every rule lives. **Trigger to build it:** the
VC generator in §5 turns out to need reflection to meet the kernel-cost ceilings. Until then (D)
would be a second system with nothing asking for it.

**(M) MYREEN-STYLE separation logic over machine code** (FMCAD 2008; TACAS 2007, already cited in
paper 1's §7) — named as the prior art the frame rule is measured against. This model's memory is a
total function and its frame facts are stated as `AgreeOutside R`, which composes by
`agreeOutside_trans`; a separating conjunction would be a re-encoding of that. **Not taken for v0**
because no statement this campaign owes needs a heap-shaped frame; the paper must say so and
compare.

## 4. What refutes this design (pre-registered)

1. **R-LOOP.** `Spec.loop` cannot carry a loop whose body length varies. Witness owed: a loop with
   an inner conditional proved through `loop` without naming a step count. (`countdownN` has a
   fixed-length body; it proves the variant rule works and that `dec`'s wrap case needs no
   precondition — it does NOT discharge R-LOOP.)
   ✅ **NOT REFUTED, D304:** `clampLoop_terminates` — a pass is 4 or 5 steps by an inner `jae`, and
   one concrete run mixes both (5 + 5 + 4 + 4, pinned by the kernel beside it); the loop proof never
   names a step count, only `to_skip`'s existential `k`.
2. **R-CRC.** R1's `CorrectFor` proof cannot be re-expressed through `seq` + `loop` at or below its
   hand-proof length. Measured by `scripts/proof_lines.py`, on the withheld tree only (the spec may
   never enter this public repo, D280).
   ✅ **NOT REFUTED, D309 (numbers only; the proof stays in the private record, commit `d3f166857`):**
   R1's `loop` 23 lines → 19 through `Spec.loop` (variant: bytes remaining, no `7 * n`); its top-level
   theorem 50 → 49; **73 → 68**, same block counter both sides, all on the standard three axioms with a
   `sorryAx` control. ⚠️ The counter is a block count, not `scripts/proof_lines.py`, which reads this
   repository's shas and cannot see the withheld tree; this line says so rather than borrow its name.
3. **R-READ.** The logic still cannot state read-safety (paper 1 §6, "What cannot be stated"): a
   load leaves no trace, so no single-run `Spec` can say *"reads only inside the buffer"*. The
   design's answer is a RELATIONAL two-run judgment (non-interference over two runs agreeing on the
   buffer). Nothing is built for it in v0; if it cannot be stated over `runP` without changing the
   semantics, that is a finding for paper 2, not a defect to hide.

## 4a. The non-author refuter pass (math, 2026-09-26, 3/3, 0 kills, FIRE) and what it changed

Receipts, in the fleet's private record: the criteria commit `69322f034` (before the drive) and the evidence commit `99df4b304`
(8 scratch files, 7 logs, the verdicts).
- **W1, W2, the missing `reach`:** repaired in D305 as above.
- **R-LOOP:** discharged IN THIS TREE by `clampLoop` (D304); two further witnesses, `condLoop` and `nested`
  (an inner `Spec` with a live exit discharging the outer body by `seq` + `conseq`), are in the refuters'
  private record and are not checkable from here.
- **R-READ is statable over the UNCHANGED `runP`:** the terminal two-run form is an EXTENSION (a `Spec`
  whose post nests a `Spec`, and needs `reach`); the lockstep all-fuel form would be a SECOND logic.
- **Census 3b — A LIMIT THAT RIDES WITH THE CLAIM:** since D307 every rule has at least one use in this tree
  (`seq` and `step` in `clampLoop_to_jne`). That measures REACH, not adequacy: paper 2's LIMITS section
  carries, BESIDE any "proof system" claim, that no rule has yet met a routine of the PoC's size (R-CRC).
- ⚠️ **THE HALT REASON (UNDRIVEN).** `CorrectFor`'s `t.stopped ∧ t.rip = ret` does not pin WHY the machine
  stopped: a fault is also `stopped`. A fault halting with `rip = ret` would need an instruction at `ret`,
  which `SysVCall`'s `prog.at? ret = none` forbids, so it is probably unreachable — and nobody has proved it.
  ⚖️ **THE FREEZE'S POSITION: the reason belongs in the POST, as `t.ms = some (.outsideProgram _)`** — `Hyps`
  describes the START state and cannot say how a run ends. A `Total` post written for this logic states the
  reason — and the tree's one `Total` witness, `countdownN_total`, does (D306). Changing the statement the PoC's cells are scored against is its owner's ruling, not this
  repository's; the finding is routed to them.
- The refuters supplied repairs, so a re-read of the amended text is a FRESH non-author read, owed.

## 5. Next, in order

1. The nonvacuity pair for every new judgment (precondition met; a concrete run reaches `Q`,
   computed by the kernel independently of the rule). **Done for `countdownN`.**
2. R-LOOP's witness: a loop with an inner branch. **Done (D304, `clampLoop`).**
3. A relational composition kit. **Done (D307):** `Spec.with_invariant` (a frame-tier step invariant
   rides along any `Spec`) and `Spec.Total.and` (total specs conjoin; FALSE for a bare `Spec`, and the
   tree carries the counterexample).
4. The VC tactic — the remedy paper 1 §6 names for the per-label residue — measured on the P2
   sample against the ~7.6 lines/label law, with its prediction pre-registered.
   ⚖️ **PRE-REGISTERED 2026-09-26, BEFORE ANY TACTIC CODE EXISTS (D307):**
   - **Subject:** `fill_safe` (5 labels, 57 lines by `scripts/proof_lines.py`, the fit 22 + 7.6/label,
     `docs/CLAIMS.tsv`), re-proved with the tactic, same statement token for token.
   - **Mechanism predicted:** the tactic removes the DISPATCH and the EFFECT-THEOREM naming at each label
     (`stepP_at` + the instruction's `step_*` lemma + the record-field `simp`). It cannot remove the
     invariant TABLE, since that is the specification, or the per-label re-establishing argument where
     the argument is arithmetic.
   - **Prediction:** `fill_safe` ≤ 40 lines, i.e. ≤ ~3.6/label above the 22-line base.
   - **Refutation:** > 47 lines (> 5/label). Then this tactic design does NOT carry paper 1 §6's claim
     that "a tactic … rather than more lemmas" is the remedy, and paper 2 says so.
   - **Declared floor (the residue, stated with the prediction so a win cannot read as arrival):** the
     table itself is ~2 lines/label, so no tactic of this kind goes below ~22 + 2 × 5 = 32 lines. A
     result between 32 and 40 is the prediction met; nothing below 32 is claimable from this design.
   📌 **ADDENDUM, SAME DAY, AFTER THE REGISTRATION AND BEFORE ANY BUILD — the registration above is left as
   written.** A line census of `fill_safe` by role, taken to test the layer before building it: **dispatch
   ~11 lines** (the halt case 7, the per-instruction case split 4) · **effect-naming ~6** (one `rw [step_*]`
   per label, two at the store) · **the rest ~40** (unpacking, re-establishing, and the arithmetic —
   `regcalc`, `decide`, `omega` — at the loop and the branch). A tactic of the registered design removes at
   most the first two, so the expected result is **~41–45 lines**: above the ≤ 40 prediction and below the
   > 47 refutation. ⇒ **The prediction was optimistic by ~1 line/label before a line of tactic was written**,
   and the census says the lever is the ARITHMETIC RE-ESTABLISHMENT, not the dispatch — which is paper 1
   §6's residue argument, now with a count behind it.
   ⛔ **AND THE ADDENDUM'S OWN ARITHMETIC WAS OPTIMISTIC, CORRECTED WITHIN THE HOUR.** It subtracted the
   ~6 effect-naming lines as REMOVABLE. They are not: `runP_code` already does the dispatch, and a tactic
   call REPLACES a `rw [step_*]` line one for one. Only the halt case and the case split (~10 lines)
   collapse, to about one line. ⇒ **Expected ≈ 47–48 lines: AT OR PAST THE REGISTERED REFUTATION (> 47).**
   ⚖️ **THE REGISTERED DESIGN IS REFUTED AT DESIGN TIME BY A MEASURED CENSUS, AND IS NOT BUILT.** This is a
   census of the proof text plus an argument, not a build of the tactic; a build would pin the number,
   and it is declared owed only if paper 2 wants the point measured rather than argued. **The next design
   aims at the ~40 lines of re-establishment and arithmetic** (a closer that tries `decide` / `omega` /
   the `Flags` normalisations on each side goal), and it will be pre-registered in the same way.
   ⚖️ **DESIGN 2, PRE-REGISTERED 2026-09-26 BEFORE ANY CODE (D310):** a closer macro `vc_close`, applied to
   every side goal left after the effect rewrite, trying in order `rfl` · `decide` · the `regcalc`
   normalisation followed by `omega` · `simp_all` then `omega`; no `bv_decide` (theorem tier, TRUSTBASE).
   **Same subject and thresholds as design 1, so the two are comparable:** `fill_safe` re-proved, same statement;
   ≤ 40 lines is the prediction met, > 47 refuted, the floor ~32 declared. **The census's expectation, stated
   now:** of the ~40 residue lines, the arithmetic at the loop and at the branch (~15) is what `vc_close` can
   reach; the unpacking and the `Loop` witnesses (`⟨k, hk, …⟩`) it cannot. So the expectation is **~42–46,
   inside the band and short of the prediction**, and a result at or under 40 would mean the closer reached
   the witnesses too.
   ⛔ **RESULT, BUILT AND MEASURED (D310): 55 LINES — DESIGN 2 IS REFUTED (> 47).** Probed site by site
   before writing the macro, because the census had already been wrong once in each direction:
   `bv_omega` (theorem-tier safe, standard axioms) closes **2 of the 3** arithmetic sites (the `inc`
   pointer step and the `dec` counter step, the second WITHOUT the four-way case split on `k`), and
   **does not** close the third (the ZF-flag goal, which mixes a Boolean flag with the arithmetic; omega
   returns a counterexample shape). `fill_safe` 57 → **55**, `EXIT`-clean, same statement. Design 1's halt
   collapse on top would give ~49: **still refuted.**
   ⇒ **The measured law:** at this interface the per-label cost is the CASE STRUCTURE (the branch's
   `by_cases` on the flag) and the LOOP WITNESSES (`⟨k, hk, …⟩`), not arithmetic a closer can reach. That
   is paper 1 §6's residue argument, now with two refuted designs behind it, and it points at the
   INVARIANT'S REPRESENTATION (the witness shape), not at automation, as the next lever.
   📌 **The expectation registered above (~42–46) was wrong too, in the flattering direction:** it priced
   the reachable arithmetic at ~15 lines, and the measured saving is 2.
5. R-CRC, on the withheld tree.
6. The two-run judgment for R-READ. **Done in its TERMINAL form (D308):** `ReadsOnly` is an instance of
   `Spec` (the post nests a second `Spec`), so there is still one judgment. `ldb_readsOnly` proves a load
   from `[rdi]` reads only `R = {rdi}` for every start; `ldb1_not_readsOnly` proves a load from `[rdi+1]`
   does NOT (the red control). ⚠️ **What the terminal form does NOT say:** it constrains the END states
   only, so a routine that reads outside `R`, and whose result never depends on that read, passes. The
   lockstep all-fuel form would catch that, and it is a SECOND judgment — named, not built. Paper 2 states
   which one it claims.

## 6. Receipts

`X86/Logic.lean` and `Tests/Logic.lean`, built through `scripts/lean_route.py`; the axiom gate
enumerates `X86.Logic` through `X86.lean`'s import list.
