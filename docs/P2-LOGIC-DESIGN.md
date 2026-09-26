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

1. **It is TOTAL correctness** — `∃ n`, reaching an exit. `runP_invariant` (every fuel) is the
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
| `runP_final` | a stopped state is final under more fuel | `runP_stopped` |

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
2. **R-CRC.** R1's `CorrectFor` proof cannot be re-expressed through `seq` + `loop` at or below its
   hand-proof length. Measured by `scripts/proof_lines.py`, on the withheld tree only (the spec may
   never enter this public repo, D280).
3. **R-READ.** The logic still cannot state read-safety (paper 1 §6, "What cannot be stated"): a
   load leaves no trace, so no single-run `Spec` can say *"reads only inside the buffer"*. The
   design's answer is a RELATIONAL two-run judgment (non-interference over two runs agreeing on the
   buffer). Nothing is built for it in v0; if it cannot be stated over `runP` without changing the
   semantics, that is a finding for paper 2, not a defect to hide.

## 5. Next, in order

1. The nonvacuity pair for every new judgment (precondition met; a concrete run reaches `Q`,
   computed by the kernel independently of the rule). **Done for `countdownN`.**
2. R-LOOP's witness: a loop with an inner branch (the guarded store, `Tests/Program.lean`
   `guarded`, as a loop).
3. A relational composition kit: `AgreeOutside`/`CalleeSaved` transitivity lifted to `seq` posts.
4. The VC tactic — the remedy paper 1 §6 names for the per-label residue — measured on the P2
   sample against the ~7.6 lines/label law, with its prediction pre-registered.
5. R-CRC, on the withheld tree.
6. The two-run judgment for R-READ.

## 6. Receipts

`X86/Logic.lean` and `Tests/Logic.lean`, built through `scripts/lean_route.py`; the axiom gate
enumerates `X86.Logic` through `X86.lean`'s import list.
