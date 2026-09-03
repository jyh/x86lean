# P1 BATCH 16 — the repeat prefixes, and the loop whose exit is not where it looks

**Forms.** Roster families 7 and 23: the eleven `rep`/`repe`/`repne`/`repnz`/
`repz`-prefixed string rows — `rep` on `movs`/`stos`/`lods`, `repe` and `repne`
on `cmps`/`scas`, each at all four widths. **11 roster rows, 3 roster mnemonics,
28 differential vectors**, taking the model to **429 of the 525 rows (82%)**.

```
cases=51414  matched=36353  explained=20767  unexplained=0  oracle-leaks=0  missing=0
  spec: 0   refusal: 0   harness: 0   undefined-region: 20767
627 vectors · 82 pre-states · 75 mnemonics
```

Gate met on the FIRST run, in 1 m 55 s.

⚠️ **Eleven rows, three mnemonics, twenty-eight vectors — three different counts,
each right for its own question.** `repz` and `repnz` are roster rows with no
mnemonic and no vector of their own: they assemble to bytes identical to
`repe`/`repne`. The counting command is batch 15's with the filter inverted
(`$3 != ""`), so the two batches partition the twenty-one rows exactly.

## The batch opened on a question and answered it by measuring

The boot brief handed this batch one open question — *how do `Instr.len` and RIP
interact when the model must not advance?* — with the instruction to settle it
before writing vectors. A 21-case oracle probe, **4.4 seconds, every case
`refused=0`**, settled it and found the answer was not the obvious one.

| case | RCX in | RCX out | RIP |
|---|---|---|---|
| `rep movsq` | 0 | 0 | **advanced** |
| `rep movsq` | 1 | 0 | **UNCHANGED** |
| `rep movsq` | 3 | 2 | unchanged |
| `repe cmpsq`, equal | 1 | 0 | **UNCHANGED** |
| `repe cmpsq`, differ | 3 | 2 | advanced (ZF=0) |
| `repne scasq`, equal | 3 | 2 | advanced (ZF=1) |
| `rep movsb`, RCX=0x1_0000_0001 | | 0x1_0000_0000 | unchanged |

⛔⛔ **COUNT EXHAUSTION DOES NOT ADVANCE RIP.** The count is tested only on
entry. `rep movsq` with RCX = 1 copies, leaves RCX = 0, and **stays at its own
address**; the next step, finding the count already zero, falls through. The
SDM writes REP as a `while` loop, and the natural single-step reading of one —
body, decrement, notice zero, leave — is the wrong decomposition.

⇒ **A model that advanced on the decrement reaching zero is right at every value
of RCX except 1.** One value of one register separates the two models across the
whole eleven-row group. `adversarial` contains 1 — put there in P0 for the flag
rules, nothing to do with loop counts — so the sweep reaches it and
`wrongRepAdvanceOnCountZero` is caught. **The batch was lucky and the luck is
recorded as such** (D46): a boundary list of "0, powers of two, all-ones" would
have left the whole branch green and wrong.

## The five planted defects

| arm | what it does | caught in |
|---|---|---|
| `wrongRepAdvanceOnCountZero` | falls through when the decrement reaches 0 | `rip` |
| `wrongRepDecrementFirst` | consults the count after its own decrement | `rip` |
| `wrongRepCountWidth` | decrements RCX at the OPERAND width | `rcx` |
| `wrongRepZfIncoming` | tests the INCOMING ZF, not the comparison's own | `rip` |
| `wrongRepDecrementAtZero` | decrements on the RCX = 0 path, wrapping to all-ones | `rcx` |

⚠️ The third is batch 15's `wrongStringPointerWidth` (D43) aimed at **the one
register batch 15 did not write**, and it inherits that arm's blind spot: it is
invisible unless the decrement carries across the operand width. `adversarial`'s
`0x100000000` and `0x10` are what make it visible.

## What the batch did NOT need, and why that was checked rather than assumed

**No new pre-state.** RCX already carries the swept value `c`, and
`adversarial` contains 0, 1 and 2 — the three counts the rule distinguishes.
Batch 15 priced this batch as needing none; the claim was re-checked against the
emitted cases rather than inherited, because an inherited diagnosis is a
hypothesis. **No new watch window, no new oracle draw** — the whole group is
`T-exact`, as batch 15's was.

## Three smaller findings

**`repApplies` looks like `bitcntEncodable` and means something different.**
That table records forms with NO ENCODING — an architectural fact. This one is a
ROSTER partition: every pair it rejects assembles. `rep cmpsq` and `repe cmpsq`
are the identical bytes `f3 48 a7`; `repne movsq` (`f2 48 a5`) assembles too,
and **x86isa executes it as an unprefixed string op — one iteration, RCX not
decremented, RIP advanced**. The model declines it rather than copying an
oracle's treatment of a shape the roster does not file. ⇒ The resemblance
between the two tables is exactly the kind a later reader takes on trust, so the
difference is written where the table is.

**A refactor audited by a theorem rather than a diff.** `stringIter` is batch
15's body with the RIP write lifted out, shared by both constructors so the five
subtly-ordered arms exist once. `step_repstrop_iterates_like_strop` asserts the
prefixed form leaves the same memory and flags as the unprefixed one — the
statement that fails if the two ever drift, and re-runnable in a way "I checked
the diff" is not. The eight batch-15 characterization lemmas pass through the
refactor unchanged, which is the second half of the same guard.

**A theorem narrower than the group it names.** `step_repstrop_decrements_rcx`
was first written with `k ≠ .lods` and `k ≠ .scas` hypotheses that nothing in
its statement needs — `stringIter` never writes RCX for any kind. `simp_all`
discharged those two cases **from the contradiction**, not from the semantics,
so the theorem was green and silent about two fifths of the group in its own
name. Widened to all five.

## Two gates the batch did not set out to write

Sweeping for stale numbers after the coverage literal moved 418 → 429 turned up
two classes of unchecked claim, both older than this batch.

**D47 — `README.md` was four batches stale, under a disclaimer.** "twelve
batches landed", "388 of the 525 forms", "527 vectors · 80 pre-states · 42160
cases". Batches 13, 14 and 15 each updated the literal, regenerated
`docs/COVERAGE.md` and wrote a differential record, and left the README alone.
⇒ The sentence beneath it — *"the numbers in this paragraph are a snapshot and
that file is the claim"* — is why. It reads as diligence, it names the real
authority, **and it was true**, and its effect was to tell every reader not to
check the figures. A number nobody is expected to trust is a number nobody
corrects. `scripts/check_readme_snapshot.py` now gates all six against the
generated table and the per-batch records; its control mutates every claim and
one SOURCE, since a gate comparing the README to itself would pass every
README-side arm.

**D48 — three phantom citations, the oldest from batch 11.** This batch cited a
theorem it had not written; grepping to fix its own slip found three already
standing, each occurring exactly once in the repository — in the comment that
cited it. `loop_synonyms_are_one_encoding` **never existed**;
`bit_counting_reaches_a_zero_source` was split in two by batch 14 and the
citation not updated; `undefined_column_matches_the_model` names a check that is
real under another name. ⇒ **A citation reads as the gate it names**, and nobody
greps for a theorem they have just been told exists.

⭐ The part worth carrying: batch 11's could not have been written as stated.
There are no `loopz`/`repz` vectors and there must not be — a vector per
spelling is one instruction differentially tested twice — so a theorem "over the
vector table" had nothing to quantify over. **The phantom did not name a missing
theorem; it named an impossible one**, and writing the name is what made the
impossibility invisible for five batches. The claim is about an assembler and is
now checked by one (`SYNONYMS` in `scripts/check_encodings.py`, six spelling
pairs, probed with a pair that must differ). `scripts/check_citations.py` gates
the rest.
