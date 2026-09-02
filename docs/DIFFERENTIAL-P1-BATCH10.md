<!-- P1 batch 10's gate evidence. Regenerate with scripts/run_differential.sh. -->

# P1 batch 10 — the width-changing and two-destination moves

**The batch.** Roster family 15 (`-------|-|reg`), its NO-FLAG core: MOVZX,
MOVSX/MOVSXD, the six accumulator sign-extensions, XCHG and BSWAP. **24 roster
forms**, 33 new vectors. Coverage 343 → **367 of the 525** (70%).

## Result

```
cases=37518  matched=25999  explained=14347  unexplained=0
oracle-leaks=0  missing=0
  spec: 0          refusal: 0        harness: 0
  undefined-region: 14347
```

**507 vectors · 74 pre-states · 37518 cases · 0 unexplained**, on the first run.
Every arm green: axioms (three, red-first drive) · tier isolation · **507/507
encodings against clang** · kernel ceilings · roster 13/13 + `--check` ·
coverage table generated · commit trailers.

## ⭐ `explained` DID NOT MOVE, AND THAT IS THE BATCH IN ONE NUMBER

It is **14347** — exactly batch 9's figure. The batch added 2442 cases and
**not one explained disagreement**, because not one of these instructions writes
a flag. All 2442 went into `matched`.

Batch 9's law was that a WIDE undefined set is a NARROW test: `bt`/`bts`/`btr`/
`btc` leave four flags undefined, so ZF alone carried the whole weight. This
batch is that law's other end. There is nothing for the comparator to absorb, so
**every disagreement these forms can produce is a data-path disagreement** — and
the two mechanisms they introduce are exactly the kind a self-consistent wrong
model swallows: a write whose width is not the operand's, and a write to a
register the operands do not name.

## What the batch actually contains

| group | forms | what is new |
|---|---|---|
| `movzx` / `movsx` / `movslq` | 10 | the first forms whose SOURCE WIDTH DIFFERS FROM THEIR DESTINATION WIDTH |
| `cbtw` `cwtl` `cltq` / `cwtd` `cltd` `cqto` | 6 | implicit accumulator; the second trio writes **rDX**, a register the operands never name |
| `xchg` | 7 | the first form that writes BOTH its operands |
| `bswap` | 1 | byte reversal, at the two widths the SDM defines |

The three destination widths are the subject throughout: `.w` PRESERVES what is
above it, `.d` ZERO-EXTENDS over it, `.q` replaces the register (SDM Vol. 1
§3.4.1.1). `movzbw` and `movsbw` are the only vectors in the whole table with a
16-bit destination.

## ⭐ THE ASSEMBLER SETTLED A READING BEFORE THE ORACLE COULD (D24)

`xchg %eax, %eax` moves no data and still CLEARS the upper half of RAX, because
each of its two writes zero-extends. The evidence is not the manual — it is that
**clang refuses to encode it as `90`**. It emits `87 c0`. `xchg %rax, %rax`, by
contrast, assembles to `90`. The reason is that `90` in 64-bit mode is NOP, and
NOP does not touch RAX; using it for the 32-bit spelling would silently drop the
zero-extension.

So `90` is not this instruction, and is not in the vector table. This is the
first time in this repository that the ENCODING CROSS-CHECK, rather than the
differential run, has settled what a form means.

⚠️ And a second thing the assembler said: `xchg %ax, %cx` and `xchg %cx, %ax`
are **the same bytes**, `6691`. The roster counts them as two forms; there is
one encoding. Both spellings are in the table so that the claim is checked
(`xchg_operand_orders_are_one_encoding`) rather than asserted in a comment.

## ⛔ TWO SHAPES REFUSED RATHER THAN APPROXIMATED (D25)

`xchg` with a memory operand asserts LOCK unconditionally — an ATOMICITY claim a
single-threaded model cannot make or break, so a model of the data movement
alone would be right about every observation this harness can make and wrong
about the only thing that distinguishes the instruction. `bswap` at a 16-bit
operand size is undefined in the SDM — not its flags, not some of its bits, the
RESULT.

⚠️ **The undefined-bit oracle is the wrong instrument for the second one, and
that is the useful part.** The oracle says "this model declines to commit to
these BITS", which presupposes a value that exists. Drawing oracle bits where
the manual declines to define the value at all would dress a refusal up as a
`T-frame` answer. Both halt instead, and both refusals are theorems
(`xchg_refuses_a_memory_operand`, `bswap_refuses_sixteen_bits`).

## ⭐ A WHOLE REGISTER WAS A CONSTANT IN ALL 74 PRE-STATES (D26)

`cwtd`/`cltd`/`cqto` are the first instructions here to write a register their
operands do not name, and `cltd`'s write is 32 bits wide, so it clears RDX's
upper half. **RDX was zero in every pre-state**, so a model that merged instead
— the 16-bit rule applied to all three off one sentence, which is D20's shape
exactly — would have been indistinguishable from the correct one.

This is D14 (the constant memory window) arriving a second time in a different
place. ⇒ **A pre-state set is adversarial only with respect to the instructions
that already exist.** Each batch has to ask what its own new destinations were
doing before it arrived. `mkPre` now sets `rdx := ~~~a`.

## The planted pair, doubled — and both halves probed by DELETION

Four arms, 19 → **23**. Two easy, two hard, one per new mechanism.

| arm | half | catches | depends on |
|---|---|---|---|
| `movsx` zero-extends | easy | 241 in `rax` | any negative source |
| `xchg` copies instead of swapping | easy | 191 in `rcx` | any `xchg` vector |
| the `99` trio merges where `cltd` must zero-extend | **hard** | 65 in `rdx` | **the new RDX pre-state** |
| a width-changing move bounds the VALUE not the WRITE | **hard** | 66 in `rax` | **the two `bw` vectors** |

Both hard halves were probed, and in BOTH directions per D21 — an assertion
narrower than the coverage it guards cries wolf, so each was checked for SILENCE
as well as for noise:

* **Delete `rdx := ~~~a`** → the `cltd` arm catches **ZERO**, and
  `pre_states_give_rdx_a_nonzero_upper_half` **fails**. Both halves fire.
* **Delete `movsx_rr_bw` alone** → the arm still catches (33 instead of 66) and
  `movx_writes_a_preserving_destination` stays **silent**. No wolf cry.
* **Delete both `bw` vectors** → the arm catches **ZERO** and the assertion
  **fires**.

That is the second batch running in which a law from an earlier batch was built
in by design rather than rediscovered.

## ⭐ AND THE PROBE ITSELF GOT CHEAPER, WHICH IS WHY THERE ARE THREE OF THEM

A full `selftest` re-emits the whole vector table twice per arm, 23 times over —
about **eleven minutes** at this size, for a question about one arm. Every batch
here pays that tax two or three times, because "is this coverage load-bearing?"
is answered by deleting the coverage and re-running (D13, D14, batch 5's
constant, D21).

`x86lean-diff selftest <substring>` runs only the matching arms: **44 seconds**.
It is a FILTER, not a second selftest — the arms are the same arms from one
`selftestArms` table, driven by the same `driveWrong`, and the no-argument form
is what CI still runs. A probe mode that could pass while the real gate failed
would be worse than the eleven minutes.

## ⛔ THE SCALING PROBLEM, MEASURED RATHER THAN INHERITED

Batch 9 handed on `Tests.Coverage`'s kernel time (378 → 1960 → 3130 → 6520 ms
across batches 3, 5, 7, 9) with a diagnosis: (assertions × vectors × pre-states),
and an instruction to restructure before raising the ceiling a third time.

Measured here:

| change | cost |
|---|---|
| batch 10's **eight new theorems**, three over (vector × pre-state) | **+720 ms** |
| batch 10's **thirty-three vectors**, no new theorem | **+2400 ms** |

**The pre-states are not in it.** The vector table grew 7% and the module grew
37%; the rows grew 29% at the same time, and three theorems here were each a
45 × 507 sweep of `List Char` equalities.

Collapsing the inner factor once instead of per row (`vectorMnemonics`,
`memDestMnemonics`) and hoisting the pre-states' 80-byte background pattern to a
closed constant (`baseMem`) takes the module **9640 → 8250 ms**. Nothing is
weakened: `List.contains` and `List.all` cannot tell a list from its
duplicate-free image, and the hoisted bytes are identical.

⛔ **And the honest part: that recovered 1390 of this batch's own 2400 ms, so
1010 ms of the growth is still unaccounted for.** The three collapses were aimed
at the products that were easiest to SEE. The next head should measure per
theorem rather than reason about shapes — which is the mistake this note is
correcting in its own inherited diagnosis. The ceiling stands untouched at
19560, with 2.4× headroom, so that can be done properly rather than under
pressure.

## Still open, named

* `docs/COVERAGE.md`'s "**367** of the 525" is a hand-maintained literal. Making
  it derivable needs a claimed-forms table keyed to `p1/roster.tsv`'s (base,
  shape) pairs — real work, and a better batch than a tack-on.
* `isMemDestVector` still ENUMERATES AST constructors. Batch 10's four are
  written out with their `false`s explicit, in the same commit as the
  constructors, rather than after a gate refused a true claim.
