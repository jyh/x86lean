<!-- P1 batch 2's gate evidence. Regenerate with scripts/run_differential.sh. -->

# P1 batch 2 — ADC and SBB: the first forms whose RESULT reads a flag

**The batch.** `p1/roster.tsv` family `xxxxxx-|cf|reg` — **14 forms, 48 K
variants.** Chosen, unlike batch 1, *against* the script's order: it is the
first batch that needs a **new template**, and the wave's quote was missing
exactly that term (bus, the wave quote). Batch 1 measured the marginal cost of a
form under an existing template; this batch measures what a template costs.

## Result

```
cases=10360  matched=7572  explained=2862  unexplained=0
oracle-leaks=0  missing=0
  spec: 0          refusal: 0        harness: 0
  undefined-region: 2862
```

**140 vectors · 74 pre-states · 10360 cases · 0 unexplained.** Every gate arm
green; the full gate runs in **35.7 s** warm.

Positive control, as at batch 1: a CF bit flipped in an `adc` record at a
carry-boundary pre-state was **contradicted by the oracle** —
`[spec] adc_rr_q/61 (adc) cf: lean=0 oracle=1`. x86isa computed the carry-out at
the boundary independently.

## What makes it a new template, in one subterm

Every P0 form computes its result from its operands alone. `adc` and `sbb` read
CF *into* the result:

```
step_adc_reg_op … = { s with regs := … Flags.adcResult sz a b s.flags.cf … }
```

`s.flags.cf` on the right of a characterization equation is the whole novelty.
The same instruction on the same operands has two different results depending on
the state it starts in, and anything reasoning above this layer now has to carry
CF.

Two theorems say the new template **degenerates** to the old one —
`adc_no_carry_is_add` and `sbb_no_carry_is_sub`, plus the same for the flags.
That is the strongest single statement available about a carry-propagating form:
without it, `adc` would be a second, subtly different adder living beside `add`,
and the differential run would have to find the difference one operand at a time.

**AF and OF needed no new rule**, and that is a fact rather than a convenience:
`auxCarry a b res` is bit 4 of `a ⊕ b ⊕ res`, and `res`'s bit 4 is
`a₄ ⊕ b₄ ⊕ c₄` whatever the carry into bit 0 was, so the identity survives a
carry-in unchanged. CF is the one rule that genuinely changes, because it is the
only one that counts past the top bit.

## ⛔ The claim this batch made and then refuted about itself

Batch 2 added six `carryBoundary` pre-states and a comment asserting that P0's
three sweeps could not reach `0xFF + 0x00 + 1` — so that, without them, a model
whose carry-**out** forgot the carry-**in** would go uncaught.

**That claim was tested by deleting the list and re-running the arm, and it was
false.** The bug was still caught, 62 disagreements instead of 76. Two accidents
reach the boundary: `0xAAAA…AA` and `0x5555…55` are adjacent in `adversarial`
and are exact complements, so the `pairs` sweep hands `adc` a sum of `2^64 − 1`
with CF set; and truncating `0x100000000` to a byte gives zero, so several pairs
become `0xFF + 0x00` at width b. Neither constant was put there for this.

⇒ 🔑 **COVERAGE THAT ARISES INCIDENTALLY FROM A LIST WRITTEN FOR ANOTHER PURPOSE
IS COVERAGE NOBODY IS MAINTAINING.** Reordering `adversarial`, or dropping one of
those two constants, would remove the only states exercising the carry rule, and
every gate would stay green — because a rule nothing exercises cannot disagree
with anything.

So the six states stay, not as the only way to reach the boundary but as the
only *deliberate* one, and `Tests/Coverage.lean` now **asserts the crossings**
(`pre_states_cross_the_carry_boundary_q` / `_b`, `_borrow_`, and `sweep_cf`).
Those four are the first checks in this repository that test the PRE-STATES
rather than the model. Nothing else can see a boundary stop being crossed.

## The harness selftest is now five bugs, and two of them are this batch's

| planted bug | caught in | disagreements |
|---|---|---|
| `inc` clobbers CF | `cf` | 140 |
| `movl` fails to zero-extend | `rax` | 24 |
| shift forgets to mask its count | `rax` | 90 |
| **`adc` drops the carry-in** | `rax` | 630 |
| **`adc`'s carry-OUT forgets the carry-in** | `cf` | 76 |

The fourth is the easy half and is labelled as such in `Main.lean`: dropping the
carry moves the result by one almost everywhere, so any CF-set pre-state catches
it. The fifth gets the result right and only the carry-out wrong, so it is
invisible except at the boundary — which is why it, and not the fourth, is the
arm that was used to test the claim above.

## What is NOT claimed

* The memory-destination `adc`/`sbb` forms are a different family (`…|cf|mem`,
  batch 23 of the roster). The equations here take a register destination.
* `adc`/`sbb` at the flags-only shapes do not exist — both always write a
  destination.
* Hardware co-simulation, for the same reason as batch 1.
