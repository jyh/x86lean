<!-- P1 batch 9's gate evidence. Regenerate with scripts/run_differential.sh. -->

# P1 batch 9 — the bit-test group, and the one flag that survives

**The batch.** Roster families 31, 32 and 41 — `bt`/`bts`/`btr`/`btc` at
`r,imm`, `r,r` and `m,imm`, widths w/l/q (there is no 8-bit form). **12 of the
group's 16 forms**; the four `m,r` forms are declined and named (D23).

## Result

```
cases=35076  matched=23557  explained=14347  unexplained=0
oracle-leaks=0  missing=0
  spec: 0          refusal: 0        harness: 0
  undefined-region: 14347
```

**474 vectors · 74 pre-states · 35076 cases · 0 unexplained.** Every arm green.

⚠️ **The `explained` count jumped from 9019 to 14347** — by more than the new
cases. That is not drift: these four instructions leave **four** flags undefined
(OF, SF, AF, PF), the widest undefined set in the model, so each of their 2664
cases can contribute several explained disagreements. An instruction that
computes almost nothing has the largest undefined footprint here.

## `bt` is to this group what `cmp` is to the ALU

The test is identical in all four — CF takes the selected bit — and only then
does the destination change, or not. `bt` writes nothing at all. And **all four
report the bit as it was BEFORE the write**: `bts` on a clear bit sets it and
leaves CF at 0.

## ⭐ ZF is the only arithmetic flag that survives

SDM Vol. 2A: *"the ZF flag is unaffected... the OF, SF, AF, and PF flags are
undefined."* `btr` clearing the last set bit leaves a zero destination and ZF
exactly as it was — where every other read-modify-write in this model would set
it.

**And that is why this batch's hard half is sharp rather than lucky.** The
planted bug recomputes ZF from the result, which is the natural thing to write
because every neighbouring instruction does. A disagreement in PF, AF, SF or OF
would be classified **explained** — those flags are in the undefined set and the
comparator absorbs them by design. ZF is the only one of the six whose
disagreement can be unexplained here, so the whole bug is visible through a
single narrow window.

⇒ **A wide undefined set is a narrow test.** The more of an instruction's flags
the manual declines to define, the fewer of them a differential run can hold it
to — and the ones that remain carry the entire weight.

## ⛔ Four forms declined rather than approximated

With a memory base and a **register** offset, the operand is the base of a
**bit string**: the offset is signed, may reach far outside the addressed
operand, and the effective address moves with it. A model that quietly applied
the modulo rule there would be self-consistent, would pass every anchor in this
repository, and would be wrong in a way nothing here asks about.

So it is declined, and the coverage rows say so (`m,r: bit-string, not
modelled`) — the first time the shapes column has had to report an **absent
shape** rather than merely undefined bits. See D23.

## What is NOT claimed

* `bt`'s `m,r` bit-string forms — four roster forms, named above.
* `bsf`/`bsr`/`popcnt`/`lzcnt`/`tzcnt` — families 39, 42, 46.
* Hardware co-simulation, as in every batch so far.
