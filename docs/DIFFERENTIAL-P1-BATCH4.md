<!-- P1 batch 4's gate evidence. Regenerate with scripts/run_differential.sh. -->

# P1 batch 4 — the READ-MODIFY-WRITE to a memory destination

**The batch.** `p1/roster.tsv` families `0xuxx0-|-|mem` (AND/OR/XOR to a memory
destination, **6 forms**), `-xxxxx-|-|mem` (INC/DEC at a memory destination,
**2 forms**) and `-xxxxx-|-|reg` (INC/DEC at a register destination, **2 forms**)
— **10 forms**, and the **last zero-surcharge batch in the wave**. Every batch
after this one invents a template.

## Result

```
cases=16798  matched=12308  explained=4564  unexplained=0
oracle-leaks=0  missing=0
  spec: 0          refusal: 0        harness: 0
  undefined-region: 4564
```

**227 vectors · 74 pre-states · 16798 cases · 0 unexplained.** Every gate arm
green; the differential is 15.3 s warm.

**Positive control**, as in every batch. Two one-bit changes planted in batch-4
records, both contradicted by the oracle and nothing else firing:

```
[spec] and_mr_b/5 (and) mem@…1ff0: lean=…af7e00… oracle=…af7f00…
[spec] inc_m_w/5  (inc) mem@…1ff0: lean=…af8001… oracle=…af8000…
```

The first is the store itself; the second is the HIGH byte of a 16-bit store,
which x86isa computed independently.

## The new ground

Batch 3 put a memory operand in a destination that is **read and never
written**. These forms **read it, compute, write it back, and set flags** — and
until now the only memory this repository ever *wrote* was `mov`, `push` and
`call`, none of which touch a flag and none of which read the location first.

⭐ **The width of the store is the whole risk.** A store that ignores its operand
width is invisible at width `q` and invisible at every register destination —
the register path truncates in `setReg` and has no neighbours — and shows only
as clobbered bytes in the data window at b, w and l.

`and_mem_l_does_not_zero_extend_into_memory` is the anchor that matters most: a
32-bit write to a REGISTER zero-extends into the upper half (SDM Vol. 1
§3.4.1.1), and a 32-bit write to MEMORY touches four bytes and no more. A model
that carried the register rule across would zero the fifth byte. Its contrast,
`andl_reg_does_zero_extend`, is what stops the pair from being satisfiable by a
model that simply never zero-extends anything.

## ⛔ The claim this batch made about itself

That its **sub-`q` widths** are load-bearing. Tested, not asserted: the 24
memory-destination vectors at b, w and l were deleted, the `q` ones kept, and
the width arm re-run.

```
✔ a memory read-modify-write drops its STORE:   459 disagreements   (still caught)
⛔ a memory store ignores its operand WIDTH:    ZERO disagreements
```

**True.** Without them the width rule is exercised by nothing at all.

## ⭐ What batch 4's gate found in the table — four more over-claims

D15's `mem_dest_claims_are_backed` needed a second pattern here, because
`inc`/`dec` have no source operand and cannot express a memory destination as
`m,r`. The first attempt at that pattern was `· m ` — and it **fired on
`push`**, whose shapes read `r · m · imm` where `m` is a memory *source*.

⇒ 🔑 **A CHECK CANNOT BE MORE PRECISE THAN THE NOTATION IT READS.** The shapes
column had no way to distinguish a memory operand that is written from one that
is read, for unary forms, so no pattern over it could mean what was needed. The
fix belonged in the notation: a written memory destination is now `m(rmw)`.

**And the wrong pattern earned its keep on the way out.** Firing on `push` is how
it came out that:

| row | claimed | vectors that exist |
|---|---|---|
| `push` | `r · m · imm` | `push_r` only |
| `pop` | `r · m` | `pop_r` only |
| `neg` | `r/m` | `neg_q`, `neg_b` — register only |
| `not` | `r/m` | `not_q` — register only |

**Four more rows over-claiming exactly as `and`/`or`/`xor` had**, all four from
P0, all four invisible to every mnemonic-level theorem — `push` has a row, has
a vector, is in the roster. Each is now narrowed to what is executed, with the
roster family that will earn it back named in the row itself (families 10 and
11). ⇒ **The over-claim was not a slip in one row; it was the column's default
behaviour, because nothing read it.**

## And the claim `and`/`or`/`xor` earned back

Batch 3 deleted their false `m,r (q)`. This batch restores `m,r · m,imm` **at
all four widths** — more than the false claim ever asserted — and
`mem_dest_claims_are_backed`, not a comment, is what holds it.

## The planted-bug set is now nine, in pairs

| planted bug | caught in | disagreements |
|---|---|---|
| `inc` clobbers CF | `cf` | 560 |
| `movl` fails to zero-extend | `rax` | 24 |
| shift forgets to mask its count | `rax` | 90 |
| `adc` drops the carry-in | `rax` | 630 |
| `adc`'s carry-OUT forgets the carry-in | `cf` | 115 |
| `cmp` writes its result back | `rax` | 826 |
| `cmp` writes back ONLY to a memory destination | `mem@…1ff0` | 575 |
| **a memory RMW drops its STORE** | `mem@…1ff0` | 1726 |
| **a memory store ignores its operand WIDTH** | `mem@…1ff0` | 792 |

Each batch plants an easy half and a hard half; the hard half is the arm that
says whether the batch's new coverage is load-bearing.

## What is NOT claimed

* `neg`/`not`/`push`/`pop` at a memory operand — roster families 10 and 11, and
  the table no longer says otherwise.
* `xadd`, `cmpxchg` and the locked forms are families 10 and 14.
* Hardware co-simulation, as in every batch so far.
