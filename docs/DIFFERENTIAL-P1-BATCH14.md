# P1 BATCH 14 — the bit-counting group, and the first undefined DESTINATION

**Forms.** Roster families 33, 39, 42 and 46: `popcnt`, `lzcnt`, `tzcnt`, `bsf`,
`bsr` and `blsi` at `r,r` and `r,m` — **12 roster rows, 34 differential
vectors**, taking the model to **408 of the 525 rows (78%)**.

```
cases=46320  matched=31640  explained=20248  unexplained=0  oracle-leaks=0  missing=0
  spec: 0   refusal: 0   harness: 0   undefined-region: 20248
579 vectors · 80 pre-states · 67 mnemonics
```

Gate met on the FIRST run, in 2 m 28 s.

## What the batch actually was

Six mnemonics on ONE operand shape — read a source at the operand width, write a
GPR, set flags — whose **flag rules agree on almost nothing**, and one of which
required the harness to learn a distinction it had never had to make.

| # | finding | where |
|---|---|---|
| **D38** | the kernel ceiling's UNITS were wrong, not its value; the absolute form provably missed a 3.2× per-row regression | `scripts/kernel_cost.py`, `scripts/kernel_ceilings.txt` |
| **D39** | the `undefined` column was a published claim NO GATE READ | `Main.lean`, `X86/Coverage.lean` |
| **D40** | the first undefined DESTINATION, and the repair that would have gutted the leak check | `X86/Serialize.lean`, `X86/Semantics.lean` |
| **D41** | the count had a comment and survived 13 batches; the sentence beside it had none and did not | `scripts/check_coverage_prose.py` |

## D40 — where this model and ACL2 x86isa deliberately part

`bsf`/`bsr` at a **zero source** leave the destination register undefined (SDM
Vol. 2A). Real silicon leaves it unmodified and AMD documents that it does;
Intel does not. This model follows its stated source and draws the destination
from the oracle, because writing the old value back would be inventing a fact —
the more tempting invention for matching the machine on the desk.

The two models therefore disagree exactly there, and it is visible in the run:

| case | pre-state `rax` | Lean (zero oracle) | ACL2 x86isa | classified |
|---|---|---|---|---|
| `bsf_rr_q/39` | `5555555555555555` | `0000000000000000` | `5555555555555555` | undefined-region |
| `bsf_rr_q/60` | `ffffffffffffffff` | `0000000000000000` | `ffffffffffffffff` | undefined-region |
| `bsr_rr_q/39` | `5555555555555555` | `0000000000000000` | `5555555555555555` | undefined-region |

**108 disagreements in `rax`, all in `bsf`/`bsr`, every one explained.** ⛔ Before
this batch the comparator's guard read `flagNames.contains k && a.undef.contains
k`, with a comment saying in as many words that *"a disagreement in a register
never is"* tested against the undefined set. Those 108 would have been
**unexplained — the gate failing on the model being RIGHT.**

⭐ **And the widening did not cost the leak check its teeth.** The undefined
registers are not simply derived from the two oracle runs the check compares —
that would make a register leak impossible to detect, since a stray oracle bit in
`rcx` would be re-read as "`rcx` is undefined here". There are two sources and the
gate is their EQUALITY: `declaredUndefRegs` reads the AST and the SDM rule,
`undefinedRegs` reports what actually moved. Probed three ways, all red:

| the declaration broken as | leaks |
|---|---|
| the destination is undefined ALWAYS, not only at a zero source | 378 |
| the destination is never declared (the old flags-only world) | 78 |
| **the right NUMBER of registers, the wrong NAME** | **78** |

The third is the one a count-based check would have passed.

## The zero source was reachable, and that was asserted rather than assumed

The batch needed **no new pre-state**: `preStates`' diagonal arm is `mkPre a a 0`
and `adversarial` contains 0, so RCX and the eight bytes at RBX are both zero in
some state. That is the same claim D14, D26 and D27 each caught being FALSE after
the fact, so it is a theorem here —
`bit_counting_reaches_a_zero_register_source`, `…_memory_source`, and a
`…_nonzero_source` beside them so that an all-zero pre-state set could not
satisfy the first two vacuously.

## The encoding hazard the batch is built around

**`lzcnt` is `bsr` plus an `F3` prefix, and `tzcnt` is `bsf` plus an `F3`
prefix** — the same opcodes `0F BD` and `0F BC`. A CPU without the feature
executes `lzcnt` AS `bsr`, silently. And they answer different questions about
the same bits: BSR reports the INDEX of the top set bit, LZCNT counts the zeros
ABOVE it. Batch 13's ACL2 probe measured the witness — `lzcntq 0x123456789ABCDEF0`
is 3 where `bsr` is 60 — and this model reproduces both before any differential
run.

Three of the four new selftest arms are that family of confusion:

| arm | field | caught |
|---|---|---|
| `bsr` reports leading zeros instead of the top bit's index | `rax` | 378 |
| `lzcnt` takes ZF from the source, as `bsf` does | `zf` | ✔ |
| `blsi` sets CF when the source IS zero | `cf` | ✔ |
| `popcnt` counts the whole register, not the operand | `rax` | ✔ |

The second is the one only a theorem could have stated: `ZF ← (DEST = 0)` and
`ZF ← (SRC = 0)` have the same answer for every source **except** those whose top
bit is set, where the count is zero and the source is not.

## Oracle support, MEASURED

All six execute against ACL2 x86isa: **2720 batch-14 cases, 2720 executed, 0
refused.** `lzcnt` and `blsi` are in this batch at all only because batch 13's
D36 overturned the catalogue prose that had struck them off — the rule being
*price a form against the oracle by EXECUTING one instance of it*, and this run
is that measurement at scale.
