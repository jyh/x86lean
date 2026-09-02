<!-- P1 batch 11's gate evidence. Regenerate with scripts/run_differential.sh. -->

# P1 batch 11 — the loop group and the flag-control singles

**The batch.** Roster family 15's loop group (LOOP/LOOPE/LOOPNE, with the
`loopz`/`loopnz` spellings) and families 54–59 (CLC/STC/CMC/CLD/STD).
**15 roster forms**, 12 new vectors, **4 new pre-states**. Coverage 367 →
**382 of the 525** (73%).

## Result

```
cases=40482  matched=28367  explained=15097  unexplained=0
oracle-leaks=0  missing=0
  spec: 0          refusal: 0        harness: 0
  undefined-region: 15097
```

**519 vectors · 78 pre-states · 40482 cases · 0 unexplained**, on the first run.
Encoding cross-check **519/519 against clang**; axiom gate clean on the three
standard axioms; 27/27 selftest arms caught.

## ⛔ AND THE GATE THAT REPORTS THAT WAS RUNNING TWENTY-THREE OF THE TWENTY-SEVEN

The batch's four new arms all caught under `selftest <substring>`. The
no-argument form — **the one CI runs** — then printed:

```
harness selftest — twenty-three deliberately wrong models, each must be caught:
...
harness selftest: PASS
```

PASS, over 23 arms, from a table of 27. The filtered probe folded over
`selftestArms`; the gate had its own hand-written sequence of 23 `driveWrong`
calls and a 23-term conjunction. **The four new arms had never run, and nothing
in the output said so except a hardcoded banner literal.**

The table's own doc comment said this could not happen — *"named once so the
filtered probe mode and the full selftest cannot drift apart"* — and that
sentence, written one commit earlier by the batch that introduced the table, is
what made the duplicate invisible.

Verified from the history: `selftestArms` appears first in `3f0111e`, and
`HEAD:Main.lean` holds exactly **23** `driveWrong` calls against a 23-row table.
**The duplicate was created in agreement.** It needed no mistake to diverge, only
the next batch to append a row — the thing the table exists to make easy.

Fixed here: both readers fold over the table, and every count in the file is now
`selftestArms.length` rather than a literal. Recorded as D29.

⚠️ Batch 10's own four arms were in the hand-written list, so no earlier batch's
green is void. Only this batch's four were at risk — and what caught it was the
stale literal, the one number in the file nobody trusts.

## ⛔ THE HEADLINE IS NOT A FORM. IT IS A FLAG THE COMPARATOR HAD BEEN WATCHING FOR TEN BATCHES WITHOUT BEING ABLE TO SEE IT MOVE.

`df` has been a field of `Flags` since P0. `Serialize.lean` has PRINTED it since
P0 and DIFFED it since P0; it is in `flagNames`; it is packed into bit 10 of the
RFLAGS word handed to ACL2. Every instrument in the repository said DF was under
test.

It was `false` in all seventy-four pre-states, and **until this batch no
instruction in the model could write it**.

`cld` clears DF. Against a state where DF is already clear, **`cld` and a no-op
are the same function.** The `wrongCldIsNoOp` arm — a `cld` that does nothing at
all — catches **2 disagreements** with the new pre-states and **ZERO** without
them, and the comparator reports the zero as agreement.

⇒ **A component under a working comparator is not thereby tested. It is tested
only if something can change it.** Recorded as D27.

### And the fix was verified END-TO-END, at the oracle, not just in Lean

The selftest arms compare Lean against Lean, so the `cld` arm's catch proves
only that *this* model's comparator can see `df`. What proves the ORACLE sees it
is the emitted case file:

```
$ grep -o ':rflags #x[0-9A-Fa-f]*' run/cases.lsp | ...
1038 of 40482 emitted ACL2 cases carry DF=1      # = 519 vectors × 2 new pre-states
     519  :rflags #x00000402                     # DF alone
     519  :rflags #x00000cd7                     # DF and all six arithmetic flags
```

Those 1038 cases returned **zero unexplained disagreements**. That is the
load-bearing part: 507 of the 519 vectors do not write DF at all, so if the
harness had dropped bit 10 on the way to ACL2 — or if x86isa had ignored it —
the oracle would have come back with `df=0` where this model preserved `df=1`,
on more than a thousand cases. It did not. **DF is now carried, set, preserved
and compared across both models**, where for ten batches it was carried, never
set, and compared against itself.

## AND THE SAME DEFECT, IN THE SAME BATCH, IN ITS OTHER FORM

`addr32 loop` counts in **ECX**; the unprefixed form counts in **RCX**. A model
that wrote the counter back at the right width but TESTED all sixty-four bits
differs from the correct one on exactly the states where the low 32 bits of RCX
are 1 while the upper half is not zero.

`adversarial` holds `1` (upper half zero) and `0x100000000` (low half zero) and
**nothing that is both**. The bug was invisible — not because a register was a
constant, as in D26, but because two halves of one register had never been asked
to disagree.

⇒ D14 was a constant memory window; D26 a constant RDX; **D27 is a constant flag
AND an unreached combination, which is what says the rule is not about
registers**: a state component *or distinction* that no existing instruction
exercises is a constant, and a gate watching a constant reports agreement it
never tested.

## The probes — three, both directions, one per new mechanism

| probe | arm | assertion |
|---|---|---|
| delete `dfStates` | `cld` arm catches **0** | `pre_states_set_df` **FIRES** |
| delete `loopCounterStates` | `addr32` arm catches **0** | `pre_states_reach_ecx_one_over_a_nonzero_upper_half` **FIRES** |
| delete **one of two** `dfStates` | `cld` arm still catches (**1** of 2) | assertion **SILENT** — no wolf cry |

The third row is the calibration D21 asks for, run by design rather than after a
false alarm: an assertion narrower than the coverage it guards would have fired
on the half-deletion, and this one does not.

## The four planted bugs

| arm | half | caught |
|---|---|---|
| `loop` tests the counter before decrementing it | easy | 71 in `rip` |
| `loop` writes the counter back only when it branches | hard | 167 in `rcx` |
| `addr32 loop` tests the full 64-bit counter | hard | **4** in `rip` |
| `cld` is a no-op | easy | **2** in `df` |

⭐ **THE TWO NARROW COUNTS ARE THE POINT.** 4 and 2 are exactly the new
pre-states multiplied by the vectors that can distinguish them — the arms are
narrow because the coverage they depend on is narrow, and both were **zero**
before this batch touched `preStates`.

## ⭐ AND A FORM'S COVERAGE CAN DEPEND ON A SIBLING FORM RATHER THAN ON ITS OWN VECTORS

`wrongLoopNoWritebackOnFallthrough` — decrement and write back only when
branching — is caught **167** times. But plain `loop` falls through at exactly
ONE counter value (1), so a table of `loop` alone would have rested the entire
bug on whether `adversarial` happened to contain a 1.

`loope`/`loopne` fall through whenever ZF has the wrong polarity, which is about
half of every pre-state. The bug is caught broadly **only because the
conditional predicates are in the table** — the plain form's own vectors barely
touch it.

## `explained` rose, and NOT ONE UNIT OF THE RISE IS THIS BATCH'S

`explained` went 14347 → **15097**, +750. Batch 11's forms write **no undefined
bit at all**: the loop group's "Flags Affected: None" and the flag singles'
"all other flags are unaffected" leave the model with zero oracle draws here,
which `step_loop_oracle` and `step_flagop_oracle` prove rather than assert.

The whole +750 comes from the **4 new pre-states multiplying across the 507
OLDER vectors** — forms that do draw oracle bits. Batch 10's `explained` did not
move because it added vectors only; this one moved because it added *states*,
and a state is multiplied by every form that already exists.

⇒ **A pre-state addition is priced against the WHOLE table, not against the
batch that needs it.** 4 states cost 2028 new cases on old forms; the 12 new
vectors cost 936. (37518 + 2028 + 936 = 40482. ✓)

**And the attribution is checkable rather than merely plausible.** If the +750
really came from old forms in new states, its rate should match the old forms'
existing explained rate:

| | explained / cases | rate |
|---|---|---|
| batch 10, whole table | 14347 / 37518 | **38.2%** |
| the 2028 new cases on OLD vectors | 750 / 2028 | **37.0%** |
| the 936 new cases on BATCH 11 vectors | **0** / 936 | **0%** |

The two rates agree to about a point, and batch 11's own contribution is exactly
zero — which is what `step_loop_oracle` and `step_flagop_oracle` require, since a
form that draws no oracle bit has an empty undefined set and *cannot* produce an
explained disagreement.

## What the batch contains

| group | forms | what is new |
|---|---|---|
| `loop`/`loope`/`loopne`, both counter widths | 10 | decrement-then-test; write-back on both paths; `addr32` as a width on read, wrap AND test |
| `clc`/`stc`/`cmc`/`cld`/`std` | 5 | the first writers of DF; one flag bit each, five cases from one template |

Also new: the **first backward branch vector** in the repository (`loop .-2`,
rel8 = `0xFC`). Every other branch vector jumps forward, against which a dropped
displacement sign is invisible.

## An assembler note, kept because the source string is misleading

For the prefixed forms clang computes `.` from the address AFTER the `0x67`
byte, so `addr32 loop .+18` encodes rel8 = `0x10` and actually targets `.+19`.
The **bytes** are the authority — `scripts/check_encodings.py` compares the
model's `d` against the disassembly, and it agrees — but a reader checking the
`asm` string by hand would come out one short. Second time this batch that the
assembler, not the manual, settled a question (cf. D24).
