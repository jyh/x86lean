# P1 BATCH 15 — the string group, and the pointer that never crossed a boundary

**Forms.** Roster families 11, 14 and 15: `movs`, `stos`, `lods`, `cmps` and
`scas` at all four widths — **10 roster rows, 20 differential vectors**, taking
the model to **418 of the 525 rows (80%)**.

```
cases=49118  matched=34057  explained=20767  unexplained=0  oracle-leaks=0  missing=0
  spec: 0   refusal: 0   harness: 0   undefined-region: 20767
599 vectors · 82 pre-states · 72 mnemonics
```

Gate met on the FIRST run, in 1 m 32 s.

⚠️ **The 21 rows the roster files under these five base names are NOT all this
batch's.** Eleven carry a `rep`/`repe`/`repne`/`repnz`/`repz` prefix and are
loop control over the same data movement; this batch claims the ten unprefixed
rows. Counting by base name alone would have over-stated the coverage literal by
eleven — the first group in the roster where the base-name rule is not the
counting rule.

## What the batch actually was

The first forms in this model with **no operand field at all** — the addresses
are RSI and RDI by opcode, the accumulator is RAX by opcode, and the encoding
varies only the width — and the first that **read DF**, a flag that had been
diffed since P0, writable since batch 11, and never read by anything.

| # | finding | where |
|---|---|---|
| **D42** | the watch window had to be WIDENED or the backward case would have passed by construction | `Tests/Vectors.lean`, `scripts/x86isa_driver.lisp` |
| **D43** | a planted defect caught NOTHING: the pointers never crossed a width boundary | `Tests/Vectors.lean` |
| **D44** | the coverage table's `shapes` column was checked in ONE direction for fourteen batches | `Tests/Coverage.lean` |
| **D45** | a cross-language duplicate, and the parser written to gate it was itself wrong | `scripts/check_windows.py` |

## The oracle was measured before a line of semantics was written

Per D36 — support is measured by EXECUTING, never read from a catalogue — 24
probe cases went to ACL2 x86isa first. All 24 came back `refused=0`. Three
results shaped the batch:

1. ⭐⭐ **`rep` is not a loop in this oracle.** `x86-fetch-decode-execute`
   performs exactly ONE iteration and expresses "go round again" by *not
   advancing RIP*: `rep movsq` with RCX=3 came back `rcx=2, rip=0x400000`
   (unchanged), while `repe cmpsq` on unequal operands came back `rcx=2,
   rip=0x400003` (advanced — ZF=0 ended the repeat). That is why the `rep` rows
   are a separate batch and not eleven more vectors here: they are a different
   mechanism, and they need no new pre-state.
2. ⛔ **`cmps` computes `[RSI] − [RDI]`**, the reverse of the AT&T print order
   (`cmpsq %es:(%rdi), (%rsi)`). Measured from the flags — `[rsi]=a0`,
   `[rdi]=b0` gave `cf=1 sf=1 pf=1`, i.e. `0xa0 − 0xb0`. ⚠️ `scas` is
   `RAX − [RDI]` and would NOT be inverted by the same mistake, so the two do
   not fail together.
3. The copy happens at the CURRENT pointers and the update comes after — with DF
   set, the oracle still wrote at RDI's original address.

## D42 — a backward step off the end of a window is a test that passes by construction

RSI and RDI were **0 in all 80 pre-states** (measured in the emitted cases, not
only read off `mkPre`), and address 0 is outside both watched windows. That is
batch 12's `leaveq` trap exactly: both models unobserved, and agreement that
tested nothing.

⛔ But the deeper problem is the one that survives giving the pointers a home.
Off the end of a watched window, this model's `Mem` reads 0 for an unwritten
byte and the ACL2 driver renders an unmapped read as `00`. **So a pointer that
decremented when it should have incremented would have the two models agreeing
on zeroes.** The DF case would have been green without being tested.

The data window is therefore widened from 32 bytes to 64 (`0x1ff0 len 32` →
`0x1fe0 len 64`), with RSI at `0x1fe8` and RDI at `0x2010`: each has eight bytes
of operand and at least eight of margin *in both directions*, forty bytes apart,
so one step either way stays inside watched memory at every width.

⭐ **Every one of the original 32 bytes kept its address and its contents.** The
two new flanks get their own patterns (`0x60+i`, `0xE0+i`) rather than re-basing
`0xA0+i`, which would have moved the whole window and broken
`memory_window_margin_is_fixed`. The same device batch 11 used to make DF bit 6
of the flag seed without renumbering the six below it.

⚠️ **And the string operands had to be a THIRD and FOURTH swept value.** With
`[RSI] = a` the whole of `lods` is a no-op — it loads RAX from RSI and RAX
already holds `a` — so a model that never wrote the accumulator would agree in
every state; `[RDI] = a` does the same to `stos`. This is D14 in a sharper form:
the operand *does* sweep, and the form is still untested, because it sweeps in
lockstep with the register it is compared against. So `[RSI] = c` and
`[RDI] = a XOR c`, which also keeps ZF reachable for both comparisons
(`cmps` is zero exactly when `a = 0`, `scas` exactly when `c = 0`).

## D43 — the planted defect that caught nothing, and why it was the pre-states' fault

An arm updated RSI and RDI through the ordinary operand-width rule (`setReg sz`)
instead of writing all 64 bits — the natural mistake, because every other
register write in this model does go through that rule. The comparator's verdict:

```
⛔ a string pointer is updated at the OPERAND width, not 64 bits:
   comparator reported ZERO unexplained disagreements against a KNOWN-WRONG model.
```

⚠️ **The arm was right; the pre-states were wrong.** A merged write and a full
write differ only when the new pointer differs from the old *above* the operand
width — that is, only when the update CARRIES or BORROWS across a byte or word
boundary. With RSI at `0x1fe8` and RDI at `0x2010`, `±1` and `±2` never touch
bit 8, so the wrong model **is** the right model on all eighty states, at every
width, in both directions.

⇒ D27's rule in its `loopCounterStates` form: **an adversarial set is
adversarial only with respect to the questions already asked of it.** The
pointer addresses were chosen to keep every access inside a watched window —
a question about ADDRESSES. Nothing had yet asked a question about the
ARITHMETIC that produces the next address.

`stringBoundaryStates` adds the two directions: forward with both pointers at
`…FF` so the increment carries (`0x1fff`, `0x7fff`), backward with both at `…00`
so the decrement borrows (`0x2000`, `0x8000`). All four addresses are inside a
watched window at every width, so the states test the pointer arithmetic without
giving up the observation that made the group testable. The arm now catches 8
disagreements in `rdi`.

⇒ 🔑 **A probe that reports nothing has two possible causes, and the flattering
one is that the model is right.** The other is that the state cannot express the
difference — and only one of the two is visible from the green.

## D44 — the shapes column was checked in one direction only

`mem_dest_claims_are_backed` catches a row claiming MORE than its vectors
deliver. Nothing caught a row claiming LESS.

⛔ **This batch would have been the first to fall in it.** The string rows were
first written as `implicit [rdi] ← [rsi]` — accurate English, containing no
first-position `m`, so `claimsMemDest` was false for `movs` and `stos` while
their vectors plainly write memory. Every gate in the file stayed green on a
coverage table that had quietly stopped saying what the model does.

`mem_dest_vectors_are_claimed` is the other direction. ⇒ **A table checked in
one direction is only half checked, and the unchecked half is the one where the
claim is too SMALL — which is exactly the half a reader trusts, because an
under-claim never looks like a mistake.**

⭐ Rewriting the shapes in the column's own destination-first notation also made
`mem_dest_rewrite_changed_exactly_the_three_operand_rows` grow its first
`(_, false)` entries: `cmps` and `scas` are claimed by the positional rule and
missed by the legacy loose one, which searches for the literal string `m,r`.
**Batch 14 added that slot with no row exercising it. One batch later, two rows
did.**

## D45 — a cross-language duplicate, and the gate for it was itself wrong

The watch windows are declared twice — `Tests/Vectors.lean` and
`scripts/x86isa_driver.lisp` — because neither toolchain can read the other's
source, and until this batch a comment was the only thing holding them together.
This batch's ordinary append was widening that constant.

⚠️ Stated honestly: the drift fails **loud**, not silent — any mismatch makes
every rendered record differ. What `scripts/check_windows.py` buys is detection
in 20 ms instead of after a 4-minute ACL2 run, which is the difference between a
check that runs before a commit and one that does not.

⛔ **And its first version parsed only the FIRST window** — a non-greedy regex
ended its capture at the first `))`, and the last pair's closing paren is the
list's closing paren. **Its selftest passed anyway**, because both planted
mutations happened to be in the first window. ⇒ **A positive control proves the
gate reacts to the condition it CREATES; it says nothing about the part of the
subject the control never touches.** The parser is now a paren-balance scan, the
selftest mutates each side's FIRST and LAST window, and the count of parsed
windows is compared directly.

## What the group needed, and what it did not

| | cost |
|---|---|
| semantics | one `step` case, five arms, no new helper |
| AST | one constructor with no operand field |
| undefined-bit oracle | **nothing** — every row is `T-exact`, the first whole group since batch 12 to draw no oracle bit |
| pre-state | ⭐ **the expensive half**: two pointer registers, two swept operand spans, a window widened by 32 bytes, and two new boundary states |

⇒ Batch 12's law, confirmed a fourth time: **the cheapness of a form is a fact
about its SEMANTICS; its cost is a fact about the STATE it needs.**
