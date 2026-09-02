<!-- P1 batch 8's gate evidence. Regenerate with scripts/run_differential.sh. -->

# P1 batch 8 — the rotates, where the count is reduced twice

**The batch.** Roster families 25, 26, 49, 50, 51 and 52 — **24 forms**:
`rol`/`ror`/`rcl`/`rcr` at a register **and** a memory destination, in all three
count encodings. The same opcode block as batch 7's shifts (`D0`–`D3`,
`C0`/`C1`), a different `/r` field, and entirely different flag rules.

## Result

```
cases=32412  matched=23557  explained=9019  unexplained=0
oracle-leaks=0  missing=0
  spec: 0          refusal: 0        harness: 0
  undefined-region: 9019
```

**438 vectors · 74 pre-states · 32412 cases · 0 unexplained.** Every arm green;
43.0 s warm.

⭐ **This is the batch where the differential earned its keep most plainly.**
`rcl`/`rcr` rotate a `w+1`-bit ring, reduce their counts modulo 9 and 17 at
widths b and w, and place their OF computation on opposite sides of the rotate
from each other. Four rules, each read off one SDM page, each implementable
wrongly in a way the model would not notice — and all four came back agreeing
with ACL2 x86isa on the first run.

## The count is reduced twice, and the two reductions differ

1. The processor masks the count to 5 bits (6 at width `q`), exactly as the
   shifts do.
2. Then `rol`/`ror` reduce **modulo the width** — a rotate by the width is the
   identity — while `rcl`/`rcr` reduce **modulo the width plus one**, because
   the value they rotate is the operand *and CF together*.

⚠️ **And the flag rules key off the FIRST reduction, not the second.**

## The three vectors that are the whole point

| vector | masked | reduced | data | CF |
|---|---|---|---|---|
| `rol_b8` | 8 | 0 | unchanged | **written** |
| `rol_b9` | 9 | 1 | rotates by 1 | written, **OF undefined** |
| `rcl_b9` | 9 | 0 (mod **9**) | unchanged | **unchanged** |

* `rol_b8` — the SDM's rule is *"IF COUNT ≠ 0 THEN CF ← LSB(DEST)"*, and COUNT
  there is the **masked** count. The data does not move and CF is written
  anyway. A model asking "did the data move?" is wrong here and nowhere else.
* `rol_b9` — the data rotates by one and **OF is still undefined**, because the
  SDM's OF rule asks whether the count is 1, and it is 9. The reduced count
  being 1 is not the question.
* `rcl_b9` — the opposite of `rol_b8`, at the same count, one opcode away.
  `rcl` reduces modulo **nine**, so its reduced count is also 0 — but `rcl`'s CF
  rule *is* the rotate loop, and a loop that does not execute writes nothing.

## Two more rules that differ by a line of the manual

**RCR's OF is computed BEFORE the rotate; RCL's after.** The SDM writes the same
sentence — `OF ← MSB(DEST) XOR CF` — above RCR's loop and below RCL's. On
`rcrb $1` of `0x80` with CF clear the two readings give 1 and 0.

**A rotate touches only CF and OF.** SF, ZF, PF and AF come out exactly as they
went in — the sharpest difference from the shifts, which recompute all four from
the result, and the reason the rotate rows' undefined lists have one entry where
the shifts' have three.

## What is NOT claimed

* `shld`/`shrd` — families 24 and 40.
* Bit-string rotates or `rorx` (BMI2).
* Hardware co-simulation, as in every batch so far.

## One number on the coverage page that nothing checks

`docs/COVERAGE.md`'s header now reads its mnemonic count from `rosterSize` and
its form count from the vector table — but **"331 of the 525" is a
hand-maintained literal**, because the roster lives in a TSV the executable does
not read. It is named here rather than left to be discovered: a stale count in a
generated header is precisely the defect D15 and D16 are about, and this one is
sitting inside the file those decisions were written to protect.

Closing it means teaching `x86lean-diff coverage` to read `p1/roster.tsv`, or
having `scripts/k_roster.py` emit the covered count. Neither is done.
