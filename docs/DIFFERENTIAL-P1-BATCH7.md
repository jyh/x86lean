<!-- P1 batch 7's gate evidence. Regenerate with scripts/run_differential.sh. -->

# P1 batch 7 — the shift group, and SAR's flag rule

**The batch.** Roster families 8, 9, 12, 13, 60 and 61 — **24 forms**:
`shl`/`sal`/`shr`/`sar` at a register **and** a memory destination, in all three
count encodings (`,one` = `D1 /r`, `,imm` = `C1 /r ib`, `,cl` = `D3 /r`).

## Result

```
cases=28046  matched=20582  explained=7628  unexplained=0
oracle-leaks=0  missing=0
  spec: 0          refusal: 0        harness: 0
  undefined-region: 7628
```

**379 vectors · 74 pre-states · 28046 cases · 0 unexplained.** Every arm green;
32.0 s warm.

## Two of the four mnemonics cost nothing

`sal` is an **alias** of `shl` — the same opcode `/4` — so a post-decode model
cannot distinguish them and must not try; covered by identity, like batch 5's
`jcc` synonyms. And `,one` is an **encoding** distinction: `D1` carries the count
in the opcode, `C1 ib` in a byte, and both decode to `.imm8 1`. Separate vectors
because the *bytes* differ, and the bytes are what XED is trusted for.

## ⭐ SAR's CF is DEFINED where SHL's and SHR's is not

The SDM's undefined clause names *"SHL and SHR instructions where the count is
greater than or equal to the size of the destination operand"*. **SAR has no such
clause** — shifting right past the width still has an answer, because every
vacated bit, and the last one out, is the sign.

So `sarb $9` (count 9, width 8) draws **no oracle bit** for CF where `shrb $9`
does, and `X86/Flags.lean`'s `shiftFlags` has a separate `.sar` branch for it.
`sar`'s row in the coverage table therefore carries a **shorter undefined list**
than `shl`'s and `shr`'s — two entries instead of three.

**And the oracle settled it.** This is a reading of one sentence, implemented and
then arbitrated. The planted control is the receipt:

```
[spec] sar_b9/6 (sar) cf: lean=0 oracle=1
```

Flipping CF on that record is contradicted by x86isa, which computed **1** — the
sign — independently. A model that had copied SHR's rule would have marked the
flag undefined and drawn a zero. (Second plant, in memory:
`sar_mi5_q/12 mem@…1ff0: lean=…0100…, oracle=…0000…`.)

## ⛔ The claim this batch made, and the defect the test found in the GATE

The claim: `sar_b9` is what makes SAR's CF rule visible. **Tested by deleting
it** — and the differential arm **still caught the bug, 49 disagreements instead
of 79**, because `sarb %cl, %al` reaches the same region whenever RCX's low five
bits are ≥ 8, which many pre-states satisfy. Over-specific and refuted, the third
time a claim of this shape has been.

**But this time the refutation landed on the assertion, not just the comment.**
`sar_covered_at_count_ge_width` had quantified over *vectors alone*, matching
only an `.imm8` count — so deleting `sar_b9` made **the theorem fail while the
coverage it guards was intact**.

⇒ 🔑 **AN ASSERTION NARROWER THAN THE COVERAGE IT GUARDS REPORTS A LOSS THAT HAS
NOT HAPPENED**, and a gate that cries wolf is one somebody eventually switches
off. It is the exact mirror of the over-claiming shapes column: there, prose
claimed more than the tests reached; here, a theorem claimed less.

It now quantifies over **(vector × pre-state)** — what "the tests reach this
region" actually means — and is calibrated three ways:

| state of the vector table | assertion | differential arm |
|---|---|---|
| everything present | passes | catches 79 |
| `sar_b9` deleted | **passes** (no false alarm) | catches 49 |
| `sar_b9` *and* the `cl` forms deleted | **fails** | catches **ZERO** |

It is silent exactly when the coverage survives and fires exactly when it does
not. None of the earlier pre-state assertions had been calibrated in both
directions.

## The planted-bug set is fifteen

The two new arms: `sar` brings in zeros instead of the sign (198 in `rax` — the
easy half, any negative operand catches it), and `sar` given SHL/SHR's
undefined-CF rule at a large count (79 in `cf` — the hard half, a misreading of
the SDM rather than a typo).

## What is NOT claimed

* `shld`/`shrd` (double-precision shifts) — roster families 24 and 40.
* `rcl`/`rcr`/`rol`/`ror` — families 25, 26, 49–52.
* Hardware co-simulation, as in every batch so far.
