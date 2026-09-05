# P2 BATCH 18 — `PMOVMSKB`, and a ceiling with two milliseconds of headroom

> ⚠️ **TWO COUNTERS.** Eighteenth differential record; the seat's **batch 23** in
> `docs/DECISIONS.md`.
>
> ⛔⛔ **THIS BATCH IS NOT ON `master`.** Its differential is green and its
> kernel-cost gate returns a RED VERDICT IN BAND. See D122; it waits on
> `p2-batch23-pmovmskb` until D111's delta gate or CI's runner can score it.

**Form.** `pmovmskb` — one roster row, 2 vectors, one constructor, no new state,
**453 instructions**. The last form in the measured residue needing no new
vocabulary.

## 1. ⭐⭐ NO WIDTH FIELD, ON TWO INDEPENDENT SOURCES

The SDM lists `PMOVMSKB r32, xmm` and `PMOVMSKB r64, xmm` as separate rows, which
invites a `Size` parameter. Both sources say otherwise:

* **K** gives `pmovmskb_r32_xmm.k` and `pmovmskb_r64_xmm.k` the identical value,
  `concatenateMInt(mi(48,0), <16 bits>)` — one semantics under two names;
* **the assembler** goes further: `pmovmskb %xmm1,%eax` and `pmovmskb %xmm1,%rax`
  emit the **same bytes**, `660fd7c1`. REX.W buys nothing when the result is
  zero-extended, so the two spellings are not merely equivalent — they are the
  same instruction.

⇒ 🔑 A width field here would be **one no encoding can set and no semantics can
read**. The 32-bit write already zero-extends by SDM Vol. 1 §3.4.1.1, which
`Cpu.setReg .d` implements, so the rule is INHERITED rather than restated.

⚠️ **And that is why there is no r64 vector.** A second vector would be the first
one under another name — a duplicate born in agreement, not a second test.

## 2. THE ARMS, AND WHAT THEIR SCORES ARE ABOUT

```
pmovmskb reads the LOW bit of each byte        83
pmovmskb reverses the lane order               51
pmovmskb merges instead of clearing 63:16      46
```

⚠️ The last two score low **for reasons about the pre-states, not the
instruction**: a reversed mask is invisible wherever the byte-sign pattern is a
palindrome, and a merging model is invisible unless the destination already holds
bits above 15. Both are joint facts about model and pre-states
([[a-wrong-models-score-is-a-joint-fact]]), and neither number would improve by
making the model more correct.

⭐ The merging arm is D93's defect in its natural home: there the oracle MERGED
where the SDM clears. Here the model must clear, and the arm that fails to is the
one a reader writes when they forget §3.4.1.1.

## 3. RECEIPTS

```
cases=84128 matched=63596 explained=29435 unexplained=0 oracle-divergence=171 oracle-leaks=0 missing=0
956 vectors · 88 pre-states · 84128 cases · 0 unexplained · 0 oracle leaks
```
171 oracle-divergences, unchanged; this batch adds none.

### ⛔ The kernel-cost gate, IN BAND, RED

```
                          parent 0f7baee (3.90)   this batch (3.04)   delta   ceiling
X86.Syntax                       198.0 ok              206.0 ⛔         +8      200
Tests.Coverage (residue)        12610  ⛔             13190  ⛔       +580    12420
```

⛔ **The `X86.Syntax` ceiling has 2 ms of headroom on `master`** — the parent passes
at 198 of 200, and one AST constructor costs +8. So this is **not a fact about
`pmovmskb`**: the next batch that adds any constructor crosses it too. And
`Tests.Coverage`'s residue is over on `master` already.

No ceiling was raised — see D122 §3 for why doing so inside the batch the gate just
stopped is the worst available moment, and for the two legitimate routes.
