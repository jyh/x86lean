# P2 BATCH 15 — `packuswb`, the one member of its group the oracle can execute

> ⚠️ **TWO COUNTERS.** Fifteenth differential record; the seat's **batch 18** in
> `docs/DECISIONS.md`.

**Form.** `packuswb` at both operand shapes. One roster row, 2 vectors, one new
`VBinKind` constructor and one combinator — `Op.vbin` and `Op.vbinm` carry the
shapes and batch 15's alignment rule comes with them. **5,105 buildable
instructions** (6,230 total, 18.1% MMX-register and declined).

## 1. ⛔⛔ THE GROUP IS ONE MNEMONIC WIDE, AND THAT IS A MEASUREMENT

`packuswb` has two siblings and **both refuse on the oracle at every pre-state**
(D115): `packsswb`, and `packssdw` — **roster rank 15, 5,613 instructions**, which
the roster ranked as available work until it was measured.

⇒ 🔑 **A BATCH SAMPLED AT `packuswb` WOULD HAVE PASSED.** It is the group's
natural representative: same encoding family, adjacent opcodes, same operand
shapes, and it executes and returns the SDM's answer at 88 of 88. Two thirds of
the group cannot be run at all. [[a-batch-cannot-be-sampled]], and the sample that
would have been taken here is drawn from **the same mnemonic family**, which is
the sampling that feels safest of all.

## 2. THE SATURATION IS ASYMMETRIC, AND THAT IS THE INSTRUCTION

The SOURCE lanes are read **signed**; the RESULT lanes are **unsigned**. A
negative word saturates to **0** and a word above 255 to **255** — opposite ends.
Measured against the oracle, three wrong models, 88 pre-states:

```
                          trunc   unsigned-source   swapped
packuswb %xmm1,%xmm0          0                32        20
packuswb (%rbx),%xmm0         0                 0        38
```

⚠️ **Truncation is the model to fear.** Keeping the low byte is bit-identical at
every IN-RANGE value — which is every value a vector table written without
adversarial constants contains. It survives 0 of 88 here *only because*
`adversarial` reaches out of range; a table of small positives would have scored
it 88 and said nothing.

⭐ **The unsigned-source model is refuted best by the MEMORY vector** (0 of 88
against 32 at the register shape), because the memory source sweeps while `xmm1`
is a fixed pattern. The two vectors are not interchangeable.

## 3. NOT `vlanes`, AND THE REASON IS STRUCTURAL

This is the first operation in this model that **narrows**: lane `i` of the result
is not a function of lane `i` of the operands, so the combinator that pairs them
cannot express it. `vpackus` is written beside `vlanes`, `vunpack`, `vlanes1` and
`vselect` — five combinators now, each existing because a previous one could not
say the thing.

## 4. RECEIPTS

```
cases=83072 matched=62540 explained=29435 unexplained=0 oracle-divergence=171 oracle-leaks=0 missing=0
944 vectors · 88 pre-states · 83072 cases · 0 unexplained · 0 oracle leaks
```

⚠️ 171 oracle-divergences, unchanged; this batch adds none.

The remaining local gates and the CI run URL are in the commit message.
