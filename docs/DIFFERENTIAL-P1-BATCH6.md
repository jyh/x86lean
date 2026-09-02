<!-- P1 batch 6's gate evidence. Regenerate with scripts/run_differential.sh. -->

# P1 batch 6 — SETcc and CMOVcc: 120 forms over two `step` cases

**The batch.** The condition-code families of `p1/roster.tsv` — 16, 18–22,
28–30, 34–38, 44 and 45 — **120 forms**: `SETcc` at a register and a memory
destination (30 spellings × 2) and `CMOVcc` at `r,r` and `r,m` (30 × 2).

## Result

```
cases=24346  matched=19856  explained=4564  unexplained=0
oracle-leaks=0  missing=0
  spec: 0          refusal: 0        harness: 0
  undefined-region: 4564
```

**329 vectors · 74 pre-states · 24346 cases · 0 unexplained.** Every arm green;
24.4 s warm. Positive control — two planted one-bit changes, both contradicted:

```
[spec] sete_m/9        (setcc)  mem@…1ff0: lean=…af0180… oracle=…af0080…
[spec] cmovne_rr_l/17  (cmovcc) rax: lean=00000000fffffffe oracle=00000000ffffffff
```

## ⭐ 120 forms for two `step` cases, and a P0 decision is why

`Cc` has **one constructor per PREDICATE, not per mnemonic** — a P0 choice, made
because `jz` and `je` are the same instruction and a model that distinguishes
them is modelling the assembler. K files 30 branch mnemonics, 30 `set`
mnemonics and 30 `cmov` mnemonics: **ninety names, sixteen predicates, one
table.** `Cc.suffixes` is that table; `Cc.synonyms`, `Cc.setSpellings` and
`Cc.cmovSpellings` derive the three families of names from it.

⇒ **This is what "cheapest by BEHAVIOUR, not by form count" looks like when an
earlier design was right.** A model with one constructor per mnemonic would be
writing 90 cases here and would have paid batch 5's cost three times over.

## ⚠️ The one place CMOVcc is not what it looks like

**The destination is written whether or not the condition holds** — only the
*value* is conditional. At widths `w` and `q` that is invisible. At width `d`
the write **zero-extends** (SDM Vol. 1 §3.4.1.1), so:

```
cmovel %ecx, %eax   with ZF CLEAR   moves nothing and still CLEARS the upper half of RAX
```

Writing this as "if the condition holds, move" is the natural reading of the
mnemonic and is wrong on exactly the 32-bit forms. **Every `cmov` vector here is
at width `l` for that reason**, with `w` and `q` present for two conditions to
supply the contrast — without them, `cmov_not_taken_still_zero_extends_at_d`
would be satisfied by a model that zero-extends everything.

**And the oracle settled it.** This is a subtle SDM reading, implemented from the
manual and then arbitrated: x86isa agrees, across all 74 pre-states of all 32
width-`l` vectors, 0 unexplained. The planted control shows the same —
`cmovne_rr_l/17` comes back `rax=00000000ffffffff`, upper half cleared, from
both models independently.

## ⛔ The claim this batch made about itself

That the width-`l` vectors are load-bearing. **Tested by deleting all 32 of
them** (keeping `w` and `q`) and re-running:

```
✔ setcc inverts its condition:                   1190 disagreements  (unchanged)
⛔ cmov skips the write when the condition is false:  ZERO disagreements
```

And — the second batch running — the assertions written *before* the probe
fired too: `vectors_cover_every_cmov_condition` and `cmov_covered_at_width_d`
both failed. The gate stood in front of the loss rather than being written after
one.

## The gate's notation grew a third case, without bending

D15's `mem_dest_claims_are_backed` knew `m,r` (binary memory destination) and
`m(rmw)` (unary read-modify-write). `setcc`'s memory form is neither: it is a
**write that never reads**, so `m(rmw)` would be a false description of it.

The pattern was generalised from the literal `m(rmw)` to the **prefix `m(`**, and
`setcc`'s shapes read `m8(w)`. The parenthesis is what distinguishes a memory
*destination* from `r,m`'s memory *source*; what goes inside is free to say
which kind of write it is. ⇒ **D16's law applied prospectively for once: the
notation was extended so the check could stay honest, rather than the claim
being bent to fit the check.**

## The planted-bug set is thirteen, still in pairs

| planted bug | caught in | disagreements |
|---|---|---|
| `inc` clobbers CF | `cf` | 560 |
| `movl` fails to zero-extend | `rax` | 24 |
| shift forgets to mask its count | `rax` | 90 |
| `adc` drops the carry-in | `rax` | 630 |
| `adc`'s carry-OUT forgets the carry-in | `cf` | 115 |
| `cmp` writes its result back | `rax` | 826 |
| `cmp` writes back ONLY to a memory destination | `mem@…1ff0` | 575 |
| a memory RMW drops its STORE | `mem@…1ff0` | 1726 |
| a memory store ignores its operand WIDTH | `mem@…1ff0` | 792 |
| `jcxz` inverts its test | `rip` | 140 |
| `jecxz` ignores the address-size prefix | `rip` | 6 |
| **`setcc` inverts its condition** | `rax` | 1190 |
| **`cmov` skips the write on a false condition** | `rax` | 384 |

## What is NOT claimed

* `cmovcc` at a memory destination — **no such form exists** (`cmovcc r, r/m`
  only), which is why its shapes read `r,m` and never `m,r`.
* `setcc` at any width but 8: the destination is one byte by definition.
* Hardware co-simulation, as in every batch so far.
