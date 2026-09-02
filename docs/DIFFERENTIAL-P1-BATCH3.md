<!-- P1 batch 3's gate evidence. Regenerate with scripts/run_differential.sh. -->

# P1 batch 3 — CMP and TEST: the forms whose destination is the FLAGS

**The batch.** `p1/roster.tsv` families `xxxxxx-|-|flags/ctl` (CMP, **11 forms**,
38 K variants) and `0xuxx0-|-|flags/ctl` (TEST, **8 forms**, 25 K variants) —
**19 forms**, run together because they are one template question, *does the
destination get written?*, asked of `sub` and of `and` respectively.

**Chosen as the cheapest-template-first batch** the helm's wave word ordered.
Both mnemonics were already in P0's roster and `step` already discards their
results, so this batch adds **no semantics, no mnemonic and no template** — 51
vectors, 11 anchors, 5 assertions and its evidence. This is what a
zero-surcharge batch looks like, and the wave has 29 such forms left in it
(families 2–6) before every remaining batch invents a template.

## Result

```
cases=14060  matched=10458  explained=3676  unexplained=0
oracle-leaks=0  missing=0
  spec: 0          refusal: 0        harness: 0
  undefined-region: 3676
```

**190 vectors · 74 pre-states · 14060 cases · 0 unexplained.** Every gate arm
green. The differential run is **12.8 s** warm; the whole gate, selftest
included, is **~48 s**.

## The fast green, checked before it was believed

12.8 s against batch 2's banked 35.7 s, on 36% more cases. Per this seat's
standing law that was investigated rather than reported:

1. `run/acl2.out` was written **at run time** and carries the `ACL2 Version 8.7+`
   banner; the oracle file is 8.9 MB.
2. The 14060 oracle records hold **7653 distinct post-states**.
3. `cmp_rip_q` — the newest form — has **74 records in the oracle file**, so
   x86isa really executed the RIP-relative addressing mode.
4. **Two one-bit changes planted in batch-3 records were contradicted by the
   oracle**, right vector, right field, and *nothing else fired*:

```
[spec] cmp_mr_q/3 (cmp) mem@0000000000001ff0: lean=…af0e0000… oracle=…af0f0000…
[spec] cmp_rip_q/3 (cmp) zf: lean=1 oracle=0
```

The second says x86isa computed the RIP-relative comparison independently and at
the same address. The first says x86isa independently agrees that `cmp` writes
no memory. (The 35.7 s in batch 2's bank was the FULL gate, not the differential
alone — the runs are consistent.)

## What is new here, and it is all operand shape

* ⭐ **A memory operand in the DESTINATION position, read and never written** —
  `cmpq %rax, (%rbx)`, `testq $imm, (%rbx)`. Every earlier memory destination in
  this repository (`mov`, `push`, `call`) was *written*. "The destination is not
  written" had never been an anchored claim about a memory operand at all.
* **`cmp` and `test` at widths b, w and l.** P0 shipped one vector each, both at
  q; three quarters of their width behaviour was untested.
* ⭐ **RIP-relative addressing.** `Ea.addr`'s `ripRel` branch has existed since
  P0 and **no differential vector had ever executed it** — the only evidence was
  one `lea` anchor, i.e. this model checked against itself. Two anchors now pin
  *which* address it is (`nextRip + disp`, with the off-by-`len` address
  populated with a different byte so the wrong answer is a different answer),
  and clang's own bytes close decode trust on the form.
* The accumulator short encodings at all four widths, for both mnemonics.

**And what a `label` operand turns out to be**, since two of CMP's eleven forms
are `r,label` and `m,label`: K reads it from `<functargets>` as a `PointerVal` —
an address the assembler has not yet resolved. After linking it is an ordinary
sign-extended imm32, so `cmpq $L, %rax` and `cmpq $0x12345678, %rax` are **the
same bytes with a different number in them**. A post-decode model cannot
distinguish them and should not try. Those two forms are covered by
`cmp_ri_q`/`cmp_mi_q` **by identity**, stated rather than counted twice — and the
addressing mode a label actually implies is the RIP-relative one above, which is
how the roster's own vocabulary led to the untested branch.

## ⛔ The claim this batch made about itself, and the answer this time

Batch 3 claims its memory-destination vectors are **load-bearing**: that a `cmp`
which wrote its result back only at a memory destination would have been
invisible before them.

**The claim was tested, not asserted** — the nine memory-destination `cmp`
vectors were deleted and the arm re-run:

```
✔ cmp writes its result back:                     826 in `rax`      (unchanged)
⛔ cmp writes back ONLY to a memory destination:   ZERO disagreements
```

**True this time.** Batch 2 made the analogous claim and testing *refuted* it —
the accident-crossings in `adversarial`. The discipline is the same either way,
and the point is that neither answer was knowable without running it.

## The planted-bug pair, now a deliberate pattern

| planted bug | caught in | disagreements |
|---|---|---|
| `inc` clobbers CF | `cf` | 140 |
| `movl` fails to zero-extend | `rax` | 24 |
| shift forgets to mask its count | `rax` | 90 |
| `adc` drops the carry-in | `rax` | 630 |
| `adc`'s carry-OUT forgets the carry-in | `cf` | **115** (was 76) |
| **`cmp` writes its result back** | `rax` | 826 |
| **`cmp` writes back ONLY to a memory destination** | `mem@…1ff0` | 575 |

Each batch now plants a **pair**: an easy half almost any pre-state catches, and
a hard half only the batch's own new coverage can see. Batch 2's pair turns on
the carry boundary in the pre-states; batch 3's turns on a memory operand in the
destination. The hard half is the arm to run when asking whether some coverage
could be dropped.

## ⭐ Two findings this batch made about the work BEFORE it

**1. The memory operand was a constant (docs/DECISIONS.md D14).** Until now
`mkPre` wrote the same fixed pattern into the data window in all 74 pre-states,
so every `_rm_` form batches 1 and 2 shipped read **one source value, 74 times**.
The window's operand span now carries RCX. The proof that it mattered is in the
table above: `adc`'s hardest arm went **76 → 115** disagreements on the same
planted bug, because the memory-source `adc` forms now reach the carry boundary
too. Batch 2's evidence got stronger retroactively.

**2. The coverage table over-claimed, and a comment protected it
(docs/DECISIONS.md D15).** The `and`/`or`/`xor` row claimed the operand shape
`m,r (q)` — a memory destination — and no such vector has ever existed. Directly
above it sat a comment explaining that "`m,r` below is P0's row, at width q
only", describing something that was not there. Every mnemonic-level theorem
passed throughout. `mem_dest_claims_are_backed` now gates the shapes column
itself, was **driven red against exactly that string**, and costs 1292 ms of
kernel time — a price recorded in `scripts/kernel_ceilings.txt` rather than
absorbed.

## What is NOT claimed

* The memory-destination `and`/`or`/`xor` forms are roster family 4 and are **not
  covered**; the false claim that they were is what D15 removed.
* `cmp`/`test` with two memory operands cannot be encoded and are refused.
* Hardware co-simulation, for the same reason as batches 1 and 2.
