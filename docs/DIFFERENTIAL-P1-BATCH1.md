<!-- P1 batch 1's gate evidence. Regenerate with scripts/run_differential.sh. -->

# P1 batch 1 — the logic group at every operand shape

**The batch.** `p1/roster.tsv` family `0xuxx0-|-|reg`, the first of the wave's
61: **AND, OR and XOR writing a REGISTER** — CF and OF cleared, SF/ZF/PF from
the result, AF undefined. **21 forms in K's roster, 72 K variants.** The batch
was chosen by `scripts/k_roster.py`'s stated order (families P0 already has a
template for first, largest first), not by hand.

## Result — the per-batch gate, every arm

```
cases=6800  matched=4236  explained=2632  unexplained=0
oracle-leaks=0  missing=0
  spec: 0          refusal: 0        harness: 0
  undefined-region: 2632
```

| gate arm | result |
|---|---|
| differential vs ACL2 x86isa, zero unexplained, explained class DERIVED | ✅ 6800 cases, 0 unexplained |
| axiom allowlist over the model library | ✅ clean, and the red-first drive still fires |
| native-tier isolation | ✅ no module under `X86/` imports `X86Native` |
| encoding cross-check (every byte and length against clang) | ✅ 100 forms |
| harness selftest (three planted bugs) | ✅ all three caught, control silent |
| kernel-cost ceilings, measured from **stderr** | ✅ 586.9 ms total, under every ceiling |
| roster derivation selftest + `--check` | ✅ 13/13, roster equals what K's tree derives |
| coverage table regenerated, `git diff --exit-code` | ✅ |

**100 vectors · 68 pre-states each · 6800 cases.** Sixty of those vectors are
batch 1's; three P0 rows (`and_q`, `or_q`, `xor_q`) were retired into it, so the
table grew by 57.

## What the batch actually reaches that P0 did not

P0 covered `and`/`or`/`xor` at ONE shape and ONE width: `r,r` at 64 bits. The
21 forms are shapes and widths, and four of them are behaviours no P0 vector
touched at all:

| new ground | vectors | why it is not a formality |
|---|---|---|
| the 32-bit forms | 3 | a 32-bit write ZERO-EXTENDS (SDM Vol. 1 §3.4.1.1). P0 proved this for `mov` only; a model that merged instead would pass every `q` and every `b`/`w` vector. |
| memory SOURCE, register destination | 12 | P0's only memory reads were `mov` and `pop`. |
| the high-8 registers AH/CH | 6 | P0 never read or wrote bits 15:8 of any register. |
| sign-extended immediates | 6 | `$-1` as an imm8 and `$-2147483648` as an imm32. `Operand.imm` is defined to arrive already extended (X86/Syntax.lean); nothing had exercised the convention. |

Each has an anchor in `Tests/Anchors.lean` proved by `decide`, so it fails at
BUILD time rather than waiting for the oracle.

## Why the explained count nearly quadrupled, and why that is the point

694 → 2632. Batch 1 adds sixty vectors that ALL draw an AF bit, and x86isa's
`create-undef` attachment is `nfix` — deliberately not a constant
(`scripts/x86isa_driver.lisp`). So the two models disagree on AF wherever the
draw differs, and the harness has to classify 2632 of them as lying inside the
set this model marks undefined **for that exact (instruction, state)** — a set
DERIVED by running the same step under two opposite oracles, never declared
(docs/DECISIONS.md D6).

⭐ **That is also this run's positive control.** An oracle that were echoing the
Lean side, or a stale record file, would produce ZERO disagreements of any
class, and the gate would print the same reassuring `unexplained=0`. It produced
2632, in exactly the flag the SDM leaves undefined and in no other field.

## The fast green, checked rather than believed

The full gate — build, six local arms, and the ACL2 differential over 6800
cases — runs in **14.0 s warm**, and the oracle's own phase is **5.0 s**. The P0
bank recorded the differential as "~2 min end to end", so a run 2.3× larger
finishing in a twelfth of the time is exactly the shape of a check that has
stopped seeing its subject, and it was treated as one.

Three things were confirmed before the green was accepted:

1. `run/acl2.out` is 4.3 MB written at the time of the run, carrying the SBCL
   and ACL2 8.7+ banners and the x86isa book load — the oracle started.
2. The 6800 oracle records contain **5039 distinct post-states** — it computed.
3. **A one-bit change planted in a batch-1 record was contradicted by the
   oracle**, in the right vector and the right field:
   `[spec] and_rm_l/3 (and) rax: lean=…40 oracle=…00`. The oracle is answering
   about THIS batch's new forms, not replaying ours.

The 2-minute figure was the cold path: certifying `projects/x86isa/top.cert` is
the long pole (docs/ORACLE-SETUP.md) and it is paid once per machine, not once
per batch. **The per-batch machine cost of this wave is seconds, and the price
is therefore almost entirely the executor's, not the oracle's.**

## What is NOT claimed

* The memory-DESTINATION logic forms (`and %rcx, (%rbx)`) are **batch 4** of the
  roster, not this batch. The characterization theorems here take a REGISTER
  destination and a generic source; a memory destination is a different equation
  with a different frame, and merging them is how a frame condition goes missing.
* `test` is a separate family (`0xuxx0-|-|flags/ctl`, batch 3) because it writes
  no register. P0 already covers it at `r,r`.
* Hardware co-simulation (plan v1 §4.4) is not in this gate. It needs a real
  x86-64 processor; this machine is arm64 and the CI runner has no ACL2 image.
  The helm's 10:4x dispatch named three gate arms and this was not among them —
  recorded here so its absence is a decision and not an oversight.
