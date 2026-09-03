# P1 BATCH 18 — the compare-exchange pair and the double shifts, and the manual that was wrong twice

**Forms.** Roster families 10, 14, 24 and 40 by BASE NAME: `cmpxchg` and `xadd` at `r,r`
and `m,r`; `shld` and `shrd` at `r,r,cl|imm8` and `m,r,cl|imm8`. **12 roster rows, 4
roster mnemonics, 41 differential vectors**, taking the model to **453 of the 525 rows
(86%)**.

```
cases=57400  matched=38603  explained=27195  unexplained=0  oracle-leaks=0  missing=0
  spec: 0   refusal: 0   harness: 0   undefined-region: 27195
700 vectors · 82 pre-states · 83 mnemonics
```

Gate met on the **THIRD** run, in 2 m 12 s. The first two runs are the batch: 80
disagreements, then 51, and both were the model obeying the SDM's pseudo-code.

## The scope, re-derived rather than inherited (D49)

```
awk -F'\t' 'NR>2 && $4 ~ /^(xadd|cmpxchg|shld|shrd)$/' p1/roster.tsv | wc -l   →  12
```

Four base names over FOUR families — 10 and 14 for the compare-exchange pair, 24 and 40
for the double shifts. Family 24's other four rows are `div`/`idiv`, discharged by batch
17, so the base-name rule cannot double-count. The handover's count and this one agree at
12; the agreement is the result of the check, not a reason to have skipped it.

⚠️ **Twelve rows, four mnemonics, forty-one vectors.** The last number is large because
`shld`/`shrd`'s IMMEDIATE is not a sample but a BRANCH SELECTOR: `$0`, `$1`, `$5`, `$16`
and `$20` pick out the no-operation, the OF-defined, the ordinary, the exact-boundary and
the bad-parameters cases, and none can be reached from another.

## The probe, run before any vector existed — 2 runs, 3444 cases, 9.5 s

**Probe 1 — support and branch density.** All 40 candidate forms are executed by x86isa at
every width and shape: **zero refusals in 3280 cases**. And `cmpxchg`'s branch is genuinely
split over the harness's own 82 pre-states — **22 to 27 take the equal branch, 55 to 60 the
unequal**, depending on width. No new pre-state was needed.

**Probe 2 — the oracle's undefined set, MEASURED BY DIFFERENTIAL ATTACHMENT.** The same
3444 cases run twice, under `create-undef` attached to `(nfix x)` and then to
`(+ 1 (nfix x))`; a field that differs between the two runs is one x86isa fills from its
undefined generator.

| form | cases with an undefined field | which |
|---|---|---|
| `cmpxchg` (8 shapes) | **0** | — |
| `xadd` (8 shapes) | **0** | — |
| `shld`/`shrd` `r,cl` at `.l`/`.q` | 59 | `af` 59, `of` 54 |
| `shld`/`shrd` `r,cl` at `.w` | 59 | `af` 59, `of` 54, **and `cf` `pf` `sf` `zf` and the DESTINATION in 35** |
| `shld`/`shrd` `*,imm8 $5` | 82 | `af` 82, `of` 82 |
| control `andq %rcx,%rax` | 82 | `af` 82 |
| control `movq %rcx,%rax` | **0** | — |

⛔⛔ **THE FIRST VERSION OF THIS PROBE WAS BLIND AND ONLY THE POSITIVE CONTROL SAID SO.**
The second attachment was `(+ 1000 (nfix x))`, and 1000 is EVEN — so every one-bit
undefined field kept its parity and came back identical. The whole table read zero, which
looked like a clean answer. `andq`, whose AF is undefined and which this repository's own
driver comment records as the instruction that first forced the attachment to exist, also
read zero — and that is the only reason the probe was not believed.

⇒ 🔑 **A DIFFERENTIAL PROBE'S PERTURBATION MUST BE ABLE TO REACH THE WIDTH OF THE FIELD IT
IS PROBING.** An even offset cannot move a bit. The probe with an odd offset is the same
probe, 4.7 s, and it answers.

⭐ **And the control is no longer a head's to remember.** `scripts/oracle_undef_probe.py`
is this probe as a committed tool: it takes `id<TAB>asm` lines, patches the harness's own
emitted `mov_d` cases so the pre-states are the differential run's, runs ACL2 twice with an
ODD offset, **appends both controls the caller cannot remove**, and **exits 2 printing
nothing else if either control fails**. Nine seconds for forty forms; verified in both
directions by setting the offset back to 1000 and watching it refuse and name the cause.
See D55.

## The measurement that designed the batch

The probe's numbers are derived TWICE from independent sources and agree exactly: from the
oracle's undefined fields, and from the pre-states' own CL values computed in Python. Over
the 82 pre-states, `CL mod 32` is **0 in 23**, **1 in 5**, **2…16 in 19**, and **17…31 in
35**.

- 23 → the no-operation branch,
- 5 → the one count at which OF is defined,
- 35 → **the bad-parameters branch, at `.w` only** — the SDM's "if the count is greater
  than the operand size, the result is undefined".

**Forty-three per cent of the pre-states put a 16-bit double shift into the branch where
the DESTINATION is undefined.** That is this model's SECOND undefined destination, and the
first that is undefined because of an operand OTHER than the one it overwrites (`bsf`/`bsr`
are undefined at a zero SOURCE).

## ⛔⛔ The SDM was wrong twice, in opposite directions, about the same thing

**D53 — `DEST := TEMP` does not happen.** CMPXCHG's pseudo-code writes the destination back
on the unequal branch. That line looks like a no-op and is not one at `.d`, where a 32-bit
register write ZERO-EXTENDS. **80 unexplained disagreements**, every one `cmpxchg_r_l`,
every one RCX's upper half. ACL2 x86isa's else branch writes only the accumulator; K's
`CMPXCHGL-R32-R32` — learned by EXECUTION, not read off the manual — gives the destination
`getParentValue(R2, RSMap)`, the full 64-bit value unchanged, while zero-extending the
accumulator. Two independent public models against the manual.

**D54 — "no operation" is not one either.** SHLD/SHRD's `IF COUNT = 0 THEN no operation`.
**51 more disagreements**, again all at `.d`, again the destination's upper half. K's rule
for this exact case is `setParentValue(concatenateMInt(mi(32,0), MIdest), R) // Intel Bug`.
⛔ **And `.shift` in this very file already knew** — its count-zero branch has written the
unchanged value back since P0, with a comment saying the instruction is a read-modify-write.
This batch departed from the code beside it on the strength of SDM prose.

⇒ 🔑 **A SPECIFICATION'S NO-OP IS ONLY A NO-OP AT THE WIDTHS WHERE THE WRITE IS INVISIBLE.**
Three of four widths agreed both times. One 32-bit register vector out of seven `cmpxchg`
vectors is the entire evidence for D53.

⇒ ⭐ **Both rejected models are now ARMS** (`wrongCmpxchgSdmWriteBack`,
`wrongDshiftZeroCountWritesNothing`), so re-"correcting" either rule back to the manual is
a red selftest in seventy-five seconds rather than a red differential two hundred vectors
later.

## The one thing this model refuses — D52

A 16-bit MEMORY destination with a masked count above 16 would put an oracle-drawn value
into MEMORY. `X86.undefinedLeaked` demands that the two opposite oracle runs agree on every
watched byte, and the comparator's `undefinableFields` is a CLOSED list of flag and register
names whose own comment named this as the day it would have to be widened. Rather than widen
the model's strongest gate as a side effect of one batch, `step` REFUSES exactly that
combination — a theorem, `step_dshift_mem_undefined_refuses`, not a comment — and the
coverage row says so. Every other double shift is answered, including `.w` in memory with a
count that is defined. The repair, when a batch is willing to pay for it, is named in D52.

## The arms

Eight, of which two are the rejected SDM models above and two exist to price the
observation rather than to be plausible.

| arm | field |
|---|---|
| `cmpxchg` always stores — **the arm that proves the unequal branch is reached** | `rax` |
| `cmpxchg` never stores — **the arm that proves the equal branch is reached** | `rcx` |
| `cmpxchg` writes `DEST := TEMP`, as the SDM says (D53) | `rcx` |
| `xadd` forgets to write its source | `rcx` |
| `shld`/`shrd` perform the SDM's "no operation" at a count of zero (D54) | `rax` |
| `shld`/`shrd` call a count EQUAL to the operand size bad parameters | `rax` |
| `shrd` fills from the source's top bits, as `shld` does | `rax` |
| `shld`/`shrd` take CF from the result instead of the original destination | `cf` |

⭐ **The boundary arm is wrong at exactly one count.** A count equal to the width is legal
and its answer is the SOURCE; `adversarial` contains `0x10`, so the five pre-states whose CL
masks to 16 are the whole of its evidence.

## ⚠️ The kernel-cost ceiling will be met in about two batches — the first comparable pair

`Tests.Coverage`: **35 400 ms = 426.5 ms/row against the 470 ceiling, 1.10× headroom, no
raise**, at one-minute load 3.09. Batch 17 read 394.9 at load 2.20/4.08.

⭐ **This is the first pair of readings that may honestly be compared**, because D51's repair
landed in batch 17 and both figures now carry their conditions. In the ROW unit the growth is
**+8.0%**; in the flat unit — nanoseconds per (assertion × vector), which is what the cost is
actually linear in — it is **+2.2%** (706.6 → 722.4 ns). The row unit inflates because the
denominator grows slower than the product: this batch added 4 rows and 41 vectors.

⇒ **At this batch's own ratio the ceiling is exceeded at batch 20.** 426.5 × 1.08 = 460.6
(batch 19, inside), × 1.08 = 497 (batch 20, over). A batch adding more mnemonics and fewer
vectors moves that out; one adding many vectors per mnemonic moves it in. Handed on as a
number rather than as "watch it", because D51's whole finding was that a trend nobody can
compare gets handed on as a warning instead of a decision.

## What is NOT claimed

- `shld`/`shrd` at `.w` with a MEMORY destination and a CL count: refused, see D52 above.
- No `LOCK` prefix, no atomicity, no page protection — so CMPXCHG's memory write-back on the
  unequal branch, which is what the SDM's `DEST := TEMP` is really about, has no observable
  content in this model and is not modelled.
- `cmpxchg8b`/`cmpxchg16b` are separate roster rows and are not this batch.
