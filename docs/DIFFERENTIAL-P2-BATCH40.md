# P2 BATCH 54 — the bit string: D23's four declined rows, modelled

Record 40. Decision note: D331 (predictions committed as tag `d331-predictions` before the first run). First run as
record 39 on `cb08c68`; re-based onto W1b (record 39, D330) and re-run, with the re-base predictions written into D331 before
the re-run. The silicon reading is W2b's decision note (branch `paris/w2b-bitstring-silicon`), landing after this batch.

## 1. THE RUN

```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=105424  matched=82367  explained=34155  unexplained=0  oracle-divergence=616  oracle-leaks=0  missing=0
1198 vectors · 88 pre-states · 105424 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 34155 · oracle-divergence: 616
```
Against W1b's run (record 39: 102960 cases, matched 82131, explained 29699, divergence 292): +28 vectors ⇒ **+2464
cases**, **+236 matched**, **+4456 explained**, **+324 oracle-divergence**. Every total is the one D331 and its re-base note
predicted. (Before the re-base, on `cb08c68`, the same 28 vectors gave the same deltas against record 37: 104368 cases.)

⭐ **HELD CASE BY CASE, NOT ONLY IN TOTAL.** Each of the 28 vectors' records was filtered out of `run/lean.txt` and
`run/oracle.txt` and compared against a simulation of two rules over the same 88 pre-states (the simulation that produced
D331's numbers): the Lean record equals the SDM rule (byte `EA + (offset SAR 3)`, bit `offset AND 7`) in all 2464 cases,
and the oracle record equals x86isa's rule (the same byte, bit `|offset| mod 8`) in all 2464. Per vector, matched /
explained / divergence are exactly D331 §3, and every declared (vector, field, state) diverged — which `compare` now checks
(below). Each id has 88 records on both sides.

| vectors | matched | explained | divergence | in-window cases |
|---|---|---|---|---|
| `bt_mr_{w,l}`, `bts_mr_{w,l}` | 0 | 176 | 0 | 59 / 50 |
| `bt_mr_q`, `bts_mr_q` | 31 (both refuse) | 114 | 0 | 36 |
| `btr_mr_{w,l,q}`, `btc_mr_{w,l,q}` | 0 / 0 / 31 | 176 / 176 / 114 | 18 / 12 / 6 | 59 / 50 / 36 |
| `bt_mr_neg_{w,l,q}` | 0 / 0 / 28 | 176 / 176 / 120 | 6 | 56 / 47 / 35 |
| `bts_mr_neg_{w,l,q}`, `lock_btsl_neg` (`.l`) | 0 / 0 / 28 | 176 / 176 / 120 | 12 | 56 / 47 / 35 |
| `btr_mr_neg_{w,l,q}`, `btc_mr_neg_{w,l,q}` | 0 / 0 / 28 | 176 / 176 / 120 | 35 / 32 / 26 | 56 / 47 / 35 |
| `btsw_far_neg`, `btcl_far_pos`, `btrq_far_pos` | 0 | 176 | 0 | 88 |

No case is matched outright except where both models refuse: every executed case differs in PF and SF, which the bit-test
group leaves undefined (x86isa's undefined values differ from this model's drawn bits in 88 of 88 cases on the existing
`bt*_mi_*` vectors too). Among in-window cases CF is 0 in 12–38 and 1 in 14–50 per vector, so both bit values are selected.

## 2. THE FIRST RUN WAS RED, AND THE DEFECT WAS IN THE HARNESS

```
run 1 (on cb08c68):  cases=104368 matched=81399 explained=33979 unexplained=284 oracle-divergence=616   (spec 284)
```
Every count but `unexplained` was the predicted one. The 284 were all CF: the oracle read 1 where the Lean pre-state reads 0,
on `bts`/`btr`/`btc` vectors only, and **in every one of the 284 the byte lay OUTSIDE both watched windows**. `bt_mr_*`,
which run first and write nothing, had none.

⛔ **THE ORACLE'S MEMORY PERSISTS BETWEEN CASES.** `x86l-run-all` threads one x86 state through all 104368 cases and
`init-x86-state-64` writes only the bytes a case lists — the instruction and the two windows. Until this batch no case read
outside the windows, so nothing could see it. A bit-string write 4 KB from the base is kept, and a later case that reads
that byte sees it. The Lean pre-state says an unwritten byte is 0.

✅ **The repair is to the EMITTER, so the two pre-states are equal again:** `memToLisp` now lists the byte a bit-string form
addresses (from `bitStringByte`, the same function `step` uses) with the Lean pre-state's value, unless it is non-canonical
(both models refuse) or already in a window. 36 cases of `run/cases.lsp` carry `0x2fff`, the byte at offset 0x7fff. Run 2,
above, is clean with no other change. ⚠️ This was found by the run and not predicted: D331's predictions assumed the oracle
reads 0 outside the windows, and run 1 refuted that assumption, not the model.

## 3. THE ORACLE DIVERGENCE, DECLARED PER PRE-STATE

ACL2 x86isa (`machine/instructions/bit.lisp`, all four `def-inst`s) computes `bitNumber = (mod (abs bitOffset) 8)`. For a
negative offset with |offset| ≢ 0, 4 (mod 8) that is the wrong bit of the right byte: offset −1 is bit 7 of byte EA−1 by
SDM Vol. 2A §3.1.1.9 and bit 1 by x86isa. The independent witnesses, counted by mechanism:
- **the SDM** (§3.1.1.9, Table 3-2): bit `offset MOD 8`, non-negative, of the byte at `BitBase + offset DIV 8`;
- **K** (`memoryInstructions/bt*_m*_r*.k`): the bit number is the offset's low three bits. ⚠️ K's ADDRESS term for a negative
  offset is a LOGICAL shift (`concatenateMInt(mi(3, 0), extractMInt(…, 0, 61))`), so K is cited for the bit number only;
- **a Rosetta 2 translation** on an Apple M4 Pro (an x86-64 implementation, NOT silicon): at 20 offsets from −256 to 255,
  at all three widths, CF matches the SDM rule, and BTS changes exactly the SDM's byte and bit. At −1, −3, −5, −7 and −129
  its CF differs from x86isa's rule.

The divergence depends on the operand VALUE, so a whole-vector declaration would also excuse the plant (§4). ⇒
`KnownDivergence` gains `states`: an entry with states excuses its field ONLY at those pre-state indices, and `compare`
fails if ANY listed state does not diverge (the old stale check asked only whether the entry fired at all). 29 entries, 324
(vector, field, state) triples, every one D331's prediction.

## 4. THE PLANT — D23's approximation, caught

`wrongBitStringModulo` is `step` with the modulo rule on this shape: the operand-size word AT the effective address, the
offset unsigned and modulo the width. Its records for the 28 vectors, compared against the oracle output of the
pre-rebase clean run (the 28 vectors' oracle records are identical across the re-base) with the shipped divergence list:
```
cases=2464 matched=0 explained=4456 unexplained=2402 oracle-divergence=282   (spec 2166 · refusal 236)
```
**Every one of the 28 vectors is red** — the fewest at `bt_mr_w` (8 CF disagreements: its in-word offsets are where the two
rules agree), the most at the `.q` and far vectors, where the plant also executes what both real models refuse. 282 plant
disagreements fall on declared states and are absorbed; that is the cost of declaring the oracle's defect, and the reason
the declaration is per state rather than per vector. The same plant is a selftest arm (`selftest bit-string`), driven
against `step` rather than the oracle: caught, 763 disagreements in `cf`, 2475 unexplained in all (one of the 208 arms).

## 5. WHAT IT CHANGES
- `step`'s `.bit` case dispatches on its operand pair; `.mem` with `.reg` is the bit string, every other pair is unchanged.
  One byte is accessed; a non-canonical byte address halts (the branch checks' `#GP(0)` reason). No new constructor.
- The residue: **REMAINING 21 of 525** (from 25), **DECLINED 0** (from 4). Claimed rows 500 → 504, machine forms 351 → 355.
  `claimed_forms.DECLINE_REVERSED` holds the four rows to the claimed set.
- The coverage rows read `m,r` (`bt`) and `m(rmw),r` (`bts`/`btr`/`btc`); `bt` leaves the loose/strict mem-dest disagreement
  list, because the shape it lacked is now there.

## 6. KERNEL COST
The run's retired-ceiling readings printed `kernel-cost gate UNMEASURABLE` (one-minute load 4.66, outside the 0.0–4.1 band),
rc 3 — a reading, not this batch's verdict (D123 §7). The kernel-time gate is CI's `kernel-delta`.
