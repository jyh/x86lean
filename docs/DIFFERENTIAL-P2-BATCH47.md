# D404 d1 — nineteen packed MMX binary operations, by a width rule checked per member

Record 47. Decision note: D404 (predictions committed as `3d884f3` before any model work).

D404 §1 checked the price brief's *"a width parameter"* claim per member against `vbinApply`: for the lane-wise kinds
and the low unpacks, MMX(a, b) = low64(XMM(zext a, zext b)); for `punpckh*` and `pack*` it is NOT, so those are refused
here and left to d2. Every write goes through `setMm`, so the x87 side effect (tag 0, TOP 0) cannot be forgotten.

## 1. THE RUN

The main differential table:
```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=113520 matched=89652 explained=34407 unexplained=0 oracle-divergence=1399 oracle-leaks=0 missing=0
1290 vectors · 88 pre-states · 113520 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 34407 · oracle-divergence: 1399
```
Measured as records 42–46 were (the 1290 ids of `def vectors`, kept from both record files, then `x86lean-diff compare`; rc 1
only for the six VEX.256 declarations the filter removes). Against record 46 (1252 vectors, 110,176 cases, matched 86,308):
**+3,344 cases (38 vectors × 88), +3,344 matched, nothing else moved.**

The whole run: `136488` cases, `112356` matched, `34407` explained, `0` unexplained, `1927` divergence, 0 leaks, 0 missing.
That equals, count for count, a line sealed before the run (D404 §4).

## 2. THE ARMS
A low unpack reading the high halves (192 in mm0), pandn complementing the source (84), an op ignoring its destination
(1,114), and the load x87-touch arm widened to the packed forms (3,780 in fptag). All are caught.

## 3. WHAT IT CHANGES
- Vectors 1252 → **1290** (main table), 1513 → 1551 (whole run). CLAIMED unchanged at 504; rows unchanged at 200 (the MMX
  shapes `mm,mm · mm,m` join 19 existing rows).
- **The census**: covered +14,678, the figure derived beforehand. The MMX miss falls 28,551 → 13,873. `docs/P2-ROSTER.md`'s
  gap falls 330,948 → **316,270**.
- **Not in d1, stated**: `punpckh*` and `pack*` (D404 §1: the XMM definition reads or writes the wrong half), and the seven
  silicon-table mnemonics (the census classes per mnemonic). MMX memory forms are vectored at an aligned address only.
  MMX has no alignment rule, so there is no fault branch to miss, but an unaligned vector is not in the table.
