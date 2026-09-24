# P2 BATCH 48 — sub-group B6a: the rounding conversions to an integer (cvtsd2si/cvtss2si)

QUEUE P3, B6a. Decision notes: D287 (the hardware reading, taken before any Lean), D288 (the shape), D289 (this batch).

## 1. THE RUN

```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=100584  matched=79935  explained=29479  unexplained=0  oracle-divergence=244  oracle-leaks=0  missing=0
1143 vectors · 88 pre-states · 100584 cases · 0 unexplained · 0 oracle leaks
```
Against batch 47's run (record 33), **every field is as committed before the run** (D289 §4, `992fcb9`), and the
account CLOSES: **+12 vectors ⇒ +1,056 cases** (12 × 88), **+1,056 matched**, explained +0, `oracle-divergence` +0
(244 → 244).

⭐ **ATTRIBUTED PER VECTOR**, because an aggregate zero over 1,143 vectors is not evidence about 12 of them. Each B6a
vector emitted **88 cases on BOTH sides** (`id=<v>/` counted in `run/lean.txt` and `run/oracle.txt`), and **0 of the
1,056 were refused on either side**. The check is live: the field is present in all of those records, and the oracle
file carries 1,736 real refusals elsewhere.
```
  cvtsd2si_x0_eax      88 matched
  cvtsd2si_x11_r9d     88 matched
  cvtsd2si_mN10_ecx    88 matched
  cvtsd2si_x0_rax      88 matched
  cvtsd2si_x11_r9      88 matched
  cvtsd2si_mN10_rdx    88 matched
  cvtss2si_x0_eax      88 matched
  cvtss2si_x11_r9d     88 matched
  cvtss2si_mN10_ecx    88 matched
  cvtss2si_x0_rax      88 matched
  cvtss2si_x11_r9      88 matched
  cvtss2si_mN10_rdx    88 matched
```

## 2. WHAT THE VECTORS REACH, AND WHAT THEY DO NOT
Chosen by a reach census over the 88 pre-states (D289 §1, `run/b6a_census.txt`). Each vector's census line is a
comment above it in `Tests/Vectors.lean`.
⛔ **NOT REACHED BY ANY VECTOR: rounding to nearest where it differs from truncation.** No pre-state puts a fraction
≥ 1/2 under RC = nearest for binary64 (0 states for every source), and 2 at most for binary32 (D289 §2). The vectors
therefore cannot tell `cvtsd2si` from `cvttsd2si` at nearest. The hardware rows ask it (`*_tie/nearest`,
`*_tieodd/nearest`, `*_half/nearest`, `*_frac/nearest`, D287), and B6a's kernel pins are where it is carried.
Nor are the range edges reached (`*_top/*`, `*_bottom/*`: the range test comes after rounding), for the same reason.

## 3. THE ARMS — predicted before the run, read after
```
  cvts?2si truncates instead of reading MXCSR.RC        rax          56 = 56   (total unexplained 208 = 208)
  cvts?2si raises DE on a denormal source               mxcsr.de    114 = 114
  cvts?2si ignores REX.W and rounds to an int32         rax          43 = 43   (total 143: the 139 value cases predicted, + 4 in mxcsr.ie,
                                                                          reconciled AFTER the run: an int32 out of range)
```
A NEAREST-ONLY arm is not registered: over the selftest's 84 states it fails on the truncation arm's cases exactly,
in every destination, which is §2's gap seen from the arms' side.
