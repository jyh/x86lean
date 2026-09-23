# P2 BATCH 47 — sub-group B5: the packed arithmetic (mulps/mulpd, addps/addpd, subps/subpd, divps/divpd)

QUEUE P3, B5. Decision notes: D281 (the hardware reading, taken before any Lean), D282 (the shape), D283 (this batch).

## 1. THE RUN

```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=99528  matched=78879  explained=29479  unexplained=0  oracle-divergence=244  oracle-leaks=0  missing=0
1131 vectors · 88 pre-states · 99528 cases · 0 unexplained · 0 oracle leaks
```
Against batch 46's run (record 32), **every field is as posted on the bus before the run**, and the account CLOSES:
**+19 vectors ⇒ +1,672 cases** (19 × 88), **+1,672 matched**, explained +0, `oracle-divergence` +0 (244 → 244).

⭐ **ATTRIBUTED PER VECTOR**, because an aggregate zero over 1,131 vectors is not evidence about 19 of them. Each B5
vector emitted **88 cases on BOTH sides** (`id=<v>/` counted in `run/lean.txt` and `run/oracle.txt`; control
`divsd_x1_x0` 88/88), and **0 of the 1,672 were refused on either side**. That rules out the both-refused case, which
compares as agreement; the check is live, since the field is present in those records and the oracle file carries 1,736
real refusals elsewhere.
```
  mulps_x15_x0     88 matched
  mulps_x7_x0      88 matched
  mulps_m10        88 matched
  mulpd_x15_x0     88 matched
  mulpd_mN20       88 matched
  addps_x15_x0     88 matched
  addps_m0         88 matched
  addps_x7_x0      88 matched
  addpd_x15_x0     88 matched
  addpd_m0         88 matched
  subps_x15_x0     88 matched
  subps_m0         88 matched
  subps_x2_x0      88 matched
  subpd_x15_x0     88 matched
  subpd_m0         88 matched
  divps_mN10       88 matched
  divpd_x15_x0     88 matched
  divpd_x5_x0      88 matched
  divpd_mN10       88 matched
```

## 2. WHAT THE VECTORS REACH, AND WHAT THEY DO NOT
Chosen by a reach census over the 88 pre-states (D283 §1). Each vector's census line is a comment above it in
`Tests/Vectors.lean`.
⛔ **NOT REACHED BY ANY VECTOR:** the packed indefinite (every source is chosen indefinite-free; x86isa's indefinite
has no sign bit and `knownDivergences`' pair form excuses a low lane only), and so `divps`'s IE, UE and ZE. They
remain on D281's hardware rows; the packed indefinite is on no row at all. Nor is the m128 alignment fault (x86isa
does not check alignment, D91).

## 3. THE ARMS — predicted before the run, read after
```
  mulps..divpd raises lane 0's flags alone                          mxcsr.pe     377 = 377
  mulps..divpd suppresses DE in every lane when any lane holds a NaN mxcsr.de     354 = 354
  mulps..divpd computes lane 0 and keeps the lanes above it         xmm0       1,412 = 1,412
  mulps..divpd ignores MXCSR.RC and rounds to nearest               xmm0         521 (526 predicted: D283 §3)
  B0: flags replace the sticky bits                                 mxcsr.ze   2,269 (base derived 1,891; +378 predicted)
```
The two misses were the prediction's premise (the selftest's random states are not the differential's), reconciled
to the case in D283 §3.
