# P2 BATCH 49 — sub-group B6b: the square roots (sqrtsd/sqrtss)

QUEUE P3, B6b. Decision notes: D287 (the hardware reading), D291 (the shape), D292 (this batch).

## 1. THE RUN

```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=101112  matched=80415  explained=29479  unexplained=0  oracle-divergence=292  oracle-leaks=0  missing=0
1149 vectors · 88 pre-states · 101112 cases · 0 unexplained · 0 oracle leaks
```
Against batch 48's run (record 34), **every field is as committed before the run** (D292 §3, `4ed7cec`), and the
account CLOSES: **+6 vectors ⇒ +528 cases**, **+480 matched**, explained +0, **`oracle-divergence` +48 (244 → 292)**.
The 48 are sqrt of a negative source, where x86isa's indefinite is sign-less. They are declared per vector in D266's
`pair` form: low lane only, with every bit above it required to agree.
Each vector emitted **88 cases on BOTH sides**, and **0 were refused on either side** (the field is present on every record).
```
  sqrtsd_x0_x1       88 cases  76 matched · 12 declared divergence (the signed indefinite)
  sqrtsd_mN20_x9     88 cases  88 matched
  sqrtsd_x15_x2      88 cases  75 matched · 13 declared divergence (the signed indefinite)
  sqrtss_x0_x1       88 cases  77 matched · 11 declared divergence (the signed indefinite)
  sqrtss_mN20_x9     88 cases  88 matched
  sqrtss_x15_x2      88 cases  76 matched · 12 declared divergence (the signed indefinite)
```
⚠️ The per-vector split of the 48 is the census's NEG column (`run/b6b_census.txt`). The run verifies the TOTAL, 48,
which equals that column's sum. The split is attributed from the census, not measured from the run.

## 2. WHAT THE VECTORS REACH, AND WHAT THEY DO NOT
Every source that reaches DE or IE also reaches a negative source. The two memory vectors reach PE alone (RC-sensitive
in all 88 states). Not reached by any vector: a positive-infinity source, an SNaN source, and the least denormal.
The hardware rows ask them (D287), and B6b's kernel pins are where they belong.

## 3. THE ARMS — predicted before the run, read after
```
  sqrts? ignores MXCSR.RC and rounds to nearest     xmm1         32 = 32    (total 129 = 129)
  sqrts? raises no DE on a denormal source          mxcsr.de     57 = 57
  sqrts? zeroes the bits above the lane             xmm1        162 = 162   (total 498 = 498)
```
