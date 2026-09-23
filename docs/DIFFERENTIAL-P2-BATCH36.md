# P2 BATCH 50 — sub-group B7: the packed narrowing (cvtpd2ps)

QUEUE P3, B7. Decision notes: D294 (the hardware reading), D295 (the shape and this batch).

## 1. THE RUN

```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=101376  matched=80679  explained=29479  unexplained=0  oracle-divergence=292  oracle-leaks=0  missing=0
1152 vectors · 88 pre-states · 101376 cases · 0 unexplained · 0 oracle leaks
```
Against batch 49's run (record 35), **every field is as committed before the run** (D295 §3, `e4ea545`): **+3 vectors ⇒
+264 cases, +264 matched**, explained +0, divergence +0. Each vector emitted 88 cases on BOTH sides, 0 refused on either
(the field is present on every record).
```
  cvtpd2ps_x2_x1     88 matched
  cvtpd2ps_x9_x10    88 matched
  cvtpd2ps_mN10_x1   88 matched
```

## 2. WHAT THE VECTORS REACH, AND WHAT THEY DO NOT
Every source avoids a zero binary64 lane in all 88 states (x86isa aborts the run on a zero narrowing, D258/D272), and no
pre-state presets OE (D294's x86isa defect). Not reached: a zero lane, an SNaN lane, a preset OE. The hardware rows ask
all three (D294).
⛔ **SQRTPS IS NOT CLAIMED (D295 §2):** every source meets a negative lane above lane 0, where the divergence is
inexpressible. It is the whole of sub-group B's residue: 2 instructions, named.

## 3. THE ARMS — predicted before the run, read after
```
  cvtpd2ps ignores MXCSR.RC                        xmm1     54 = 54    (total 97 = 97)
  cvtpd2ps keeps bits 127:64 of the destination    xmm1    156 = 156   (total 240 = 240)
  cvtpd2ps narrows lane 0 only                     xmm1    125 = 125   (total 166 = 166)
```
