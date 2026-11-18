# D404 d2 — the MMX high unpacks and the pack, each with its own 64-bit placement

Record 48. Decision note: D404 §5 (definitions and predictions committed as `b5b422d` before any model work) and §6.

D404 §1 found that the reuse rule (the XMM function on zero-extended operands, low 64 bits kept) reads the wrong half
for `punpckh*` and drops the source from `pack*`. d2 gives the four differential forms their own placement in
`mmxApply`, and keeps the arithmetic `vbinApply`'s: punpckh* is the low unpack of the upper 32 bits, and packuswb keeps
r[31:0] and moves r[95:64] up to 63:32.

## 1. THE RUN

The main differential table:
```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=114224 matched=90356 explained=34407 unexplained=0 oracle-divergence=1399 oracle-leaks=0 missing=0
1298 vectors · 88 pre-states · 114224 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 34407 · oracle-divergence: 1399
```
Measured as records 42–47 were (rc 1 only for the six VEX.256 declarations the filter removes). Against record 47 (1290
vectors, 113,520 cases, matched 89,652): **+704 cases, +704 matched, nothing else moved.** The whole run (`137192` cases,
`113060` matched, `0` unexplained, `1927` divergence) equals a line sealed before it.

## 2. THE ARM, PER VECTOR
The reuse model (D404 §2 prediction 2) differs at 88 of 88 pre-states on all six high-unpack vectors, and at 79 and 53 on
the two packuswb vectors. No vector is blind. Measured by a scratch audit that copies the arm (Main cannot be imported).

## 3. WHAT IT CHANGES
- Vectors 1290 → **1298** (main), 1551 → 1559 (whole run). CLAIMED 504 and rows 200 unchanged.
- **The census**: covered +2,765, the figure derived beforehand; the MMX residue falls 13,873 → 11,108; P2-ROSTER's gap
  falls 316,270 → **313,505**.
- **What the MMX wave has not reached:** the seven silicon-table mnemonics (pmullw pmulhw paddsw psubsw psubusb psubusw
  pmaddwd), which need a per-extension census class first; the SSE-era mm forms x86isa does not implement (pmaxsw, psadbw,
  pshufw, pavgb and the rest), a silicon wave; and the MMX shifts and EMMS.
