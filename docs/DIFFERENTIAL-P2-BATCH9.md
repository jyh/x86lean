# P2 BATCH 9 — the unpack group: an operation that computes nothing and only chooses

**Forms.** `punpckl{bw,wd,dq,qdq}` and `punpckh{bw,wd,dq,qdq}` — eight mnemonics, ~4% of the measured
gap. The first vector operations here that are a **permutation** rather than lane-wise arithmetic.

```
cases=72068  matched=52023  explained=28774  unexplained=0  oracle-divergence=159  oracle-leaks=0  missing=0
838 vectors · 86 pre-states · P1 roster unchanged at 500/525
```

8 new vectors × 86 pre-states = 688 new cases; `matched` rose by exactly 688.

## 1. The rule, generalised once

For lane width `w`: `128 / (2w)` pairs, pair `i` being `dst[base+i] : src[base+i]` with the
**destination in the low half** of each pair. `base = 0` for `punpckl`, `base = pairs` for `punpckh`.
As with `vlanes`, the **count is derived from the width** and never written beside it.

⭐ **Checked by evaluation before the oracle was asked** — five hand-computed cases on a byte-ramp
pre-state, all `true`, in seconds rather than the thirty minutes a differential run costs. The
expected values came from **two** sources, not from one reading of the manual: objdump prints the
interleave in its own disassembly comment (`xmm0 = xmm0[0],xmm1[0],xmm0[1],xmm1[1],…`) and K's
`punpcklbw_xmm_xmm.k` gives the same order.

## 2. ⚠️ An arm that measures the PRE-STATES, not the model

`punpckl` and `punpckh` read **disjoint halves** of their inputs. A pre-state whose two halves
happened to agree could not tell them apart — so a green run would say nothing about *which half* is
read. That is a property of the XMM pattern rather than of the rule, and it was written into the AST
comment as a worry and then **measured**:

| arm | caught in |
|---|---|
| `punpckl` and `punpckh` read each other's half | **656** = 8 × 82 — every case |
| an unpack interleaves source-first instead of destination-first | **656** — every case |

Both fire in *all* their cases, so batch 0's deliberately non-constant pattern distinguishes the
halves everywhere.

⇒ **The worry is now a measurement.** Writing it down as a caveat would have been the cheap move;
running the arm made it a fact — and had the number come back small, *that* would have been the
finding. See D96.
