# TACAS regular track — what a 10–15 page submission needs, priced

**Routed by the helm at council close, 2026-09-11:** *"x86lean is a TACAS regular-track candidate —
price what a 10–15 submission needs, as a file"*, alongside *"two papers, semantics first, the Hoare
logic + saltbench-x86 following and citing it."* This file prices **paper 1, the semantics.**

⚠️ **THIS IS A PRICE, NOT A PLAN, AND EVERY NUMBER IN §1 IS TAKEN FROM THE TREE RATHER THAN
REMEMBERED.** Where I could not measure something I say so rather than estimating it — an unmarked
estimate in a pricing document is the defect this campaign has spent the most time correcting.

---

## 1. WHAT EXISTS TODAY, MEASURED AT `7bb57ee`

```
  Lean library modules ................ 12          Tests modules ............... 6
  total .lean lines ................... 18,824      theorems + lemmas ........... 616
  recorded decisions .................. 200         differential records ........ 44
  design documents .................... 55
```

**Coverage, and these six numbers are GATED** — `scripts/claimed_forms.py` derives them from two
independent sources (every vector's own AT&T text, and every roster row's own encoding assembled by
clang) and **CI fails if the prose disagrees with the derivation**:
```
  158 mnemonics in 1,012 differentially tested forms
  500 of 525 roster rows      351 of 374 distinct machine forms
  375 of the 500 spelled by a vector; 125 the same encoding under another spelling
```
**Oracles on record:** `x86isa`/ACL2 (73 mentions across the differential records), XED (24). Sail and
K are cited in `PROVENANCE.md` as sources, and I have **not** verified today whether either was used
as a live oracle — that is a gap in my knowledge, not a claim either way.

**The P2 proof interface**, landed this shift (council ruling ⑧):
```
  naive (if-chain invariant, by_cases per label) ....  152 lines  ≈ 25   / label
  + stepP_at / stepP_off / atTable ..................   88        ≈ 12   / label
  + runP_code .......................................   67        ≈  9.6 / label
  + round 4 (regcalc, defeq) ........................   57        ≈  7.6 / label
  measured across FOUR routines, 2–7 labels:  19 + ~7.7 / label, constant 7.5–8.1
  ⇒ ~173 lines at twenty labels  ⛔ NOT "tens of lines"
```

---

## 2. WHAT A TACAS REGULAR-TRACK PAPER NEEDS THAT WE DO NOT HAVE

### 2.1 ⛔ A STATED, DEFENSIBLE CLAIM — and ours is currently a NEGATIVE RESULT
The P2 work answers the commission *"provable in tens of lines"* with **~173 lines at twenty labels**,
i.e. **the target is not met by a lemma library**, and the finding is that **the TIER decides it**
(frame ≈ 1 line/instruction vs labelled ≈ 7.7 lines/label — a factor of eight).
⇒ **That is a real result and it is not the result the commission asked for.** A regular-track paper
must decide which claim it is making. Three honest framings, and **I am not choosing between them —
that is the Captain's and the helm's:**
* **(a) a validated executable semantics** — the coverage table is the contribution, the proofs are
  evidence it is usable. Strongest on what is measured; least novel.
* **(b) a negative/roadmap result** — "a lemma library cannot reach tens of lines; here is the measured
  law and why a tactic or VC generator is required." Honest, and TACAS rarely rewards it alone.
* **(c) hold paper 1 until the Hoare logic exists** and make THAT the claim, with the semantics as
  infrastructure. Strongest paper, latest date.

### 2.2 THE GAPS, PRICED
| # | gap | why a reviewer asks | price |
|---|---|---|---|
| G1 | **No comparison against x86isa / Sail as a stated baseline.** We differentially test against them; we do not position against them. | "why another x86 semantics?" is the first referee question | **1–2 days.** A table: forms covered, trust base, executability, proof support. Data mostly exists in `COVERAGE.md` + `PROVENANCE.md`. |
| G2 | **Undefined-bit / flag semantics not written up.** The oracle exists in the model; the *argument* is scattered across decisions. | it is the hardest part of x86 and the most citable | **2–3 days**, mostly extraction from `docs/DECISIONS.md`. |
| G3 | **No performance/scale statement for the semantics itself.** We have kernel-cost data per module, gated — but framed as CI hygiene, not as a result. | "does it scale?" | **1 day** to reframe existing gated numbers. ⚠️ See §3: the gate's dispersion is not robust, so any published timing needs a robust estimator first. |
| G4 | **The five proof problems are a sample, not a benchmark.** Four routines, 2–7 labels. | "is 19 + 7.7/label general?" | **unpriced — needs the benchmark freeze** (helm item 4, P2 in the design lane, with bench). |
| G5 | **No artifact-evaluation packaging.** TACAS AE wants a container that builds and reproduces every claim. | AE badge is near-mandatory | **2–3 days.** ⭐ Unusually cheap here: every headline number is already CI-gated and derived, so "reproduce the claims" is largely "run the gates". |
| G6 | **Related work.** Not started. | required | **2 days.** |

**Sum of what is priceable: 8–13 working days**, excluding G4 which cannot be priced until the
benchmark exists.

---

## 3. ⛔ ONE THING THAT MUST BE FIXED BEFORE ANY TIMING CLAIM IS PUBLISHED
The delta gate's dispersion estimate is **not robust to outliers**, measured this shift across seven
runs (four null pairs on the runner, three real ones locally):
```
  the MEDIAN is stable ......... local family 1.06x across independent runs
  the BAND is not .............. 326 – 1739 on the runner (5.3x) at identical load
  per-pass, one run ............ Tests.Coverage  min 26,800 / median 27,150 / max 73,500
```
**Five of six passes are tight; one or two explode.** ⇒ **Any per-module timing figure published from
this gate would carry an error bar driven by outlier passes rather than by measurement uncertainty.**
📌 The remedy is a robust estimator; D150 already measured a candidate (median |consecutive
difference|) giving 0.29 where CV gave 0.73. **It is gate design and therefore the helm's, not mine
to take** — but it is on the critical path of G3, so it is priced here as a **blocker, not a task.**

---

## 4. RECOMMENDATION — MINE, NOT RULED
**(c) with a staged hedge.** Write paper 1 as the validated semantics **now** (G1, G2, G5, G6 ≈ 7–9
days) and let the measured tier law stand as a *section*, not as the paper's claim. It is publishable
on the coverage and the gating discipline alone, and it is the paper the second one must cite.
⛔ **The thing I would NOT do is submit the tier law as the headline before the benchmark exists** —
four routines is a sample, and a referee will say so correctly.
📌 **Precedence is now THIRD** (SaltBench · twin primes · x86lean · verso · jas), so 8–13 days of
paper work competes with the benchmark freeze that is P2 in the design lane and starts now. **Those
two are the same critical path, since G4 depends on the benchmark** — which is an argument for doing
the benchmark first and the paper around it, not beside it.
