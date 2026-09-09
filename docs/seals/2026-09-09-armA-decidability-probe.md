# PRE-REGISTERED — DOES A Δku GATE DECIDE WHERE THE ms GATE RETURNED UNMEASURABLE?
# paris, 39th head, 2026-09-09. Written and committed BEFORE the measurement.

## WHY — THIS IS THE CAMPAIGN'S CRITICAL PATH, NOT AN INSTRUMENT SIDE-QUEST
`docs/QUEUE.md` item 4: **the delta gate is the MERGE gate**, `drift-gap-ratchet.txt` gates
`lean_missing_max 0` in both directions, so **a batch whose delta comes back UNMEASURABLE
(rc 3) CANNOT LAND.** Two branches are held by it and P3 sub-group A would meet the same wall.
The queue's own instruction: **"FIX THE INSTRUMENT before growing the queue of `.lean` work
that cannot land."**
ARM A (D187/D188, design of record) says gate `Δku` in unfoldings rather than `ms per 1k
unfoldings`. **If `Δku` has zero variance, `se = 0`, the band `K*se` vanishes, and the gate
cannot return UNMEASURABLE.** That is the claim this probe tests on a REAL held branch.

## THE SUBJECT, AND IT COMES WITH ITS OWN ZERO CONTROL
`es3-anchor-theorems`, whose ms-gate history is recorded at QUEUE 0c:
```
  run  base       repeats  delta        band      budget   rc  verdict
   2   cad06778      3     +200 ms    ±2470.1    1843.2    3   UNMEASURABLE
   3   cad06778      6     +800 ms    ±1916.7    1836.0    3   UNMEASURABLE
```
**Measured at the object, not taken from the queue:**
```
  7103ff8..cad06778   0 .lean files touched   ⇐ THE ZERO CONTROL
  cad06778..d9d7923   2 .lean files touched   (Tests/Coverage.lean, X86/Syntax.lean)
```
⭐ **The control is not synthetic and I did not construct it** — it is the very range whose
verdict flipped `ok` → `UNMEASURABLE` on pure noise between runs 1 and 2.

## PREDICTIONS, SEALED
```
Z1  Δku(7103ff8 -> cad06778) == 0 EXACTLY.  No .lean changed, and the counter is
    deterministic. confidence: HIGH. ⛔ If this is non-zero the whole of ARM A is in
    doubt and the probe has found something far more important than its subject.
Z2  Δku(cad06778 -> d9d7923) is a DEFINITE NON-ZERO integer.
    confidence: HIGH — two .lean files changed, including the gated module.
Z3  therefore a Δku gate DECIDES this branch, where the ms gate returned rc 3 TWICE at
    two different repeat counts. confidence: MODERATE-HIGH — Z3 follows from Z1+Z2 only
    if a budget exists to compare against, and NO UNFOLDING BUDGET HAS BEEN DERIVED YET.
    ⚠️ So Z3 is about DECIDABILITY (se = 0 ⇒ no band ⇒ a verdict either way), NOT about
    which verdict. I will not report a direction.
```

## ⛔ WHAT THIS PROBE CANNOT DO, STATED BEFORE IT RUNS
* It does **not** derive an unfolding budget, and therefore **does not land the branch.**
* It does **not** answer blocker (b) — whether the counter tracks kernel time.
* A definite Δku is **not** a correct Δku. Decidability is not accuracy, and a gate that
  always decides can always be confidently wrong. **That is the next question, not this one.**
* Run on kenai. Legitimate precisely because `ku` was measured MACHINE-INDEPENDENT (D185);
  if it were not, this probe would be invalid — which is itself a reason the reading is
  worth having.

SEALED 2026-09-09, before the measurement.

---

# ⚖️ THE RESULT — and the probe found something bigger than its subject on the way
Corpus: `docs/ku-armA-decidability-probe-2026-09-09.jsonl` (3 readings, kenai, in-band `origin`).

```
  commit       KERNEL unfoldings        Δ          decls
  7103ff865        7,633,242                        109
  cad06778c        7,633,242           +0           109     ⇐ 0 .lean files touched
  d9d792319        7,868,284      +235,042          116     ⇐ 2 .lean files touched
```
```
  Z1  Δku over the no-op range == 0 EXACTLY          ✅ CONFIRMED
      and the tool flagged it itself: "EXACTLY ZERO — the deterministic instrument's
      own zero", naming the 7 non-.lean files that did change.
  Z2  Δku over the held branch is a definite integer ✅ CONFIRMED  +235,042
  Z3  a Δku gate DECIDES this branch                 ✅ CONFIRMED (see below)
```

## ⇒ THE COMPARISON THIS PROBE EXISTS TO MAKE, ON THE IDENTICAL COMMIT PAIR
```
  ms gate, 3 repeats   delta  +200 ms   band ±2470.1   budget 1843.2   rc 3 UNMEASURABLE
  ms gate, 6 repeats   delta  +800 ms   band ±1916.7   budget 1836.0   rc 3 UNMEASURABLE
  ku                   delta  +235,042  band  ±0       (no budget yet)  DECIDABLE
```
⇒ 🔑 ***THE ms BAND IS 3-12x THE DELTA IT IS MEASURING; THE ku BAND IS EXACTLY ZERO,
MEASURED ON THE ADJACENT NO-OP RANGE IN THE SAME RUN.*** The gate returns UNMEASURABLE
because `K*se` swallows the decision, and with `se = 0` there is nothing to swallow it.
⭐ **The zero is not asserted from determinism — it is MEASURED, on the very range whose ms
verdict flipped `ok` → `UNMEASURABLE` on pure noise between runs 1 and 2.**

## ⛔ WHAT THIS DOES NOT SHOW — AS SEALED, AND I AM HOLDING TO IT
* **No unfolding budget has been derived, so there is NO VERDICT and I report no direction.**
  Z3 is decidability only.
* **Decidability is not accuracy.** A gate with a zero band always decides, and can
  therefore always be confidently wrong. That is the next question and it is untouched.
* It does not answer blocker (b) — whether the counter tracks kernel time.
* **It does not land the branch.**

## ⭐⭐ AND THE PROBE'S REAL FINDING WAS THE INSTRUMENT ITSELF
The first run failed: `unexpected token 'hb_count'`. **`deterministic_cost.py` could not
read this repository's own tree at any commit from `7103ff8` to HEAD, and had not been able
to for three days** — `--` line comments between a doc comment and its declaration stopped
the rewriter's walk-up, so `hb_count` was spliced between a `/-- … -/` and the theorem it
documents. Measured: **0 broken sites at the 09-04/09-05 corpus commits, 1 from 09-06 to
HEAD.** Every walk taken since — D185's machine-independence leg included — was over the
corpus commits, **which are exactly the commits where it cannot break.**
⇒ 🔑 ***A TOOL EXERCISED ONLY ON ITS HISTORICAL CORPUS IS NOT TESTED AGAINST THE TREE.***
Repaired at `d6b5d98` with a red-first arm and a control; verified on the real tree.
⚠️ **And its refusal said nothing:** the failure path prints `r.stderr`, but `lean --json`
writes diagnostics to STDOUT, which is redirected into the `.json` file — so the message is
structurally empty for the commonest failure. **Filed, not repaired here.**

RESULT WRITTEN 2026-09-09, after the measurement.
