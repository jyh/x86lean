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
