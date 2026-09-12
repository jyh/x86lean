# G3 — the timing claims the paper MAY carry, and the ones it may not

**Why this file exists.** The helm's dispersion ruling (2026-09-11 20:04, **re-ruled 20:59**)
narrowed G3 rather than blocking it, and fixed what may be said. Every number here is derived by
`scripts/ranking_stability.py`, gated in `docs/CLAIMS.tsv`, and re-derivable in one command.

## 1. ⛔⛔ TWO INSTRUMENTS, AND A PUBLISHABILITY RULING IS VOID UNLESS IT NAMES WHICH
The first ruling blocked absolute timings from *"a shared hosted runner"*. **The paper's timings are
not from that box**, and the helm corrected it in its own words:
> *"I conflated two instruments … I inherited the band from your block, reasoned correctly about it,
> and applied the conclusion to a population it was never measured on."*
```
  THE SHARED HOSTED RUNNER   a CI GATE. Its 5.3x band, its estimator question and its 68%
                             cancellation are CI-3 and row LA. NOTHING about it blocks a paper figure.
  THE TWO DEVELOPER BOXES    the PAPER's instrument -- and for a claim about SOFTWARE a controlled
                             box is the BETTER apparatus, not a worse one.
```
⇒ 🔑 ***A RULING ABOUT WHETHER A NUMBER MAY BE PUBLISHED IS A RULING ABOUT AN INSTRUMENT.***
📌 **I wrote the population caveat myself and gave it the wrong force** — as *the limit that outranks
everything*. It outranks the power line, but it lands on the CI gate. **The runner being unmeasured
blocks the runner.** (D210 §6.)

## 2. ✅ PUBLISHABLE — POSITIVE MEASUREMENTS
```
  instrument   the developer boxes, 10 corpora, 152 runs, 17 modules, load1 3.1 -> 98.4
  concordance  min 0.919   mean 0.991   over 1,504 within-corpus run-pairs
  the contended corpus holds min 0.942 / mean 0.977 across a 10x LOAD SWING
```
⭐ **The load-swing result is the strongest thing here**: the ordering survives an instrument whose
absolute readings do not. Modules inflate *together* within a run.
⚠️ **An earlier draft quoted min 0.930 from a per-corpus aggregation.** The gated figure is **0.919**
over comparisons. Two aggregations of one quantity, and the one I quoted first was the flattering one.

## 3. ✅ PUBLISHABLE — THE 25 INVERTING PAIRS, STATED FIRMLY
These are **positive observations**: each pair was seen to swap. `ranking_stability.py` prints all 25
with their inversion counts and the min/median/max time ratio. The largest by count:
`Tests.Vectors`↔`X86.Coverage` (3,660), `Tests.Vectors`↔`X86.Serialize` (2,860),
`X86.Semantics`↔`X86.State` (1,995).
⛔ **Every one has a minimum ratio at or near 1.00** — they invert when they are momentarily tied.

## 4. ⚠️ PUBLISHABLE ONLY AS AN ENUMERATION WITH ITS POWER — THE 111 NON-INVERTING PAIRS
**Never as "stable".** This is a NULL, and verso's fleet-binding law (2026-09-11) requires its power:
```
  zero inversions in  11,476 pooled run-pairs        ⇒ 95% upper bound   0.026%
  zero inversions in   1,504 within-corpus run-pairs ⇒                   0.199%
  zero inversions in      10 CORPORA                 ⇒                  30.0%   <- the only
                                                        arguably INDEPENDENT unit
```
⇒ 🔑 ***A FACTOR OF ~1,150, DECIDED ENTIRELY BY AN INDEPENDENCE ASSUMPTION.*** The same 152 runs are
reused across every pair; runs inside a corpus share a box, a load regime and a build.
⇒ **The paper enumerates these 111 pairs and states the bound. It does not call them stable.**

## 5. ⛔ NOT PUBLISHABLE, AND NOT LIFTED
* **Absolute per-module wall-clock — on ANY box.** The weakest claim available; the helm did not lift
  it when it lifted the rest.
* **Any separation THRESHOLD** (*"pairs more than X apart are safe"*). **Driven and refuted in both
  directions:** on median ratio the classes overlap 1.10–4.11 vs 1.37+; on minimum ratio 1.690 vs
  1.009. `X86.Coverage`↔`X86Native` has a median of 4.11 and a range of 1.03–7.75 — **the separation
  is itself unstable.** ⇒ 🔑 ***A CATEGORY IS A HYPOTHESIS ABOUT ITS MEMBERS, AND BOTH ENDS OF THIS
  ONE HAVE COUNTEREXAMPLES.***

## 6. ⚖️ STANDING METHOD RULE
**Report BOTH dispersion estimators with the raw band. Never choose one.** Their gap is itself the
information — it says the dispersion is driven by isolated excursions rather than broad spread, which
is a fact about the box. *"Choosing an estimator by which number lets you publish is choosing the
answer first."*
