# SEALED — 4b THIRD CALIBRATION NIGHT, paris 35th head, BEFORE the walk starts
## PARAMETERS
* walk    : kernel_delta_history over the SAME 12 commits, same module set, 2 sweeps per commit
            (matching both existing walks exactly — this is the `--walk` input, NOT the counters)
* counters: docs/deterministic-cost-history-2026-09-05.jsonl, UNCHANGED and NOT re-walked
            (load-invariant, measured 5/5 byte-identical across a 2.4x-9x load ratio)
* scoring : unfolding_calibration.py --counters <that> --walk <the new walk>,
            k>=8 unselected band against the quiet night's 2.39-4.12, median 3.38

## ⛔ THE USABILITY GATE, ON A COVARIATE, DECLARED BEFORE ANY READING EXISTS
The new night's MEDIAN per-commit p95 between-sweep relative spread must be
**<= 14.2%** — the QUIET night's own MAXIMUM (its min 6.1%, median 12.0%, max 14.2%).
Above that the night is UNUSABLE and is discarded ON THAT COVARIATE, whatever it
scores. ⚠️ This is judged BEFORE the calibration band is computed, and it is the
only thing that makes this an experiment rather than a third opinion: without it,
"the third night agreed" is selection on the outcome, which D179 rule 3 forbids.
⛔ ONE RUN. No re-running until it agrees.

## PREDICTIONS, SEALED
P1  the night PASSES the usability gate (median p95 <= 14.2%).
    basis: the box is at load ~5, inside the quiet night's own 3.11-6.80 range.
    confidence: HIGH — this is close to a repeat of the quiet night's conditions.
P2  the k>=8 unselected band lands INSIDE or OVERLAPPING 2.39-4.12.
    confidence: MODERATE. This is the actual question; a third night at quiet-night
    conditions should reproduce the quiet night's calibration if the counter travels
    across TIME on one machine. Machine independence is NOT addressed either way.
P3  ⚠️ WHAT A PASS DOES *NOT* BUY, stated now so it cannot be claimed later:
    it gives a SECOND USABLE NIGHT on ONE machine. 4b's machine-independence half
    is untouched, and I will not report P2 as "4b is unblocked".

## WHAT WOULD REFUTE P2
a band materially outside 2.39-4.12 at quiet-night conditions. That would say the
kernel-unfolding counter does not travel across TIME on a single machine, which is
a stronger negative than 4b currently records, and would close 4b for a measured
reason.
SEALED 2026-09-09T09:26:05Z

---
📌 **WHY THIS FILE IS IN THE REPOSITORY AND NOT IN A SCRATCH DIRECTORY.**
It was written to a session-local scratchpad first, which vanishes with the session — so nobody
but its author could ever have checked it against the result. **A seal that only its author can
read is not a seal, it is a memory of having been careful.** Committed here BEFORE the walk it
governs produced its first reading; `git log` on this path is the proof of order, which is the
only property a seal actually has.

---
# ⛔⛔ AMENDMENT, MADE BEFORE THE SUBJECT'S DATA EXISTED — AND WHY IT IS NOT SELECTION

**State when this was written: the walk had produced 4 of 24 readings and ZERO paired commits, so
the third night's gate value and band had never been computed and could not have been.** The
scorer had been run against it exactly once and refused: *"only 0 commits have paired sweeps."*
The evidence for both repairs below comes ENTIRELY from the two nights whose answers were already
known.

## 1. THE SEALED GATE COULD NOT FAIL THE NIGHT IT WAS BUILT TO EXCLUDE
Sealed as **"MEDIAN per-commit p95 <= 14.2%"**. Driven against the loaded night:
```
                       per-commit p95 spread      verdict under the SEALED gate
    quiet   night      min 6.1  median 12.0  max 14.2      PASS
    loaded  night      min 4.7  median  8.7  max 50.6      PASS   ⛔ AND IT MUST NOT
```
**The loaded night's MEDIAN is BELOW the quiet night's.** Its tail is 3.6x worse and the median
never sees it. ⇒ 🔑 ***I BUILT A TAIL-GATE OUT OF A MEDIAN.*** That is the fourth instance today of
one shape — the right-shaped measurement about the wrong object — and **the first caught before the
data landed**, by the arm that required a night with a known answer to be rejected.
⇒ **THE STATISTIC IS NOW THE MAX.** quiet 14.2% · loaded 50.6%.

## 2. AND THE BOUND IS NOW DERIVED AT RUN TIME, BECAUSE A ROUNDED LITERAL REJECTED ITS OWN AUTHOR
Typed as `0.142`, the gate **FAILED THE QUIET NIGHT** — the very night that defines the bound, whose
true maximum is fractionally above 0.142 and merely *prints* as "14.2%".
⇒ 🔑 ***A ROUNDED LITERAL IS A DIFFERENT THRESHOLD FROM THE QUANTITY IT WAS ROUNDED FROM, AND AT A
KNIFE-EDGE BOUND THAT DIFFERENCE IS THE WHOLE GATE.*** Caught only by the control requiring the quiet
night to PASS — an arm that exists because a gate must be probed for silence as well as for noise.
The bound is now `max(per-commit p95)` read from `docs/kernel-delta-history-2026-09-04.jsonl` at run
time: **14.2259%**, full precision, no margin invented.

## 3. WHY AMENDING A SEAL HERE IS LEGITIMATE, STATED SO IT CAN BE DISPUTED
A seal exists to stop a rule being fitted to a result. **Nothing here was fitted to a result**: the
subject has produced no scorable data, both repairs are forced by nights whose values were already
published, and both make the gate **STRICTER**, not looser — the loaded night went PASS → FAIL and
nothing went FAIL → PASS. ⇒ **Repairing an instrument that provably cannot fail its intended target
is not selection; it is the reason controls are run before the subject arrives.**
⚠️ **The knife-edge is real and is not hidden:** the quiet night passes only by EQUALITY, so a single
unlucky commit fails the third night. Deliberate — a FAIL means *"this night is unusable"*, never
*"the counter is refuted"*, so strictness errs safe. ⛔ **If the third night fails, that is the
reported result. It must NOT be re-run to a pass, and this paragraph is what forbids it.**

---
# ⚠️ A DESIGN FLAW IN THIS SEAL, VISIBLE MID-RUN AND RECORDED RATHER THAN PATCHED

**The usability gate cannot be evaluated until the run is COMPLETE, so it can never save any of the
run's cost.** It reads the between-sweep spread, and sweep 1 does not begin until sweep 0's twelve
profiles are done — so at the halfway point there are **zero** paired commits and the gate has
nothing to read. A night that is going to be rejected is rejected only after the whole bill is paid.
```
    measured at 5 of 24 readings:  paired commits 0/12   ⇒ gate UNEVALUABLE
    load1 so far  3.96-9.31, median 7.41   against the quiet night's 3.11-6.80
    secs/reading  median 91.3              against the quiet night's 53-86
```
⇒ 🔑 ***A GATE THAT CAN ONLY FIRE AFTER THE EXPERIMENT HAS FINISHED IS A VERDICT, NOT A GATE.***
A real gate has a cheap early form on the same covariate — here: abort if the running median `load1`
leaves the calibration night's own range — and this seal declared none.

⛔ **AND I AM NOT ADDING ONE NOW.** By my own D179 rule 4 a discard needs a condition **declared in
advance**, and the only numeric load rule on the books is `load1 > 21`; the observed 7.41 does not
meet it. **Stopping this run on load would be discarding on a condition I never declared — the exact
move the rule exists to forbid, made attractive by a prediction that it will fail.** ⇒ The run
finishes and the gate reports whatever it reports.
📌 **FOR THE NEXT DESIGN, and this is the reusable half:** declare TWO forms of every usability
condition — a cheap one evaluable early on a covariate, and the full one at the end — and state the
early one in the seal. Sweep ordering also matters: **interleaving the two sweeps per commit would
make the gate evaluable from the second reading onward** at no extra cost. That is a real change to
`kernel_delta_history`'s walk order and it is owed as a separate item, not smuggled in here.
