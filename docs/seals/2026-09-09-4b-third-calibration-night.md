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
