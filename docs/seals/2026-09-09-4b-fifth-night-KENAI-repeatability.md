# SEALED — 4b NIGHT 5, KENAI REPEATABILITY. WRITTEN AND COMMITTED BEFORE THE FIRST PASS.
# paris, 39th head, 2026-09-09. D179 keep-rule 1.

## ⚠️ DECLARED FIRST: THIS SEAL NAMES A CORPUS THAT DOES NOT EXIST YET, AND CI WILL GO RED
`out:` below names `docs/kernel-delta-history-KENAI-NIGHT5-2026-09-09.jsonl`, which cannot
exist until the walk runs. `check_corpus_claims` arm A will correctly red CI/build from this
commit until the corpus lands. **That is a DECLARED, ACCEPTED cost, not a defect** — the
conflict is recorded at arm A's own site and in night 4's seal. Stated here at sealing time
so the next head reads a declared cost rather than diagnosing a fresh red.

## ⚖️ WHAT THIS NIGHT IS FOR — BLOCKER (b), NOT BLOCKER (a)
D187 established that 4b's **second-SOURCE** blocker (a) is unsatisfiable by a second
machine, because the budget's numerator is a clock. **This night does not address (a) and
must never be quoted as doing so** — a repeat on the same box with the same corpus is a
REPEATABILITY test, not an independent source.
**It addresses (b): whether the counter TRACKS KERNEL TIME**, which is the claim 4b actually
rests on and the one no entry has ever supplied evidence for.
⭐ **AND IT WOULD BE THE CAMPAIGN'S FIRST CLEAN SAME-MACHINE REPEAT.** The only prior
same-machine pair is the quiet night and night 3, and night 3 was DISCARDED for failing the
usability gate — so a usable repeat has never existed on either box.

## THE HYPOTHESIS, AND IT WAS GENERATED POST-HOC TODAY
Night 4 (kenai) gave a k>=8 band of **4.37-5.26, CV 5.5%**; the quiet night (yukon) gave
**2.39-4.12, CV 14.2%** — same n, same k-window structure, same twelve commits. **The quieter
box gave a 2.6x tighter Δms↔Δku proportionality**, which is what you would see if the scatter
were measurement noise and the underlying relation real.
⛔ **THIS WAS NOTICED AFTER SEEING THE NUMBERS.** That is precisely why it is being
pre-registered before its test rather than banked as a finding
[[feedback-prose-written-before-the-measurement]].

## PARAMETERS — PINNED, IDENTICAL TO NIGHT 4 EXCEPT THE OUTPUT PATH
```
machine   : kenai, clone C:\Users\jyh\x86lean-4b, PowerShell only ($env:PYTHONUTF8="1")
tooling   : the sha recorded at the bottom of this file
walk      : kernel_delta_history.py --sweeps 2 --commits <the SAME 12, same order>
module    : Tests.Coverage        counters: docs/deterministic-cost-history-2026-09-05.jsonl
out       : docs/kernel-delta-history-KENAI-NIGHT5-2026-09-09.jsonl
band      : k >= 8, the UNSELECTED regime — declared now as the band I will quote
gate      : MAX per-commit p95 <= 14.2259%, judged FIRST, polled via --early
rule      : D179 keep-rule 1-4, and night 4's amendment 3 on mechanical failure, both in force
```

## PREDICTIONS, SEALED
```
Q1  the night PASSES the usability gate.
    basis: night 4 read MAX 5.1% on this box, 2.8x inside the bound.
    confidence: MODERATE-HIGH. ⛔ NOT high: night 3's P1 was sealed HIGH and refuted, and
    one prior reading on a box is one reading.
Q2  the k>=8 band's CV is BELOW 6%.        (night 4: 5.5%)
    confidence: MODERATE. This is the tightness claim and the whole point.
Q3  the k>=8 band OVERLAPS night 4's 4.37-5.26.
    confidence: MODERATE-HIGH. This is the REPRODUCIBILITY claim, and it is the one whose
    failure would matter most.
```

## ⛔ WHAT WOULD REFUTE, AND WHAT IT WOULD MEAN — WRITTEN CAREFULLY BECAUSE I GOT THIS WRONG LAST TIME
Night 4's seal said a disjoint band would show the counter *"does not travel across
machines"*. **That was false when written**, because the quantity compared contained a clock.
**Here the machine is held FIXED, so that error cannot recur** — and this is the whole reason
a same-machine repeat is the right next experiment.
* **Q3 REFUTED (a band disjoint from night 4's, on the SAME box, same corpus, same tooling)**
  would say the counter does not travel across **TIME on one machine**. That is a genuine and
  strong negative for 4b and would close it for a measured reason. **There is no clock
  difference available to explain it away.**
* **Q2 REFUTED but Q3 held** would say the tightness was a one-night accident and the
  proportionality is looser than night 4 suggested — the hypothesis dies, 4b survives unchanged.
⛔ **AND WHAT A PASS DOES NOT BUY:** it is ONE machine and ONE corpus. It supplies evidence
that Δms ≈ c·Δku is REPRODUCIBLE on a quiet box. **It does not supply a second SOURCE, it does
not make the budget machine-free, and it is not "4b unblocked".** I will not report it as any
of those.

SEALED 2026-09-09 (PDT), before any reading of this night exists.
