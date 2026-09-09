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

## ⚡ THE PIN
**TOOLING SHA FOR NIGHT 5: `88b3a5447741ca3a8179409ab28dbd79c190714e`** — this seal's own commit. kenai is reset to it
before the walk starts, and the walk records the HEAD it actually ran at.

SEALED 2026-09-09 (PDT), before any reading of this night exists.

---

# ⚖️ THE RESULT — 24 readings, 14:29:36 → 15:06:59 PDT (37 min 23 s), EXIT 0
Corpus: `docs/kernel-delta-history-KENAI-NIGHT5-2026-09-09.jsonl`.

## THE SEALED VERDICTS, IN THE SEALED ORDER
```
  Q1  passes the usability gate                        ✅ CONFIRMED
      per-commit p95: min 2.7%  median 7.5%  MAX 11.9%   bound 14.2259%
      ⚠️ READ THE MARGIN, NOT THE VERDICT: 11.9% is 84% of the bound, against night
         4's 5.1% (36%). The same box, two nights, and the noise more than doubled.
  Q2  the k>=8 band's CV is BELOW 6%                    ⛔ REFUTED — CV 9.8%
  Q3  the band OVERLAPS night 4's 4.37-5.26            ✅ CONFIRMED — overlap 4.89-5.26
```
```
  quiet night (yukon)   2.39-4.12   median 3.38   SPREAD 1.72x   CV 14.2%
  night 4 (kenai)       4.37-5.26   median 4.61   SPREAD 1.20x   CV  5.5%
  night 5 (kenai)       4.89-7.01   median 5.72   SPREAD 1.43x   CV  9.8%
```

## ⭐ THE HYPOTHESIS IS DEAD, AND ITS DEATH IS THE POINT
Night 4's CV of 5.5% was noticed **after** seeing the numbers, and I said so at the time and
pre-registered it rather than banking it. **Its own test refuted it within four hours.**
⇒ **The tightness was a ONE-NIGHT ACCIDENT.** kenai's Δms↔Δku proportionality is not 2.6x
tighter than yukon's as a property of the box; night 5 on the same box reads CV 9.8%.
📌 **This is the pre-registration working exactly as intended.** Had I banked night 4's 5.5%
as "the first evidence FOR the counter" — which is precisely what six obstacle-removals in a
row make tempting — it would have entered the record as a finding and been quoted.
[[feedback-prose-written-before-the-measurement]]

## ⚠️ AN ADDITIONAL READING, EXPLICITLY **NOT** A SEALED VERDICT
Q3 was sealed as overlap/no-overlap and it overlaps; I am not moving that goalpost. But the
same numbers carry something the seal did not ask:
```
  SAME box · SAME corpus · SAME tooling · two nights 52 minutes apart
  median band  4.61 -> 5.72  =  1.24x
  and the overlap is 0.37 wide against night 5's own 2.12 range
```
⇒ 🔑 ***THE BUDGET IS NOT REPRODUCIBLE TO BETTER THAN ~25% ON ONE MACHINE, BEFORE ANY
MACHINE DIFFERENCE ENTERS.*** Reproducibility is real in the weak sense the seal asked for
and LOOSE in the sense a budget would need.

## ⚖️ WHAT THIS DOES TO 4b — AND IT SHARPENS ARM A RATHER THAN THREATENING IT
**Every bit of this variation lives in `ms`.** `Δku` is not merely stable across the two
nights, it is IDENTICAL BY CONSTRUCTION — the counters corpus was not re-walked, and the
counter is deterministic and was measured identical across the two machines (D185).
⇒ **The noisy half is exactly the half ARM A stops gating**, and the night-to-night 1.24x
is a fourth independent reason to gate `Δku` in unfoldings rather than `ms per 1k unfoldings`:
the clock is machine-dependent (D187), night-dependent (here), cannot separate a real commit
from a no-op (D187 §ARM A), and carries the whole of both nights' scatter.
⛔ **AND BLOCKER (b) IS NOT ANSWERED.** This night was aimed at *"does the counter track
kernel time"* and what it returns is: **reproducibly, but only to ~25%.** That is not
evidence FOR the counter in any strong sense, and I am not reporting it as such. **Seventh
entry in a row that removes an unknown without supplying evidence FOR the counter** — and
this one at least changed a number rather than only a diagnosis.

SEALED RESULT WRITTEN 2026-09-09, after the gate was judged. **No re-run is permitted: the
night completed and carries a verdict.**
