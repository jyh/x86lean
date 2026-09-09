# SEALED — 4b CALIBRATION NIGHT 4 (ATTEMPT 2 OF THE SECOND-SOURCE HALF), ON KENAI
# paris, 39th head. WRITTEN AND COMMITTED BEFORE THE FIRST PASS.
Authorised by the 39th helm head, 2026-09-09 12:4x PDT, with three conditions.
This file discharges condition (1) and states condition (3).

## ⚖️ D179 KEEP-RULE 1, SLOT BY SLOT — because the rule names three things
Rule 1: *"The ledger row records the pinned `--base <sha>`, the repeat count `k`,
and this rule, BEFORE the first pass. A verdict from a run whose parameters were
not declared in advance is not quotable."*
⛔ **`kernel_delta_history.py` HAS NO `--base` FLAG.** Rule 1 was written for the
A/B delta gate, which does. Mapping it rather than pretending it fits, so nobody
later reads a missing flag as a missing declaration:

| rule 1 slot | this run's actual parameter |
|---|---|
| pinned `--base <sha>` | the pinned **12-commit walk set**, by full sha, below — the walk has no base/head pair, it has an ordered commit set, and THAT is the thing that must not move between nights |
| repeat count `k` | **`--sweeps 2`** (the walk's repeat count: forward then reverse), matching BOTH existing walks exactly |
| — and the band's `k` | **`k >= 8`**, the UNSELECTED regime, declared now as the band I will quote |
| the rule | D179 keep-rule 1–4, quoted in §RULE below |

## PARAMETERS — PINNED
```
machine   : kenai (x86_64-w64-windows-gnu, Ryzen 7 8700F), clone C:\Users\jyh\x86lean-4b
tooling   : master 009688b, the SAME sha on both machines, pinned before the run
toolchain : leanprover/lean4:v4.32.0-rc1 (lean-toolchain, unchanged)
walk      : kernel_delta_history.py --sweeps 2 --commits <the 12 below, in this order>
module    : Tests.Coverage        decl-names: the script's default three
counters  : docs/deterministic-cost-history-2026-09-05.jsonl — UNCHANGED, NOT re-walked
            (the `--counters` input, NOT the walk; measured load-invariant, 5/5
             byte-identical across a 2.4x-9x load ratio)
scoring   : score_calibration_night.py <walk>      (gate FIRST)
            unfolding_calibration.py --counters <above> --walk <the new walk>
out       : docs/kernel-delta-history-KENAI-2026-09-09.jsonl
```
The twelve, in walk order, identical to the quiet night and to night 3:
```
144e9a3cf75a742be013212868ea6f6262cda0bf   4f6766b9b57c2bf2e8a8167a885a41b5ff479508
76cb51bd07d11476157a74a0fe91ad8091959fbe   3769ea0c10754f2f226b8034a885939e93e52db0
0f929e3e507086224244af3cf8e9437aa8fe5928   320cb45721ac370afbab3e552d18d35637f72a04
762da1add0715a84c8507cd408c46598ffa2f1f0   a5326fd048fd96e0a1b90881c77131ed8b94290a
873a4d9ea97ee35f26c7c2d2fffe4b46029a90fa   0f7baee505e61a4318b52599be3e1a71745074da
e57c99fdf7b591823d51e1f4dbe182d073d2e206   5c0159983aaa0dc972048ea25aa31db8b5ab2c89
```

## ⛔ THE USABILITY GATE — JUDGED FIRST, BEFORE THE BAND EXISTS
**MAX per-commit p95 between-sweep relative spread <= 14.2259%** — the quiet
night's own maximum, derived at run time by `score_calibration_night.py`, not
typed here as a literal.
⭐ **AND IT IS POLLED IN FLIGHT VIA `--early`, WHICH IS SOUND RATHER THAN A SECOND
LOOSER TEST:** the statistic is a **MAX**, which is monotone in the readings seen
so far, so once any completed pair exceeds the bound no later reading can bring it
back under. Asking after every commit adds no multiplicity. The early form can
return a definite FAIL and never a definite PASS; "NOT YET FAILED" is its only
other answer. **This is the remedy night 3's post-mortem named and did not have.**

## §RULE — D179 KEEP-RULE, IN FORCE FOR THIS RUN
1. Declare before running (this file).
2. **The verdict is the declared run's. `UNMEASURABLE` is a verdict, not a retry.**
3. **No discard on the outcome — and no discard on load either.** A discard needs a
   covariate that PREDICTS; the best candidate is a tail correlation (Δload vs p95,
   r = +0.38) that does not reach significance at n = 24.
4. RETIRED as a discard criterion (helm, 2026-09-09); a diagnostic column only.
⛔ **ONE RUN. No re-running until it agrees.**

## ⛔⛔ CONDITION (3) — THE PORT HOLE, STATED, NOT DISCOVERED
**One hole was live on this exact route and is REPAIRED at `009688b` before this
seal:** `portable.loadavg()` returns `None` off POSIX, and four consumers in two
files formatted it as a float. `kernel_delta_history.py:706` would have killed the
walk on its FIRST reading, with that reading already written to disk. Measured on
kenai before the pass, then repaired, then re-driven on kenai (selftest OK, planted
red firing). See the commit message of `009688b`.
**What remains open, and it is not on this route:** ~25 scripts do not import
`portable.py`. `kernel_delta.py` was one and is now ported on the load dimension;
the rest are untouched and this night does not invoke them.
⛔⛔ **AND THE HOLE THIS RUN CANNOT CLOSE — THE LOAD COLUMN IS STRUCTURALLY ABSENT.**
`os.getloadavg()` does not exist on Windows, so **every row of this walk will carry
`load1: null`**. Checked against all four rules rather than the one I remembered:
* the **usability gate** is built from **SPREAD**, not load — unaffected;
* **rule 3** forbids a load-based discard anyway;
* **rule 4** is the only load-based rule and is RETIRED to a diagnostic column;
* so **nothing that can carry or withhold a verdict reads the missing column.**
⚠️ **What IS lost is the diagnostic.** If this night fails the gate I will NOT be
able to say "the box was busy" — and by rule 3 I could not have used that anyway.
A small number of out-of-band CPU readings will be taken on kenai during the run
and reported as a **LABELLED DIAGNOSTIC ONLY**; they are not a criterion, they
enter no rule, and no discard may cite them.

## 📌 A MECHANICAL SMOKE TEST IS DECLARED HERE SO IT CANNOT LOOK LIKE A DISCARD
Before the sealed walk I will take **one** `kernel_cost.py --emit-json` reading on
kenai to prove the profiler runs there at all. It uses DIFFERENT parameters (one
tree, no sweeps), produces **no commit pair, no spread, no gate reading and no
band**, and is therefore incapable of being a discarded night. Its only outcomes
are "the profiler runs" and "it does not".

## PREDICTIONS, SEALED
```
P1  the night PASSES the usability gate (MAX per-commit p95 <= 14.2259%).
    basis: on identical work kenai's per-commit wall clock spanned 54-95 s
           against yukon's 52-677 s (D185 §4) — a 7x tighter spread — and the box
           has no other users. ⛔ NOTE THE GAP IN THIS BASIS: that is a spread
           ACROSS COMMITS; the gate reads spread BETWEEN SWEEPS of the same
           commit. They are related but they are not the same statistic, and I
           have never measured the second one on kenai.
    confidence: MODERATE. Not high, and the reason is the gap just named, plus
           night 3's P1 which was sealed HIGH and REFUTED.
P2  the k>=8 unselected band lands INSIDE or OVERLAPPING the quiet night's
    2.39 - 4.12 (median 3.38).
    confidence: MODERATE. This is the actual question. A second usable night that
    reproduces the band is what the second-SOURCE blocker has always wanted.
P3  the walk completes without a crash traceable to platform portability.
    confidence: MODERATE-HIGH after 009688b, and deliberately NOT high: I found
    that class by reading one file, and ~25 scripts are unported. A second hole on
    this route would refute P3 and is the single most likely way this night dies.
```

## WHAT WOULD REFUTE, AND WHAT A PASS DOES NOT BUY
**Refutes P2:** a band materially outside 2.39–4.12 at usable conditions. That
would say the kernel-unfolding counter does not travel ACROSS MACHINES, which is a
stronger negative than 4b currently records and would close 4b for a measured
reason. **That is a real possible outcome of this run and I am not hoping against it.**
⛔ **WHAT A PASS DOES NOT BUY, stated now so it cannot be claimed later:**
* it gives a **second usable night**, on a second machine. That is ONE of 4b's two
  named blockers — the SOURCE half.
* **it is still not evidence that the counter TRACKS KERNEL TIME**, which is the
  claim 4b actually rests on. D180, D181, D183, D184 and D185 each removed an
  indictment or an unknown and **not one supplied evidence FOR the counter.**
  This night can make that six.
* **I will not report a pass as "4b is unblocked".**

SEALED 2026-09-09 (PDT), at tooling sha 009688b, before any reading of this night exists.

---

# ⛔⛔ AMENDMENT 1 — MADE BEFORE THE NIGHT'S FIRST READING EXISTS, AND FORCED BY A
# MECHANICAL FAILURE RATHER THAN BY ANY OUTCOME

**State when this was written: ZERO readings of this night exist.** The walk has not
been started. What follows was produced by the **smoke test this seal declared in
advance** — one `kernel_cost.py --emit-json` on kenai, which the seal defined as having
only two possible outcomes, "the profiler runs" and "it does not". **It did not.**
⇒ Nothing here is selection on a result, because there is no result to select on.

## 1. THE PINNED TOOLING SHA MOVES, AND WHY THAT IS NOT A LOOSENED SEAL
The seal pinned tooling at **`009688b`**. At `009688b` **this night was impossible** —
not degraded, impossible: the profiler died before producing a single reading. The pin
moves to the sha recorded at the bottom of this amendment. **Every parameter that could
bias a result — the twelve commits, `--sweeps 2`, `k >= 8`, the counters corpus, the
gate and its bound, the predictions — is UNCHANGED.**

## 2. THREE PORT DEFECTS, IN THE ORDER THEY WERE FOUND — AND TWO OF THEM WERE HIDING EACH OTHER
```
 (a) kernel_cost.py imported `resource` (POSIX-only) at MODULE level
     -> ModuleNotFoundError at import, before main(), so none of the file's own
        careful per-reading guards could ever run.
 (b) mod_name(f) = f[:-5].replace("/", ".")  -- a LOGICAL name built from a PATH.
     glob returns os.sep, so on kenai every module was `X86\Basic`, `Tests\Coverage`.
     `--decl-modules Tests.Coverage` is matched against mod_name's output, so the
     declaration set came back EMPTY.
 (c) 193 open() calls in scripts/ (42 on this route) pass no encoding=, so they
     inherit cp1252 on Windows -> UnicodeDecodeError on this repo's non-ASCII sources.
```
⛔⛔ **(b) WAS MASKING (c), AND THE FIRST SMOKE TEST "PASSED" BECAUSE OF IT.** With the
module names wrong, the declaration lookup found nothing, so `per_declaration()` — the
function whose `open(f)` raises — **was never called.** Repairing (b) is what made (c)
appear. ⇒ 🔑 ***A RUN THAT SUCCEEDS BECAUSE ONE DEFECT PREVENTED ANOTHER FROM EXECUTING
IS INDISTINGUISHABLE FROM A RUN THAT WORKS*** [[feedback-two-defects-that-cancel]].
⚠️ **AND THEIR SEVERITIES ARE NOT EQUAL, so they are not filed as one:** (a) and (c)
**crash** — loud, and incapable of producing a wrong number. **(b) is silent**: the walk
would have completed, written a full 24-row corpus, and compared as though it had
measured nothing. **(b) is the one that would have cost a night and a false result.**

## 3. ⛔ A CORRECTION TO THIS SEAL'S OWN PORT-HOLE PARAGRAPH
The seal states *"every row of this walk will carry `load1: null`"*. **MEASURED: it will
carry `-1.0`.** `kernel_cost._sentinel()` deliberately writes `-1.0` into the legacy
top-level `load1`/`load5` fields, and an existing selftest arm asserts exactly that.
**I inherited "null" from D185, which measured `deterministic_cost.py` — a DIFFERENT
producer — and applied it to this one without checking**
[[feedback-two-readings-are-not-two-witnesses]].
⚠️ **The conclusion of that paragraph is UNCHANGED and was checked again, not assumed:**
the usability gate reads SPREAD, rule 3 forbids a load discard, rule 4 is retired to a
diagnostic. **But `-1.0` is worse than `null` in one specific way that must be said: it
is a NUMBER, so any consumer that medians or maxes the load column will silently fold
`-1.0` in as if it were a reading**, where `null` would have refused. The `load1 > 21`
diagnostic column will therefore read this night as quiet. **It is a diagnostic and
cannot change a verdict — but it is not a truthful diagnostic and I am not quoting it.**

## 4. THE RECIPE GAINS ONE PINNED ENVIRONMENT VARIABLE
```
  $env:PYTHONUTF8 = "1"        on the kenai leg, for every invocation
```
PEP 540 UTF-8 Mode. It repairs all 193 sites at once **and makes Windows read exactly as
the machine this corpus is compared against**, which is convergence, not divergence.
⛔ **AND IT IS NOT LEFT AS A THING TO REMEMBER.** `portable.require_utf8_mode()` now
REFUSES, naming what it saw and the remedy, and the walk driver calls it before the first
checkout — one check covers the run because the profiler is a child and inherits the
environment. **A precondition that lives in someone's memory is not a precondition**
[[feedback-a-gate-whose-precondition-is-a-discipline]].

## 5. WHAT THE SMOKE TEST FINALLY MEASURED, AND IT IS THE PARITY THIS NIGHT NEEDS
```
  module keys      X86.Basic, X86.Coverage, X86.Flags, ...   backslash present: NO
  decls            {"Tests.Coverage": 28 declarations}       (was: empty)
  profiler         runs, 57.7 s for one tree
```
⚠️ **28 is NOT compared to D185's 103 and must not be**: different tool, different
commit. The parity that matters is per-commit across the walk and only the walk can
measure it.

## 6. PREDICTIONS — UNCHANGED, AND P3 IS NOW PARTLY RESOLVED AGAINST ME
P1 and P2 stand exactly as sealed. **P3 (`the walk completes without a portability
crash`) was sealed MODERATE-HIGH with the words *"~25 scripts are unported. A second hole
on this route would refute P3 and is the single most likely way this night dies."*
THREE holes were on this route, not one.** The prediction's *reasoning* was right and its
*confidence was too high*; that is recorded here rather than quietly re-rated, and P3 is
now re-sealed at **MODERATE** for the walk that follows.

## ⚡ THE PIN
**TOOLING SHA FOR THIS NIGHT: `74dff4facfa827f0a854885c56eb5d325df64e5d`** — the commit carrying amendments 1 and 2
and the three port repairs. This is the sha amendment 1 §1 refers to. kenai is
reset to it before the walk starts, and the walk's own first line records the HEAD
it actually ran at, so the claim is checkable against the run rather than trusted.

AMENDED 2026-09-09 (PDT), before the walk's first reading.

---

# ⚠️ AMENDMENT 2 — WHAT THE IN-FLIGHT GATE CAN AND CANNOT DO, MEASURED BEFORE THE RUN
Still zero readings of this night. The `--early` form was driven against BOTH existing
walks, truncated to a growing prefix, with the discarded night 3 as a positive control:
```
  rows      quiet night (passes)          night 3 (known FAIL, 3.89x)
   2, 6     "NOTHING to read. Not a pass"  "NOTHING to read. Not a pass"
  13        not failed                     not failed
  24        not failed                     ⛔ "ABORT IS SOUND HERE"
```
⛔ **SO THE EARLY GATE CANNOT SPEAK IN THE FIRST HALF OF THIS RUN.** Under `--sweeps 2`
in the default order the walk goes forward then reverse, so **no commit owns a completed
pair until reading 13 of 24** — `kernel_delta_history`'s own selftest says exactly this
and I confirmed it against the corpora rather than trusting it.
✅ **THE TOOL HAS A REMEDY AND I AM DELIBERATELY NOT USING IT.** `--interleave` gives the
first commit both readings by reading 2. **It would also change the walk ORDER, and both
existing walks are non-interleaved.** The reverse sweep is what cancels monotone drift in
machine conditions; changing it would make this night incomparable to the two it exists
to be compared with. **Comparability wins, and the cost is stated rather than absorbed.**
⇒ **`--early` here buys the ability to abort a doomed SECOND half — about half a night —
not to avoid one.** That is worth having and it is not what "gated in flight" would
normally imply, so it is written down at its true size.
📌 And the refusal at rows 2 and 6 is the behaviour I wanted to confirm most: it says
*"NOTHING to read. That is not a pass"* rather than returning a green from an empty set
[[feedback-an-unparseable-gate-file-reports-failure-not-absence]].
