# x86lean — THE QUEUE

The ranked work list for this repository. Created 2026-09-05 on the council's word (minute
2026-09-05 §E4: *"x86lean's queue (paris's) gains P3 'the soft-float commission'"*). Until now the
queue lived in bank prose and bus posts, which is why its P3 row's price could sit unexamined for
eleven days and be 44% wrong when finally re-derived (see the commission's §2).

⛔ **A row's PRICE is a derived number or it is absent.** Prices quoted here name the tool that
prints them, so a stale one is a bug someone can find rather than a sentence that reads fine.

---

## P0 — the scalar core · **DISCHARGED**
The 20 scalar forms, `Cpu`, `step`, the differential harness against ACL2 x86isa.
Exit criterion — one differential run of the 20 forms with zero unexplained disagreements — met.

## P1 — the scalar campaign · **DISCHARGED** (21 batches)
Roster growth to the census's scalar demand, with the vector table, the encoding gates and the
kernel-cost discipline built along the way.

## P2 — the vector campaign · **LIVE** (33 batches)
Extending the model and the oracle-availability census across the SIMD/FP buckets.

**Where it stands** — ⚠️ HAND-COPIED from the tools named, so it is a claim and not a reading;
re-run them rather than quoting this block (`python3 scripts/p2_oracle_support.py`):
```
THE UNASKED REMAINDER    172 pairs / 16,879 instructions   (2026-09-06, after batch 34)
   x86isa IMPLEMENTS       1 pairs /     88     ⇐ pandn @ MMX (mm)
   x86isa DOES NOT       171 pairs / 16,791
   NOT RESOLVED            0 pairs /      0
```
⛔⛔ **D144's "EVERY PAIR x86isa IMPLEMENTS HAS NOW BEEN ASKED" HAS A QUALIFIER, AND BATCH 34
EXPOSED IT WITHOUT CREATING IT.** The remainder loop takes each mnemonic's **DOMINANT** bucket
(`p2_roster.dominant_bucket` = `most_common(1)`) and skips the mnemonic entirely if THAT pair is
measured. So the table shows **at most one bucket per mnemonic**, and every non-dominant bucket has
never been in its denominator at all.
`pandn` had demand at two buckets — SSE-legacy 2,980 and MMX 88 — so SSE-legacy was dominant and
measured, and the MMX pair was invisible. Batch 34 covered the SSE-legacy demand, which took it to
zero, which promoted MMX to dominant, which made a pair that was ALWAYS unasked appear as new work.
⇒ 🔑 **a census keyed by "the biggest bucket per name" reports about names, not keys** — and
covering a mnemonic can only ever reveal its next bucket, never add one. The honest statement is
*"every DOMINANT pair x86isa implements has been asked"*; the size of the unobserved region is
every mnemonic whose demand straddles buckets (the tool prints 3,991 instructions sitting at
mnemonics' other buckets).
⚠️ **This is a finding about the TOOL, not a regression.** Two candidate repairs, neither taken
here: enumerate every (mnemonic, bucket) pair with demand rather than the dominant one, or keep the
dominant-bucket view and print the count of non-dominant pairs beside it so the blind spot has a
number. [[feedback-a-census-is-per-key-not-per-name]]
⇒ ⭐⭐ **EVERY PAIR x86isa IMPLEMENTS HAS NOW BEEN ASKED** (D144). D138 could only reach *"every
implemented pair that CAN be asked"*, with `vzeroupper` / `AVX (state)` — 1,241 instructions —
outside the probe's reach for three batches. The availability census is finished without a
qualifier.

### P2 open items, in order
1. **`probe_bucket` — the RULE is repaired (D143); the PROBE is not yet run.**
   `probe_bucket` now calls `demand_census.isa_bucket`, the census's own total rule, instead of
   being a second rule that agreed with it on 256 of 256 rows. `vzeroupper` buckets as
   `AVX (state)`, so the key it needs now exists. The `None` return that used to decide BOTH the
   bucket and whether a row was a question is split: `NOT_AN_AVAILABILITY_QUESTION` is a declared
   list with a reason per entry, gated for orphans, and the delegation itself is gated by an arm
   that stubs the census's function and requires the answer to move.
   ⛔ **What remains, and it needs the oracle**: a probe row for `vzeroupper` — `hx` from `clang`
   like every other row's, verdict from an ACL2 pass at CR4=0x600 — after which the unasked
   remainder's *implemented* column goes from 1 pair / 1,241 instructions to **0**, and the
   availability census is finished in the sense D138 could not reach.
   ⚠️ Six rows stay excluded ONLY because they were excluded yesterday (`endbr64`, `prefetcht0`,
   `prefetchnta`, `emms`, and the two `CONTROL:` rows). Each maps to a real census bucket under the
   census's rule, so each verdict IS an availability fact this table could carry. Ruling on them
   widens what `measured_availability()` means and moves the roster — a batch, not a side effect.

2. **Land the buildable groups the census has surfaced** — the ordinary batch work.
   ⭐⭐⭐ **THE GROUP IS NAMED AND DERIVED NOW (D157).** This row asked for "the buildable
   groups" for three sittings and named none, because the P2 roster's ranked table prints its
   top FORTY rows and every unclaimed row there that EXECUTES is either VEX or scalar FP. The
   residue reads as blocked on one of two large additions. It is not:
   ```
     64 unclaimed SSE-legacy (xmm) pairs EXECUTE   47,965 instructions
   − 40 that are the soft-float commission's       36,925
   = 24 needing NO rounding rule at all            11,040
   ```
   ⚠️ **THOSE ARE THE PRE-BATCH FIGURES AND THE TOOL NO LONGER PRINTS THEM.** A covered
   mnemonic's gap demand is zero, so claiming the nine moved the total to `55 pairs / 44,409`
   the moment they landed. Re-run the tool for today's residue; read `47,965` as a reading
   dated 2026-09-06, not as something to reproduce.
   ⇒ 🔑 **a category named for what it contains says nothing about its complement** — these
   read as "FP" only because their mnemonics end in `ps`/`pd`, and `xorps` rounds nothing.
   Priced by `python3 scripts/p2_residue.py` (3 gates, selftest 4/4, control first), whose
   third gate re-derives the commission's published sub-group totals from the live census.
   - ✅ **The BITWISE half LANDED as P2 batch 34** — `pandn`/`andnps`/`andnpd` and the
     `ps`/`pd` spellings of AND/OR/XOR, 9 rows, 3,556 instructions.
   - ⭐ **NEXT, and the tool prints it:** the MOVE half — 15 pairs, **7,484 instructions**,
     `movapd` 2,420 · `shufps` 1,545 · `movhlps` 1,341 · `movhpd` 556 · `movddup` 506 ·
     `movlhps` 340 · `movlpd` 274 · `movupd` 113 · `movlps` 101 · `shufpd` 70 · `unpcklps` 64 ·
     `movmskps` 53 · `unpcklpd` 45 · `unpckhps` 40 · `unpckhpd` 16. No rounding, no new state.
     ⚠️ Two of them are NOT their integer siblings: `shufps` takes two lanes from the
     destination and two from the source (unlike `pshufd`, which takes four from one source),
     and `shufpd` selects one from each. The rest are moves and interleaves the model already
     expresses. Price the batch by VECTOR COUNT before starting — see the warning below.

   ⛔⛔ **AND A COMPLETE BATCH IS SITTING UNLANDED ON A BRANCH — `p2-batch32-fp-compares`
   (`3a811fb`, 2026-09-05).** It builds `comiss`/`comisd`/`ucomiss`/`ucomisd` — FOUR of
   sub-group A's twelve pairs, 2,256 instructions — with a green differential. It is held off
   `master` by a kernel-cost verdict of **UNMEASURABLE**, whose honest reading was that the
   batch MAY FAIL: `+2,900` on a `24,700` base is `+11.7%` against a `7.2%` budget, and the
   run's spread between repeats of the SAME tree (3,400 ms) exceeded the budget (1,778 ms).
   ⇒ **it waits on a QUIET-BOX measurement and on nothing else.** Neither the P3 commission
   nor this row mentioned it, so "take sub-group A as a batch" was advice to build a third of
   something already built. ⚠️ Its 8 vectors cost ~375 ms each; batch 23's 2 cost ~290. A
   batch's kernel price is set by its VECTOR COUNT, so size the next one against that first.
2a. ⛔⛔ **`vectorCoverage` HAS ROOM FOR ABOUT THREE MORE VECTORS, AND THAT IS ARITHMETIC (D157).**
   Batch 34's delta gate refused on this declaration: `+230.0` against a budget of `260.6`, band
   `±39.2`. At ~11 ms per vector the allowance affords ~24 vectors per batch and batch 34 spent 21.
   ⇒ **the next vector batch on this declaration does not have room, whatever it contains.** The
   move half (item 2) is 15 mnemonics; at both operand shapes that is 30+ vectors and it will not
   fit. Split it, or repair the unit first (item 4).
   ⛔ Do NOT buy repeats to resolve it — D153 measured the spread SATURATING at n≈3-4, and
   `repeats_to_decide`'s "~5 repeats a side" is a `1/sqrt(n)` projection with no floor.
   ⚠️ `X86.Coverage` also refused, at `+0.5` against a `@floor 6` budget with an `±8.5` band. That
   one is item 4 itself and no repeat count fixes it.

3. **The kernel-delta gate** stays the merge gate; the absolute ceilings ride beside every merge as
   readings, never as a gate (helm 2026-09-04 21:42).
4. **The gated unit is noisier than the budget it is gated against** (D141 opened it, D142 settled
   what it is, **D146 refuted the proposed remedy and named a better one**). MEASURED, two runs an
   hour apart on the same box:
   - `kernel_delta.py --base c372d80 --head c372d80` — **the same commit on both sides** — read
     `Tests.Coverage` at −2,150 ms with a ±2,474 band against a 1,980 ms budget, and returned `ok`.
     The instrument invented a difference larger than the allowance it was policing.
   - The same base tree read **27,500 and 24,500** in the two runs, 12% apart, with no code between
     them. Batch 32's whole disputed delta is +1,000.
   - ⛔⛔ **AND THE CLAIM THAT USED TO BE THIS ITEM WAS WRONG TWICE, IN BOTH DIRECTIONS.** First:
     *"a floor is a MINIMUM allowance, so it can only be too generous."* Then, corrected off the
     batch run: *"three units' budgets are under what this box invents."* The control passed all
     three, with bands 3-5× smaller. ⇒ 🔑 **"the box's noise" is not a property of the box**, it
     varies several-fold between runs, and no single run supports a sentence about it.
     [[feedback-a-single-reading-is-about-its-run]]
   - ⇒ The item is NOT "re-derive `@floor`" and NOT "widen a budget". It is: **reduce the variance
     of the measurement, or gate a quantity that has less of it.**

   ### 4a. ⛔⛔ THE HEARTBEAT PROXY IS REFUTED — do not re-open it (D146)
   Heartbeats ARE exactly deterministic (103/103 declarations identical on two runs of one tree),
   and they are **blind to the growth this gate exists to catch**. Planted, in ninety seconds, with
   a checked module whose source is byte-identical across arms and only the data changing:
   `N=2000/4000/8000` → heartbeats **12,084 / 12,084 / 12,084**, kernel `type checking`
   **82 / 229 / 460 ms**. The positive control in the same run (source grows, data held) moves the
   count 12,084 → 225,043, so the instrument is live and is measuring the wrong thing.
   **Heartbeats measure the SOURCE elaborated; the gate measures the DATA reduced**, because
   `decide`'s evaluation is kernel work and the kernel is not charged heartbeats. The corpus agrees
   independently: batches 17 and 18 changed seven `.lean` files each and moved the proxy by
   **−29 and +14 out of 4.9 million**. And `--threads 1` changes a heartbeat count by 0.052%, so
   even the determinism is per-configuration, not per-machine.
   ⚠️ Also settled: **the kernel reference cannot referee a proxy in its present state.** Of the
   eleven adjacent pairs in the history, it resolves **two**, and one of those two changed no
   `.lean` file at all and reads −350 ms.

   ### 4b. ⭐⭐⭐ THE LIVE CANDIDATE: the counter the kernel keeps about itself
   `set_option diagnostics true` reports, per declaration, `[kernel] unfolded declarations` — the
   KERNEL's own reduction counters. On the same synthetic arms it is **exactly linear in the data**
   (`Bool.casesOn ↦ 6,002 / 12,002 / 24,002`), and on the real module its per-declaration ratio to
   kernel milliseconds spans **4.1×** where heartbeats span **63.5×**.
   **The twelve-commit walk is RUN** (`scripts/deterministic_cost.py`, readings committed at
   `docs/deterministic-cost-history-2026-09-05.jsonl`, one pass per commit because the instrument is
   deterministic) — ⛔ **and D148 struck out two of its four columns.** What the walk reports now,
   with the referee delegating to the merge gate's own band instead of a rule it invented:
   ```
                            no-op commits reading   sign agreement,      ms per 1k unit, over
                            EXACTLY ZERO            OWN live pairs       the pairs RESOLVED
     KERNEL unfoldings      5 of 5                  6 / 6  ⛔ and so      7.65  (1 pair of 11)
     elaborator heartbeats  3 of 5  (+20, -8)       7 / 8     does a     22.01  (1 pair of 11)
                                                              CONSTANT
   ⛔ the heartbeat row read `5 / 6` while the header said "6 live pairs" for both: that is
   heartbeats scored over the KERNEL COUNTER's live set. Heartbeats move on 8 of the 11 pairs.
   [[feedback-a-borrowed-denominator-invents-its-own-gap]]
   ```
   ⛔⛔ **THE SIGN COLUMN CARRIES NO EVIDENCE (D148 §1).** Δproxy is positive on all six live pairs —
   this corpus only ever adds work — so the statistic is `sum(Δkernel > 0)` under another name and a
   constant `+1` proxy scores the same 6/6. The walk now prints the null model's score beside it.
   ⛔⛔ **AND THE REFEREE WAS A SECOND RULE (D148 §2)**, `|Δkernel| > summed sweep ranges`, LOOSER
   than the gate this repository merges on and with a measured false positive: it called RESOLVED a
   pair that changes no `.lean` file, where the truth is zero. On the gate's own band it resolves
   **1 of 11** pairs and 0 of 5 no-ops, and the `ms per 1k` figure is the single value 7.65.
   ⭐ **WHAT SURVIVES IS THE HALF THAT WAS MEASURED AGAINST A KNOWN TRUTH**: exact linearity on a
   plant (6,002 / 12,002 / 24,002), five no-op commits at exactly zero across loads 13 → 95, and a
   4.1× cross-declaration ratio spread against heartbeats' 63.5×. Also measured: ~2× elaboration
   cost with diagnostics on (30 s → 62 s for `Tests.Coverage`).
   ⛔ NOT measured: **machine independence** (a prediction until a second machine reads it — the same
   status `ci.yml` gives its ratio budgets), and **no budget has been derived**: a calibration
   resting on one resolved pair is not a second source. **Do not gate on it before that.**
   [[feedback-widening-a-gate-needs-a-second-source]] [[feedback-a-claim-the-vectors-cannot-distinguish]]

   ⭐⭐⭐ **D155 (2026-09-05) — THE WINDOW LIFTS THE FIRST HALF OF THAT BLOCKER, AND REFUTES THE 7.65.**
   `scripts/unfolding_calibration.py` (selftest 7 arms, control first, 5 distinct arms catching a
   plant) reads the SAME walks over WINDOWS instead of adjacent pairs — the join is exact, the same
   twelve commits in the same order, checked before computing. Resolution rises from **1 of 11 at
   k=1 to 4 of 4 at k=8**, so the calibration has dozens of windows instead of one.
   ⛔⛔ **AND THE CONSTANT MOVES BY HALF AS IT STOPS FILTERING ITS OWN EVIDENCE**: 7.65 at k=1 (one
   surviving window), then 2.55/3.23/3.30 entering at k=3-4, settling at **2.39-4.12, median 3.38**
   over the k>=8 rows where EVERY window resolves and nothing is selected.
   ⇒ **D148's 7.65 is the k=1 number, ~2x the unselected value; a budget set from it would have been
   twice too generous.** A ratio computed only over the windows that RESOLVED is computed over the
   windows with the biggest deltas, and a single value carries no denominator to say so. The tool
   prints the resolved FRACTION beside every ratio and marks the rows where it is 1.0.
   ⛔ **THE SECOND SOURCE STILL DOES NOT CONFIRM — SO THIS ITEM STAYS SHUT.** The loaded night never
   reaches full resolution (0 of 1 at k=11), spans **-5.90 to +37.05**, and carries **6 sign
   inversions of 106** where kernel time falls while unfoldings rise (the quiet night: 0 of 96).
   Machine independence remains unmeasured; there is no second machine.
   ⭐ Scored over the SAME resolved set (p90/p10, lower better): **ku 2.66 / 5.42 · heartbeats
   INCOHERENT (p10 negative) · the per-batch null 11.02 / 26.94**. The null is what the merge gate's
   own budget assumes, so the counter predicts kernel cost 4-5x better than the allowance the
   repository currently gates on. One selftest arm exists so the scoring CAN lose, and it does.
   ⚠️ The ten unselected windows OVERLAP and are not ten independent observations.

   ### 4c. ⛔ THE THIRD ROUTE IS MEASURED AND CLOSED (D150) — and its premise was refuted with it
   The profiler's cumulative block reads `tactic execution 47.8s` against `type checking 26.2s`, and
   `user` is 2× `real`: **Lean elaborates this file in PARALLEL and every gated number is a per-task
   WALL-CLOCK reading taken under contention.** `scripts/kernel_cost.py` never passes
   `lean -j/--threads`, so it takes the default. `--threads 1` changes how the SAME quantity is
   measured rather than which quantity is gated, so no budget is derived from the thing it checks.
   **`scripts/threads_ab.py`** runs it: two arms, interleaved A,B / B,A by round over four gated
   units, every reading carrying its own load, a positive control in the same run (a plant whose
   DATA is 4× bigger must read ≥2× bigger in EACH arm, or that arm's low variance is the variance of
   an instrument that stopped responding), and **three quantities from the same passes** — the gated
   `type checking`, the child's `user` CPU time, and its `real` wall time. `kernel_cost.py` profiles
   ONE MODULE PER `lean` PROCESS, so `user` is already a per-unit quantity: if it is materially
   quieter than the gated number, that is a fifth route measured for free. Selftest: 8 arms, green.
   ⭐ **RUN, 60 readings, `docs/threads-ab-2026-09-05.jsonl`; five sealed predictions scored 3/5.**
   `--threads 1` moves the gated LEVEL to **0.76x** and the spread from CV 23.7% to 17.2%, for
   **1.62x the wall time**. A real effect in the predicted direction that does not solve the
   problem: an instrument still swinging 17% cannot police a 7% budget. **Route closed.**
   ⛔ **AND ITS PREMISE WAS REFUTED.** *"`user` is 2x `real`, so Lean elaborates this file in
   PARALLEL"* — per reading the default arm's u/r was **1.01, 1.17, 1.66, 1.50, 1.17**, median 1.17.
   It reaches 1.66 only when the box has cores free. *"user is 2x real" is a property of Lean plus
   IDLE CORES, quoted as a property of the code.* [[feedback-a-single-reading-is-about-its-run]]

   ### 4d. ⛔⛔ REFUTED (D152) — the 14.6x does not reproduce; see the verdict block below
   `kernel_cost.py` runs **one `lean` process per module**, so `getrusage(RUSAGE_CHILDREN)` yields a
   **per-unit CPU time** at zero extra cost. Five profiles of ONE tree, `Tests.Coverage`:
   ```
     profiler `type checking`   51,400 / 42,700 / 28,900 / 31,000 / 42,700 ms   range 52.7% of median
     child `user` CPU               56.99 / 58.05 / 55.98 / 56.69 / 57.24 s     range  3.6% of median
   ```
   ⇒ the gated number's spread on one tree is **22,500 ms against a 1,764 ms budget — 12.8x the
   allowance it polices**; the CPU time from the same invocations is **14.6x tighter** in relative
   terms, and quieter on **12 of 12** subject-arm pairs with the plant control passing for it in
   both arms.
   ⛔ **Three things before anyone gates on it.** (1) It changes WHAT is gated, not how it is
   measured — `user` is elaboration AND kernel, so every budget needs re-derivation **from a second
   source**, never from these readings. (2) It is quieter, not deterministic: 3.6% is not 0%, and
   the kernel-unfolding counter (4b) is still the only candidate that reads exactly zero on a no-op.
   (3) Machine independence unmeasured, as for every candidate.
   ⇒ **THE RANKING FOR THE NEXT HEAD**: 4d is cheapest and biggest (no new instrument, 14.6x);
   4b is the only deterministic one but needs a budget and a second machine; 4c is closed.
   - ⚠️ Any budget re-derivation must still come from `docs/kernel-delta-history-2026-09-04.jsonl`.
     Deriving one from the runs above would be deriving the allowance from the thing it checks.
     [[feedback-widening-a-gate-needs-a-second-source]]

   ### 4d-VERDICT. ⛔⛔ DO NOT ADOPT `user` CPU (D152, 24 readings, 12 trees)
   ```
                          ms rel%   user rel%   rel x     ms abs   user abs   abs x
     Tests.Coverage          2.69        2.05    1.31      600ms     1159ms    0.52
     Tests.Anchors           3.87        5.00    0.77       20ms      120ms    0.17
     median, all units       4.82        3.41    1.41        2ms       16ms    0.14
   ```
   **D150's 14.6x does not reproduce, not even on `Tests.Coverage` where it was measured** — that
   evening the SHIPPED arm swung 52.7% on one tree; on the completed walk it swings 2.69% on the
   same tree. A ratio between two instruments is a reading of the worse one's night.
   ⛔ And `real_s` (the CONTROL) is as tight as `user_s`, so the small advantage is measuring the
   WHOLE PROCESS, not CPU accounting — which refutes the mechanism as well as the size.
   ⇒ a 1.3x relative gain, NEGATIVE in absolute terms, on 19 of 23 units, is not worth re-deriving
   every budget in the repository from a second source. **4b (the kernel unfolding counter) is the
   only surviving candidate.**

   ### 4f. ⭐⭐⭐ PRICED (D153) — the repair is the WINDOW and it is free; repeats SATURATE at n≈3-4
   D152's finding — the gate resolves changes the size of its own noise — is priced on the one axis
   both untried repairs move: **R = band / allowance** (`R < 1`: the instrument can see a change the
   size of the change the gate is willing to PERMIT). Tool: `scripts/delta_repair_price.py`, which
   IMPORTS the gate's own rules (selftest 10 arms, unplanted control first, 8 distinct arms catching
   plants). Corpus: the TWO independent walks over the same twelve commits 23 h apart, plus 16
   readings of one frozen tree (`docs/repeat-scaling-2026-09-05.jsonl`).
   ```
     median R over the 23 gated units    09/04 (load 4.5) 0.21    09/05 (load 12.3) 0.29
     units that cannot resolve their allowance        0%                       18%
   ```
   ⚠️ The two nights disagree about whether the gate works — same trees, same instrument.

   ⭐ **REPAIR B (accumulated multi-batch drift) — RECOMMENDED, free, and the only one that raises
   resolution.** Over k=1→11 the allowance grows **11.4x / 11.2x** while the band moves only
   **1.01x / 1.43x**, so R falls to **0.11x / 0.23x**. The loaded night's refusal rate falls
   17% → 6% → 3% → 1% → 0% at k=1..5. It costs **no extra profiling** — the gate already reads two
   trees, they are just further apart — and pays in LATENCY (caught k batches late) and ATTRIBUTION
   (a window, not a commit).
   ⛔ Its premise needed correcting and survives: the band is NOT k-independent (1.43x on the loaded
   night — trees at the ends of a longer window differ in LEVEL and the spread travels with it).
   The true claim is that the allowance grows an order of magnitude faster.
   ⛔⛔ **Both walks return ZERO `OVER` at every k** (the twelve commits landed), so the corpus
   measures REFUSAL and never DETECTION. The lever is demonstrated on a plant sized to the band in
   closed form: a corpus over budget every batch is UNMEASURABLE at k=1 and k=2 and **CONVICTED
   9 of 9 at exactly the predicted k=3**. [[feedback-an-implied-assertion-is-not-a-second-gate]]
   ⚠️ Arithmetic limit, since the R numbers hide it: with the allowance SUMMED per step, the drift
   gate cannot convict where the per-batch gate passes. Its power is entirely over what the
   per-batch gate REFUSED (17% on the loaded night) ⇒ a SECOND gate beside the first, not a
   replacement.
   ⛔⛔ **THE CHEAP SPELLING IS REFUTED.** Caching the anchor instead of re-profiling it halves the
   work and **manufactures 9 convictions the same-session comparison calls `ok`** (OVER 0 → 9;
   UNMEAS 43 → 71) — regressions made out of the difference between two nights, judged by a band
   that does not know the nights differ. Re-profile the anchor.

   ⛔⛔ **REPAIR A IS NOT A RESOLUTION REPAIR — the spread SATURATES.** `repeats_to_decide` models
   the band as falling like `1/sqrt(n)` without limit, so it always names a finite N. Measured on
   16 readings of one frozen tree, `rms |d|` over all splits:
   ```
                              n=1     n=2     n=3     n=4     n=6
     Tests.Coverage         585.9   326.7   104.4   104.1   109.5     <- flat from n=3
     1/sqrt(n) would give   585.9   414.3   338.3   293.0   239.2
     @decl vectorCoverage   131.3   105.0    25.4    16.2    17.0     <- flat from n=3
     X86.Theorems           213.7   124.0    51.9    39.2     7.7     <- still falling
   ```
   n=2→3 falls FASTER than the model (the median starts rejecting outliers — this run has a 25,800
   reading against a level of 23,800); past n≈3-4 it FLATTENS on the units with the most at stake.
   **The projection cannot express a floor, so it keeps naming N for a question no N answers.**
   ⛔ And its headline number is the wrong one anyway: the worst case on the 09/05 walk asks for
   **587,413 repeats a side (32,210 h for one merge)** with a margin of **+4.4 ms against a budget
   of 1,695.6** — a commit on its line, a fact about the commit, not the instrument. Margin-free:
   the QUIET night needs **none**; the loaded night has 45 of 253 cases with R>=1, p90 = 19 a side
   = 63 min a merge. ⇒ its price is set by the night, not the code.
   ⛔ `repeats_to_decide` returns `max(n + 1, ceil(need))`, so it can never report "fewer than
   three" or "none" — over an already-resolved corpus it prints a median of 3, the function's floor
   wearing a price's clothes.

   ⭐⭐ **What repeats DO buy is BAND HONESTY at small n** — on a frozen tree the true delta is 0, so
   every `|d|` is the gate's own error (a nominal 2σ band should be exceeded ~4.6%):
   ```
       order        n    obs    |d| > band    worst |d|/band
       block        2    273    35 (12.8%)             9.03
       block        3    231    16 ( 6.9%)             1.89
       block        4    189     8 ( 4.2%)             1.26
       alternate    2    273    35 (12.8%)             7.58
       alternate    4    189     7 ( 3.7%)             1.47
   ```
   The mechanism is serial DRIFT, not quantization (checked and refuted: the only exactly-zero bands
   are `X86`/`Tests`, the content-free aggregators). Signature: `X86.Memory` base [13.0, 13.1] head
   [11.4, 11.5] — each side tight, the sides 1.6 apart, tracking load 16 → 9 across the run.
   ⛔ The gate's ALTERNATED order and a block split are INDISTINGUISHABLE at m=16 (12.8/12.8,
   6.9/6.5, 4.2/3.7). Read at m=8 this looked like "alternation is worse at n=3 and n=4" on cells of
   6 and 1 events; it is not.
   ⚠️ n=2 runs in the history walks and in `--selftest-measure` (CI passes `--repeats 2`). The MERGE
   gate defaults to 3 (`kernel_delta.py:1185`) and CI runs 6, so the gate itself sits inside
   `delta_band_calibration.py`'s swept range — which starts at n=3 and draws i.i.d. Gaussian, and so
   cannot see any of the above.

   ⇒ **THE NEXT STEP, AND IT IS A BATCH, NOT A TACK-ON**: build the drift gate beside the per-batch
   gate (anchor policy, summed accumulated allowance, its own red probes). Do NOT buy repeats for
   resolution. **⭐ BUILT 2026-09-05 as D154 — see 4g.**
   ⛔ Portability unmeasured, as for every candidate in item 4. One box, arm64. The frozen-tree run
   is ONE session on ONE night and its n=6 column rests on five splits.

   ### 4g. ⭐⭐⭐ THE DRIFT GATE IS BUILT AND REGISTERED (D154) — what is left is RECORDING, not design
   `scripts/kernel_drift.py`: a SECOND gate beside the per-batch gate, judging a window of k landed
   batches against the SUM of the per-step budgets, read from `docs/delta-allowance-ledger.jsonl`
   (11 steps x 23 units backfilled from the 09/04 walk). Selftest **16 arms, control first, 9
   distinct arms catching a plant**; the ledger's derivation and `delta_repair_price.py`'s ten arms
   are now on the CI gate list too — the latter had never run there at all.
   ⛔⛔ **THE `k x one budget` SPELLING IS WRONG IN BOTH DIRECTIONS**, and the reason first written
   for forbidding it was wrong: over the walk's 1,518 cases, **468 (30.8%) sum > flat** (too tight)
   but **187 (12.3%) sum < flat** (too GENEROUS — it acquits accumulated drift). The trees do not
   only grow, so "it can only over-convict" was false. The selftest plants BOTH directions.
   ⚠️ **~48% of gated cases are FLOOR-BOUND** (percentage under `@floor 6`), so the two spellings are
   identical by construction on half the corpus and the median ratio is 1.0000 at every k. That also
   means half the units are gated by an ABSOLUTE millisecond number while the budget file's header
   argues *"the units are percentages BECAUSE a percentage travels"* — a finding about the REGISTRY,
   not about this gate, and not yet acted on.

   **WHAT IS LEFT, in order:**
   (a) **`--record` at merge.** The gate is free only if the per-batch gate writes each step's
       allowance as it lands; until then every window is backfilled and RETROSPECTIVE. One call to
       `kernel_drift.py --record --readings <the blob `kernel_delta --out` already writes>`.
   (b) **Choose k and register the window as a check.** k is a latency/attribution trade, not a
       resolution knob: refusal falls 17% → 6% → 3% → 1% → 0% at k=1..5 on the loaded night.
   (c) **A measured window on real trees** beyond the k=2 receipt in D154 §8.
   ⛔ It CANNOT convict where the per-batch gate passed — its whole power is over what that gate
   REFUSED. Never propose it as a replacement.

   ### 4e. ⛔⛔ 4d's DECIDING STATISTIC HAD A PREMISE, AND THE CONTROL BESIDE IT REFUTED IT (D151)
   "14.6x tighter" cannot decide a gate, because **a percentage of `user` is not a percentage of
   kernel time**: `user` charges Lean's startup, import loading and elaboration too, so on
   `Tests.Coverage` it is a ~57,000 ms number where the gated one is ~25,000 ms and on a small
   module it is almost all constant. The comparison was therefore re-cast as MINIMUM DETECTABLE
   REGRESSION, `budget% x level`, in milliseconds — and THAT carried an assumption, written into the
   code as "doing work": that X ms of extra kernel work adds about X ms to the child's CPU.
   ⭐ **Measured on the first run that printed both: `Δuser/Δms` is 8.3, not 1.0.** A real change
   moves the child's CPU several times the milliseconds it moves `type checking`, because it moves
   elaboration too. A candidate whose budget is 3x larger but which hears the signal 8x louder is
   MORE sensitive, and the uncorrected table said the opposite in 16 of 23 rows.
   ⇒ the deciding column is `MDR / transfer`, and on the contended corpus the answer is
   **better 1 · worse 2 · UNDECIDED 14 · inexpressible 6** — i.e. **that corpus cannot decide the
   item**, because 106 of 114 pairs sit below the ms noise floor and no transfer ratio exists for
   most units. A quiet re-walk is what decides it.
   [[feedback-audit-the-premise-of-a-right-decision]] [[feedback-the-burden-is-on-the-departure]]

   ⛔ **AND FOUR OF THE TWENTY-THREE GATED UNITS ARE NOT EXPRESSIBLE BY THE CANDIDATE AT ALL** —
   `Tests.Coverage @decl x3` and `@residue`. `getrusage` accounts per PROCESS and `kernel_cost.py`
   runs one process per MODULE, so no re-run of any walk will ever supply a per-DECLARATION CPU
   time. A hybrid gate leaves the three tightest per-declaration budgets on the noisy instrument.
   This is structural, not a gap in the corpus. [[feedback-unobserved-regions-report-agreement]]

5. **Arm 1's number is gated — DISCHARGED (D145).** The identical-trees control's invented delta
   now splits in two: an ASSERTION that it sits inside the run's own band (a difference the run
   cannot explain as its own noise is a BIAS, box-independent, and reds), and a printed SCOPE list
   of the budgets it does not clear today (asserting that would red on a busy box, which is the
   defect D141 removed from this same arm). Four planted defects caught, two of them only by the
   new requirement that each case declare the LINE it must print and not just its verdict.

6. **`--repeats` in CI is a guess** (D141 §9). `.github/workflows/ci.yml` asks for 6 on a runner no
   delta has ever run on. The first job that completes there prices it, and the number to read off
   is the gate's own `~N repeats a side would decide it` line. Blocked: GitHub Actions refuses every
   job on this account for billing (desk FH).

7. **The gate's conditions line records a LOAD and that is not enough (D149).** · **DISCHARGED (D151)** Measured this
   sitting: a 1-minute load of 282 with `top` reading **0.0% idle**, 44% user / 55% SYSTEM, and one
   `lean` at 160% CPU — the load was dominated by short-lived runnable processes, not by compute, so
   readings taken at "load 282" and at "load 40" can describe the same machine. `threads_ab.py`
   already records **idle %** beside the load and returns `None` rather than a default when it
   cannot read it. `scripts/kernel_cost.py` and the history walk still record load alone; porting
   the field is additive to their JSONL and cheap. ⚠️ It changes no verdict — it makes the
   conditions of every future reading comparable, which is the whole reason D142's two afternoons
   could not be told apart. [[feedback-a-measurement-without-its-conditions]]

8. **A timing run must first look for the seat's own orphans (D149).** · **DISCHARGED (D151)**
   ⚠️ Discharged with a caveat the discharge itself produced: the pre-flight runs BEFORE a run, and
   **stopping a job is where orphans are made**. Killing the walk at the helm's word left an
   orphaned `lean` holding a deleted worktree — the exact class this item names, produced forty
   minutes after the check that detects it shipped. A post-flight is not yet written. A `ci_local --job build`
   from a dead session was found running 47 minutes with ppid 1, and no instrument this seat owns
   could see it. The cheap form is a pre-flight in `kernel_cost.py` / `kernel_delta.py`: list
   processes whose cwd is this repository and whose session is gone, and REFUSE (or record them in
   the reading) rather than profile beside them. ⛔ Attribute by cwd, never by command name, and
   never `pkill -f` a pattern the seat's own tools carry.
   [[feedback-enumerate-is-not-attribute]] [[feedback-a-process-filter-matches-its-own-waiter]]

9. ⛔⛔ **WITHDRAWN THE SAME EVENING IT WAS FILED — "the budgets rest on a day 7.30x quieter" was
   an artefact of a 14-reading CONTENDED partial corpus (D151).**
   Filed at 21:0x off the interrupted walk (n=42 unit-readings, one of them taken at load 98) and
   posted on the bus TWICE as "already firm". The completed 24-reading walk over the same twelve
   commits reads **4.82% against the 09/04 corpus's 3.51% — 1.37x, not 7.30x.**
   ⇒ the shipped budgets do NOT rest on an unrepresentatively quiet afternoon. There is nothing to
   act on here, and the row is kept only so the withdrawal is as findable as the claim.
   🔑 **I called a number firm off a partial corpus while my own tool's comment beside it said "one
   extra pair of days, not a distribution over days."** The discipline was written down and not
   applied to the sentence I was writing at the time.
   [[feedback-a-single-reading-is-about-its-run]] [[feedback-ungated-prose-overclaims]]

10. **A post-flight orphan check, and a contention count in every reading (D151).** ⭐⭐⭐ **DONE
    (D156, 2026-09-05)** — `python3 scripts/kernel_cost.py --post-flight`, rc 0 nothing of mine ·
    1 my orphans survive · **2 the probe could not look** (never a clean bill). It REPORTS and never
    kills: every seat on this box runs identical command lines from identical paths, so a
    name-matched sweep at one seat's exit selects the whole fleet's watches — math came one command
    from that at 22:45 and its six hits included this seat's own watch (pid 91614).
    ⛔⛔ **AND BUILDING IT FOUND THE PROBE LOOKING IN THE ONE PLACE A KILLED TIMING JOB NEVER LEAVES
    AN ORPHAN.** `foreign_builds` excluded temp trees by the substring `"x86lean-history"` — ONE of
    the **thirteen** `mkdtemp` producers in `scripts/`; the merge gate and the drift gate use
    `x86lean-delta-`. Measured with a real process per prefix and both controls: history excluded,
    delta counted, budgetprobe counted, a genuinely foreign tree counted. Since `kernel_cost.py`
    does `os.chdir(root)` and the delta gate passes `--root <worktree>`, an orphaned profiler was
    **invisible to `repo_orphans`** (whose test was cwd == the repo root, exactly) **and counted as
    someone else's build** — the one class item 10 exists to catch, misfiled by both probes in
    opposite directions.
    ⇒ `_own_tree()` is now the single decider: the repo · the MAIN tree seen from a worktree (else
    the repository counts as foreign while its own gate profiles a worktree of it) · a STRUCTURAL
    name-free test (a worktree of this repo carries a `.git` FILE whose `gitdir:` points into this
    repo's common git dir) · and last, a name fallback **only where the directory is GONE**, the one
    case nothing structural survives. An arm reads every `mkdtemp(prefix=…)` in `scripts/` and
    requires the convention or a DECLARED fixture (stale declarations refused too).
    ⛔ The first spelling of that fallback claimed every `x86lean-*` temp dir and reddened a correct
    pre-existing arm whose fixture deliberately impersonates a foreign tree; the refusal named the
    narrower rule.
    ⭐⭐⭐ **AND THE REPORT ITSELF HAD TO BE CORRECTED: "ppid 1" IS NOT "ORPHANED".** In production it
    caught three real orphans by pid — and, between two of them, labelled **this seat's own live,
    running selftest** an orphan, because `nohup … &` reparents a wanted job to init exactly like a
    stranded one. Three right readings pre-endorsed the fourth. ⇒ `repo_orphans` never names the
    CALLING process, and the report states the ambiguity instead of asserting an orphan. It kills
    nothing; killing is by pid after confirming the process is unwanted.
    ⭐⭐ **AND THE NEW PROBE CAUGHT THE SELFTEST MANUFACTURING ORPHANS — in two arms that PREDATE
    it.** The fake-`lean` fixture was `#!/bin/sh` + `sleep 40`, so `Popen` started the SHELL and the
    `sleep` was its child; killing the shell reparented the sleep to init for 40 s. Measured: sh
    54864 → child 55138, and 55138 survives the kill with ppid 1. Fixed with `exec sleep 40`.
    🔑 A cleanup that kills a WRAPPER has not killed the work, and the leak was invisible to any
    later check because the fixtures expire.
    ⚠️ `kernel_cost.py --selftest` is a LONG gate (>10 min; it profiles real trees) and is
    deliberately not in `ci_local`'s portable list.

## P3 — THE SOFT-FLOAT COMMISSION · **OPEN, FROZEN, PARTLY REFUTED**
`docs/SOFT-FLOAT-COMMISSION.md` — opened 2026-09-05, with its premise tested at the object, its
scope re-measured, and a refuter pass run against it in the same sitting.

```
40 (mnemonic, bucket) pairs, 36,925 instructions   (the figure carried since batch 19 was 25,688)
   A   no rounding at all              12 pairs   6,619   17.9%   BUILDABLE — K1 verified
   A′  fixed mode, MXCSR.RC-free        2 pairs     898    2.4%
   B   MXCSR.RC-dependent              26 pairs  29,408   79.6%   un-priced, deliberately
```
**Recommendation on the record:** take sub-group A as an ordinary P2-shaped batch; leave B frozen
until kill-checks K3 (what a new `Cpu` field costs every record proof) and K4 (what a soft-float
`mulsd` costs the kernel) are *measured*. B's price is not stated here because it has not been
measured, and inventing one would repeat exactly the defect §2 of the commission records.

## DEFERRED, by ruling — not by silence
- **Arm C, the K-backed second oracle** — DEFERRED at the council (minute 2026-09-05 item 2(a)).
  The condition of the deferral is that **the hole is printed beside every coverage number**.
- **A public remote** — gated on the Captain's IARC approval (desk ET). The scrub gates are ported
  before any push to a public remote; commit hygiene has been clean from commit 1.
