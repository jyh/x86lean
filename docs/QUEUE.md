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
THE UNASKED REMAINDER    171 pairs / 16,791 instructions      (was 172 / 18,032 before batch 33)
   x86isa IMPLEMENTS       0 pairs /      0
   x86isa DOES NOT       171 pairs / 16,791
   NOT RESOLVED            0 pairs /      0
```
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

   ### 4d. ⭐⭐⭐ THE LIVE CANDIDATE, AND IT WAS ALREADY IN EVERY PASS (D150)
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

9. ⭐⭐ **THE SHIPPED BUDGETS REST ON A QUIETER DAY THAN AN ORDINARY ONE (D151).** Measured, not
   inferred: the SAME tool over the SAME twelve commits, re-walked on 09/05, reads a median
   within-commit spread of **25.63%** against the 09/04 corpus's **3.51%** — **7.30x** — and the
   09/04 corpus is the one `scripts/kernel_delta_budget.txt` is derived from
   (`user_cost_budget.py --readings NEW --baseline docs/kernel-delta-history-2026-09-04.jsonl`).
   ⛔ This is a finding about the GATE and it is independent of every candidate: whatever quantity
   ends up gated, a budget calibrated on an unrepresentatively quiet afternoon is tighter than the
   instrument supports on an ordinary one.
   ⚠️ ⛔ **AND IT IS NOT A LICENCE TO WIDEN.** Re-deriving the budgets from the noisier corpus would
   be deriving the allowance from a measurement of contention, which is the same defect one level
   out. Two readings of two days are not a distribution over days.
   [[feedback-widening-a-gate-needs-a-second-source]] [[feedback-a-single-reading-is-about-its-run]]

10. **A post-flight orphan check, and a contention count in every reading (D151).** The stamp half
    is DONE — `conditions()` now counts `lean`/`lake` processes whose cwd is OUTSIDE this repository
    and sets `contended`, so the helm's rule of 09/05 (*a reading taken under contention must be
    marked CONTENDED in its own receipt*) is enforced by the tool rather than by whoever writes the
    receipt. What remains is the POST-flight: re-run the orphan probe after a job is killed, since
    that is when orphans are made.

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
