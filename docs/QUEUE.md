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
THE UNASKED REMAINDER    172 pairs / 16,879 instructions   (2026-09-06, after batch 35)
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

0. ✅✅ **DISCHARGED 2026-09-08 (D177) — (a), (b) AND (c) ALL LANDED, AND THE DEFECT HAD FOUR MORE
   HOMES THAN THIS ITEM NAMED.** The buildable residue is now **0 pairs / 0 instructions**, derived
   rather than predicted. `measure_cr4` gained the stall test — and the OBVIOUS port of `measure`'s
   regex would have re-created D170's defect inside the repair for D170, because that sibling reads
   the DRIVER's hex output while this one prints in ACL2's ambient base, **measured to be 10**; RIP
   is now printed twice, the second copy computed in ACL2 as a base-independent 0/1, cross-checked
   every record. The sealed rows are **byte-unchanged**; `REFUTED_BY_MEASUREMENT` records the
   refutation beside them and `p2_run` scores against the RECORDED MEASUREMENT, so a row that starts
   executing tomorrow goes red rather than being excused. The cross-table gate joins on **bytes**,
   not names (a mnemonic legitimately differs by bucket), reports **VACUOUS** on an empty domain,
   and its measured reach is **1 shared encoding of 18 vs 227 mnemonics** — its whole domain is its
   own founding case, which is stated rather than left implied.
   ⭐ **THE SWEEP FOUND TWO MORE STALLING ROWS**: `vmovmskps_v` (the sibling nothing asked about) and
   **`emms`**, declared `(executes, executes)` and stalling under BOTH CR4 arms — found ONLY by the
   full 267-row run, not by the four-form probe that confirmed the other two
   ([[feedback-a-batch-cannot-be-sampled]]).
   ⛔ **AND THE SAME RESIDUAL HAD FIVE HOMES, OF WHICH THIS ITEM NAMED ONE**: the classifier;
   `oracle_note`, which rendered a stall as **"⚠️ not measured"** — the exact string that
   re-commissions the work D170 refuted; BOTH of `p2_roster`'s accountings, which published it as
   **"the oracle REFUSES"**; and `p2_residue`'s `NO_ROUNDING`, which called it **BUILDABLE TODAY**.
   ⇒ 🔑 **A CONSERVATION GATE CANNOT SEE A MISCLASSIFICATION, ONLY A LOSS** — the by-bucket totals
   conserved perfectly while 77 instructions sat under the wrong verdict.
   ⚠️ **`docs/P2-ROSTER.md` was ALREADY stale at HEAD** (committed `EXECUTES 106` vs derived `107`,
   measured with the change stashed); that drift and D177's own −2/+2 are recorded separately in
   D177 so neither is attributed to the other. All seven gates rc=0; no `.lean` changed.
   *(The original statement follows, unedited.)*

   ⛔⛔⛔ **THE AVAILABILITY CENSUS STILL ANSWERS "EXECUTES" FOR `movmskps`, AND THAT IS WHY TWO
   CARRIERS COMMISSIONED A BATCH THAT WOULD UNDO D170.** Opened 2026-09-08 by paris, measured at
   the object, no ACL2 run needed — the whole finding is readable in `scripts/oracle_availability.py`.

   **What the record already says.** D170 measured `movmskps` STALLING on x86isa (88/88, RIP never
   advanced, refused-flag CLEAR) and ruled that the model KEEPS `VMovMskKind.ps`, its semantics and
   its five anchors but does **not** claim it, *because a roster row here means differentially
   tested*. `FORMS` (line ~95) carries `("movmskps", …, "stalls")` with that reasoning in full.

   **What is still live.** D170's three-valued repair landed in `FORMS` and **not in `P2_FORMS`**,
   which is the table the availability answer is actually built from:
   ```
   line   41   measure_cr4:  got[tag] = "refuses" if refused == 1 else "executes"
               ⇒ NO RIP TEST, NO STALL STATE — the two-valued classifier D170's own
                 headline condemns, 850 lines above the row that condemns it.
   line  917   P2_FORMS:     ("movmskps", "movmskps %xmm1, %eax", "0f50c1", "refuses", "executes")
   line 1680   the (mnemonic, bucket) availability map is built from **e1** — that "executes".
   ```
   `movmskps` is **not** in `NOT_AN_AVAILABILITY_QUESTION`, so nothing excludes it; and **no gate
   compares `FORMS` against `P2_FORMS`**, so one file declares `stalls` at line 95 and `executes`
   at line 917 and nothing has ever looked at both.

   ⇒ 🔑 **THE CENSUS IS THE THING THAT ANSWERS "WHAT CAN WE BUILD", SO A DEFECT LEFT IN THE CENSUS
   TABLE BECOMES A WORK ORDER.** The "1 pair / 53 instructions buildable" residue, the bank's §5
   "violation", and the relight gate's ⭐ *"claim `movmskps` — the WHOLE buildable-today residue"*
   are all one reading of `e1`. Acting on it would have re-added the roster row D170 removed.
   ⇒ 🔑 **AND A FORM'S ABSENCE FROM A ROSTER IS EVIDENCE OF NOTHING UNTIL YOU READ THE DECISION
   THAT PUT IT THERE.** The absence looked like an escape because the reason lived in a different
   document — the same shape as this queue's own owed-item refutations, one level up.

   ⚠️ **`P2_FORMS` IS NOT SIMPLY WRONG AND SAYING SO WOULD MISS THE POINT.** Under `measure_cr4`'s
   vocabulary "executes" is a TRUE statement about the refused flag and a FALSE statement about the
   world. The defect is the classifier's VALUE SET, not the row
   ([[feedback-a-classifiers-value-set-is-a-claim]], the card written FROM D170 — and the defect it
   names survived in the sibling table, which is [[feedback-naming-a-defect-is-not-finding-its-siblings]]:
   grep the same file for the same shape before writing the decision note).

   **THE REPAIR, ORDERED, AND WHY IT IS NOT DONE HERE.**
   (a) `measure_cr4`'s emitted ACL2 form must print RIP as well as `flg`/`refused`, and the
       classifier must gain the stall test `measure` already has (compare against `ENTRY_RIP`).
       ⛔ **This needs an ACL2 run to verify and the box is at load 10.15/14 against a quiet 4.5,
       with SaltBench holding precedence — so it is NOT started rather than started unverified.**
   (b) only then can `P2_FORMS`'s `movmskps` row declare `stalls` and be MEASURED as such.
       ⚠️ That row is inside the block SEALED at `sha256 = 6e8474ff…`, 2026-09-05T20:02:18Z. The
       seal is enforced by NO gate (it appears only here and in D170's neighbourhood), so the
       question is integrity, not mechanism: **record the sealed declaration's refutation, do not
       retro-fit it.** A seal exists to stop a declaration being fitted to a measurement; D170's
       measurement came AFTER, and refuting a sealed row is the honest outcome, not a violation.
   (c) a cross-table gate — `FORMS` and `P2_FORMS` must not declare contradictory verdicts for the
       same mnemonic. **Pure string work, microseconds, the `p2_structure_check` precedent**, and
       it is the gate that would have caught this on the day D170 landed. ⛔ It goes RED on the
       shipped tree today, so it lands WITH (a)+(b) and not before — a gate landed with its one
       real violation filed as an exception is [[feedback-a-declared-list-inherits-its-default]].

   ⛔ **UNTIL (a)–(c) LAND, `movmskps` IS NOT AVAILABLE WORK AND THE RESIDUE IS NOT "1 pair".**
   Any head reading a buildable-today count that includes it is reading `e1`.
   ✅ **(a), (b) and (c) LANDED 2026-09-08 (D177). The residue is 0 pairs, derived.**

0b. ⚖️ **(7) DISCHARGED 2026-09-08; (6) STILL OPEN.** The sweep that verified D177's "five homes"
   found two more. **(7) `claimed_forms.py`'s `UNAVAILABLE` now reads `{refuses, stalls}`** — a
   repair to the RULE that moves **no published number** (verified: the tool's whole 261-line output
   is BYTE-IDENTICAL before and after, because no `movmskps` row reaches `rows` at all). It ships
   with a **build-free arm**, `--check-unavailable-rule`, run first inside `selftest` so it fires
   even when the Lean build is unavailable — the rule is pure string work and an arm behind a build
   is a discipline nobody exercises ([[feedback-make-the-probe-cheap]]).
   ⛔ **THE ARM'S FIRST FIXTURE WAS ONE-DIRECTIONAL AND SAID NOTHING ABOUT IT.** Its only `executes`
   row was `CONTROL:mov`, which the CONTROL filter drops whatever the rule says — so an OVER-BROAD
   rule passed untouched. Measured before the fix: narrow-rule arm CAUGHT, over-broad arm **NOT
   CAUGHT**. A non-CONTROL `executes` row (`paddd`) was added and all three drives now fire.
   ⇒ 🔑 **A CONTROL EXCLUDED BY A DIFFERENT FILTER CANNOT WITNESS THE RULE UNDER TEST**
   ([[feedback-a-control-can-share-the-blind-spot]]).
   ⛔ **(6) `check_driver_cr4.py` REMAINS OPEN and is NOT to be patched unverified.** It wants an
   ACL2 run, and the seat that found it had released the box to systems with an explicit commitment
   not to re-take it. Patching a gate's classifier without executing it is exactly what item 0(a)
   refused to do. **RELEASE: any sitting with oracle access. OWNER: the next paris head.**

   *(the original statement follows)*

   ⛔ **THE SWEEP THAT VERIFIED D177's "FIVE HOMES" FOUND TWO MORE, AND D177 IS THEREFORE AN
   UNDER-CLAIM.** Opened 2026-09-08 by paris immediately after D177 landed, by grepping the
   defect's SHAPE repo-wide rather than trusting the note
   ([[feedback-a-sibling-sweep-inherits-its-scope]]). No ACL2 run needed; both are readable.

   **(6) `scripts/check_driver_cr4.py` — the same two-valued classifier, LATENT.** Its counter is a
   2-tuple `e, r = res.get(cur, (0, 0))` with **no stall state**, and its verdict is
   `refuses if r == n else executes if e == n else MIXED`. A stalling form in its list would be
   scored `executes` — D170's defect exactly. **It is unpoliced BY LUCK: its `FORMS` list is six
   rows (`movdqa`, `paddd`, `movdqu`, `pxor`, and two CONTROLs) and contains none of the three
   known stalling forms.** ⇒ 🔑 **A DEFECT ABSENT ONLY BECAUSE THE INPUT SET HAPPENS TO EXCLUDE IT
   IS NOT FIXED, AND THE NEXT ROW ADDED TO THAT LIST IS WHAT DECIDES.** This is the gate that
   certifies the differential runs at CR4=0x600, so a wrong verdict here misprices every run below it.

   **(7) `scripts/claimed_forms.py`'s `UNAVAILABLE` — under-inclusive, live.** It is built by regex
   over `FORMS` selecting `exp == "refuses"`, so a `stalls` row is excluded. **Measured: 18 rows
   parsed, 10 in UNAVAILABLE, and `movmskps` — the one form in `FORMS` the oracle demonstrably
   cannot run — is NOT among them.** The set whose whole meaning is "the oracle cannot run this"
   excludes the clearest member of it.
   ⚠️ **The gate passes rc=0 today**, so nothing is currently mis-reported; this is recorded as a
   defect in the RULE, not as a live wrong number. ⇒ 🔑 **AN UNDER-CLAIM IS THE UNPOLICED
   DIRECTION** — an over-claim looks like a mistake and an under-claim looks like caution
   ([[feedback-under-claims-are-unpoliced]]).

   ⛔ **NOT FIXED IN D177 AND THE REASON IS SCOPE, NOT DIFFICULTY.** Both were found while a
   profiling run for `es3-anchor-theorems` was in flight; the landing ritual needs a clean tree, and
   starting two more repairs mid-flight is how a merge ritual acquires an unrelated diff. (7) is
   pure string work. (6) wants an ACL2 run to verify, like 0(a) did.
   ⇒ **REGISTERED HERE, ON A SWEPT SURFACE, RATHER THAN LEFT IN THE BUS POST that announced D177** —
   this queue's own law: a block in a bus post is not registered.

0c. ⛔⛔ **`es3-anchor-theorems` IS BLOCKED ON AN UNDECIDABLE BAND, NOT ON A BUDGET — AND THE GATE'S
   OWN "MORE REPEATS" REMEDY WAS REFUTED BY THE RUN IT RECOMMENDED.** Measured 2026-09-08 by paris on
   a box that was genuinely quiet at the start (load 3.49, after 50 orphaned `wi-test` loops were
   reaped). **Three runs, and the branch is NOT landed.**
```
   run  base       repeats  Tests.Coverage        band      budget   rc  verdict
    1   7103ff865     3     delta  +300         ±1108.5    1864.8    0   ok            (WRONG KEY)
    2   cad06778      3     delta  +200         ±2470.1    1843.2    3   UNMEASURABLE
    3   cad06778      6     delta  +800         ±1916.7    1836.0    3   UNMEASURABLE  (3 units)
```
   ⛔ **THIS IS AN INSTANCE OF ITEM 4, NOT A NEW ITEM — READ ITEM 4 FIRST.** Item 4 (*"the gated
   unit is noisier than the budget it is gated against"*) has owned this condition since D141 and
   already carries the stronger general fact: **the band is a PER-RUN quantity**, with a case on
   09/06 where the same unit, same budget, same repeats and the same base median gave a band 20×
   apart on two runs an hour apart. **The evidence below is contributed THERE**; what is 0c's own is
   only the branch state. Recorded this way deliberately: a second home for one fact is a second
   register that goes stale against the first ([[feedback-a-duplicate-born-in-agreement]]).

   ⇒ 🔑 **RUNS 1 AND 2 MEASURE THE SAME PHYSICAL `.lean` DELTA** — `7103ff865..cad06778` touches no
   `.lean` and no profiler/budget/ceiling file, measured with a positive control on the range. **The
   verdict flipped `ok` → `UNMEASURABLE` on pure noise**, and run 1's green is therefore not evidence
   about this commit. **It would have shipped as a verdict if an unrelated key error had not forced a
   re-run** ([[feedback-a-single-reading-is-about-its-run]]).

   ⇒ 🔑 **AND THE REMEDY REFUTED ITSELF.** Run 2 refused with *"~6 repeats a side would decide it"*.
   Run 3 ran exactly 6 and came back with MORE unmeasurable units (3, not 2) and a worse projection:
   *"~33"* and *"~69 repeats a side"*. Doubling `n` did not shrink the band, because the spread is
   not Gaussian noise that averages out — it is **rare load excursions from other seats on a shared
   box**: the two worst passes read `Tests.Coverage` 30,600 and 27,400 at `load1` **11.52** and
   **12.04**, against ~25,700 at load ~6.
   ⇒ **`repeats_to_decide` has no floor, so it always names a price**; it is a projection under an
   assumption this box violates ([[feedback-a-projection-with-no-floor-always-names-a-price]]).
   ⛔ **DO NOT QUOTE IT AND DO NOT SPEND THE BOX ON IT.** A fourth run chosen after seeing three
   verdicts is fishing, not measurement.

   **STATE: the merge was made and UNWOUND** (`git reset --hard cad0677`); the branch is intact at
   `d9d792319` and `--gap` reads rc 0. Nothing half-landed. This is the same state
   `p2-batch32-fp-compares` has been in since 09-05 — **two branches now blocked on the same
   condition, which makes it a property of the INSTRUMENT ON THIS BOX, not of either branch.**
   **RELEASE CONDITION:** a genuinely idle box (no other seat profiling), or a gate change ruled
   elsewhere — *not* more repeats. **OWNER:** paris. **RE-MEASURE:** next sitting that finds the box
   idle; check `uptime` AND that no other seat is running a wave.
   ⚠️ **The `.lean` deltas themselves look small and benign in all three runs** (+200/+300/+800 ms on
   a ~25,700 ms unit, against budgets ~1,840). **That is a reading, not a verdict**, and it must not
   be quoted as one — which is the entire distinction this gate exists to enforce.

1. **`probe_bucket` — the RULE is repaired (D143); the PROBE is not yet run.**
   `probe_bucket` now calls `demand_census.isa_bucket`, the census's own total rule, instead of
   being a second rule that agreed with it on 256 of 256 rows. `vzeroupper` buckets as
   `AVX (state)`, so the key it needs now exists. The `None` return that used to decide BOTH the
   bucket and whether a row was a question is split: `NOT_AN_AVAILABILITY_QUESTION` is a declared
   list with a reason per entry, gated for orphans, and the delegation itself is gated by an arm
   that stubs the census's function and requires the answer to move.
   ✅✅ **DISCHARGED 2026-09-06. THE AVAILABILITY CENSUS IS FINISHED: the unasked remainder's
   implemented column reads `0 pairs / 0 instructions / 0.0%`** (`p2_oracle_support.py`), so every
   pair x86isa implements has been ASKED. 171 pairs remain unasked and x86isa implements none of
   them — asking is impossible, not merely undone.

   ⛔⛔ **AND THIS ROW WAS STALE IN BOTH HALVES, WHICH IS THE SECOND TIME TODAY THE SAME SHAPE COST
   A RE-DERIVATION.** It read *"what remains, and it needs the oracle: a probe row for
   `vzeroupper` … after which the implemented column goes from 1 pair / 1,241 instructions to 0,
   and the availability census is finished"*.
   * **The `vzeroupper` row already existed, had been run, and its sealed declaration had been
     REFUTED by the run** (P2 batch 33; the finding is written at its site — the oracle's catalogue
     declares an exception check its execution does not perform).
   * **And the column did not go to 0. It read `1 pair / 88` — a DIFFERENT pair**: `pandn` at
     `MMX (mm)`, surfaced because P2 batch 34 claimed `pandn` at `xmm`, which is another key.
   ⇒ 🔑 **A PREDICTION ABOUT A TOTAL IS A PREDICTION THAT THE SET WILL NOT MOVE UNDERNEATH IT —
   and the act that discharges one row is exactly the kind of act that adds another.** Right in
   direction, wrong in value, and it read as arithmetic because the subtraction was real.
   [[feedback-a-census-is-per-key-not-per-name]]

   ⭐ **WHAT ACTUALLY FINISHED IT:** one probe row, `pandn %mm1, %mm0` / `0fdfc1`, `hx` from
   `clang` with `pand %mm1, %mm0` in the same assembly unit as a POSITIVE CONTROL ON THE RECIPE
   (it came back `0fdbc1`, byte-identical to the `pand_mmx` row already shipped). Declaration
   SEALED before ACL2 ran, predicted `(executes, executes)` from `inst-listing.lisp`'s two entries
   being identical in every field but the opcode and sharing a semantic function that is DEFINED —
   measured `(executes, executes)`, gate CLEAN.
   ⚠️ **And what that prediction was worth was written down BEFORE the run and is not upgraded
   now**: it is close to the null model for this table (every shipped MMX row executes in both
   arms except `pshufw`), so the green is weak evidence about the ORACLE. It is exactly the
   evidence the CENSUS needs, whose question is *"has this pair been ASKED"*.
   ⭐ **COST: 16 SECONDS.** This row said *"it needs the oracle"* for three sittings, which read as
   a heavyweight blocker. Both CR4 arms over all 256 rows are a 16-second run.
   [[feedback-inherited-diagnosis-is-a-hypothesis]] [[feedback-make-the-probe-cheap]]

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
     expresses.
     ⭐⭐ **SPLIT IT 8 + 7, BY SEMANTIC KIND AND NOT BY DEMAND (D158).** 8 is what the
     declaration affords (item 2a; `p2_batch_size.py`), and splitting by KIND rather than by
     the demand ranking puts the whole new-semantics risk in the second batch instead of
     spreading it over both:
     ```
       BATCH 35 — the moves, 8 mnemonics / 5,651 instructions.  NO new semantics: every one
         is an addressing or lane-position variant of a move the model already executes.
         movapd 2420 · movhlps 1341 · movhpd 556 · movddup 506 · movlhps 340 · movlpd 274 ·
         movupd 113 · movlps 101
       BATCH 36 — the lane selectors, 7 mnemonics / 1,833 instructions.  ALL the new
         semantics, and the two the warning above is about.
         shufps 1545 · shufpd 70 · unpcklps 64 · movmskps 53 · unpcklpd 45 · unpckhps 40 ·
         unpckhpd 16
     ```
     ⇒ by demand the top 8 would have pulled `shufps` (rank 2) into batch 35 and left it
     carrying the one genuinely new rule; by kind, batch 35 is 76% of the instructions and
     none of the risk.

   ⭐⭐⭐ **THE NEXT BATCH IS SPECIFIED AT THE OBJECT (D167, 2026-09-06) — `p2_residue.py` today:
   7 pairs / 1,833 instructions, needing no rounding rule.** `shufps` 1545 · `shufpd` 70 ·
   `unpcklps` 64 · `movmskps` 53 · `unpcklpd` 45 · `unpckhps` 40 · `unpckhpd` 16. It was handed on
   as *"ALL the new semantics"*; measured, it is three kinds of work in very unequal proportions:
   ```
      4 mnemonics are BIT-IDENTICAL to VBinKind members already in the model      165 instr
          unpcklps≡punpckldq  unpckhps≡punpckhdq  unpcklpd≡punpcklqdq  unpckhpd≡punpckhqdq
      1 mnemonic is a FIELD CHANGE on `vmovmsk` (a kind: byte-signs vs ps)          53 instr
      2 mnemonics are GENUINELY NEW SEMANTICS reading BOTH operands              1,615 instr
          shufps · shufpd — and that is 88% of the batch's demand
   ```
   ⛔⛔ **AND A TEXT DIFF OF K's FILES WOULD HAVE SAID TWO OF THE FOUR ARE DIFFERENT.** The `ps`
   pairs' rule bodies differ at char 122 by **pure re-association** (`concatenateMInt` is
   associative); under the leaf-sequence normal form all four are identical, with controls
   differing. The two `pd` pairs matched textually and the two `ps` pairs did not ⇒ a byte
   comparison reads as *"two spellings, two new semantics"*, a self-consistent wrong design with a
   ready-made `ps`/`pd` explanation. **A comparison that fails on HALF a set invites a theory of
   the half.**
   ⇒ **ORDER**: (1) the `vmovmsk` field change ALONE, isolable and measurable (D160's proven
   shape); (2) the four inert spellings + `movmskps`, with an inertness THEOREM driven red by
   routing one kind to another — no vector can witness the identity; (3) `shufps`/`shufpd`, the new
   constructor, where every wrong-model arm belongs. ⛔ Land it `--no-ff` with `--record` inside the
   merge commit (D164) or `--gap` goes red. ⚠️ Re-run `p2_batch_size.py` first: the affordable batch
   GROWS with the roster, so yesterday's number is a floor.

   ⛔⛔⛔ **FOUR BRANCHES ARE UNMERGED AND THEY ARE NOT IN THE SAME STATE — ENUMERATED, BECAUSE MY
   FIRST DRAFT OF THIS ROW SAID "THREE" AND LISTED TWO (2026-09-06).**
   ```
     es3-anchor-theorems     d9d7923  09-06  GREEN; owes the landing ritual's measurement
     p2-batch32-fp-compares  3a811fb  09-05  UNMEASURABLE verdict — the batch MAY FAIL
     p2-batch23-pmovmskb     f7ead14  09-04  finished; `pmovmskb` IS in the roster ⇒ content LANDED
     p2-batch35-moves        73bc95c  09-06  `movapd`/`movupd` ARE in the roster ⇒ content LANDED
                                             (squashed onto master; the branch is a leftover ref)
   ```
   ⇒ ⭐ **ONLY TWO OF THE FOUR ARE ACTUALLY WAITING**, and the other two are refs whose work is
   already on `master` — checked by asking the ROSTER whether each branch's mnemonics are claimed,
   not by reading the branch names. ⛔ **A LIST OF "HELD BRANCHES" DERIVED FROM
   `merge-base --is-ancestor` COUNTS SQUASHED WORK AS OUTSTANDING**, in the direction that invents
   a backlog; two of these four would have been re-derived by whoever believed the count.
   ⚠️ I wrote the number before measuring it, in the row about numbers written before they are
   measured. [[feedback-a-complete-count-of-a-subset]] [[feedback-prose-written-before-the-measurement]]

   ⛔⛔ **AND THE TWO THAT ARE WAITING WAIT ON ONE UNWATCHED CONDITION — "A QUIET BOX" — WHICH
   NOTHING IN THIS REPOSITORY REPORTS THE ARRIVAL OF.**
   `es3-anchor-theorems` carries TWO landings on one measurement: the pre-state anchor theorems
   (row ES item (3)'s step 2) and the roster-docstring gate below. Both are green and both are
   `.lean`, so `--gap` demands a real `kernel_delta` before either merges.
   ⇒ 🔑 **A PRECONDITION NOBODY WATCHES IS A PRECONDITION NOBODY MEETS.** The condition is stated
   in three commit messages and in this row, and the only thing that would tell us it has arrived
   is somebody running `uptime` while remembering these branches exist. Quiet reference is
   `load1 ≈ 4.5` (`docs/kernel-delta-history-2026-09-04.jsonl`); at 12–14 every unit reads
   ×1.14–×1.18 high, and the box was at **14.23 of 14 cpus** when these were held.
   ⚠️ Held for PRECEDENCE as much as for noise: the council of 09-06 13:49 made SaltBench
   precedence FIRST for 48 h (to ~09-08 13:45) and x86lean is fourth; a two-tree profile
   saturates the box the first-precedence campaign is using.
   [[feedback-a-gate-whose-precondition-is-a-discipline]] [[feedback-a-leak-filed-as-housekeeping]]

   ⛔⛔ **AND `movmskps` IS BUILDABLE WORK THE MODEL HAS ALREADY HALF-BUILT — the whole of today's
   buildable-today residue (1 pair / 53 instructions).** `Op.vmovmsk` carries a `.ps` kind whose
   `Op.mnemonic` prints `movmskps` (the batch-36 field change), but `movmskps` is NOT in
   `rosterP0`, has no coverage row and no vector. Its sibling `pmovmskb` IS a roster entry, so ONE
   constructor is both named-per-kind and not.
   ⇒ It escaped because `rosterP0`'s docstring claimed a gate against *"the set of `Op.mnemonic`
   values"* that does not exist — the theorems compare `rosterP0` to `tableP0`, a second
   hand-maintained list — and that claim **could not have been true**: the roster names `jcc`,
   `setcc`, `cmovcc` as FORMS while `Op.mnemonic` yields the ~48 condition spellings.
   ⇒ 🔑 **A CLAIM FALSIFIED IN BULK BY DESIGN IS A CLAIM NOBODY WILL EVER TEST, AND THE ONE REAL
   VIOLATION HIDES INSIDE THE NOISE OF THE INTENDED ONES.**
   ⭐ The gate is built and driven red-first on `es3-anchor-theorems`, with the gap carried as a
   DECLARED entry (`declaredUnclaimedKindMnemonics`) plus an ORPHAN arm so it must be deleted when
   claimed. **The repair itself is a batch**: roster entry + coverage row + vector + differential
   run, after which the declared list empties and the buildable residue reaches 0 — which is the
   arm-C ripening question, so this one pair is worth more than its 53 instructions.
   [[feedback-a-citation-is-an-ungated-claim]] [[feedback-under-claims-are-unpoliced]]

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
2a. ⭐⭐⭐ **THE SIZING RULE WAS KEYED TO THE WRONG QUANTITY, AND THE ALLOWANCE IS NOT A
   CONSTANT (D158). Priced now by `python3 scripts/p2_batch_size.py` (selftest 6/6, control
   first, a LYING plant among the arms; `--check` in CI).**
   ```
     THE NEXT BATCH FITS 8 NEW MNEMONICS at both operand shapes.
       8 mnemonics -> +210 ms = 10.9% of base   ✅ clean, band included
      10 mnemonics -> +310 ms = 16.1% of base   ⛔ over the 15.7% budget
     Calibrated against a REAL batch: replaying P2 batch 34's own transition
     (134/239/954 -> 144/260/977) the plant reads +240 vs the +230.0 `kernel_delta.py`
     measured — 1.04x. The plant's LEVEL is synthetic; only its RATIOS transfer.
   ```
   ⛔⛔ **WHAT THIS ROW SAID UNTIL 09/06, REPRODUCED VERBATIM INTO TWO BANKS:** *"`vectorCoverage`
   has room for about three more vectors, and that is arithmetic — at ~11 ms per vector the
   allowance affords ~24 vectors per batch and batch 34 spent 21."* Every number in it is a real
   reading and its conclusion (*the move half will not fit; split it*) is RIGHT. It is still wrong
   where it counts, in TWO independent ways:
   * **`vectorCoverage` does not cost by the vector.** Read its four conjuncts: conjunct 2 is
     `rosterSize` membership tests over a list of runs (O(rows x runs)), conjunct 4's `eraseDups`
     is O(runs^2), conjunct 1's `getD` is O(rows) per run. Vectors enter ONCE, linearly, through
     `collapseAdjacent`. ⇒ the law is **quadratic in (rows x runs) and FLAT IN VECTORS**. Measured
     with the two models predicting OPPOSITE SIGNS, so the run could lose: **+30 vectors with no
     new mnemonic costs −10 ms; +15 mnemonics costs +370 ms.** A mnemonic costs ~25 ms — which is
     what batch 34 itself paid (230/9 = 25.6) and what the twelve-commit history pays (22.5 by
     least squares, 27.3 by endpoints). The per-ROW price reproduces on three independent routes;
     the per-VECTOR price does not survive a change of mix, and batch 34's mix (21 vectors over 9
     mnemonics) was half the history's. ⭐ The positive control is the second witness: doubling
     every dimension reads **4.13x**, not 2x.
     ⇒ 🔑 **a price divided out of one batch is keyed to whatever that batch's ratio happened to
     be**, and it reads as arithmetic because the division is real.
   * **`260.6 ms` IS NOT THE ALLOWANCE.** `scripts/kernel_delta_budget.txt` sets
     `Tests.Coverage @decl vectorCoverage 15.7%` — a PERCENTAGE OF THE BASE. 260.6 was that
     percentage times one particular base, quoted onward as a constant. And the direction of the
     error is the opposite of the intuition: marginal cost grows like R while a percentage budget
     grows like R^2, so `k_max ≈ 0.157·R·U/(U+2R) ≈ 0.074·R` — **the affordable batch GROWS with
     the roster** (~10 mnemonics at R=144, ~15 at R=200, ~22 at R=300). Read with the frozen
     260.6, the same arithmetic says batch sizes shrink toward zero and the gate needs redesigning
     soon; that alarm was an artefact of freezing a percentage into a number.
   [[feedback-match-the-gate-units-to-the-growth-law]] [[feedback-a-total-cannot-see-its-parts]]
   [[feedback-a-citation-is-an-ungated-claim]] [[feedback-a-ratio-travels-where-a-ceiling-cannot]]
   ⛔ Do NOT buy repeats to resolve a refusal — D153 measured the spread SATURATING at n≈3-4, and
   `repeats_to_decide`'s "~5 repeats a side" is a `1/sqrt(n)` projection with no floor.
   ⚠️ `X86.Coverage` also refused, at `+0.5` against a `@floor 6` budget with an `±8.5` band. That
   one is item 4 itself and no repeat count fixes it.

3. **The kernel-delta gate** stays the merge gate; the absolute ceilings ride beside every merge as
   readings, never as a gate (helm 2026-09-04 21:42).
   ### 4i. ⭐⭐ A NULL RUN WITH KNOWN GROUND TRUTH, AND A BAND SET BY ONE PASS IN TEN (D166)

The 4g(b) landing's merge gate measured a branch changing **no `.lean` file**, so the true delta was
exactly zero for every unit — the only kind of run where the answer is known independently of the
instrument. At repeats 5:
```
   Tests.Coverage           -400.0  ±4651.2   budget 1922.4   UNMEASURABLE
   Tests.Coverage @residue   +40.0  ±4205.9   budget 2293.5   UNMEASURABLE
   X86.Syntax                 +5.0    ±53.4   budget   47.7   UNMEASURABLE
```
⭐ **Accuracy is fine — every point estimate is at or near zero. RESOLUTION is what fails**, at
2.4x and 1.8x the budgets. And the gate REFUSED rather than passing, unlike D146's identical-trees
control which returned `ok` while inventing −2,150 ms.

⭐⭐ **Leave-one-out over all ten passes**: dropping any of nine leaves the band at ±4650–5932;
dropping ONE head pass (load 15.89, read 35,600 against 25,900–27,200 for the rest) collapses it to
**±817** — below the budget, where the gate would correctly have said `ok`.

⛔⛔ **AND THE OBVIOUS LOAD-EXCLUSION RULE IS REFUTED BY THE CORPUS ALREADY ON DISK.** Within a
tree, the higher-`load1` pass reads higher in **6 of 11** pairs of the committed walk — chance —
and tonight's own two sides disagree (base 3 concordant / 7 discordant; head 9/0). ⛔ Nor can the
corpus settle it: **every load in the committed walk is 3.75–5.57**, so it has no observation
anywhere near 15.9 and its silence is about a region the tail does not live in.
⛔ "Drop the worst pass" is not available at all — it derives the verdict from the readings it
judges.

⇒ **THE CHEAP THING THAT WOULD DECIDE IT, AND IT ACCRUES FROM WORK ALREADY DONE**: every merge
gate's blob already carries `(load1, secs, per-unit ms)` per pass and is thrown away with the
session scratchpad. Persist a per-pass summary beside each ledger row — a few hundred bytes per
landing — and the corpus that can test a load-based exclusion builds itself, at loads that actually
occur. Until then this is ONE observation and is recorded as one.

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
   - ⭐⭐ **AND THE BAND MOVED 20x ON ONE UNIT IN ONE DAY, OFF AN IDENTICAL BASE READING** (batch
     35, 09/06). `Tests.Coverage @decl vectorCoverage`, six passes a side both nights:
     ```
       09/06 02:0x   base 1850   head 1880   delta  +30.0   band +-657.3   UNMEASURABLE
       09/06 03:1x   base 1850   head 1915   delta  +65.0   band  +-32.0   ok  (budget 290.4)
     ```
     Same unit, same budget, same repeats, **the same base median of 1850**, and a band that fell
     from 2.3x the budget to 0.11x of it. The second run resolved a delta the first could not see
     at all. ⇒ this is the sharpest instance yet of *"the box's noise is not a property of the
     box"*: it is not a constant to be designed around but a per-run quantity, and a single
     night's refusal says nothing about whether the NEXT run can decide the same commit.
     ⚠️ It also means `repeats_to_decide` was answering the wrong question on the first night —
     no repeat count would have helped, because a different run resolved it at n=6.
     [[feedback-a-single-reading-is-about-its-run]]
   - ⭐⭐⭐ **THIRD INSTANCE, AND THE FIRST DELIBERATE DOUBLING: `repeats_to_decide` REFUTED BY THE
     RUN IT RECOMMENDED** (2026-09-08, landing `es3-anchor-theorems`). The projection is not merely
     "answering the wrong question" — it moves the WRONG WAY when obeyed:
     ```
       run 2   n=3   Tests.Coverage @residue  delta  +250   band ±2377.9   ⇒ advised "~6 repeats"
       run 3   n=6   Tests.Coverage @residue  delta +1170   band ±2377.9   ⇒ now advises "~33"
                     and pre_states_…frame    delta   -40   band ±1304.8   ⇒ "~69"; 3 units, not 2
     ```
     **`n` was doubled exactly as advised and the advice got worse.** A 1/sqrt(n) projection assumes
     the spread is noise that averages out; here it is **rare load excursions from other seats on a
     shared box** — the two worst passes read `Tests.Coverage` 30,600 and 27,400 at `load1` **11.52**
     and **12.04**, against ~25,700 at load ~6. ⇒ 🔑 **A PROJECTION WITH NO FLOOR ALWAYS NAMES A
     PRICE, AND OBEYING IT IS NOT A TEST OF IT** ([[feedback-a-projection-with-no-floor-always-names-a-price]]).
   - ⚠️⚠️ **AND A TENSION THIS ITEM SHOULD OWN RATHER THAN LEAVE IMPLICIT.** The 09/06 entry above
     resolves a unit by RE-RUNNING at the same `n` and takes the second run's verdict. If the band is
     a per-run quantity, that is legitimate physics — **and it is also, procedurally, selection on the
     outcome.** Two runs, one UNMEASURABLE and one `ok`, and the one that is kept is the one that
     decided. ⇒ 🔑 **"THE BAND IS PER-RUN" AND "RE-RUN UNTIL IT DECIDES" ARE THE SAME SENTENCE READ
     TWO WAYS, AND ONLY A RULE FIXED IN ADVANCE TELLS THEM APART.** Nothing in this repo currently
     says how many runs may be taken or which is kept. **Until it does, a verdict quoted after an
     unrecorded number of runs is not gated** — and this seat declined a fourth run on those grounds
     while noting the 09/06 precedent would have permitted it.
     📌 **PROPOSED, NOT RULED:** declare the run count and the keep-rule BEFORE running (e.g. "one
     run at n=6; UNMEASURABLE is a verdict, not a retry"), so a re-run is a stated exception with a
     reason rather than the default.

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

   ### 4g. ⭐⭐⭐ THE DRIFT GATE — (a) AND (b) BOTH DISCHARGED; WHAT REMAINS IS FIVE MEASUREMENTS

✅✅ **4g(b) DISCHARGED 2026-09-06 (D164).** The `--no-ff` landing ritual is proven end to end on a
throwaway branch WITH ITS NEGATIVE CONTROL (a 2-commit branch became ONE first-parent step; the walk
priced 23 units with no missing step; deleting that one row made the SAME walk refuse rc 2). The row
rides **inside** the merge commit, so recording needs no commit of its own:
```
   python3 scripts/kernel_delta.py --base $(git rev-parse HEAD) --head <branch> --out R.json
   git merge --no-ff --no-commit <branch>
   python3 scripts/kernel_drift.py --record --readings R.json
   git add docs/delta-allowance-ledger.jsonl && git commit
```
⛔⛔ **THE `--base` IS PINNED, AND IT IS PINNED BECAUSE THE RITUAL WITHOUT IT IS WRONG IN EXACTLY THE
CASE THE RITUAL EXISTS FOR** (2026-09-08, paris, landing `es3-anchor-theorems`). The recipe used to
be three commands and named no base. Followed literally, `kernel_delta`'s default
`resolve_base(head)` takes the **branch's FORK POINT** — but this ledger keys on the **first-parent
step**, whose base is the merge's FIRST PARENT. Those are the same commit **only when the branch was
just cut from master's tip.** A branch that OWES a measurement has by definition been waiting, so
master has advanced, so the default is wrong — and `--gap` refuses the row with *"names head X, which
is neither this base's first-parent child Y nor a commit reachable from it"*.
⇒ 🔑 **A RECIPE THAT PINS ITS STEPS BUT NOT ITS SELECTION INHERITS WHATEVER THE TOOL DEFAULTS TO, AND
A DEFAULT IS ONLY EVER RIGHT IN THE CASE ITS AUTHOR HAD IN MIND**
([[feedback-a-recipe-that-pins-inputs-but-not-selection]]).
⚠️ **AND THE TEMPTING WRONG FIX IS TO RE-KEY THE ROW.** Where master's advance touches no `.lean` and
no profiler file the readings ARE physically valid for the step, and this file already makes that
argument for the HEAD side. It is still wrong: the row would assert a base its measurement never
used, and the alternative — widening `records_step` symmetrically — derives a gate's new allowance
from the row it just rejected ([[feedback-widening-a-gate-needs-a-second-source]]). **Re-measure.**
⛔ **AND IT IS GATED, BECAUSE IT IS A DISCIPLINE.** `kernel_drift.py --gap` against
`docs/drift-gap-ratchet.txt`, on the CI list (`kernel-delta` job, step 4). A batch landed without
its row raises the gated count and goes red naming the ritual; a backfill that lowers it must lower
the ratchet in the same commit (that refuses too — slack is where the next unrecorded landing
hides). Selftest **37 arms / 23 distinct plants**, up from 18 / 10.

⭐⭐⭐ **AND THE BACKFILL IS FIVE PROFILING RUNS, NOT FIFTY.** *"The gap is 48 commits"* was the
inherited framing and it is a total that cannot see its parts. Measured at `79bb658` (51 steps):
```
    5  change a `.lean` file      ⇐ batches 23, 34, 35, 36a, 36b — a REAL measurement each
    5  change no `.lean` but DO change scripts/kernel_cost.py or the budget registry
                                  ⇐ they move the READING or the ALLOWANCE without moving
                                    the code, so "nothing to price" is FALSE for them
   41  change none of the above   ⇐ an exemption CANDIDATE; the tool exempts nothing
```
⛔ The obvious exemption — *no `.lean` change ⇒ no kernel delta* — is **wrong for the middle five**,
which is why the tool prints three numbers instead of one. Writing and gating that argument is what
is actually left. [[feedback-a-total-cannot-see-its-parts]]

✅ **4g(a) DISCHARGED 2026-09-06 (D161).** The ledger is re-keyed on `base` alone. `allowance` is
`f(parent tree, budget registry)`, so it never depended on the produced sha — the fixed point was
in the KEY, not the data. Selftest 18/18 with 10 distinct plants; fork check driven red on the real
ledger. ⛔ A proposed refusal clause for a re-cut branch was REFUTED and NOT added: two children of
one base are priced from the same tree, so their allowances are identical.

*(4g(b)'s original statement, kept because its diagnosis was right and its ARITHMETIC was off by
one: the ledger wants one row per first-parent COMMIT and the gate produces one delta per BATCH.
Measured at the object, batch 36's span `e6dd9c6 → 5c18c59` is **four** first-parent steps, not
five, and its THREE paid draws can price exactly ONE of them. Squashing reconciles the units at the
cost of the per-commit history that made batch 36's price decomposable; `--no-ff` reconciles them
and keeps it.)*

#### (the original 4g note)
### 4g-orig. THE DRIFT GATE IS BUILT AND REGISTERED (D154) — what is left is RECORDING, not design
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
   (a) ⛔⛔ **`--record` AT MERGE IS NOT "ONE CALL", AND THE LEDGER IS A DEAD LETTER UNTIL IT IS.**
       Priced as one call for two sittings. Measured 09/06, and both halves are wrong:

       **(i) THE LEDGER STOPPED 40 COMMITS AGO AND NOTHING NOTICED.** Its 11 rows are all
       `backfill:`, ending at `5c0159983`; master was 40 commits past that before batch 35.
       `window_steps` is `rev-list --first-parent`, so all 40 are steps, and the gate's own law is
       that **a gap is a REFUSAL, not a zero**. Demonstrated, rc 2, no profiling:
       `kernel_drift.py --anchor 51e760b --head 26eb0b6` → *"the ledger is missing 1 of 1 steps"*.
       ⇒ the second gate this repository built to answer item 4's refusals **cannot adjudicate any
       recent window at all**, and could not on the day it shipped. Nothing complained because the
       only thing that would have complained is the gate itself.
       🔑 **An unrecorded landing does not merely fail to help — it extends a dead zone.**

       **(ii) AND RECORDING HAS A FIXED POINT.** The ledger is a TRACKED file, so writing step
       N's row is a commit, and that commit is itself a first-parent step needing a row — whose
       recording is another commit, and so on. This is not hypothetical: **D154's own commit
       (`491dcff`), the one that wrote the 11 rows, has no row of its own**, and there is no
       exemption path in `window_steps` or `accumulated_allowance` for a commit that changes no
       `.lean`. A design that terminates must break the recursion somewhere. Candidates, none
       taken here: exempt commits with no `.lean` change (needs an argument that their kernel
       delta is zero, not an assumption); key rows by TREE rather than commit; or let the ledger
       lag one commit and price each recording commit from the **head** readings the SAME blob
       already carries — free, since that tree was profiled — recorded by the next `--record`.
       ⚠️ Whichever is chosen, the row's key is an **adjacent (parent, child) pair** (all 11 rows
       are adjacent; master has 0 merge commits) and `--record` keys off the blob's
       `base_rev`/`head_rev`. So **the commit that lands must be the commit that was measured** —
       a three-commit branch measured base→tip produces a row matching no step. Batch 35 was
       squashed to one commit for this reason; the constraint had been silently satisfied by every
       earlier batch and only bites once anything is recorded.
   (b) **Choose k and register the window as a check.** k is a latency/attribution trade, not a
       resolution knob: refusal falls 17% → 6% → 3% → 1% → 0% at k=1..5 on the loaded night.
   (c) **A measured window on real trees** beyond the k=2 receipt in D154 §8.
   ⛔ It CANNOT convict where the per-batch gate passed — its whole power is over what that gate
   REFUSED. Never propose it as a replacement.

   ### 4h. ✅ BATCH 35's `@residue` +1435 — ANSWERED, AND THE ANSWER IS THAT IT CANNOT BE ATTRIBUTED (D165)

⛔ **THIS ROW EXISTED ONLY IN BANK PROSE FOR THREE SITTINGS**, inherited and deferred each time,
which is precisely the failure this queue's own header was written about. It is here now because
it is *closed*, and a closed item that lives in a bank is re-opened by the next reader.

**The named suspect is refuted at the object.** D159 proposed `vmov_alignment_is_by_kind` (the §4
gate repair). That theorem is **absent from the `decls` map of all twelve readings**, six a side —
the profiler emits nothing under **100 ms** — so it cannot be a 1,435 ms item.

**And no other declaration can be it either.** Decomposed with the identity `residue == ungated +
unemitted` verified per reading: `ungated ≥100 ms` +223, **in NO declaration block +728**. Then the
same decomposition over **seven** saved base→head blobs — zero new measurement, they were all on
disk:
```
   unemitted BASE across all seven:   1,045 – 1,792 ms      (stable)
   unemitted DELTA across all seven:   −262 – +2,668 ms     (b35's +728 sits mid-range)
   ungated  DELTA:  −796 on batch 36 step 1, a commit that added two fields
```
⇒ 🔑 **EVERY COMPONENT OF THE RESIDUE MOVES MORE THAN THE NUMBER BEING EXPLAINED.** Three sittings
deferred this as work to be done; it was work that could not succeed, and an hour of readings
already paid for says so.

⭐ **INSTRUMENT FINDING THAT OUTLIVES THE ROW**: the profiler's 100 ms emit threshold makes a
declaration's FIRST CROSSING look like its whole cost appearing from nowhere. Three untouched
theorems (`cmpxchg…`, `dshift…`, `loop…`) "appeared" at head worth 100/131/135 ms — in 1 or 2 of six
passes. Per-declaration attribution is unreliable within ~2× of the threshold.

⇒ **WHAT IS LEFT IS ITEM 4's QUESTION, NOT THIS ONE**: `@residue` is gated at 2,184 ms while its
constituents swing ±700–2,700 between runs, so the gate watches a quantity it cannot resolve — the
first per-COMPONENT evidence for item 4 rather than per-module. ⛔ Do not buy repeats (D153: the
spread saturates at n≈3–4). The route with a floor is to gate the DECLARATIONS, whose base values
are stable, instead of the difference of two large numbers.

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
   delta has ever run on. Blocked: GitHub Actions refuses every job on this account for billing
   (desk FH).
   ⛔⛔ **THIS ITEM'S STATED METHOD WAS REFUTED 2026-09-08 AND IS CORRECTED HERE RATHER THAN LEFT TO
   BE FOLLOWED.** It used to end: *"the number to read off is the gate's own `~N repeats a side
   would decide it` line."* **Do not read that number off.** Measured on this box the same evening
   (item 4, third instance): the gate advised `~6` at n=3; obeying it produced `~33` and `~69` at
   n=6, over three unmeasurable units instead of two. **The projection moved the wrong way when
   obeyed**, because it models the spread as noise that averages out and the spread here is rare
   load excursions.
   ⇒ 🔑 **A BLOCKED ITEM'S METHOD IS THE LEAST-INSPECTED TEXT IN A QUEUE.** Nobody re-reads the
   recipe for work nobody can start, so a refuted method sits there looking like a plan and is
   followed on the day the block lifts — by which time the measurement that refuted it is a hundred
   commits back ([[feedback-a-blocked-repair-blocks-a-design]], [[feedback-a-justification-outlives-its-condition]]).
   ⇒ **WHAT TO DO INSTEAD when the runner is reachable:** run the gate on the runner at a FIXED,
   PRE-DECLARED `n` and record the BAND it produces, several times. The question is not "what `n`
   decides this commit" but **"what is this runner's band distribution"** — which is the quantity
   item 4 says to reduce, and it cannot be read off a single refusal.

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

### 2b. ✅ **DISCHARGED 2026-09-06** — P2 BATCH 36 LANDED (master `f46de06`, D160, differential record 21). Six mnemonics, 15 vectors, all six wrong-model arms caught. The field price came back NOT dear and the duplicated-rule fallback was refused; the cited hazard was about a RECORD, not an inductive constructor. Kept below as the batch's specification.

#### (the original 2b specification)
`movhlps` 1,341 · `movhpd` 556 · `movddup` 506 · `movlhps` 340 · `movlpd` 274 · `movlps` 101.
**PRICE: inside the gate on two independent runs of `p2_batch_size.py`** — 6 mnemonics read 6.2%
(02:0x) and 9.0% (03:3x) against a 15.7% budget.
⚠️ **QUOTE THE AGREEMENT, NOT A RUN.** The tool was NON-MONOTONE at 03:3x (8 → 16.0% ⛔OVER while
10 → 15.5% ⚠UNMEASURABLE) and its 8-mnemonic verdict FLIPPED between runs (clean → OVER). Its plant
is noise-dominated at this resolution exactly as the delta gate's band is. The two runs agree only
that **6 is clean and 15 is over**; batch 36 is inside both, and `k_max` is not a number to quote.

**THE ENCODING TABLE, RE-MEASURED 09/06 (clang -target x86_64, disassembled) — do not re-derive it
from the manual, and do not inherit it on trust either; this is the second independent measurement:**
```
  0f 12  mem  movlps   xmm0 = mem[0,1],xmm0[2,3]     0f 13  mem  movlps  (store)
  66 ..  mem  movlpd   xmm0 = mem[0],xmm0[1]         66 0f 13    movlpd  (store)
  0f 16  mem  movhps   xmm0 = xmm0[0,1],mem[0,1]     0f 17  mem  movhps  (HAVE)
  66 ..  mem  movhpd   xmm0 = xmm0[0],mem[0]         66 0f 17    movhpd  (store)
  0f 12  REG  movhlps  xmm0 = xmm1[1],xmm0[1]        dst LOW  <- src HIGH, dst high PRESERVED
  0f 16  REG  movlhps  xmm0 = xmm0[0],xmm1[0]        dst HIGH <- src LOW,  dst low  PRESERVED
  f2 0f 12  REG and mem  movddup  xmm0 = xmm1[0,0]   BOTH halves <- the low quadword
```
⇒ **the ModRM `mod` field selects the MNEMONIC, not merely the operand shape**: `0f 12` is four
mnemonics and `0f 16` is two. New vocabulary for this model, and the reason these six are not the
spelling change `movapd` was.
⭐⭐ **AND IT RETROACTIVELY JUSTIFIES A CHOICE ALREADY IN THE TREE.** `movlps`/`movhps` have **no
register-to-register encoding at all** — mod=11 is a DIFFERENT MNEMONIC — so `vloadh`/`vstoreh`
being two constructors with no `x,x` shape is not a convenience, it is the encoding. The low pair
must be built the same way. `movddup` is the only one of the six with both forms.

**THE CONSTRUCTOR DESIGN (proposed, not built).** Two small enums carry four of the six, by the
`movdqa`/`movaps` rule this repository already uses — same semantics, different bytes ⇒ a KIND, and
the semantics is shared by NOT branching:
```
  inductive VHalf     where | lo | hi     -- which quadword of the DESTINATION is written
  inductive VQuadKind where | ps | pd     -- the mandatory prefix (none / 66), i.e. the spelling
  | vloadq  (h : VHalf) (k : VQuadKind) (dst : XmmReg) (ea : Ea)   -- movhps movhpd movlps movlpd
  | vstoreq (h : VHalf) (k : VQuadKind) (ea : Ea) (src : XmmReg)   -- 0f 13 / 0f 17
  | vmovhl  (d : VHalf) (dst src : XmmReg)   -- d=.lo movhlps · d=.hi movlhps (duals, one rule)
  | vddupR  (dst src : XmmReg)               -- f2 0f 12 mod=11
  | vddupM  (dst : XmmReg) (ea : Ea)         -- f2 0f 12 mem
```
⛔ **THIS MODIFIES `vloadh`/`vstoreh`, WHICH IS THE EXPENSIVE PART AND MUST BE PRICED FIRST.** Two
fields on an existing constructor blew three unrelated record proofs before
([[feedback-a-state-field-costs-every-record-proof]]). Measure that before writing semantics; if it
is dear, the fallback is to leave `vloadh`/`vstoreh` untouched and add the low pair beside them,
paying a duplicated rule instead of a proof sweep.
⛔ **AND `VMovKind`'s DOCSTRING ARGUES AGAINST A KIND HERE — READ IT BEFORE OVERRIDING IT.**
`vloadh`'s comment says it is deliberately NOT a `VMovKind` because that kind's whole content is the
16-byte alignment rule and this form has none (8-byte operand, Exception Type 5, MEASURED on the
oracle at three alignments with a two-sided control, D119). `VQuadKind` is a DIFFERENT field whose
content is the prefix byte and therefore the mnemonic — which is meaningful where an `aligned`
answer would not have been. That distinction is the argument; if it does not survive contact with
the build, the kind is wrong and not the docstring.
⚠️ **THE PRESERVED HALF IS THE CONTENT, AS IT WAS FOR `movhps`.** Every one of the four half-moves
preserves the other half, so the plausible wrong model is the one that ZEROES it, and it is
invisible on any pre-state whose untouched half is already zero — `xmmPattern` must give both halves
non-zero values or the arm scores 0 and reports green about a model that destroys half a register.
`movddup` is the exception: it writes both halves, so its wrong-model arm is the one that preserves.
⚠️ Keep every new `Row.shapes` string SHORT — that field is walked character by character inside a
kernel `decide` and has been re-paid twice ([[feedback-prose-in-a-kernel-reduced-string-is-a-cost]]).
The prose goes in `note`, which is not reduced.

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
