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
   what it is). MEASURED, two runs an hour apart on the same box:
   - `kernel_delta.py --base c372d80 --head c372d80` — **the same commit on both sides** — read
     `Tests.Coverage` at −2,150 ms with a ±2,474 band against a 1,980 ms budget, and returned `ok`.
     The instrument invented a difference larger than the allowance it was policing.
   - The same base tree read **27,500 and 24,500** in the two runs, 12% apart, with no code between
     them. Batch 32's whole disputed delta is +1,000.
   - ⛔⛔ **AND THE CLAIM THAT USED TO BE THIS ITEM WAS WRONG TWICE, IN BOTH DIRECTIONS.** First:
     *"a floor is a MINIMUM allowance, so it can only be too generous."* Then, corrected off the
     batch run: *"three units' budgets are under what this box invents."* The control passed all
     three, with bands 3-5× smaller (`X86.Basic` ±34.7 → ±10.9; `X86.Semantics` ±6.7 → ±2.6;
     `X86.Value` ±14.1 → ±2.6). ⇒ 🔑 **"the box's noise" is not a property of the box**, it varies
     several-fold between runs, and no single run supports a sentence about it.
     [[feedback-a-single-reading-is-about-its-run]]
   - ⇒ The item is NOT "re-derive `@floor`" and NOT "widen a budget". It is: **reduce the variance
     of the measurement, or gate a quantity that has less of it.** `Tests.Coverage` is ~25 s of
     kernel `decide` over a table and carries ~8-12% run-to-run variation; its budget is 7.2%. No
     number of repeats fixes a budget under the instrument's own drift.
   - ⚠️ Any budget re-derivation must come from `docs/kernel-delta-history-2026-09-04.jsonl` — a
     walk over twelve commits that predates every batch now waiting on the gate. Deriving one from
     the runs above would be deriving the allowance from the thing it checks.
     [[feedback-widening-a-gate-needs-a-second-source]]

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
