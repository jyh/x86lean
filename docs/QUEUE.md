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

## P2 — the vector campaign · **LIVE** (31 batches)
Extending the model and the oracle-availability census across the SIMD/FP buckets.

**Where it stands** (`scripts/p2_oracle_support.py`, `scripts/p2_roster.py`):
```
THE UNASKED REMAINDER    172 pairs / 18,032 instructions
   x86isa IMPLEMENTS       1 pair  /  1,241   — vzeroupper, and NOT askable (below)
   x86isa DOES NOT       171 pairs / 16,791
   NOT RESOLVED            0 pairs /      0
```
⇒ **Every implemented pair that can be asked has been asked** (D138). The availability census is
finished except for what the probe cannot express.

### P2 open items, in order
1. **Widen `probe_bucket`** — it expresses 5 of 18 census buckets. `AVX (state)` is the one that
   costs measurably: `vzeroupper`, 1,241 instructions, x86isa implements it and no probe can carry
   its key (D128 §5, D138 §3). This is the only remaining *implemented* pair. A design item.
2. **Land the buildable groups the census has surfaced** — the ordinary batch work.
3. **The kernel-delta gate** stays the merge gate; the absolute ceilings ride beside every merge as
   readings, never as a gate (helm 2026-09-04 21:42).
4. **Re-derive `@floor` against the BAND, not the spread** (opened by D141). The 6 ms floor in
   `scripts/kernel_delta_budget.txt` was derived from the worst within-commit RANGE because the
   refusal used to read `budget < spread`; it no longer does, so the constraint that set the number
   is gone. ⛔ The number was deliberately left alone — moving an ALLOWANCE in the same commit that
   moved a RULE makes the two inseparable afterwards — and the direction of the staleness is known:
   a floor is a MINIMUM allowance, so this one can only be too generous. Re-deriving it can only
   tighten the gate. Price: no new measurement — `kernel_delta_history.py --register-budget` over
   the committed readings at `docs/kernel-delta-history-2026-09-04.jsonl`, plus the arm that says
   which units it binds.
5. **`--repeats` in CI is a guess** (D141 §9). `.github/workflows/ci.yml` asks for 6 on a runner no
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
