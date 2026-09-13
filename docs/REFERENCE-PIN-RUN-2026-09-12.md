# The differential, re-run at the pinned reference model — 2026-09-12

**Why this record exists (D218, `docs/TACAS-G5-ARTIFACT.md` §1).** No earlier differential record names
the ACL2 / x86isa revision it ran against. The reference model is now pinned in
`scripts/oracle_revision.txt`, and this is the first run whose output carries the revision, so the
paper's §4.1 figures can be cited to a run whose reference model is named.
⚠️ Deliberately NOT named `DIFFERENTIAL-P<p>-BATCH<n>.md`: it is a re-run, not a batch, and the batch
count is derived from that filename pattern (`check_coverage_prose.py`, `check_readme_snapshot.py`).

```
started           2026-09-13T03:19:05Z   (2026-09-12 20:19 PDT)
x86lean           16a9220, the Lean side built by the script
reference-model:  acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
command           bash scripts/run_differential.sh     (log kept locally at run/repin-2026-09-12.log, not tracked)
```

## The run, verbatim
```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
driver-CR4 gate: CLEAN
emitted 1012 vectors × 88 pre-states = 89056 cases → run/lean.txt
oracle produced 89056 case records
cases=89056 matched=68524 explained=29435 unexplained=0 oracle-divergence=171 oracle-leaks=0 missing=0
  spec: 0
  refusal: 0
  harness: 0
  undefined-region: 29435
  oracle-divergence: 171
```
The oracle-availability declarations (18 forms × 88 pre-states) were checked first and held.

## Against the last batch record
**All seven counters equal `docs/DIFFERENTIAL-P2-BATCH22.md`'s** (cases 89,056 · matched 68,524 ·
explained 29,435 · unexplained 0 · oracle-divergence 171 · oracle-leaks 0 · missing 0). That is
consistent with batch 22 having run against this revision; **it does not prove it**, because a revision
that differed only where no vector reaches would give the same counts.

## ⛔ The script's exit status was 3, and it is NOT about the differential
The last step, `kernel_cost.py`, printed its readings and refused a verdict: *"kernel-cost gate
UNMEASURABLE — one-minute load was 9.10, outside the band this tool's own effect measurement covers
(loads 0.0-4.1)."* The box was shared (load 5.3 at start). **No kernel-cost claim is made from this run.**
