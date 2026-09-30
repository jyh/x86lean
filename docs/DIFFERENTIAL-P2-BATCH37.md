# P2 BATCH 51 — the six width siblings the primitive census named

Decision note: D327. The census: `scripts/primitive_census.py`, `docs/PRIMITIVE-CENSUS.md`.

## 1. THE RUN

```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=101904  matched=81163  explained=29523  unexplained=0  oracle-divergence=292  oracle-leaks=0  missing=0
1158 vectors · 88 pre-states · 101904 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · harness: 0 · undefined-region: 29523 · oracle-divergence: 292
```
Against batch 50's run (record 36), **every field is as D327 predicted**: +6 vectors ⇒ **+528 cases**, **+484
matched**, **+44 explained**, divergence and leaks unmoved. **484 + 44 = 528.**

⭐ **ATTRIBUTED PER VECTOR**, each vector's own records filtered out of `run/lean.txt` and `run/oracle.txt` and compared
alone, with `add_q` as the control:
```
  cmovb_rr_q      88 matched            predicted 88 matched (cmov writes no flag)
  cmovae_rr_q     88 matched            predicted 88 matched
  add_d           88 matched            predicted 88 matched (every flag written is defined)
  sub_d           88 matched            predicted 88 matched
  neg_d           88 matched            predicted 88 matched
  shr_r_one_d     44 matched + 44 explained    predicted matched + explained = 88, split unpredicted
  add_q (control) 88 matched
```
Each id has 88 CASE records on BOTH sides, so none was skipped, refused or dropped. `shr_r_one_d`'s split is a fact about
the values: a shift by a non-zero count leaves AF undefined, so all 88 cases carry a declared-undefined component, and in 44
of them the two models' AF differ.

⚠️ **THE ORDER OF PREDICTION AND RUN, STATED EXACTLY.** D327 was committed at 12:52:17 PDT after `run_differential.sh` had
been launched. `run/lean.txt` was last written at 12:52:59 and `run/oracle.txt` at 12:53:33, and the comparison came after
both. So the predictions precede every output that could have informed them; they do not provably precede the START of the
Lean emit, and D327's own phrase "before its emit" claims more than the file times show (corrected under D327).

## 2. THE PLANT — the arm is load-bearing, measured backwards
The content of the four `.d` vectors is that a 32-bit write ZERO-EXTENDS. `add_d`'s Lean records were given `add_q`'s POST
states (the same 88 pre-states under the 64-bit rule) and compared against the oracle: **rc 1, 88 of 88 cases unmatched,
193 unexplained disagreements.** A model that ran `addl` at 64 bits would not pass this vector.

## 3. WHAT IT CHANGES
- **No semantics.** Every constructor already took the size; `claimed_forms.py` resolves each new vector to the SAME roster
  row as its tested sibling, so the vectors add five runs (338 → 343 — the two `cmovcc` vectors are adjacent and share one) and no row.
- **The census, re-derived from the 1158-vector table:** 40 of 57 public primitives ALL COVERED (from 23), exactly the
  ladder's prediction; the s2n-bignum appendix moves from 145 to 199 of 332.
- **Not added, and why:** `imull imm,m,r32` and `roll r32` (XXH32's two remaining forms) are also width siblings; they were
  held out of this batch so it carries exactly the six the ladder priced.

## 4. KERNEL COST
The run's retired-ceiling readings printed `kernel-cost gate UNMEASURABLE` (one-minute load 8.83, outside the 0.0–4.1 band
the tool's effect measurement covers), rc 3 — a reading, not this batch's verdict (D123 §7). The kernel-time gate is CI's
`kernel-delta`. The six vectors add entries to lists that `decide` walks in `Tests/Coverage.lean`; `Tests` built clean with
`vector_count_is_1158`.
