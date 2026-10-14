# P2 BATCH 52 — the four remaining width siblings the primitive census named

Decision note: D329. The census: `scripts/primitive_census.py`, `docs/PRIMITIVE-CENSUS.md`.

## 1. THE RUN

```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=102256  matched=81427  explained=29699  unexplained=0  oracle-divergence=292  oracle-leaks=0  missing=0
1162 vectors · 88 pre-states · 102256 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 29699 · oracle-divergence: 292
```
Against batch 51's run (record 37): +4 vectors ⇒ **+352 cases**, **+264 matched**, **+176 explained**, divergence and
leaks unmoved. ⚠️ **264 + 176 = 440, not 352, and that is a fact about the counter, not the run:** `compareRecs` counts
`matched` in CASES and `explained` in DISAGREEMENTS, so a case with two explained components adds 2. Record 37's
`484 + 44 = 528` held only because its one explained vector had one component per case.

⭐ **ATTRIBUTED PER VECTOR**, each vector's own records filtered out of `run/lean.txt` and `run/oracle.txt` and compared
alone, with each one's tested sibling as its control:
```
  mov_ri_b        88 matched                         predicted 88 matched (mov writes no flag)
  rol_r_one_d     88 matched                         predicted 88 matched (OF defined at count 1)
  imul3_ml         0 matched, 176 explained           predicted matched + explained = 88 — FAILED as written (§1a)
  cmovns_rr_q     88 matched                         predicted 88 matched (cmov writes no flag)
  mov_ri_d    (control)  88 matched
  rol_r_one_q (control)  88 matched
  imul3_mq    (control)   0 matched, 176 explained
  cmovns_rr_l (control)  88 matched
```
Each new id has 88 CASE records on BOTH sides, so none was skipped, refused or dropped. (A single-vector compare exits 1
on every vector, controls included, because the declared oracle divergences of the other vectors do not occur in it; the
counts, not that exit code, are the reading.)

### 1a. The prediction that failed, and what it measured
D329's prediction 4 said `imul3_ml` would read **matched + explained = 88**. It reads **0 + 176**. The two models disagree
on **ZF and PF in all 88 cases** (field-by-field diff of the POST records: `zf` 88, `pf` 88, nothing else), both declared
undefined after a three-operand `imul`, so every disagreement is explained and none is unexplained. The prediction added a
case count to a disagreement count; it was written from record 37's `shr_r_one_d`, where the two units coincide. The
`.q` sibling `imul3_mq` reads the identical 0 / 176, so the value is the width-independent behaviour of the undefined
generators, not a defect at `.d`. What the prediction was FOR — every case carries only declared-undefined differences —
holds; the arithmetic it was stated in does not, and it is left as written in D329.

⚠️ **THE ORDER OF PREDICTION AND RUN.** D329 was committed (tag `d329-predictions`) at 16:29:39 PDT. `run_differential.sh`
was first launched at 16:29:57 and refused at its reference-revision gate (the worktree has no `vendor/acl2` tree), then
relaunched at 16:30:25; `run/lean.txt` was written at 16:31 and `run/oracle.txt` at 16:32. So the predictions precede the
run's launch and every output.

## 2. THE PLANT — the arm is load-bearing, measured backwards
The content of `mov_ri_b` is that an 8-bit write KEEPS bits 8..63 of RAX. Its Lean records were given the zero-extending
rule (POST `rax` = `0x5a` with the upper bits cleared, the `.d` rule) and compared against the oracle: **59 of 88 cases
unmatched, 59 unexplained (`spec`).** The other 29 are the pre-states whose RAX already has zero upper bits, where the two
rules agree — a joint fact about the model and the pre-states, so the number is 59 and not 88.

## 3. WHAT IT CHANGES
- **No semantics.** Every constructor already took the size; `claimed_forms.py` resolves each new vector to the SAME roster
  row as its tested sibling (256 · 509 · 416 · 434), claimed rows stay 500 of 525, and the vectors add four runs (343 → 347)
  and no row.
- **The census, re-derived from the 1162-vector table:** 41 of 57 public primitives ALL COVERED (from 40; `xxh32`), as
  D329 predicted; the s2n-bignum appendix moves from 199 to 202 of 332. The table of not-covered forms carries no † form:
  every remaining gap is an extension (SSSE3/SSE4, BMI/ADX, AES-NI, SHA-NI, AVX) or `movq m,xmm`. The four HACL* rows that
  missed only `movb imm,r8` now read *covered, calls out* — they call `memcpy` and are never counted.

## 4. KERNEL COST
Not read in this run: the run was driven through the fleet build wrapper and stopped after `compare`, so the retired
ceiling readings (D123 §7) were not taken. The kernel-time gate is CI's `kernel-delta`. The four vectors add entries to
lists that `decide` walks in `Tests/Coverage.lean`; `Tests` built clean with `vector_count_is_1162`.
