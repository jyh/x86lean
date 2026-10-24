# D357 — `comis*`/`ucomis*` with a memory source

Record 44. Decision note: D357 (predictions committed as `57c1dfe` before any model work). One `Op` constructor, `vcomism`,
whose `step` arm is `vcomis`'s with the second operand read from memory; eight vectors at `%xmm1` and `%xmm9` (never `%xmm0`,
whose low quadword equals the memory operand in every pre-state, D356); four declarations of D266's class.

## 1. THE RUN

```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=108944 matched=85428 explained=34407 unexplained=0 oracle-divergence=835 oracle-leaks=0 missing=0
1238 vectors · 88 pre-states · 108944 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 34407 · oracle-divergence: 835
```
Main table measured as records 42 and 43 were. Against record 43 (1230 vectors, 108240 cases, matched 84766, divergence 793):
**+704 cases, +662 matched, +42 divergence.** The 42 are x86isa dispatching COMIS as UCOMIS (D266): IE left clear on a quiet NaN,
13 at each `comiss` vector and 8 at each `comisd`, the counts derived from the PRE lines before the run by a rule that reproduces
the shipped `comiss_x1_x0` (13) and `comisd_x1_x0` (8) exactly.
The whole run: `cases=131472 matched=107692 explained=34407 unexplained=0 oracle-divergence=1363 oracle-leaks=0 missing=0`.

## 2. RED BACKWARDS
- A (source from `%xmm0`): **no record changed**, because xmm0's low quadword is the memory operand in every pre-state; the mutant
  could not be told apart from the model by construction. A′ (source 8 bytes past its address): all eight vectors red, 70-122
  fields each.
- B (COMIS with UCOMIS's IE rule): the 42 declared divergences do not occur; nothing else moves.
- C (single precision read as binary64): the four single-precision vectors change (34-37 cases each); the double ones do not.
Each mutant was built through the wrapper with every theorem in place, emitted only from a fresh binary, compared against this
run's `run/oracle.txt`, and restored with `cmp`.

## 3. WHAT IT CHANGES
- Vectors 1230 → **1238**; CLAIMED unchanged at 504 (the eight ids exempt under the SIMD rule); `docs/COVERAGE.md` rows carry `x,m`.
- The demand census: +1,336 user-space; every column's differential-class memory-form demand is now modelled in full.
