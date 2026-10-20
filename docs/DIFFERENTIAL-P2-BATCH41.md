# V8a — `endbr64`, the census's largest uncovered row, modelled

Record 41. Decision note: D347 (predictions committed as `36d5cd0` before any model change). One new vector, `endbr64`
(`F3 0F 1E FA`), a NOP on every field this model carries (SDM 253666-093US Vol. 2A p. 3-288; x86isa's
`x86-endbr32/endbr64` is also a no-op).

## 1. THE RUN

The main differential table (`vectors`, the population `README.md` and `docs/COVERAGE.md` count):
```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=105512 matched=82455 explained=34047 unexplained=0 oracle-divergence=616 oracle-leaks=0 missing=0
1199 vectors · 88 pre-states · 105512 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 34047 · oracle-divergence: 616
```
**How the main-table line was measured, not derived:** `run_differential.sh` runs all three vector tables at once
(1279 vectors, below). The 1199 main-table ids were read from `def vectors` in `Tests/Vectors.lean` (lines 58 up to
`def vexVectors`), every case whose id is one of them was kept from `run/lean.txt` and `run/oracle.txt` (105,512 of
112,552 on each side), and `x86lean-diff compare` was run on the pair. Its rc is 1, and only because the two declared
oracle divergences it did not see, `vandps_yyy / xmm0` and `vandps_yyy / ymmhi0` (D344), belong to the VEX.256 table that
the filter removed. That is the filter working, not a finding.

Against record 40 (1198 vectors, 105424 cases, matched 82367, explained 34155, divergence 616): **+88 cases, +88 matched,
explained −108, divergence unchanged.** The +88 are the new vector, every case matched. The −108 is D346 (BSF/BSR at a
zero source, `f9e6860`), whose own note reports explained 34,155 → 34,047 on the full run; it landed after record 40 and
wrote no record of its own, because it added no vector.

The whole run, all three tables:
```
cases=112552 matched=89407 explained=34047 unexplained=0 oracle-divergence=792 oracle-leaks=0 missing=0
1199 + 80 VEX vectors · 88 pre-states · 112552 cases · 0 unexplained · 0 oracle leaks
```
Against D346's full run (112464 cases, matched 89319): +88 cases, +88 matched, nothing else moved.

## 2. THE PLANT — a mutant `endbr64` that writes RAX, caught twice

`.endbr64 => (s.setReg .q .rax 0x5a5a).setRip nr`, never committed:
- the theorem `step_endbr64` fails (unsolved goals, `X86/Theorems.lean:1239`); `step_endbr64_flags` still holds, as it
  should, since the mutant leaves the flags alone;
- with that one theorem set aside so the binary builds, the mutant's records against the SAME `run/oracle.txt`:
  `cases=112552 matched=89319 explained=34047 unexplained=88` (`spec: 88`), every one an `endbr64` case reading
  `rax: lean=0000000000005a5a`, and no other case moved.
The files were restored and checked byte-identical to the commit (`git diff -- '*.lean'` empty) before the rebuild.

## 3. WHAT IT CHANGES
- Roster 199 → **200** mnemonics, vectors 1198 → **1199**, T-exact 173 → 174 (`docs/COVERAGE.md`, regenerated).
- The demand census (katmai, `9e1bd1b`): `endbr64` is covered in every corpus, **+29,689** pooled, each corpus's covered
  count rising by exactly its `endbr64` count; the only other field that moved is the uncovered-by-extension map, whose
  CET-IBT bucket is now empty.
- `docs/P2-ROSTER.md`: the uncovered gap 362,093 → **345,605** (−16,488, `endbr64` in that roster's population).
- `claimed_forms.py` exempts `endbr64` for the reason it exempts ADX: K's tree has no `endbr` rule (measured: 0 files, 0
  content hits; `mulx` control 4), so the P1 roster derived from it has no row.
