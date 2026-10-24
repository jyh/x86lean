# D358 — the `%xmm0` store blind spot: `%xmm9` twins for `movss`, `movsd`, `movlpd`

Record 45. Decision note: D358 (predictions committed as `49ebe14` before any row). No model change; three vectors.

`xmmPattern` makes xmm0's low quadword `c`, the quadword at 0x2000 in every pre-state, so a low-lane store from `%xmm0` to
`(%rbx)` rewrites the bytes already there and a model that drops the store passes. Found by D356's mutant C, then swept over
every `%xmm0` → `(%rbx)` store: `movss`, `movsd` and `movlpd` had no other-register store row.

## 1. THE RUN

The main differential table:
```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=109208 matched=85692 explained=34407 unexplained=0 oracle-divergence=835 oracle-leaks=0 missing=0
1241 vectors · 88 pre-states · 109208 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 34407 · oracle-divergence: 835
```
Measured as records 42-44 were: against record 44 (1238 vectors, 108944 cases), +264 cases, +264 matched, nothing else moved.

The whole run: `131736` cases, `107956` matched, `34407` explained, `0` unexplained, `1363` divergence, 0 leaks, 0 missing.

## 2. THE PLANT — a dropped low-lane store
`vmovsst` and `vstoreq .lo` write nothing: `unexplained=352` = the three new rows and `movlps_store_x5` at 88 of 88 each; the four
`%xmm0` store rows (`movss_store_m`, `movsd_store_m`, `movlps_store_m`, `movlpd_store_m`) at **0**, which is the blind spot
measured. Built with every theorem in place, emitted from a fresh binary, compared against this run's oracle output, restored.

## 3. WHAT IT CHANGES
- Vectors 1238 → **1241**; CLAIMED unchanged at 504; the census moves only its forms stamp.
- The `%xmm0` rows stay: they still check the address and width of the bytes written; they cannot check that bytes were written.
