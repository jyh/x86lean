# V3 — the VEX.128 register twins, and the YMM upper half in the record

Decision note: D341 (design and six predictions committed as `cf05167` before any model change; result paragraph beside it).
Scoping: D339. Run on yukon.lan, 2026-10-14.

## 1. THE RUN WITH THE CHANNEL LIVE, BEFORE ANY VEX FORM (P2)

```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=105424 matched=82367 explained=34155 unexplained=0 oracle-divergence=616 oracle-leaks=0 missing=0
1198 vectors · 88 pre-states · 105424 cases · 0 unexplained · 0 oracle leaks
```
Identical to record 40 in every total. The record now carries `ymmhi0 … ymmhi15` (bits 255:128 of each YMM register) on both
sides, every pre-state seeds all sixteen non-zero and distinct (`ymmHiPattern`), and all 105424 oracle POST lines carry a
non-zero `ymmhi15`: x86isa's legacy SSE writes and this model's `Xmms.set` both preserve the upper half.

## 2. THE RUN WITH THE 33 TWINS (P3, P5)

```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=108856 matched=85799 explained=34155 unexplained=0 oracle-divergence=616 oracle-leaks=0 missing=0
1198 + 39 VEX vectors · 88 pre-states · 108856 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 34155 · oracle-divergence: 616
```
+39 vectors (`vexVectors`: 33 at xmm1/xmm2 → xmm0, six off them — the C4 form and clang's store-form opcode for a high
source) ⇒ **+3432 cases, all matched**; every other total unchanged. Held case by case from `run/lean.txt` and `run/oracle.txt`:
in all 3432, `ymmhi(dst)` is non-zero before and zero after on both sides, every other `ymmhi` is unchanged on both sides, and
none refused (CR4 `#x600`, no XCR0). The emitted records of the final tree are byte-identical to this run's.

## 3. THE MUTANTS (P4), never committed

| mutant | vectors changed | caught | cases caught |
|---|---|---|---|
| `setVex128 := set` (the three VEX arms call `setXmm`) | 39 | 39 | 3432 / 3432 |
| legacy `setXmm` zeroes the written register's upper half | 282 | 282 | 24816 / 24816 |

## 4. WHAT THE ORACLE DOES WITH THE ENCODINGS V3 DOES NOT TAKE (P6)

`oracle_availability.py` rows, re-read every run: VEX.256 `vpaddd`/`vmovdqa` EXECUTE 88/88 (not taken: the model has no
256-bit operand); `vvvv ≠ 1111b` on `vmovdqa`/`vmovddup` and a `66`/REX prefix before VEX REFUSE 88/88. LLVM `objdump`, the
vector path's decoder, decodes the two prefixed strings as plain `vpaddd` (D341 (i)); no vector carries them.
