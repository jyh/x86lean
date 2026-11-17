# D400–D403 — the MMX register file, its channel, and the MMX moves; x86isa's MMX stores skip its own x87 rule

Record 46. Decision notes: D400 (the state field, priced on a draft), D401 (the channel and its red arms), D402 (predictions
committed as `efe7ecc` before any model work; the model and its results), D403 (the silicon verdict and the declaration).

`Cpu` gained one nested field, `mmx : Mmxs` (mm0–mm7, the x87 tag word, TOP). The record gained `mm0=`…`mm7=`, `fptag=` and
`fptop=` on both sides, and the driver loads all three on every case. Six `Op` constructors model `movd`/`movq` between an
MMX register and a GPR, memory, or another MMX register. Every MMX write goes through `Cpu.setMm`, which applies the x87 side
effect (tag := 0, TOP := 0), and the stores apply it through `mmxTouch`.

## 1. THE RUN

The main differential table:
```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=110176 matched=86308 explained=34407 unexplained=0 oracle-divergence=1399 oracle-leaks=0 missing=0
1252 vectors · 88 pre-states · 110176 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 34407 · oracle-divergence: 1399
```
Measured as records 42–45 were. The 1252 main-table ids were read from `def vectors` in `Tests/Vectors.lean` (up to
`def vexVectors`). Every case whose id is one of them was kept from `run/lean.txt` and `run/oracle.txt` (110,176 of 133,144
on each side), and `x86lean-diff compare` was run on the pair. Its rc is 1, only because of the six VEX.256 declarations
(D344, D353) that the filter removes. Against record 45 (1241 vectors, 109,208 cases, matched 85,692, divergence 835):
**+968 cases, +616 matched (7 to-MMX vectors × 88), +564 divergence (the four from-MMX vectors, §3), nothing else moved.**

The whole run: `133144` cases, `109012` matched, `34407` explained, `0` unexplained, `1927` divergence, 0 leaks, 0 missing.
That equals, count for count, a line sealed before the run (D403 §6).

## 2. THE CHANNEL (D401) — before any MMX instruction
The branch at D401 and a control on master `3fcb7ee` read identical counts (132,176 cases, unexplained 0, divergence 1363).
`mm3=` keys in the oracle's output: 132,176 on the branch, 0 on master. Three planted arms are caught (mm3, fptag, fptop).

## 3. THE FINDING (D402, D403)
The four from-MMX vectors (`mmx_movd_from`, `mmx_movq_from`, `mmx_movd_st`, `mmx_movq_st`) disagree with x86isa in `fptag`
in 88 of 88 cases each and in `fptop` in the 53 cases each whose pre-state TOP is non-zero: 352 + 212 = 564. That is exactly
the figure sealed before the comparison was read. x86isa's two store `def-inst`s (`0F 7E`, `0F 7F`) never call
`mmx-instruction-updates`, whose own documentation covers *"all MMX instructions except EMMS"*.
**Silicon** (`hwprobe/mmx87_probe.c`, run 44194743241: AMD EPYC 7763 and Intel Core i7-8700B) reads **VERDICT rule, 8 of 8
store readings on each**: after every store no x87 register is empty and TOP is 0. The 564 are declared (eight entries:
`fptag` at its pair 0000/ffff, `fptop` at the 53 derived states).

## 4. WHAT IT CHANGES
- Vectors 1241 → **1252** (main table), 1502 → 1513 (whole run). CLAIMED unchanged at 504. Rows unchanged at 200: the
  MMX forms are shapes on the existing `movd`/`movq` rows.
- **The demand census**: MMX joins its scope, and an `%mm` spelling maps only to a mnemonic with an MMX row (derived from
  COVERAGE.md). Covered rises by **14,495**, exactly the movd/movq mm demand derived beforehand (ffmpeg 6,797 · x264 5,220 ·
  vlc-video_chroma 2,303 · vpx 175). The MMX miss falls 43,046 → 28,551. No other column moves and no total changes.
- **`docs/P2-ROSTER.md`** (regenerated from the census): the instructions the model does not differentially validate fall
  345,443 → **330,948**, which is −14,495, the same figure. The paper's §4.3 sentence quotes 345,443 through `CLAIMS.tsv`
  `p2_gap_total`, pinned to `6f85116`, so it stays true of that commit. Whether it should quote the new figure is the
  paper's decision at landing.
- **`README.md`** no longer lists MMX as unmodelled without qualification: "MMX beyond `movd`/`movq`".
- **NOT vectored, stated**: REX.R on an MMX register field (no assembler emits it, and the table's bytes come from one), and
  the REX.W `0f 6e`/`0f 7e` memory spellings (clang spells those `0f 6f`/`0f 7f`).
