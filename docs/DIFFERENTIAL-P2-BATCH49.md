# D405, the census half — the MMX twins of the processor-refereed rows get their own roster name

Record 49. Decision note: D405 §4 (the census seal that failed) and §5.

D405 gave the MMX forms of the seven `siliconTable` mnemonics (pmullw pmulhw paddsw psubsw psubusb psubusw pmaddwd)
differential rows, and the differential read as sealed. The census did not: `report()` classes by roster name, and the
bare name is silicon, so the 3,530 twin instructions were filed in class (b). This record gives each twin the roster
name `mm:<m>`, inside the model's differential set, and regenerates the census and the P2 roster (§1–§3); and D405 §6
moves D404's MMX forms into a table of their own (§3b).

## 1. THE RUN
The differential at this record's tree (`scripts/run_differential.sh`, rc 0), after D405 §6 moved D404's 23 MMX forms
into `mmxTable`:
```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=114224 matched=90356 explained=34407 unexplained=0 oracle-divergence=1399 oracle-leaks=0 missing=0
1298 vectors · 88 pre-states · 114224 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 34407 · oracle-divergence: 1399
```
The main table, measured as records 42–48 were (`artifact/main_table.py run`: 1,298 ids, 114,224 cases kept from each
side, then `x86lean-diff compare`). It equals record 48's line exactly. The compare's rc 1 is the declared divergences the
split removes: the six VEX.256 ones of records 42–48, and since D405 the two MMX `pmaddwd` twin declarations
(`mmx_pmaddwd_rr`/mm0, `mmx_pmaddwd_rm`/mm2), whose vectors are outside the main table. The whole run
(`cases=138424 matched=114130 explained=34407 unexplained=0 oracle-divergence=2089 oracle-leaks=0 missing=0`) equals
D405 §4's sealed line exactly. Nothing in the differential moved, which is the prediction for a record that adds no vector.

### The census run
`python3 scripts/demand_census.py --corpus <the corpus> --out docs/DEMAND-CENSUS.md` (rc 0), then
`python3 scripts/p2_roster.py` (rc 0; `--check` rc 0). The census stamps:
```
<!-- census-model: mnemonics=310 sha=dd665c1c51fd17d4 rules=cdc4e0554c871c27 -->
<!-- census-forms: vectors=1573 probes=573 sha=47087979c26a4261 -->
```
The model half is unchanged (310 mnemonics); the mapping half moved (rules `26753e910641aa3b` → `cdc4e0554c871c27`).

## 2. AGAINST THE SEAL
Sealed before this code (D405 §4): covered +3,530.
```
  ffmpeg            covered +1,409   silicon +0
  vlc-video_chroma  covered +1,536   silicon +0
  vpx               covered    +65   silicon +0
  x264              covered   +520   silicon +0
  TOTAL             covered +3,530   silicon +0   total +0
  MMX (mm) residue  11,108 -> 7,578  (MMX covered 31,938 -> 35,468)
  P2-ROSTER gap     313,505 -> 309,975
```
Read from `docs/DEMAND-CENSUS.md.json` against record 48's copy, summed over the non-underscore columns. **The seal
holds.** The figure the failed run printed (covered +0, silicon +3,530) is gone, so the twins left class (b) and joined (a).

## 3. THE ARMS
- `demand_census.py --selftest`: PASS, 260 arms. The no-pooling fixture carries 7 `pmaddwd %mm`, and `honest` reads
  `report()`'s covered 57 and silicon 35.
- Red backwards, the twin name removed: `honest` reads covered 50, silicon 42; `D405:twin` and `class pmaddwd in MMX`
  red with it.
- `census_redprobe.py`: PASS, control + 38 mutations, every one caught.

## 3b. D405 §6 — THE MMX FORMS LEAVE THE MAIN TABLE'S SHAPES COLUMN
D405's K1 on katmai (`75c41df` → `d452411`, `--repeats 6`, both arms) refused the NEW unit `Tests.CoverageMmx` as designed,
and also convicted `Tests.Coverage @decl memDestSweep`: 7,165 → 8,445 ms, +1,280 (±70) against a 616 ms budget. That theorem
reads `tableP0`'s shapes column character by character (D38), and D404 d1/d2 had added ` · mm,mm · mm,m` to 23 rows (345
characters). The repair is D341's and D353's: `X86.mmxTable` (23 rows, its own COVERAGE.md section after the main table and
before the processor section), with `tableP0`'s cells back to their XMM-only text and the bookkeeping in `Tests.CoverageMmx`
(size 23, distinct, each row a main-table and not a processor-refereed mnemonic, and the rows and the packed MMX vectors of
`vectors` naming each other). Red backwards: the table without `pandn` is refused by the vectors theorem, with a control
in the same file passing. The census reads the MMX set from every row before the VEX section, so it is byte-identical to
§2's. The differential above is at this tree.

## 4. WHAT IS LEFT OF THE MMX RESIDUE (7,578)
The SSE-era mm forms x86isa does not implement (pmaxsw, psadbw, pshufw, pavgb and the rest), a silicon wave; the MMX
shifts; and EMMS (it read TOP 0 from TOP 7 on both processors, D403).
