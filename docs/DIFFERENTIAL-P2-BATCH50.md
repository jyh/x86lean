# D406 — the MMX shifts by immediate

Record 50. Decision note: D406 (predictions and price committed before any model work, §5 the results).

D406 gives the eight MMX shifts by immediate (`NP 0F 71/72/73 /2 /4 /6 ib`: psllw pslld psllq psrlw psrld psrlq psraw
psrad) a meaning, `low64 (vshiftApply op w (zext a) imm8)`, through a new `Op.mmshifti`, with 16 vectors (each kind at
count 3 and at the lane width) in `vectors` and eight rows in `X86.mmxTable`. The register- and memory-count forms are
not modelled: x86isa dispatches no handler for them (D406 §1), so they stay a silicon item.

## 1. THE RUN
The differential at this record's tree (`scripts/run_differential.sh`, rc 0), split to the main table as records 42–49
were (`artifact/main_table.py run`: 1,314 ids, 115,632 cases kept from each side, then `x86lean-diff compare`):
```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=115632 matched=91764 explained=34407 unexplained=0 oracle-divergence=1399 oracle-leaks=0 missing=0
1314 vectors · 88 pre-states · 115632 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 34407 · oracle-divergence: 1399
```
The compare's rc 1 is the declared divergences the split removes, as in record 49. The whole run
(`cases=139832 matched=115538 explained=34407 unexplained=0 oracle-divergence=2089 oracle-leaks=0 missing=0`) is record
49's whole run plus 1,408 cases (16 vectors × 88 pre-states), every one matched; the explained and oracle-divergence
counts are identical, so the new vectors added no disagreement of any kind.

### The census run
`python3 scripts/demand_census.py --corpus <the corpus> --debug <the debug tree> --out docs/DEMAND-CENSUS.md` (rc 0),
then `python3 scripts/p2_roster.py` (rc 0; `--check` rc 0). The census stamps:
```
<!-- census-model: mnemonics=310 sha=dd665c1c51fd17d4 rules=beab57887ba9fd9b -->
<!-- census-forms: vectors=1589 probes=573 sha=4f39c374fe828b88 -->
```

## 2. AGAINST THE PREDICTIONS (D406 §3)
1. **Differential: HELD.** Unexplained 0 at every pre-state, no new declared divergence (§1).
2. **Arms: HELD, each caught on these vectors only** (every arm differs from `step` on `.mmshifti` alone):
   (a) count modulo the lane width, 599 in `mm0` · (b) psra filling zeros, 284 in `mm0` · (c) the x87 touch dropped,
   1,344 in `fptag` · (d) one 64-bit lane for w16/w32, 388 in `mm0` (`x86lean-diff selftest MMX`, 14 of 225 arms).
   ⚠️ (c) was first registered against `mm0` and the harness refused it ("none in the field the bug is in"); the field is
   `fptag`, as for D402's load arm. Re-registered, it catches.
3. **Census: REFUTED as first run, then HELD once the census could see the count form.** The first run read covered
   **+2,822**, not +2,671. 2,822 is every MMX shift: the census bucketed by register file, so the 151 register- and
   memory-count forms (144 + 7, counted by the objdump pass before any code) were credited by the `%mm` identity rule to
   rows that model only the immediate. That is an over-claim, and the census gained a bucket of its own for them,
   `MMX shift, register/memory count (D406)` (in scope, mapped to nothing). Re-run:
```
  ffmpeg            covered +1,608   silicon +0   total +0
  vlc-video_chroma  covered   +592   silicon +0   total +0
  vpx               covered    +16   silicon +0   total +0
  x264              covered   +455   silicon +0   total +0
  TOTAL             covered +2,671        (predicted +2,671)
  MMX residue       7,578 -> 4,907        (predicted 4,907) = MMX (mm) 4,756 + the shift-count bucket 151
  P2-ROSTER gap     309,975 -> 307,304
```
   ⚠️ The census rule was changed after its first reading. The 151 it removes were counted independently before the
   model existed (D406's form census), and the new bucket holds exactly 151 (ffmpeg 21, x264 130). So the 2,671 is the
   pre-registered figure and not a fit to the reading.
   Every figure in this table is read from `docs/DEMAND-CENSUS.md.json` against record 49's copy, summed over the
   non-underscore columns. ⚠️ A first draft of this table was typed from the refuted run's columns and read ffmpeg
   +1,629 and x264 +434. The derivation corrected both: the 21 and 130 left those two columns.
4. **Kernel cost: FAILED at K1, then CLEAN at K1b** (D406 §5). `memDestSweep` did not move (−50 ms), as predicted. The
   unit that failed was `Tests.CoverageMmx` (+1,505 ms over a 310 budget), whose per-row scan of `vectors` grew as
   rows × vectors. Repaired at `c500038` (one linear pass); K1b on katmai reads both arms CLEAN, `Tests.CoverageMmx`
   −1,845 ms and −100,830 ku against master.

## 3. THE ARMS OF THE TOOLS
- `demand_census.py --selftest`: PASS, 263 arms (three new bucket arms: an immediate count stays `MMX (mm)`, and a
  register and a memory count go to the new bucket).
- Red backwards, the bucket rule disabled: the selftest reads FAIL (4 arms). The two count-form bucket arms red, and
  so do the two staleness arms, because the mapping hash moved.
- `census_redprobe.py`: PASS, control + 38 mutations, every one caught.
