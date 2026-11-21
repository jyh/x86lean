# D405, the census half — the MMX twins of the processor-refereed rows get their own roster name

Record 49. Decision note: D405 §4 (the census seal that failed) and §5.

D405 gave the MMX forms of the seven `siliconTable` mnemonics (pmullw pmulhw paddsw psubsw psubusb psubusw pmaddwd)
differential rows, and the differential read as sealed. The census did not: `report()` classes by roster name, and the
bare name is silicon, so the 3,530 twin instructions were filed in class (b). This record gives each twin the roster
name `mm:<m>`, inside the model's differential set, and regenerates the census and the P2 roster. No Lean changes.

## 1. THE RUN
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

## 4. WHAT IS LEFT OF THE MMX RESIDUE (7,578)
The SSE-era mm forms x86isa does not implement (pmaxsw, psadbw, pshufw, pavgb and the rest), a silicon wave; the MMX
shifts; and EMMS (it read TOP 0 from TOP 7 on both processors, D403).
