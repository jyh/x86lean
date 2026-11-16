# D355 — the census's segment-base remainder: the stack-canary check and the kernel's per-CPU forms

Record 42. Decision note: D355 (predictions committed as `e024582`, widened as `68ec872`, both before any reading). Twenty-three
new vectors, no model change: `sub` `cmp` `xchg` `test` through `%fs:`/`%gs:` (glibc's `subq %fs:0x28,%reg` canary check and
errno test) and the kernel's per-CPU `inc` `dec` `xadd` `and` `or` `cmpxchg` `bt` `btr` `push` through `%gs:`, most of them
segment base PLUS RIP-relative. The model has added the segment base in `Ea.addr` since record 22 (D70, D72); these rows let the
demand census credit those names in the segment bucket.

## 1. THE RUN

The main differential table (`vectors`, the population `README.md` and `docs/COVERAGE.md` count):
```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=107536 matched=84233 explained=34407 unexplained=0 oracle-divergence=622 oracle-leaks=0 missing=0
1222 vectors · 88 pre-states · 107536 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 34407 · oracle-divergence: 622
```
**How the main-table line was measured, not derived:** as record 41's. The 1222 main-table ids were read from `def vectors` in
`Tests/Vectors.lean` (up to `def vexVectors`), every case whose id is one of them was kept from `run/lean.txt` and
`run/oracle.txt` (107,536 of 130,064 on each side), and `x86lean-diff compare` was run on the pair. Its rc is 1, and only
because six declared oracle divergences it did not see (`vandps_yyy` D344, `vandps_yym` and `vandps_y9y13m_u` D353) belong to
the VEX.256 tables the filter removed.

Against record 41 (1199 vectors, 105512 cases, matched 82455, explained 34047, divergence 616): **+2,024 cases, +1,778 matched,
+360 explained, +6 divergence.** Over the 23 new ids alone: `cases=2024 matched=1778 explained=360 unexplained=0
oracle-divergence=6`. The 360 are SDM-undefined flags, per id: `bt_gs_q` 114 and `btr_gs_q` 114 (OF/SF/AF/PF),
`and_gs_rip_l`, `or_gs_rip_w`, `test_gs_mi_b` 44 each (AF), the other 18 ids 0. The 6 are `btr_gs_q` at pre-states 17, 36,
50, 64, 65, 67: x86isa's negative-offset bit rule (D331, acl2/acl2#2066), the same states as `btr_mr_q` because the row
addresses the same byte with the same RCX, and declared in `Main.lean` beside D331's entries.
⚠️ **The first run read `unexplained=6`, all six these states, before the declaration existed.** D355 predicted 0 and did not
foresee them; the miss and its cause are recorded in D355's result.

The whole run, all three tables:
```
cases=130064 matched=106497 explained=34407 unexplained=0 oracle-divergence=1150 oracle-leaks=0 missing=0
1222 + 256 VEX vectors · 88 pre-states · 130064 cases · 0 unexplained · 0 oracle leaks
```
Against D354's full run (128040 cases, matched 104719, explained 34047, divergence 1144): the same +2,024 / +1,778 / +360 / +6.

## 2. THE PLANTS — two, because no model change means no model mutant

Both in one build, never committed, re-emitted and compared against this run's own `run/oracle.txt` (the bytes do not change,
so neither do the oracle's records):
- `sub_fs_canary_rax` with its AST's segment `.gs` (bytes unchanged): 80 of its 88 cases disagree (194 fields);
- `inc_gs_rip_l` with `ripRel := false` (the AST then addresses `gsBase + disp`, outside the window): 88 of 88 (181 fields).
Every other record of the 130,064 was byte-identical to the unplanted run. `Tests/Vectors.lean` was restored and `cmp`-verified
against the commit before the rebuild.

## 3. WHAT IT CHANGES
- Vectors 1199 → **1222**; roster unchanged at 200 mnemonics; `claimed_forms.py` CLAIMED unchanged at 504 of 525. The 23 rows
  are exempted under batch 22's rule (a segment override is a prefix on a row an unsegmented sibling already claims).
- The demand census: the modelled memory-form figure rises by exactly the derived amounts in nine columns (user-space
  +20,542, kernel +15,232, its remainder 15,248 → 16), cc1 unchanged (D355 result 3).
- `Main.lean`'s known-divergence list: one entry (`btr_gs_q`, six states). When acl2#2067 lands, it goes with D331's.
