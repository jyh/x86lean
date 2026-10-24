# D356 — `movd`/`movq` between an XMM register and memory: the largest unmodelled memory-form remainder

Record 43. Decision note: D356 (predictions committed as `5e0284a` before any model work; rebased onto D355 as `e53abbb`).
Two `Op` constructors, `vmovgld` and `vmovgst`, whose `step` arms are `vmovsld`'s and `vmovsst`'s formulas spelled
`movd`/`movq`; eight vectors (each width, each direction, at `%xmm0` and `%xmm9`); two declared divergences.

## 1. THE RUN

The main differential table:
```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=108240 matched=84766 explained=34407 unexplained=0 oracle-divergence=793 oracle-leaks=0 missing=0
1230 vectors · 88 pre-states · 108240 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 34407 · oracle-divergence: 793
```
Measured as record 42's was: the 1230 `def vectors` ids, their 108,240 cases kept from `run/lean.txt` and `run/oracle.txt`, and
`x86lean-diff compare` on the pair (rc 1 only for the six VEX.256 declarations the filter removes).
Against record 42 (1222 vectors, 107536 cases, matched 84233, divergence 622): **+704 cases, +533 matched, +171 divergence,
explained unchanged.** Per id: `movd_ld_x0` 5 matched / 83 declared, `movd_ld_x9` 0 / 88 declared, the other six 88/88 matched.
The 171 are x86isa's `x86-movd/movq-to-xmm` (`66 0f 6e`) writing 4 bytes and keeping bits 127:32 (D93, through memory), in
exactly the pre-states whose destination bits 127:32 are non-zero; that count was derived from the PRE lines before the run.

The whole run:
```
cases=130768 matched=107030 explained=34407 unexplained=0 oracle-divergence=1321 oracle-leaks=0 missing=0
1230 + 256 VEX vectors · 88 pre-states · 130768 cases · 0 unexplained · 0 oracle leaks
```

## 2. RED BACKWARDS — three mutants, each against this run's own oracle output

Each built twice through the wrapper, first with every theorem (to record which fail) and then with the three D356 theorems set
aside so the binary builds; a mutant with no fresh binary is refused, never emitted. Restored and `cmp`-verified each time.
- A, the load MERGES (x86isa's rule): `vmovgld_zeroes_upper` fails; `unexplained=168` = `movq_ld_x0` 80 + `movq_ld_x9` 88;
  both `movd` load declarations reported as NOT occurring; every other id unchanged.
- B, the store writes 16 bytes: theorems hold (none pins the store width); `unexplained=352`, the four store ids at 88/88 each.
- C, `movq` at 4 bytes: `vmovgld_zeroes_upper` fails; `movq_ld_x0`/`x9` 40 each (the 48 states whose high dword at 0x2004 is
  zero agree), `movq_st_x9` 88, **`movq_st_x0` 0**; the `movd` ids unchanged.
⚠️ **The `%xmm0` store rows are blind to their own store.** `xmmPattern` makes xmm0's low quadword `c`, which is the value already
at 0x2000 in all 88 pre-states (measured), so storing it changes nothing a comparator can see. The `%xmm9` rows carry the store.
The same holds for the shipped `movss_store_m`, `movsd_store_m` and `movlpd_store_m`, which have no other-register store row; a
model that dropped those stores would pass. Recorded in D356; a follow-up adds the rows.

## 3. WHAT IT CHANGES
- Vectors 1222 → **1230**; roster unchanged at 200; CLAIMED unchanged at 504 (the eight ids exempt under the SIMD rule).
- The demand census: modelled memory-form +41,343 user-space and +16 kernel, exactly as derived; dav1d, vlc-video_chroma and
  the kernel now model every differential-class memory form they contain.
- `docs/COVERAGE.md`: the `movd`/`movq` rows carry `x,m · m,x`.
