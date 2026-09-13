# PRE-REGISTERED — DOES A Δku GATE SEE THE ms GATE'S OWN RED-FIRST PLANT?
# paris, 2026-09-13. Written and committed BEFORE the measurement. Follows D228.

## WHY
D228 found the unfolding counter blind to literal arithmetic and to no-unfolding terms, and the first ku walk of
every module (D229, same day) put **77% of `X86.Syntax`'s kernel time on `inductive`/`structure` and `deriving`
commands** — the kind of work a P2 batch adds when it grows an enum. The ms gate's own red-first arm 2
(`kernel_delta.py plant_constructors`, default 512) plants exactly that: N constructors on `PrefetchHint` in
`X86/Syntax.lean` plus N match arms. **A replacement gate that cannot see its predecessor's own positive control
is not a replacement.**

## THE MEASUREMENT
A detached worktree at HEAD; `plant_constructors(N)` applied as `kernel_delta.py` applies it; `X86.Syntax` read
by `deterministic_cost.measure` (ku, wrapped + unattributed) and by one `lean -D profiler=true` pass per repeat
(sum of `type checking` over the module). N = 0 (CONTROL, twice), 128, 512.

## PREDICTIONS, SEALED
```
B1  CONTROL: N = 0 read twice gives Δku = 0 exactly.                                   HIGH
B2  Δms(X86.Syntax, N = 512) exceeds the unit's current allowance (44.7 ms, ledger
    row c8ee127 → d5608a7) — the plant is visible to the gate it was built for.         HIGH
B3  Δku(X86.Syntax, N = 512) is NON-ZERO and at least doubles from N = 128 to 512
    (deriving DecidableEq / BEq / Repr and the match arms unfold per constructor).   MODERATE
B4  The plant's marginal ms per 1k ku is ABOVE D228's unfolding band top (3.41):
    part of what it adds is inductive checking, which unfolds nothing.               MODERATE
```
**Meaning, fixed now:** B3 REFUTED ⇒ a Δku gate does not see the ms gate's own positive control, and ARM A cannot
replace the ms gate as designed. B3 CONFIRMED with B4 CONFIRMED ⇒ it sees the plant but under-prices it against the
unfolding constant, so a ku budget converted to time by that constant would be generous by the ratio measured.

SEALED 2026-09-13, before the measurement.

---

# ⚖️ THE RESULT — all four CONFIRMED: a Δku gate SEES the plant, and under-prices it by a ratio that GROWS with N
Corpus `docs/ku-constructor-plant-2026-09-13.json`, head `c7ed191`, yukon arm64, load1 3.66 → 5.31, 5 profiler
passes a tree. Tool `scripts/ku_constructor_plant.py` (committed at `5ed2eab` byte-identical to what ran);
`deterministic_cost.py` as of `0b96566` — the later same-line-attribute widening moves ku between WRAPPED and
UNATTRIBUTED only, and this reading uses their SUM.
```
  N      ku (module)   type checking median   range
  0         23,918          246.0 ms           243-249
  0         23,918          262.7 ms           247-265     ⇐ the same tree again
  128       37,038          333.9 ms           323-354
  512       88,158        1,044.0 ms          1028-1123

  B1 control         Δku 0 exactly                                                    ✅  (Δms +16.8 on identical trees)
  B2 Δms at 512      +789.7 ms against an allowance of 44.7                          ✅
  B3 Δku             +13,120 at 128 · +64,240 at 512, ×4.9                           ✅
  B4 ms per 1k Δku   6.06 at 128 · 12.29 at 512 · MARGINAL 128→512 13.89; band top 3.41 ✅  (4.1x above it)
```
⇒ **B3 CONFIRMED: ARM A would see its predecessor's positive control** — +64,240 against a band of exactly zero.
⇒ **B4 CONFIRMED, and the reading the seal did not ask for is the sharper one:** from N = 128 to 512 (×4) ku grew
×4.9 and kernel ms ×9.9 over base. **ku is near-linear in constructors and time is not**, so the under-pricing is
not a constant a budget could absorb — a ku allowance converted to time by the unfolding constant is 1.8x generous
at 128 constructors and 3.6x at 512 (6.06 and 12.29 over 3.41), and the factor rises with the size of the change.
