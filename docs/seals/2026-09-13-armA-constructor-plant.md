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
