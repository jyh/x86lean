# PRE-REGISTERED — IS A Δku BUDGET ACCURATE ACROSS THE KINDS OF KERNEL WORK, OR ONLY DECIDABLE?
# paris, 2026-09-13. Written and committed BEFORE the measurement.

## WHY — THE QUESTION D189 LEFT AS THE CRITICAL PATH
`docs/QUEUE.md` item 0b, closing D189: *"derive an unfolding budget and ask whether it is ACCURATE,
not merely decidable."* ARM A (the design of record after D187/D188) gates `Δku`, the kernel's
`unfolded declarations` counter, in place of kernel milliseconds. D185 measured it identical across
two machines; D189 measured its band to be exactly zero. **Neither says it sees every kind of kernel
work.** A gate with a zero band always decides, so a kind of work the counter cannot see would pass
with a confident, exact zero.

⛔ **THE DIMENSION NOTHING HAS VARIED.** Every reading FOR the counter so far holds the KIND of work
fixed: the tool's own linearity arms (6,002 / 12,002 / 24,002) are one plant at three sizes, and the
twelve-commit corpus is this repository's own `decide`-over-tables changes. The Lean 4 kernel does
work that is not delta-unfolding — GMP-accelerated `Nat` literal arithmetic (`Nat.add`, `mul`, `pow`,
`mod`, … on literals) and type inference over a term that needs no unfolding. A counter of
unfoldings has no stated reason to see either.

## THE PLANTS — one declaration per file, the kind varied, the size varied within a kind
Core Lean only, toolchain pinned by this repository's `lean-toolchain`. Each plant at three sizes.
```
  K1 list-decide     (List.replicate N 1).foldr (· + ·) 0 = N          by decide   delta, the corpus's kind
  K2 gmp-literal     3 ^ N % 1000000007 = r                              by decide   Nat literal arithmetic
  K3 inference       True ∧ … ∧ True (N conjuncts) := And.intro trivial …  term     no unfolding needed
  K4 bitvec-decide   N conjuncts  (a_i#64 + b_i#64 = c_i#64)             by decide   the model's own values
  K5 string-decide   "a…a" (N) ++ "b" = "a…ab"                           by decide   the mnemonic tables' kind
```
Two readings per plant, in SEPARATE elaborations so neither instrument perturbs the other:
`ku` from `set_option diagnostics true` + `diagnostics.threshold 1` (the `[kernel]` section only,
parsed by `deterministic_cost._diag_counts`); kernel ms from `profiler true` + `profiler.threshold 0`,
the `type checking took` line, repeated, median reported with its spread.
**CONTROL, first:** the same K1 file elaborated twice must read Δku = 0 exactly.

**THE STATISTIC.** For each kind, the marginal cost between its two largest sizes:
`Δms / Δku` (ms per 1k unfoldings). A kind whose `Δku` is ≤ 10 while `Δms` rises is BLIND
(the ratio is undefined; a ku budget passes it at any size).

## PREDICTIONS, SEALED
```
A1  CONTROL: the same file twice reads Δku = 0 exactly.                       HIGH
A2  K1's ku is affine in N (exactly: equal second differences).               HIGH
A3  K2 is BLIND: Δku ≤ 10 across its sizes while median kernel ms rises
    at least 5x from the smallest to the largest.                             HIGH
A4  K3 is BLIND: Δku ≤ 10 across its sizes while median kernel ms rises
    at least 3x.                                                              MODERATE
    (Risk to this one: hash-consing may make the inferred and expected types
     pointer-equal and the whole check near free, in which case ms does not
     rise either. That outcome is NOT a pass for the counter — it is "no
     cost to see" — and is reported as such.)
A5  Among the delta kinds K1, K4, K5 the marginal ms per 1k ku agrees to
    within 3x (max/min).                                                      MODERATE
A6  The corpus constant (D155/D188: 2.39 - 7.01 ms per 1k ku, k>=8, across
    two machines) overlaps the delta kinds' range on this box.               LOW-MODERATE
```

## WHAT EACH OUTCOME MEANS FOR ARM A — stated before, so a result cannot choose its reading
* **A3 or A4 CONFIRMED** ⇒ ARM A as recorded is **not accurate for that kind**: a `.lean` change
  whose cost is literal arithmetic or large inferred terms is invisible to a Δku gate at any size.
  ARM A then needs a COMPLEMENT for that kind (a coarse absolute ms ceiling is the obvious one; a
  second deterministic counter is not available from Lean's diagnostics as far as this seat knows).
  Whether this repository's `.lean` actually contains such work is a SEPARATE question and is not
  answered by a plant.
* **A3 and A4 REFUTED** (the counter rises with the work) ⇒ the blind-spot hypothesis is dead and
  the counter is better than its definition suggests; recorded as such.
* **A5 REFUTED** ⇒ even among delta kinds one unfolding is not one unit of time, and a ku budget
  cannot be converted to a time allowance by a single constant. The budget would then have to be
  stated in unfoldings only, with NO time interpretation — which is weaker than ARM A claims.
* **A6** is context, not a verdict: plants are not the corpus.

## ⛔ WHAT THIS CANNOT DO, STATED BEFORE IT RUNS
* It derives **no budget** and **lands no branch.**
* A plant is not the repository. It says which KINDS the counter can see; the repository's own
  mix of kinds is a census question this seal does not ask.
* Kernel ms is a single-box, single-session reading with its load recorded; it is used for RATIOS
  within one run, never quoted as an absolute.
* Run on yukon, after the G5 x86isa certification run finishes, so the two do not share the box.

SEALED 2026-09-13, before the measurement.

---

# ⚖️ THE RESULT — every prediction CONFIRMED, on two complete runs; ARM A is blind to two kinds
Corpus: `docs/ku-kind-plants-2026-09-13.json` (run 4, with its `origin`: Lean 4.32.0-rc1 arm64, 14 CPUs,
load1 3.96 → 3.94, 5 ms repeats a plant). Run 3, minutes earlier and without the origin block, is the
reproduction column. Decision record: `docs/DECISIONS.md` D228.
```
                         run 4 (corpus)                         run 3
  A1 control             ku 4816 / 4816, Δ 0          ✅       Δ 0
  A2 K1 affine           4816 · 9616 · 19216 = 12N+16 ✅       identical
  A3 K2 gmp-literal      ku 10 at 1M · 4M · 16M; ms 2.1 → 50.7, 24.3x   ✅ BLIND    24.0x
  A4 K3 inference        ku 0 (no [diag] at all); ms 1.7 → 23.3, 13.6x   ✅ BLIND    13.3x
  A5 delta kinds         K1 2.562 · K4 1.652 · K5 3.411 ms/1k ku, max/min 2.06x (bound 3)  ✅   2.44x
  A6 corpus 2.39–7.01    overlaps 1.65–3.41 on 2.39–3.41  ✅ (context only)
```
⚠️ **READ THE MARGIN ON A5:** 2.06x and 2.44x against a bound of 3 — 69% and 81% of it.

## ⛔ TWO HARNESS DEVIATIONS FROM THE SEAL'S TEXT, BOTH BEFORE ANY VERDICT WAS READ
* **K2's sizes.** The sealed statement was `3 ^ N % 1000000007 = r by decide`; sizes were not sealed. The first
  run REFUSED at N = 80,000 with `maximum recursion depth has been reached`, at elaboration. Measured the same
  minute: refused at 80k, 1M and 4M without `set_option exponentiation.threshold 20000000`, and elaborated with
  ku 10 at all three with it (the option's default is 256; that the elaborator unfolds `^` above it is this
  seat's reading of the symptom, not verified in Lean's source). Both headers now set it, and K2 runs at
  1M / 4M / 16M, kept under 2^24 on the belief that the kernel's literal `Nat.pow` is bounded there (also NOT
  verified here; 16M elaborated and checked). The KIND is unchanged.
* **K4's sizes.** 100 conjuncts failed `Decidable` instance synthesis; K4 runs at 12 / 25 / 50. Run 2 read 25 and
  50 before failing, at 1551 / 3101 ku, identical to run 4.

## WHAT IT MEANS, AS SEALED
**A3 and A4 CONFIRMED ⇒ ARM A as recorded is NOT ACCURATE for literal arithmetic or for large no-unfolding
terms:** a `.lean` change whose kernel cost is either is invisible to a Δku gate AT ANY SIZE, reading an exact
zero with a zero band — a confident pass. **A5 CONFIRMED ⇒ among unfolding kinds one constant converts ku to time
to within ~2–2.5x**, so a ku budget does carry a time interpretation for the work it can see.
📌 **The separate question the seal declined, read once afterwards and NOT sealed:** at `5c01599` the ms and ku
corpora share `Tests.Coverage`, and its 27 profiled declarations (19,597 of ~20,900 ms) contain **no** declaration
with ku < 10 and ms ≥ 50. The blind kinds are absent from the ONE module ku has ever been walked on — which is
the module chosen because it is the `decide`-over-tables kind. **No other module has a ku reading.**
