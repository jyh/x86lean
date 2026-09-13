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
