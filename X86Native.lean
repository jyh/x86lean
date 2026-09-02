/-
# X86Native — the SEPARATELY LABELLED native-computation tier

Plan v1 §3.3: `bv_decide`, `native_decide`, and anything introducing
`Lean.ofReduceBool` or a per-computation native axiom are CONFINED to (a) test
executables and (b) THIS tier, which has its own CI gate line, its own coverage
column, and which NOTHING in the `X86` library imports.

⛔ NOTHING IN `X86` MAY IMPORT THIS MODULE.  That is checked mechanically:
`scripts/check_tier_isolation.sh` greps the `X86` tree for `X86Native` and fails
on a hit, and the axiom gate would in any case catch the leak the moment a
native axiom reached a main-tier theorem.

⭐ THIS FILE IS ALSO THE GATE'S RED-FIRST DRIVE.  `nativeWitness` below really
does use `native_decide`, so it really does carry an axiom outside the
allowlist, and `scripts/axiom_gate_selftest.sh` runs the gate over this module
with `--expect-violation`.  A gate that has never been observed to FAIL is not
known to be a gate — and in this specific case the failure mode is not
hypothetical: Lean ≥ 4.29 mints a fresh per-computation axiom NAME, so the
denylist most projects would have written passes this file silently.
-/
import X86

namespace X86Native
open X86

/-- A closed fact about the model, established by NATIVE evaluation rather than
by kernel reduction.  Its content is deliberately trivial — its JOB is to carry
a native axiom so the allowlist gate can be seen to fire.

The fact itself: over all 256 byte values `a`, `add` at width 8 sets ZF exactly
when `a + 1` wraps to zero.  A kernel `decide` could do this too; the point is
the ROUTE, not the result. -/
theorem addByteZf_native :
    (List.range 256).all (fun a =>
      (Flags.add .b (BitVec.ofNat 64 a) 1 {}).zf == (a == 255)) = true := by
  native_decide

set_option maxRecDepth 8000 in
/-- The same fact by the KERNEL, so the tier boundary is not hiding a
disagreement: if these two ever differed, the model's compiled behaviour and its
kernel behaviour would have diverged, which is the one thing a differential
harness built on the COMPILED model could not detect by itself.

⚠️ It needs `maxRecDepth 8000` where the native route needs none: that is the
kernel-cost asymmetry of plan v1 §3.7 showing up at 256 cases, and it is a
measured fact worth carrying rather than a nuisance to silence. -/
theorem addByteZf_kernel :
    (List.range 256).all (fun a =>
      (Flags.add .b (BitVec.ofNat 64 a) 1 {}).zf == (a == 255)) = true := by
  decide

end X86Native
