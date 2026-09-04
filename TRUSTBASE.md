# TRUSTBASE — what a theorem in x86lean depends on

## Axiom policy (the ruling of record, 2026-09-02)
- Every theorem in the main tier (everything outside `X86.Native` and the test tree) depends on at
  most the three standard axioms: `propext`, `Classical.choice`, `Quot.sound`.
- `bv_decide`, `native_decide`, and anything that introduces `Lean.ofReduceBool` or a per-computation
  native axiom are CONFINED to (a) test executables and (b) the separately labelled tier `X86Native`,
  which has its own CI gate line and its own column in the coverage table, and which no main-tier
  theorem imports. (Amended at P0: a separate `lean_lib` rather than a sibling module `X86.Native`,
  because a sibling module is one stray `import` away from the model tree while a separate library
  cannot be imported by accident. See docs/DECISIONS.md D7.)
- The CI gate is an ALLOWLIST of exactly the three names, checked per declaration. It is NOT a
  denylist of `Lean.ofReduceBool`: since Lean 4.29.0 each native computation is represented as its own
  auto-generated axiom, so a name-based denylist misses them. The gate is driven red-first with a
  deliberate `native_decide` before it is trusted.
- ✅ DRIVEN AT P0, and the trap is now MEASURED rather than inherited: on Lean 4.32.0-rc1 the
  `native_decide` in `X86Native.addByteZf_native` introduces the axiom
  `X86Native.addByteZf_native._native.native_decide.ax_1_1` — a per-computation name, NOT
  `Lean.ofReduceBool`. A denylist keyed on `Lean.ofReduceBool` passes that file in silence.
  `scripts/axiom_gate_selftest.sh` is the standing evidence that the allowlist fires.

## Decode trust
The model's AST is produced by Intel XED (Apache-2.0) in phase 1; a Lean decoder for the covered
subset is a later phase. Until then, "this instruction's bytes mean this AST node" is TRUSTED, not
proven, and the coverage table carries a decode-trust column saying so per form.

## The undefined-bit oracle
Where the SDM says a flag or result is undefined, the model draws the value from an oracle stream in
the state (a cursor and a `Nat → Bool`/byte stream). Theorems cannot learn the drawn value; the
nonvacuity check (two oracles, two results) is a test. This is the ACL2 x86isa `UNDEF` discipline.

## Atomicity is RECORDED, never verified (P2 batch 23)

`Ea.lock` records that a memory access is architecturally atomic — the `f0` prefix, or `xchg`'s
implicit LOCK. **It is not a claim that this model verifies anything about concurrency.**

A single-step, single-threaded semantics has no observation that distinguishes an atomic
read-modify-write from a non-atomic one: `lock addq %rcx, (%rbx)` and `addq %rcx, (%rbx)` compute
the same state transition here, and every differential case agrees with the oracle either way.
What the vocabulary buys is the ability to SAY the property, which is what D25 said the model
lacked when it declined `xchg` at memory — and the ability to enforce the SDM's rule about where
the prefix is legal, which is observable (a `lock` on a form the manual does not list is #UD, and
the `refused` channel compares it).

⇒ **The trust boundary, stated plainly:** a reader may rely on this model for what a locked
instruction COMPUTES and for WHICH forms accept the prefix. A reader may not rely on it for
memory ordering, for interleaving with another thread, or for anything a memory model would have
to say. Multi-threading and memory ordering are v0.x non-goals (plan v1 §1), and this field does
not quietly change that.

## What is validated, not proven
Agreement with ACL2 x86isa, with K, and with real hardware is EVIDENCE gathered by execution
(differential and co-simulation runs recorded per form), never a theorem about those systems.

## Kernel cost
Kernel time is measured in CI and gated at a registered ceiling; a blowup on a composite is a stop
condition, posted, never worked around by defeq.

P0 MEASUREMENT (`scripts/kernel_cost.py`, the §3.3 measurement): **606 ms of kernel (type-checking)
time across the whole development**, 18 modules, on the three-axiom route. The measurement is
reported, not obeyed — the axiom base was fixed by ruling, not by this number. Ceilings are
registered per module at 3x baseline with a 50 ms floor (docs/DECISIONS.md D8).
