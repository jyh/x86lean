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

## SSE availability is ASSUMED, never modelled (P2 vector wave, batch 1)

Real hardware raises `#UD` on every SSE instruction when `CR4.OSFXSR` is 0 — the bit by which an
operating system declares it has FXSAVE storage and an SSE-exception handler. **x86lean does not
model that check.** `X86/State.lean` has no control-register file; the model computes a vector
form's result unconditionally, as though the OS had already enabled SSE.

The oracle is CONFIGURED TO MATCH rather than left to disagree: `scripts/x86isa_driver.lisp` sets
`CR4 = 0x600` (`OSFXSR | OSXMMEXCPT`) in the pre-state of every differential case, so both sides
answer the same question. Before this batch it passed `nil`, and x86isa refused every SSE form
exactly as hardware would — a disagreement about the machine's CONFIGURATION that would have been
read as a disagreement about its SEMANTICS.

⇒ **The trust boundary, stated plainly:** a reader may rely on this model for what an SSE
instruction COMPUTES on a machine where SSE is enabled — which is every 64-bit OS in ordinary use.
A reader may NOT rely on it to decide whether a given instruction faults on a machine where it is
not: this model will happily compute a result where hardware raises `#UD`. Modelling the
availability check means adding CR4 to the state, and that is not free (D71 measured what a `Cpu`
field costs every record proof); it is a v0.x non-goal until something needs it.

⚠️ The configuration is GATED, not asserted: `scripts/check_driver_cr4.py` runs SSE forms through
`x86l-run-case` under the shipped driver and under a driver whose `*x86l-ctrs*` is planted back to
`nil`, and requires that they execute in the first and refuse in the second (D86).

## MXCSR: every exception MASKED, no DAZ, no FZ (sub-group B0, D266)

`Cpu.mxcsr` holds the SSE control/status register. The landed floating-point forms OR the sticky
exception flags they raise into it (`Cpu.withSimd`), and the differential compares each flag.
**Two things are assumed, not modelled:**
- **Every exception is masked.** An instruction that would raise an UNMASKED exception refuses
  (`byDesign`) instead of delivering `#XM`. x86isa halts there too, so the two agree on the refusal,
  and no pre-state unmasks one, so the refusal path is never compared.
- **DAZ and FZ are clear.** No form reads either bit. A program that sets them gets this model's
  answer for a machine where they are clear.

**RC is READ, since sub-group B1 (D268):** `mulss`/`mulsd`, and since B2 (D271) `addss`/`addsd`/`subss`/`subsd`/
`divss`/`divsd`, round under MXCSR bits 13–14, and every
pre-state index meets all four modes. Tininess is detected AFTER rounding, the rule x86isa and both
processors below follow.

The pre-states vary RC and preset the sticky bits (never OE: x86isa reads a preset OE as a
conversion's overflow, D266 §4); the masks stay set and DAZ/FZ stay clear. A reader may rely on the
flags a form raises under those conditions, and on nothing about an unmasked exception or about DAZ/FZ.

## What is validated, not proven
Agreement with ACL2 x86isa is EVIDENCE gathered by execution (the differential runs recorded in
`docs/DIFFERENTIAL-*.md`), never a theorem about that system.
⛔ *This paragraph read "Agreement with ACL2 x86isa, with K, and with real hardware is EVIDENCE
gathered by execution (differential and co-simulation runs recorded per form)" until 2026-09-12.*
**Two of its three sources have never been run:** K is READ — for coverage, and to arbitrate a
disagreement, as each `knownDivergences` entry's source field shows — and has never been executed by
this project; no hardware co-simulation has been run (`docs/COSIM-DESIGN.md` is a design). A policy
sentence that names evidence categories reads as a statement that the evidence exists.
⚠️ *Since 2026-09-17 one processor HAS been read, and for rules rather than for this model:*
`hwprobe/` ran 174 SDM-derived rows on an AMD EPYC 7763 (D266 §5) and on an Intel Core i7-8700B
(D267 §10), and both agreed with all of them; with B2's 110 add, sub and divide rows added, both read
all 284, their outputs byte-identical (D269). B3's 77 `cvtsd2ss` rows make 361, read with byte-identical outputs on
the EPYC, the i7-8700B and an Intel Xeon Platinum 8370C (D272). ubuntu-latest drew the Xeon on one run and the EPYC on
another, so the processor belongs to a RUN, not to the runner label. B4's 127 integer-conversion rows make 488, read with
byte-identical outputs on the EPYC and the i7-8700B (D274). The 155 rows the differential cannot carry are kernel
pins in `Tests/Anchors.lean` (D267 §2, D268, D271, D273), so for those rows the model is checked against rules
processors confirmed (two for B0–B2's rows, three for B3's). That is still not a co-simulation of `step`.

## Kernel cost
Kernel time is measured in CI and gated at a registered ceiling; a blowup on a composite is a stop
condition, posted, never worked around by defeq.

P0 MEASUREMENT (`scripts/kernel_cost.py`, the §3.3 measurement): **606 ms of kernel (type-checking)
time across the whole development**, 18 modules, on the three-axiom route. The measurement is
reported, not obeyed — the axiom base was fixed by ruling, not by this number. Ceilings are
registered per module at 3x baseline with a 50 ms floor (docs/DECISIONS.md D8).
