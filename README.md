# x86lean

A **user-level x86-64 ISA semantics in Lean 4** — definitional, executable,
kernel-checked, and differentially validated against public executable models
and (from P1) against real hardware. Built from **public sources only** and
intended to be permissively licensed and published.

See [`PROVENANCE.md`](PROVENANCE.md) for every source and its licence,
[`TRUSTBASE.md`](TRUSTBASE.md) for what is proven and what is trusted,
[`docs/DECISIONS.md`](docs/DECISIONS.md) for the P0 decisions and their reasons,
and [`docs/COVERAGE.md`](docs/COVERAGE.md) for the generated coverage table.

## What kind of semantics

A **small-step operational** semantics: each instruction form is a TOTAL state
transformer

```lean
def step (i : Instr) (s : Cpu) : Cpu
```

an interpreter in Lean, in the style of ACL2 x86isa and LNSym — not a rewriting
system, not an axiomatic ISA. It is operational because differential testing and
hardware co-simulation need something that RUNS, and the definition the theorems
are about must be the same one the harness executes.

**Hoare logic is a layer derived on top, never the base.** Every form has a
characterization theorem of the shape

```lean
step i s = { s with … }
```

which is a frame condition as well as a result: every field not named is
unchanged, so an incomplete frame is impossible rather than merely unlikely.
That equation is exactly what a machine-code Hoare triple or a big-step block
semantics consumes, and since each is a theorem about `step`, any logic layered
on it is sound by construction.

## What the model refuses to invent

Where the Intel SDM says a flag is *undefined*, this model does not write
`false` — it draws from an **adversarial oracle** carried in the state, so no
theorem can learn the value. The draw is visible in the theorem statement:

```lean
step ⟨.bin .and sz (.reg r) (.reg r'), len⟩ s =
  { s with regs := …,
           flags := Flags.logic … (s.oracle.bits s.oracle.cursor) s.flags,
           oracle := { s.oracle with cursor := s.oracle.cursor + 1 },
           rip := s.rip + BitVec.ofNat 64 len }
```

`add` spends no oracle bits; `and` spends one (AF); a non-zero-count shift
spends three (CF, OF, AF). `Tests/Nonvacuity.lean` proves both halves of the
claim: the undefined bits really do move with the oracle, and the **defined**
ones really do not.

## Building

```bash
lake build X86 X86Native Tests x86lean-diff x86lean-axioms
```

Lean 4 core only — **no mathlib dependency** (see `docs/DECISIONS.md` D1). The
toolchain is pinned in `lean-toolchain`.

## The gates

| gate | what it asserts |
|---|---|
| `scripts/axiom_gate.sh` | every declaration in `X86` depends on exactly `propext`, `Classical.choice`, `Quot.sound` |
| `scripts/axiom_gate_selftest.sh` | the gate FIRES on a real `native_decide` — red-first, not a fixture |
| `scripts/check_tier_isolation.sh` | no module under `X86/` imports the native tier |
| `scripts/check_encodings.py` | every `Instr.len` and byte string agrees with a real assembler |
| `scripts/kernel_cost.py` | per-module kernel time under its registered ceiling |
| `x86lean-diff selftest` | the differential comparator catches three planted bugs |

**On the axiom gate being an allowlist.** The obvious gate rejects anything
depending on `Lean.ofReduceBool`. It does not work: since Lean 4.29 each
`native_decide` mints a fresh *per-computation* axiom name, so a denylist sees
nothing and passes. Measured on 4.32.0-rc1, the axiom introduced by this
repository's own deliberate `native_decide` is
`X86Native.addByteZf_native._native.native_decide.ax_1_1`.

## Status

**P0.** State, values, memory, the undefined-bit oracle, the instruction AST,
`step`, and one characterization theorem per form for the twenty scalar
mnemonics (`mov add sub and or xor cmp test shl shr lea inc dec neg not push pop
jmp jcc call`), in 43 differentially tested forms. All gates green; the ACL2
x86isa differential run is the P0 exit criterion and is in progress.
