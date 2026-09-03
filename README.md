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

**P0 COMPLETE.** State, values, memory, the undefined-bit oracle, the
instruction AST, `step`, and one characterization theorem per form for the
twenty scalar mnemonics (`mov add sub and or xor cmp test shl shr lea inc dec
neg not push pop jmp jcc call`), in 43 forms.

**The P0 exit criterion is met:** one differential run against ACL2 x86isa —
**2924 cases, 0 unexplained disagreements**, every explained one inside the
undefined regions the SDM names. Evidence and findings in
[`docs/DIFFERENTIAL-P0.md`](docs/DIFFERENTIAL-P0.md); the run found a real model
bug (non-canonical branch targets) that nothing inside this repository could
have caught.

**P1 IN PROGRESS — 20 batches landed.** The roster now stands at
**497 of the 525 rows** in [`p1/roster.tsv`](p1/roster.tsv) — which are 349 of
the 374 distinct MACHINE FORMS those rows describe, 149 of the rows being alias
spellings or narrowings of another (`jz` for `je`, `sal` for `shl`, `stos m` for
`stos -`) — differentially tested
against ACL2 x86isa on every batch:

```
775 vectors · 82 pre-states · 63550 cases · 0 unexplained · 0 oracle leaks
```

⚠️ **THE AUTHORITATIVE LIST IS GENERATED, NOT WRITTEN HERE.**
[`docs/COVERAGE.md`](docs/COVERAGE.md) is emitted by
`lake exe x86lean-diff coverage` and carries every form's fidelity tier, its
decode-trust column and its undefined bits.

⛔ **AND EVERY NUMBER IN THE PARAGRAPH ABOVE IS GATED**, by
`scripts/check_readme_snapshot.py` in CI, against the generated coverage table
and the per-batch differential records. Until P1 batch 16 it was not, and it had
been wrong for four batches — 388 forms, twelve batches, 527 vectors — while
every other gate in the repository stayed green.

⇒ 🔑 The sentence that used to stand here said the numbers were "a snapshot" and
that the generated file "is the claim". That disclaimer is what made the
staleness invisible: it told every reader not to trust the figures, so nobody
checked them, and four batches went by. **A disclaimer is not a gate** — it
converts a wrong number into an expected one, which is strictly worse than
leaving it unqualified, because an unqualified wrong number still looks wrong to
somebody. See `docs/DECISIONS.md` D47. Per-batch evidence, including every
disagreement and every finding, is in `docs/DIFFERENTIAL-P1-BATCH*.md`, and
every design call that cost something is in
[`docs/DECISIONS.md`](docs/DECISIONS.md).

What P1 has added, in one line each: the ALU forms at every operand shape and
width including read-modify-write to memory · ADC/SBB, whose result reads a
flag · every branch condition at rel8 and rel32, plus JRCXZ/JECXZ · SETcc and
CMOVcc (120 roster forms over two `step` cases) · the shifts, SAR and the four
rotates · the bit-test group · the width-changing and two-destination moves ·
the loop group and the flag-control singles · NOP/UD2/RETQ/LEAVEQ, including the
first form whose whole meaning is a FAULT.

**Refused rather than approximated**, each with its reason recorded: `xchg` at
memory (implicit LOCK, an atomicity claim a single-threaded model cannot make),
`bswap` at 16 bits (the SDM leaves the whole result undefined, so the
undefined-BIT oracle is the wrong instrument), and the bit-string `m,r` shape of
BT/BTS/BTR/BTC.
