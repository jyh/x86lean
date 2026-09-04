# x86lean

A **user-level x86-64 ISA semantics in Lean 4** — definitional, executable,
kernel-checked, and differentially validated against public executable models
and (from P1) against real hardware. Built from **public sources only** and
intended to be permissively licensed and published.

See [`PROVENANCE.md`](PROVENANCE.md) for every source and its licence,
[`TRUSTBASE.md`](TRUSTBASE.md) for what is proven and what is trusted,
[`docs/DECISIONS.md`](docs/DECISIONS.md) for the P0 decisions and their reasons,
and [`docs/COVERAGE.md`](docs/COVERAGE.md) for the generated coverage table.

## What this is

x86lean is an executable, machine-checked semantics of **user-level 64-bit x86**
in Lean 4. It answers one question exactly: given the processor's visible state
and one instruction, what is the state afterwards. Every instruction form is a
total function `step`, and every form has a theorem stating its effect as an
equation on the state record, so what a form does not change is **proved**
unchanged, not assumed.

It is built from public sources only: the Intel SDM for the intent, and three
executable models the SDM's prose is checked against — ACL2 x86isa, the K
semantics of x86-64, and Sail — plus Intel XED for decoding. Where the SDM
leaves a bit undefined the model does not pick a value: it draws one from an
oracle carried in the state, so no theorem can depend on it. The whole main tier
depends on exactly the three standard Lean axioms and nothing else, gated per
declaration in CI.

### What it covers

- **Scope.** The integer instruction set of 64-bit mode as a user program sees
  it: registers, flags, RIP, RSP, a byte-addressed memory, and the undefined-bit
  oracle. Single-threaded, one instruction at a time.
- **Instructions.** 84 mnemonics in 804 differentially tested forms, covering
  500 of the 525 rows of the P1 roster — the rows are K's grammar of encodable
  forms, and 149 of them are alias spellings of another row. The moves, the ALU
  group at every width and operand shape including read-modify-write to memory,
  the shifts and rotates, the bit-test and bit-count groups, conditional set and
  move, the branch and loop group, push/pop/call/ret, the string instructions
  with their repeat prefixes, multiply and divide, compare-exchange (including
  `cmpxchg8b`) and the double-width shifts.
- **Fidelity per form** is stated in [`docs/COVERAGE.md`](docs/COVERAGE.md),
  generated from the model: `T-exact` (the result and every flag the SDM defines
  are proved), `T-frame` (the defined parts proved, the undefined bits declared
  and drawn from the oracle), and a decode-trust column.
- **Validation.** Every form is run against ACL2 x86isa on 69144 generated cases
  with zero unexplained disagreements; disagreements inside SDM-undefined
  regions are recorded as such per form. Agreement is evidence gathered by
  execution, never a theorem about the other model.

### What it does not cover — yet

- **Not in scope.** SIMD and floating point (SSE, AVX, x87), segmentation and
  paging, privileged and system instructions, interrupts and exceptions beyond
  the faults named below, memory ordering and multi-threading, 32-bit and 16-bit
  modes.
- **No decoder yet.** "These bytes mean this instruction" is trusted to Intel
  XED and recorded as trusted in the coverage table. A Lean decoder for the
  covered subset is a later phase.
- **Rows of the roster not modelled, with the reason** — 25 of 525, and
  **nothing on that list is merely undone**:
  - 19 rows the oracle does not implement (the BMI group and `movnti`), so no
    differential evidence can exist for them. Measured by executing them, not
    read off a catalogue (`scripts/oracle_availability.py`); a second oracle is
    the route.
  - 2 rows that describe no encoding at all — `jecxz rel32` and `jrcxz rel32`,
    which the assembler refuses because those instructions have only an 8-bit
    displacement.
  - 4 rows declined on record: the bit-string `m,r` shape of
    `bt`/`bts`/`btr`/`btc`, where the offset is signed and the effective address
    moves with it (`docs/DECISIONS.md` D23). ⚠️ That is a decision and not an
    oracle limitation: all four execute on ACL2 x86isa, and the availability
    gate records it so the reason cannot quietly be re-read as "unsupported".
    ⭐ It was **6** until P2 batch 23: `xchg` at a memory operand was declined
    because its implicit LOCK is an atomicity claim a model with no LOCK
    vocabulary could neither make nor break (D25), and the LOCK vocabulary is
    what that addition added. The two rows are claimed now, and the claim is
    gated — `scripts/claimed_forms.py` requires every row it records as
    unblocked to be in the claimed set, so shrinking this residue cannot be a
    deletion nobody checked.
  - 0 rows of available work. This is what the number means: the residue is
    fully accounted for, and the partition is checked rather than asserted.
- **Faults** are modelled as refusals of `step`, not as exception delivery:
  division by zero and quotient overflow, `ud2`, non-canonical addresses.
- **Hardware co-simulation** against a real x86-64 processor is planned and not
  yet run. ACL2 x86isa is the only oracle so far.

### How to use it

Build — Lean 4 core only, no mathlib:

```bash
lake build            # X86, X86Native, Tests, x86lean-diff, x86lean-axioms
```

State a fact about an instruction. Each form's characterization theorem is an
equation you can rewrite with, and it names every field that changes — so the
frame comes with the result:

```lean
import X86
open X86

-- `Live s` says the model has not halted; `h` is what every characterization
-- theorem takes, because a halted state is not a state an equation is about.
example (s : Cpu) (h : Live s) :
    (step ⟨.bin .add .q (.reg .rax) (.reg .rbx), 3⟩ s).regs.get .rcx
      = s.regs.get .rcx := by
  simp [step_add_reg_reg .q .rax .rbx h]
```

Run the harness:

```bash
lake exe x86lean-diff coverage docs/COVERAGE.md   # regenerate the coverage table
lake exe x86lean-diff selftest                    # the comparator catches its planted bugs
lake exe x86lean-diff selftest cmpxchg8b          # …just the arms whose name matches
./scripts/run_differential.sh                     # the differential run (needs the oracle)
./scripts/oracle_availability.py                  # what the oracle will and will not execute
```

Add a form: a constructor in the AST, its `step` case, its characterization
theorem, a vector in the roster's spelling, and a differential run.
`python3 scripts/claimed_forms.py --remaining` lists the unclaimed rows with
their shapes and says which bucket each is in.

Read the trust story before citing a theorem:
[`TRUSTBASE.md`](TRUSTBASE.md) (what is proven, what is trusted, what is
validated), [`PROVENANCE.md`](PROVENANCE.md) (every source and its licence), and
[`docs/DECISIONS.md`](docs/DECISIONS.md) (every design call and its reason).

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

**P1 SEALED — 21 batches landed. P2 IN PROGRESS — 4 batches landed.** ⭐ **P1's AVAILABLE WORK IS ZERO**: every
remaining row either has no encoding, is refused by the oracle at every
pre-state (measured, `scripts/oracle_availability.py`), or was declined by a
recorded decision. The roster stands at
**500 of the 525 rows** in [`p1/roster.tsv`](p1/roster.tsv) — which are 350 of
the 374 distinct MACHINE FORMS those rows describe, 149 of the rows being alias
spellings or narrowings of another (`jz` for `je`, `sal` for `shl`, `stos m` for
`stos -`) — differentially tested
against ACL2 x86isa on every batch:

```
804 vectors · 86 pre-states · 69144 cases · 0 unexplained · 0 oracle leaks
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
