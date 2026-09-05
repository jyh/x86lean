# P2 BATCH 16 — `movhps`, and the half that does not move

> ⚠️ **TWO COUNTERS.** Sixteenth differential record; the seat's **batch 20** in
> `docs/DECISIONS.md`.

**Form.** `movhps` at both directions — `0f 16` loads, `0f 17` stores. One roster
row for both (one mnemonic, two opcodes), 6 vectors, two new AST constructors
(`Op.vloadh`/`Op.vstoreh`), **no new state**. **3,672 instructions** of the
assembly class.

⭐ **The first member of the never-asked scalar-SSE-FP group to land** (D118): six
mnemonics worth 26,757 instructions that the residue had been reporting as absent
because a bank's closing sentence offered a two-valued partition — "refuses or
VEX" — for a three-valued remainder. `movhps` is the one of the six that needs no
floating-point arithmetic at all.

## 1. THE CONTENT IS THE HALF THAT DOES **NOT** MOVE

Load: `dst[127:64] ← m64`, and **`dst[63:0]` is PRESERVED**.
Store: `m64 ← src[127:64]`.

⛔ **So the plausible wrong model is the one that CLEARS the low half**, and it is
bit-identical to the right one at every pre-state whose low quadword is already
zero. ⭐ It is the exact MIRROR of D93: there ACL2 x86isa **merged** what the SDM
clears (`movd` into XMM); here the SDM **preserves**, so the direction of the
plausible error reverses with it. Measured against the oracle, three wrong models,
88 pre-states:

```
                                        loads-low   clears-low   stores-low
movhps (loads, xmm0)                          146          152            —
movhps (store, mem@…1fe0)                       —            —          208
```

⚠️ **`clears-low`'s 152 is a joint fact about the model and the pre-states**, not
a property of the instruction: what refutes it is `xmmPattern` giving xmm0 a
NON-ZERO low quadword. A pre-state table that zeroed the destination would have
scored it 0 disagreements and reported green about a model that destroys half the
register on every load.

## 2. ⛔ NO ALIGNMENT RULE, AND THE ABSENCE IS MEASURED RATHER THAN ASSERTED

The memory operand is **eight bytes**, so SDM Exception Type 5 applies and there
is no 16-byte requirement. D110 is why that sentence is not left to a comment:
there, *"NO ALIGNMENT CHECK … the absence is the rule"* was written about a group
that **did** have one, and the model's missing check and the oracle's missing
check were the same omission — two defects that cancel.

So it was measured, with a **two-sided control in the same run**:

```
movhps (%rbx) / 4(%rbx) / 8(%rbx), both directions   EXECUTES at every alignment
pand 0x8(%rbx),%xmm0    [the one x86isa file that checks 16 bytes]      REFUSES
pand (%rbx),%xmm0                                                      EXECUTES
```

⇒ The harness demonstrably **can** see an alignment refusal, so `movhps`'s silence
is a reading rather than a blind spot. K's rules carry no check either (third
source, independent of both).

⚠️ **The unaligned vectors sit at displacement 4, not 8.** Eight is still 8-byte
aligned and could not distinguish "no alignment rule at all" from "an 8-byte
rule". `0x2004` is aligned to four and to nothing more. Both addresses were
checked to lie inside the watched window (`0x1fe0` + 64) rather than assumed.

## 3. TWO CONSTRUCTORS, AND NOT A `VMovKind`

`Op.vloadh`/`Op.vstoreh` are two, for the reason `vload`/`vstore` are two: an
operand pair admitting `mem` on both sides could spell `movhps (%rax),(%rbx)`,
which no encoding produces — the illegal state is unrepresentable rather than
checked.

⛔ And it is deliberately **not** a fifth `VMovKind`. That type's entire content is
`VMovKind.aligned`, the 16-byte rule; a member whose answer to it is meaningless
is a field someone reads eventually. ⚠️ Two of the six vectors use `%xmm5` for
D90's reason: every vector of batch 5 moved xmm1 into xmm0, so a model with fixed
register fields was bit-identical to the real one and the fields were decoded by
nothing.

## 4. RECEIPTS

```
cases=83600 matched=63068 explained=29435 unexplained=0 oracle-divergence=171 oracle-leaks=0 missing=0
950 vectors · 88 pre-states · 83600 cases · 0 unexplained · 0 oracle leaks
```

⚠️ 171 oracle-divergences, unchanged; this batch adds none.

⛔ **The kernel-cost gate REFUSED rather than reporting**: one-minute load 4.61,
outside the band its own effect-measurement covers (0.0–4.1), because this batch's
own selftest and differential had just run. It prints its readings and withholds a
verdict, which is the right refusal — a machine-calibrated gate that answered here
would be reporting the machine. Re-measured on a quiet machine; see the commit
message. ⚠️ `vectorCoverage` sits at 1680 of its 1760 ceiling — **95%, and the
margin is the number to read, not the verdict**.

The remaining local gates and the CI run URL are in the commit message.
