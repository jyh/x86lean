# P1 BATCH 17 — the multiply-divide group, and the fault that is the majority

**Forms.** Roster family 27 and the `div`/`idiv` half of family 24: `mul` and `imul` at
six operand shapes, `div` and `idiv` at `r` and `m`. **12 roster rows, 4 roster
mnemonics, 32 differential vectors**, taking the model to **441 of the 525 rows (84%)**.

```
cases=54038  matched=37039  explained=24941  unexplained=0  oracle-leaks=0  missing=0
  spec: 0   refusal: 0   harness: 0   undefined-region: 24941
659 vectors · 82 pre-states · 79 mnemonics
```

Gate met on the FIRST run, in 1 m 58 s.

⚠️ **Twelve rows, four mnemonics, thirty-two vectors — three counts again, and `imul` is
why the middle one is not eight.** `imul` is ONE roster base name spread over SIX shapes
and TWO of this model's constructors: `.muldiv .imul` for the one-operand form that writes
`RDX:RAX`, and `.imulr` for the two- and three-operand forms that write one register.

## ⛔ The scope was wrong when it arrived — see D49

The handover named this batch as "families 14/23/27/24". Family 23 was already discharged
(it is eight of batch 16's own eleven prefixed rows); `cmpxchg`/`xadd` also occupy family
10 and `shld`/`shrd` also occupy family 40, so the family list does not partition the
mnemonics it names. **A handover's scope is a hypothesis; the roster is the authority and
the family column is a hint.** The counting rule actually used is by base name:

```
awk -F'\t' 'NR>2 && $4 ~ /^(mul|imul|div|idiv)$/' p1/roster.tsv | wc -l   →  12
```

`xadd`/`cmpxchg` (4 rows) and `shld`/`shrd` (8 rows) are batch 18.

## The probe, run before a vector existed — 2 runs, 801 cases, 9.0 s

**Probe 1 — support.** 29 candidate forms × 5 hand-built pre-states = 145 cases, 4.5 s.
All 29 are executed by x86isa — 1-, 2- and 3-operand `imul`, register and memory, every
width — with **zero refusals across the whole multiply group in all five states**.
Measured by executing (D36), never read off a catalogue.

**Probe 2 — the fault law**, on the harness's OWN eighty-two pre-states. The cases were
built by patching the bytes of the emitted `mov_d` cases, so the pre-states are the
differential run's rather than a re-implementation of them. 8 forms × 82 = 656 cases,
4.5 s.

| form | quotient computed | #DE zero divisor | #DE quotient overflow | oracle refused | mismatches |
|---|---|---|---|---|---|
| `div_b` | 39 | 20 | 23 | 43 | **0** |
| `idiv_b` | 40 | 20 | 22 | 42 | **0** |
| `div_w` | 24 | 17 | 41 | 58 | **0** |
| `idiv_w` | 13 | 17 | 52 | 69 | **0** |
| `div_l` | 20 | 14 | 48 | 62 | **0** |
| `idiv_l` | 17 | 14 | 51 | 65 | **0** |
| `div_q` | 14 | 8 | 60 | 68 | **0** |
| `idiv_q` | 19 | 8 | 55 | 63 | **0** |

**656 of 656 agree with the SDM's stated rule** — refuse iff the divisor is zero or the
quotient does not fit — at both signednesses and all four widths.

## ⛔⛔ What the measurement overturned — see D50

The bank warned that the fault would be hard to REACH and that `adversarial` should be
checked for it "rather than assumed". Checked; and the answer is the opposite.
**51%–84% of pre-states FAULT**, and at `idiv_w` only 13 of 82 divide. `mkPre` sets
`RDX := ~RAX`, put there in batch 10 for `cltd`, and a huge high half is exactly what
makes a quotient too wide.

⇒ **A group that mostly refuses is a group whose agreement is mostly silence.** Both
models refuse, the comparator records a match, and the quotient is never examined. No new
pre-state was needed — but the batch needed an arm whose only job is to prove the quotient
is observed at all.

## The seven arms, and what each is worth

| arm | field | catches |
|---|---|---|
| `div` refuses on every divisor — the observation control | `refused` | **145** |
| `div` forgets that an over-wide quotient is also #DE | `refused` | 236 |
| `idiv` rounds toward negative infinity instead of toward zero | `rax` | 63 |
| `idiv`'s remainder takes the divisor's sign | `rdx` | 55 |
| `imul` takes MUL's overflow rule | `cf` | 49 |
| `imul`'s three-operand form multiplies its destination | `rax` | 220 |
| the byte multiply writes `DX:AX` instead of `AH:AL` | `rdx` | 134 |

Three of the seven attack the FAULT rather than the arithmetic, which is the shape the
measurement dictated. The first is the positive control: without it the batch would have
had no evidence that the non-faulting path is tested at all.

## What was subtle

**The pair is `AH:AL` at eight bits and `RDX:RAX` at the other three.** One register at one
width, two at the rest — addressed through `Cpu.mdHi` and `Cpu.setMdPair` so the asymmetry
exists in exactly one place. `wrongMulBytePairInRdx` is the model with it forgotten, and it
is correct at three widths out of four.

**IMUL's overflow rule is not MUL's.** MUL sets CF when the high half is non-zero; IMUL
sets it when the full signed product differs from the sign-extension of the low half. They
agree on positive products and disagree on negative ones: `0xFF * 0xFF` at `.b` is
`-1 * -1 = 1` with no overflow, and `255 * 255 = 65025`, which does not fit.

**IDIV truncates toward zero and Lean's `Int` division does not.** `-7 / 2` is `-3`
remainder `-1` on the machine and `-4` remainder `1` in Lean's `/` and `%`. The model uses
`Int.tdiv`/`Int.tmod`; that one substitution is the whole difference between IDIV and a
plausible model of it, and it is invisible on every non-negative dividend.

**A label that lied, and the reason it matters.** The support probe's pre-state named `ok`
is a fine non-faulting state at `.w`/`.d`/`.q` and a ZERO-DIVISOR state at `.b`, because
the divisor is `CL` — the low byte of 0x1000 — which is zero. ⇒ **The fault condition is a
function of the TRUNCATED operand**, so a divisor list that is "all non-zero" is not a
non-zero-divisor list at every width.

**A shapes-column claim no gate could read.** `mul`'s memory operand is a SOURCE, so every
memory-DESTINATION gate in `Tests/Coverage.lean` is blind to it. `muldiv_memory_vectors_
are_exactly_b_and_q` is stated as an equality and fails in both directions.

**The citation gate caught this batch's own slip, one batch after it was built.** A
docstring in `X86/Value.lean` cited `Cpu.divPair` "in `X86/Semantics.lean`"; the functions
are `Cpu.mdHi` and `Cpu.setMdPair` and no `Cpu.divPair` was ever written. D48's class,
caught in seconds by the gate D48 produced.
