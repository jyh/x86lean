# P1 BATCH 20 — the shapes the model could always express, and the three claims nothing could see

**Forms.** The 28 roster rows that `scripts/claimed_forms.py --remaining` named as AVAILABLE
work: the memory-DESTINATION and accumulator-short forms of `add`, `sub`, `adc`, `sbb`, plus
`mov m,imm`, `neg m`, `not m`, `push imm/m`, `pop m` and the indirect `jmp`/`call` through
memory. **71 shape vectors + 4 order vectors, 0 new `step` cases**, taking the model to
**497 of the 525 rows (95%)**.

```
cases=63550  matched=44753  explained=27195  unexplained=0  oracle-leaks=0  missing=0
  spec: 0   refusal: 0   harness: 0   undefined-region: 27195
775 vectors · 82 pre-states · 83 mnemonics
```

## The scope, DERIVED — and the derivation corrected a DECLARED list

For the first time the scope was a command rather than a guess (batch 19's `--remaining`), and
running it rather than reading the handover's copy of it is what found the error in it.

⛔ **`movnti m,r` IS NOT AVAILABLE WORK. x86isa does not implement it** — 82/82 refused, at all
82 real pre-states. The tool counted it among the 36 available because its "oracle UNAVAILABLE"
list is **DECLARED (batch 18), not derived**, and a declared list is wrong in whichever
direction nobody has looked. Here it was wrong in the direction that INVENTS work.

⭐ **Two independent routes agree, which is why it is stated as a fact and not a symptom.**
The probe carried `movl %ecx,(%rbx)` — identical shape, identical address, identical
pre-states — and it executed 82/82 in the same run, so the refusal is the OPCODE and not the
form. And x86isa's own section doc for SSE2 cacheability control reads *"The only implemented
instruction here is LFENCE."* Execution and catalogue agree; D36 says never to trust the
catalogue alone, and this is the case where it happened to be right.

## The probe that designed the batch — 11 seconds, 90 forms, 7380 cases twice

| group | rows | refused | undefined fields |
|---|---|---|---|
| `add`/`sub`/`adc`/`sbb` at `m,imm` · `m,r` · `r,m` · `acc,imm` · `sub r,imm` | **19** | **0 of 82** | none |
| `mov m,imm` · `mov m,label` · `neg m` · `not m` · `push imm/m` · `pop m` | **7** | **0** | none |
| `jmp *m` · `call *m` | **2** | 26 of 82 | none |
| `cmpxchg8b m` | 1 | 0 | none |
| `movnti m,r` | 1 | **82 of 82 — NOT SUPPORTED** | — |
| `bt`/`bts`/`btr`/`btc` at `m,r` | 4 | 0 at `w`/`l`, **26 at `q`** | af, of, pf, sf |
| `xchg m,r` · `xchg r,m` | 2 | 0 | none |

**Zero refusals and zero undefined fields across the 28** is what said this batch was width and
shape work rather than semantics — and it is why not one line of `X86/Semantics.lean` changed.

## ⛔ THE FIRST RUN WAS GREEN, AND THAT IS THE PART THAT NEEDED WORK

`unexplained=0` on the first run of the 71 shape vectors, with all **5822 new cases MATCHED**
(38603 → 44425, exactly 71 × 82 — none refused, none explained away). The design predicted it:
`Op` is keyed by mnemonic with a shared operand pair, so these shapes have been expressible
since P0 and run through code the differential has validated for nineteen batches.

⭐ **Two receipts say the model really is untouched, rather than a comment saying so.**

```
git diff ee7a250..HEAD -- X86/Semantics.lean X86/Syntax.lean X86/Flags.lean X86/State.lean \
    X86/Value.lean X86/Memory.lean X86/Theorems.lean X86/Oracle.lean X86/Basic.lean \
    X86/Serialize.lean X86Native/      →  EMPTY
```

Every executable module is byte-identical. The one file that changed under `X86/` is
`X86/Coverage.lean` — the coverage TABLE's shapes column, which is prose about the model and
not the model. And the two differential runs agree exactly: the 71-vector run matched 44 425,
the final 775-vector run matches **44 753**, and `44 425 + 4 × 82 = 44 753` to the case. The
four order vectors added their 328 cases and disturbed nothing else.

⛔ **THIS PARAGRAPH FIRST CITED `git diff … -- X86/ X86Native/` AND CLAIMED IT WAS EMPTY. IT IS
NOT** — `X86/Coverage.lean` lives under `X86/`. The command I had actually run named the model's
modules one by one; the command I WROTE DOWN was the tidy-looking generalisation of it, and it
returns a different answer. ⇒ 🔑 **A CITED COMMAND IS EVIDENCE ONLY IF IT IS THE COMMAND THAT
WAS RUN** ([[feedback-a-citation-is-an-ungated-claim]]). The receipt above is now the exact
invocation, and the claim it supports is strictly stronger than the one it replaced.

⚠️ **A prediction that comes true is not a test of itself.** Looking for what the green did NOT
contain found **three claims in `step` that nothing in this repository could distinguish**:

1. `.push` reads its source **BEFORE** RSP moves ("so `push rsp` pushes the OLD RSP").
2. `.pop` computes its destination address **AFTER** RSP moves ("a `pop rsp` ends with the
   LOADED value").
3. `.call .indirect` reads its target **BEFORE** the return address is pushed.

All three sentences have been in the semantics since P0. Against every push/pop/call vector
that existed — including this batch's own 71, which address memory through RBX — **a model
with any of the three orders reversed is BIT-IDENTICAL to this one.**

⇒ 🔑 **A CLAIM THE VECTORS CANNOT DISTINGUISH IS NOT TESTED BY THEM, however many of them
there are and however green the run is.** Nineteen batches of differential agreement said
nothing whatever about these three lines.

## The four arms, and the deletion test that makes them mean something

| arm | field | caught |
|---|---|---|
| `push` reads its source AFTER the stack pointer moves | `mem@…7fe0` | 156 |
| `pop` computes its destination address BEFORE the increment | `mem@…7fe0` | 78 |
| `pop` into a register lets the RSP update overwrite the loaded value | `rsp` | 78 |
| an indirect branch uses the ADDRESS of its operand, not the value | `rip` | 156 |

⭐ **The claim that the four new vectors are load-bearing is TESTED, not asserted** (batch 4's
rule): the six vectors were deleted and all four arms re-run.

⚠️ **The two pop arms are separate on purpose.** One is about an ADDRESS and shows in the stack
window; the other is about WHICH WRITE WINS and shows in `rsp`. A single arm covering both
would have been caught by either vector and would not have said which claim was tested.

## ⛔ The third order claim is NOT tested, and this says so rather than leaving it to look covered

`callq *(%rsp)` is the vector that would test it — and **x86isa refuses it in 80 of the 82
pre-states**, executing only in the two frame states. A vector that is 80/82 silence is not
evidence, so it is not in the table: agreement where both models refuse is agreement about
nothing ([[a-refusing-form-needs-a-refuse-always-control]]). The claim is pinned by an anchor
against the model instead, which is a weaker instrument, and the gap is named here so that a
reader does not read the two tested orders as three.

## ⚠️ The claim instrument is structurally blind to %rsp, and this batch is the first to pay it

`popq (%rsp)` and `pushq (%rsp)` **resolve to NO roster row**, and that is the instrument being
right. `MBASE` excludes register index 4 (%rsp) and 5 (%rbp) because either changes an
encoding's LENGTH — %rsp forces a SIB byte — and a form skeleton is a fixed-length byte
pattern. The exclusion is correct and load-bearing; the consequence had simply never been paid,
because until batch 20 no vector used either base.

The two vectors claim nothing (their rows are claimed by the RBX siblings), so they are
**exempted by id, and the exemption is gated in BOTH directions**: an exempt id that starts
resolving is a finding (the list has gone stale), and an unresolved vector not on the list is a
finding exactly as before. ⛔ **The claim instrument was NOT otherwise touched this batch** —
two instrument changes in one batch is how two defects come to cancel.

## What is NOT claimed
- `movnti` — measured unavailable, above.
- `bt`/`bts`/`btr`/`btc` at `m,r` — **D23 stands, now priced rather than argued.** At `.q`
  x86isa refuses in 26 of 82 states, the bit-string address having gone non-canonical.

  ⛔ **AND THE FIRST VERSION OF THIS PARAGRAPH WAS WRONG, in the direction that flattered the
  decline.** It said the surviving states address memory "hundreds of megabytes outside every
  watched window" — inferred from the offset being a full-width signed register, and stated as
  though measured. Computing `RBX + esz × (offset div (esz×8))` over the harness's own 82 RCX
  values says otherwise:

  | width | lands INSIDE the watched window | more than 1 MB away | max displacement |
  |---|---|---|---|
  | `.w` | **58 of 82** | 0 | **4 KB** |
  | `.l` | 49 of 82 | 24 | 256 MB |
  | `.q` | 35 of 82 | 38 | 2^60 |

  So a MAJORITY of states are observable at every width, and at `.w` nothing leaves the
  neighbourhood at all. **D23 still stands** — the minority that leaves the window is exactly
  where the harness would **report agreement it never made**
  ([[feedback-unobserved-regions-report-agreement]]), and a form whose evidence is 58/82 silent
  on the interesting cases is not a form this model should claim. ⭐ But the honest reading is
  that the shape is CHEAPER than argued, not more expensive, and batch 21 should price `.w`
  specifically rather than inherit "not modelled" for all three widths.
- `xchg m,r` / `r,m` — **D25 stands.** The oracle executes both (0 refusals), so the decline is
  OURS: implicit LOCK is an atomicity claim a single-threaded model cannot make or break.
  ⚠️ The neighbouring `cmpxchg m,r` IS claimed, and the distinction is principled rather than
  convenient: `cmpxchg` asserts LOCK only when the prefix is written.
- `cmpxchg8b m` — supported (0 refusals) and **deliberately held for batch 21**, see below.

## ⚠️ The kernel ceiling: a repair unblocked, designed, and refused by its own second source

Batch 18 predicted this batch would exceed the `Tests.Coverage` per-row ceiling. **It does not** —
and the measured truth is worse than the prediction:

```
38 600 ms = 465.1 ms/row against the 470 ceiling — a PASS by 1.05%
```

⇒ 🔑 **A GATE THAT PASSES BY LESS THAN ITS OWN NOISE HAS NOT PASSED.** 1% is inside this
module's measured load sensitivity, so that green goes either way on the next machine.

The repair batch 17 recorded as blocked **was** unblocked — its blocker (*"an ASSERTION count
cannot be kernel-pinned"*) is true and rules out gating the module's **TOTAL**, while saying
nothing about gating **each declaration**, which needs no assertion count at all. `lean --json`
attributes `type checking` per declaration with `fileName` and `pos.line`.

⛔ **And then the two-point measurement refused the gate it enabled.** Profiled at 700 and at 775
vectors: the two declarations holding **53% of the module are barely vector-driven** (×1.050,
×1.077 against an input of ×1.107), so a per-vector denominator would go slack exactly where the
cost is; and **three declarations grow FASTER than their input**, because `vectorMnemonics` is
`eraseDups` and **`eraseDups` is quadratic**.

⇒ 🔑 **A TOTAL CANNOT TELL A LINEAR MODULE FROM A SUPER-LINEAR ONE.** The "linear in
(assertions × vectors)" growth law reported since batch 17 was inferred from whole-module totals
and is wrong; three batches of readings were compared in it.

**Landed:** the per-declaration measurement (printed with names and lines every run), a
kernel-pinned `vectorCount`, a corrected growth-law line, and the ceiling raised 470 → 744 at
`measured × 1.6` — the convention batch 14 registered the line with, not a margin invented to
fit — demoted in writing to a coarse tripwire. **Not landed:** the gate. See D62.

⚠️ **The real fix is a cheaper module, not a looser gate**, and it is named rather than done: the
quadratic dedup costs ~3.5 s across three theorems and grows as the square of a table that grows
every batch. **Batch 21 should price it.**

## Handoff — what batch 21 inherits

**The AVAILABLE work is closed.** All 27 remaining rows are unencodable (2), oracle-unavailable
(19 = 18 BMI + `movnti`), or a recorded decline (6 = 4 bit-string + 2 `xchg`) — except one:

⭐ **`cmpxchg8b m` is the last claimable row and it is deliberately not this batch's.** It is
supported (0 refusals at all 82 pre-states, measured) and needs one new `Op` constructor. It was
held back because it changes `rosterSize` — **the exact denominator the kernel measurement was
using** — and landing it here would have confounded the two-point comparison that produced this
batch's main finding. ⚠️ Its equal branch is reached in **1 of 82 pre-states** (measured, not
assumed: EDX:EAX matches `[RBX]` only where `a`'s high half is the complement of its low half),
so it needs a purpose-built pre-state rather than an accident, in the style of
`stringBoundaryStates`.
