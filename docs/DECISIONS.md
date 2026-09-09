# P0 decisions

Decisions taken while executing P0 that **depart from, or sharpen, plan v1**
(`~/projects/claude/seat/briefs/2026-09-02-PLAN-x86lean-v1.md`). Each says what
was decided, why, and what it would cost to reverse. A decision not written down
here is not a decision; it is a habit.

---

## D1 — The model library depends on Lean core ONLY. No mathlib.

Plan v1 §5 says the repo is "pinned to a recorded mathlib rev". The toolchain
**is** pinned — `leanprover/lean4:v4.32.0-rc1`, the same as salt, so the two
repos share an elan toolchain — and the compatible mathlib revision is recorded
here (`leanprover-community/mathlib4` at `360da6fa66c1`, the rev salt uses with
this toolchain). But `lakefile.toml` **requires** nothing.

**Why.** Three reasons, in order of weight:

1. **The consumer interface (plan v1 §6) is the deliverable.** This model exists
   so binary-level proof projects can build on it. A mathlib dependency is a tax
   on every one of them — a multi-gigabyte build and a large trusted surface —
   levied for `BitVec`, which is in Lean core.
2. **Kernel cost (§3.7).** mathlib's simp set and instance search are a
   substantial elaboration and kernel cost, and §3.7 asks for kernel time to be
   measured and capped. Starting from core keeps the baseline honest and the
   ceilings meaningful: the measured total is **606 ms across the whole
   development** (`scripts/kernel_cost.py`).
3. **The axiom allowlist stays narrow by construction** rather than by audit.

**Reversal cost: near zero, and it stays that way.** Adding a `[[require]]` is
one stanza; the direction that is expensive is the other one, and it gets more
expensive with every form. If a metatheory layer ever needs mathlib, it can be
its own library that depends on `X86` — which is exactly the shape a consumer
would want anyway.

---

## D2 — The XMM/YMM/ZMM register file and MXCSR are ABSENT at P0.

Plan v1 §3.1 lists them in the state. P0's roster is the scalar subset, so at P0
they would be fields no instruction reads and no test constrains.

**Why.** A field that nothing touches reads as coverage to anyone skimming the
state, and is worth nothing. Adding a field to a Lean structure is
source-compatible with every `{ s with … }` update and every `rfl`-shaped
characterization lemma already proven, so deferring costs nothing and claiming
costs credibility.

**Due:** P2, with the first SIMD form. **Reversal cost: one structure field.**

---

## D3 — Memory is a TOTAL read over a FINITE representation.

Plan v1 §3.1 asks for "memory as a total `BitVec 64 → BitVec 8`".
`X86.Mem.read : Mem → BitVec 64 → BitVec 8` is total — every one of the 2^64
addresses reads, with a zero background — but the representation is an
association list.

**Why.** A raw function field would satisfy the letter and make the P0 exit
criterion unreachable: the differential harness must **enumerate** a memory to
ship it to x86isa and diff a delta afterwards, and a function cannot be
enumerated, shipped or diffed. The interface (`read`/`write`/`readSize`/
`writeSize` and four lemmas) is the seam, placed at P0 deliberately — swapping
the representation after 300 forms are written against a concrete list is a
different job from swapping it now.

⚠️ **Named cost:** `write` conses, so `read` is O(n) in the number of stores. Free
at P0's handful of stores per vector; a real P1 item.

---

## D4 — Every operand value is a `BitVec 64` with the width as a datum.

**Why.** A `BitVec sz.bits` indexed by the operand width makes `step`
dependently typed, and then every characterization lemma must transport across
width equalities before it can say anything. ACL2 x86isa makes the same choice
for the same reason. The cost is one invariant — every read is truncated —
discharged by the `X86.Value` lemma pack rather than assumed.

---

## D5 — The oracle draw ORDER **and COUNT** are part of the model.

A shift with a non-zero masked count draws exactly **three** bits in the order
**CF, OF, AF**, whether or not each is undefined at that count; the logic group
draws exactly **one** (AF).

**Why.** Fixing the order alone is not enough. If the *count* varied with the
operands, the oracle cursor would not be a function of the instruction stream,
and a differential run could not be replayed from its seed — which is the only
way a disagreement gets bisected. Stated in `X86/Semantics.lean`, asserted in
`Tests/Nonvacuity.lean` §3, and visible in the characterization theorems
themselves as the `oracle := { … cursor := … + n }` component.

---

## D6 — The harness's "undefined" set is DERIVED, never declared.

`X86.undefinedFlags` runs the same step under two opposite oracles and reports
which flags moved. The harness has no list of its own.

**Why.** A declared list is a second source of truth about what the model
refuses to commit to, and it goes stale the first time a form changes tier —
silently, because a stale list makes the comparator *more* permissive. Deriving
it means there is one notion of "undefined" in the system and it is the
semantics'. `undefinedLeaked` is the companion check: if the two oracle runs
differ anywhere **outside** the flags, an undefined bit has reached a register,
RIP, memory or the model state, which no tier admits.

---

## D7 — The native tier is a separate LIBRARY (`X86Native`), not a module
`X86.Native`.

TRUSTBASE.md as written at commit 1 named the tier `X86.Native`. A sibling
module inside the `X86` library would be one stray `import` away from the model
tree; a separate `lean_lib` cannot be imported by accident and the isolation is
checkable in one line (`scripts/check_tier_isolation.sh`). TRUSTBASE.md is
amended to match, with this note as the reason.

---

## D8 — Kernel ceilings registered at 3× the measured baseline, floor 50 ms.

`scripts/kernel_ceilings.txt`, generated by `scripts/kernel_cost.py --register`.
Below 50 ms, timing noise dominates and a ratio would fail on a loaded machine;
above it, 3× is loose enough for an ordinary build and tight enough that the
defeq blow-up §3.7 warns about cannot hide. **Raising a ceiling is a decision to
record here, not an edit to make quietly.**

---

## D9 — Branch targets are checked for canonical form; the FALL-THROUGH is not.

`Cpu.setRipChecked` refuses a non-canonical branch target (SDM Vol. 1 §3.3.7.1;
#GP(0) per Vol. 2A JMP/CALL) by HALTING — the model declines rather than raising
an exception, because the fault machinery belongs to system mode and system mode
is a v0.x non-goal.

⚠️ **Named gap:** the fall-through `rip + len` is still unchecked. x86isa checks
it too (`:rip-increment-error`). It is unreachable in the P0 vectors (RIP is
0x400000 and instructions are short), so the differential run has not exercised
it — and an unexercised fix is a guess. It is a P1 item, written down rather than
written blind.

**Why this decision exists at all:** the differential run found it. See
`docs/DIFFERENTIAL-P0.md`.

---

# Three defects found in P0's own gates, and what they cost

Recorded because each was found by a gate firing on this repository rather than
by review, and each has the same shape: **a check that cannot see its subject
reports a pass.**

### 1. The harness selftest found a hole in the VECTOR TABLE, not in the model.

The planted "shift forgets to mask its count" bug went **uncaught**: every shift
vector used a count of 1 or 3, both below every mask, so an unmasked model
produced identical results everywhere. The vectors, not the comparator, were
wrong. Five masking-boundary forms were added (`shlq $64` → masks to 0,
`shlb $9` → count ≥ width, `shrq $63`, `shrb $9`, `shlq $1`), and the bug is now
caught with 88 disagreements in `rax`.
⇒ **A differential vector set that never crosses a rule's boundary cannot test
that rule, and the coverage table will still say the form is covered.**

### 2. The first "wrong model" was wrong in more ways than the one planted.

The initial `wrongShiftMask` also dropped the flag computation, so it produced
369 disagreements while the *planted* bug produced none. It looked like a pass.
⇒ **A deliberately-wrong model must be wrong in exactly one way, or a catch
proves nothing about the thing you meant to test.** The selftest now asserts the
disagreement lands in the specific FIELD the bug is in.

### 3. The kernel-cost gate read the wrong stream and reported CLEAN.

Lean's profiler writes to **stderr**; the first draft searched stdout, measured
`0.0 ms` for all eighteen modules, and printed `kernel-cost gate: CLEAN`. It now
reads both streams and — the part that matters — **distinguishes a real zero
from a failed measurement**: a module with no `type checking` line but a
cumulative profiler block genuinely type-checks nothing (`X86.lean` is only
imports), while no profiler block at all is an error and exits non-zero.
⇒ **A gate that reports zero for everything is not passing; it is blind, and
blindness and success are byte-identical in the output.**


---

# Two more, found by the differential run itself

Recorded beside the other three because they are the same shape at a larger
scale — **a check that cannot see its subject reports a pass** — and because
both were in the instrument, not the model.

### 4. The oracle could not answer, and that looked like a crash rather than an answer.

x86isa's `create-undef` is a CONSTRAINED function: the model knows only that it
returns a natural. The first run died at case 817 with *"cannot ev the call of
non-executable function CREATE-UNDEF"*. That is not a broken oracle — it is
x86isa making exactly this project's refusal, in ACL2's vocabulary, and
declining to execute until a generator is attached.
⇒ **The attachment is `nfix`, not a constant.** A constant `0` would have agreed
with this model's all-zero oracle on every undefined bit, the
`undefined-region` class would never have fired, and 694 real
declines-to-commit would have shown up as 694 silent agreements. *Agreement
obtained by making both sides guess the same way is not agreement about
anything.*

### 5. The harness read `ms` and x86isa had written `fault`.

All 80 non-canonical branches came back as "x86isa left RIP alone, and its RIP
disagrees with ours" — with x86isa's `#GP(0)` sitting unread in the field beside
the one the driver looked at. The oracle had explained itself and the harness
that asked was looking elsewhere.
⇒ **An oracle that cannot answer, and an oracle whose answer you do not read,
are indistinguishable from an oracle that agrees with you.** The record now
carries `refused=0|1` derived from BOTH fields — and, deliberately, not the
REASON, because the two models say "I decline" in different vocabularies and
comparing the words would report a disagreement on every refusal, which is the
opposite of the truth.


## D10 — Batch 1's characterization is ONE theorem per mnemonic over a generic
## source operand, and stops at the register destination.

`step_and_reg_op` and its two siblings take the source operand as a VARIABLE, so
one equation covers `r,r`, `r,imm` and `r,m`; the destination carries a variable
`h8`, so it covers AH/CH/DH/BH too. Twenty-one roster forms, three theorems.

This is sound HERE AND ONLY HERE. `wellFormed2` can fail only when both operands
are memory, and this family's destination is a register — so there is no side
condition to discharge and no case silently lost. The moment the destination can
be memory (batch 4), the equation gains a frame component and a well-formedness
hypothesis, and the same trick would quietly drop both.

**Reversal cost:** low. Splitting one generic equation into three shape-specific
ones is mechanical; the downstream consumers rewrite with the same name.

⚠️ The batch also carries three FRAME theorems (`step_and_reg_op_mem` and
siblings) stating positively that it writes no memory. A characterization
equation names the components that change and says nothing out loud about the
rest — reading that silence as a guarantee means trusting that the reader
enumerated the record's fields, and a record gains fields.

## D11 — A ninth anchor was DELETED rather than repaired.

`accumulator_form_is_not_special` was written to record that `andb $0x5a, %al`
and `andb $0x5a, %cl` decode to the same AST. What it asserted was
`step i c = step i c`, by `rfl` — true of every term in Lean, and provable of a
model that did the exact opposite. It type-checked and it was green.

It is named in `Tests/Anchors.lean` where it stood, so it is not reinvented.
⇒ **A test whose subject cancels out of its own statement passes for the same
reason an empty test suite does.** The same shape as P0's five instrument
defects, found this time in a test rather than in a gate.

**Reversal cost:** none. The claim is real but it is a claim about the vector
table, not about `step`.


## D12 — Batch 2 was chosen AGAINST the roster's own order, to price the term
## batch 1 could not.

`scripts/k_roster.py` orders families by how much of them P0 already covers, so
the script's batch 2 is `cmp` (11 forms, existing template). It was passed over.

Batch 1 measured 623 k tokens per form for a form under an EXISTING template —
and then the roster showed that only 6 of 61 families, 50 of 525 forms, are of
that kind. 55 families need a new template. A wave quoted from batch 1 alone
prices 10% of itself and guesses the rest.

`adc`/`sbb` was taken instead because it is unambiguously ONE new template, a
single family rather than a mixture, and large enough (14 forms) that
`batch 2 total − 14 × 623 k` is a real number for the surcharge.

**Reversal cost:** none — the roster's order is data, not a commitment, and the
five skipped already-templated batches are still there.

## D13 — Four checks now test the PRE-STATES, not the model.

`Tests/Coverage.lean` asserts that some pre-state crosses the carry boundary at
width q and at width b, that some crosses the borrow boundary, and that CF takes
both values across the set.

Every other check in this repository asks whether the model matches the table,
the table matches the AST, or the model matches the oracle. **None of them can
see a rule's boundary stop being crossed.** The coverage table reads the same,
every vector still runs, and the differential run still comes back clean —
because a rule nothing exercises cannot disagree with anything.

This was found by testing a claim rather than making one: batch 2 asserted that
P0's sweeps could not reach the carry boundary, deleted its own boundary states
to prove it, and discovered the sweeps reached the boundary by accident — two
adjacent constants in `adversarial` that happen to be complements.
⇒ **Coverage that arises incidentally from a list written for another purpose is
coverage nobody is maintaining.**

**Reversal cost:** low. They are four `decide` assertions over `preStates`.

## D14 — The memory operand SWEEPS; until batch 3 it was a constant.

`Tests/Vectors.lean`'s `mkPre` now writes RCX into the eight bytes at RBX — the
span every memory-operand vector addresses — so a memory operand moves through
the adversarial list exactly as a register operand does.

**What it replaced.** Until P1 batch 3 the data window held the same fixed
32-byte pattern in all 74 pre-states. Every `_rm_` form shipped by batches 1
and 2 — twenty vectors, `andq (%rbx), %rax` and its siblings — therefore read
ONE source value, seventy-four times. Nothing was wrong and no gate could have
said so: the coverage table counts FORMS, the differential run counts CASES, and
neither counts VALUES.

⇒ **A form whose operand never moves is one test reported as seventy-four.**
This is D13's law one level up. D13 found a boundary crossed by accident; this
found a whole operand position that was never swept at all, and found it by
asking what a new vector would actually vary rather than by any failure.

**Evidence that it changed something real.** The harness selftest's hardest
existing arm — `adc`'s carry-OUT forgetting the carry-in, which is invisible
except at the carry boundary — went from **76 disagreements to 115** on the same
planted bug. Batch 2's own evidence got stronger retroactively, which is the
measurable form of the claim above.

Three theorems hold it: `memory_operand_mirrors_rcx` (the invariant),
`memory_operand_sweeps` (that the invariant has teeth — twenty distinct values
at least), and `memory_window_margin_is_fixed` (the margin does NOT sweep, so an
access that ran off the end of its width is still visible outside the span).

**Reversal cost:** low, and it would be loud — the three theorems fail.

## D15 — The coverage table's SHAPES column is gated, and the gate is paid for
in kernel time.

`Tests/Coverage.lean`'s `mem_dest_claims_are_backed` reads the shapes column as
a character list and requires every `m,r` claim — a MEMORY DESTINATION, since
the column writes shapes destination-first — to be backed by a vector whose
destination operand really is memory.

**What it caught.** The row for `and`/`or`/`xor` claimed `m,r (q)` and no such
vector has ever existed: batch 1 shipped `and_rm_*`, a memory SOURCE with a
register destination, and the shapes string transposed it. The
memory-destination logic forms are roster family 4, a batch not yet run.

⛔ **And the reason it survived a batch is worth more than the defect.** A
comment sat directly above the string saying "`m,r` below is P0's row, at width
q only" — explaining a thing that was not there. ⇒ **A wrong claim with a
reassuring comment beside it is harder to see than a bare one, because the
comment answers the question the reader was about to ask.** Every mnemonic-level
theorem in the file passed throughout: `and` has a row, `and` has vectors, `and`
is in the roster. The table's most detailed column was describing coverage the
repository does not have, and the checks were all one granularity too coarse.

**The price, stated rather than absorbed.** The theorem costs **1292 ms** of
kernel time — `Tests.Coverage` goes 378 ms → 1960 ms — and the module's ceiling
in `scripts/kernel_ceilings.txt` was raised from 777 to 5880 deliberately, by
editing one line rather than by `--register`, which would have loosened every
other module at the same time.

**The cheaper design was considered and rejected.** A `Bool` field on `Row` that
the renderer turns into text would cost almost nothing and would make the prose
unable to UNDER-claim — while leaving it entirely free to OVER-claim, which is
the direction that actually failed here and the direction this repository exists
to prevent. ⇒ **A gate on the artifact costs more than a gate on a shadow of it;
1292 ms is what the difference costs, and the artifact is what a reader trusts.**

⚠️ The check is written on character lists rather than with `String.splitOn`,
and not for taste: `splitOn` is defined by well-founded recursion, the kernel
does not unfold it, and `decide` fails on a proposition that is TRUE. A gate
that cannot be evaluated is not a weaker gate — it is a build error wearing a
gate's clothes.

**Reversal cost:** low. Delete the theorem and restore the ceiling.

## D16 — A check cannot be more precise than the notation it reads.

D15's shapes-column gate needed a second pattern for P1 batch 4, because
`inc`/`dec` have no source operand and cannot write a memory destination as
`m,r`. The first attempt was the substring `· m ` — and it fired on `push`,
whose shapes read `r · m · imm`, where `m` is a memory **source**.

The pattern was not merely buggy: it was **unexpressible**. The shapes column
had no notation distinguishing a memory operand that is written from one that is
read, for a unary form, so no predicate over that column could mean "memory
destination". ⇒ **A check cannot be more precise than the notation it reads**,
and the repair belonged in the notation, not the check: a written memory
destination is now `m(rmw)`.

⭐ **The wrong pattern earned its keep on the way out.** Firing on `push`
revealed that `push` claimed `r · m · imm`, `pop` claimed `r · m`, and
`neg`/`not` claimed `r/m` — with **not one memory vector among them**. Four more
P0 rows over-claiming exactly as `and`/`or`/`xor` had in D15, and four more that
every mnemonic-level theorem passed over: `push` has a row, has a vector, is in
the roster.

⇒ **The over-claim was not a slip in one row. It was the column's default
behaviour, because nothing read it.** A prose column that no gate reads does not
drift slowly; it is wrong wherever nobody happened to look, from the moment it
is written.

All four rows are now narrowed to what is executed, each naming the roster
family that will earn its missing half back — the correction `and`/`or`/`xor`
took in batch 3 and earned back in batch 4, applied four more times.

**Reversal cost:** low, and loud: the gate fails.

## D17 — The roster's family key is not a template key.

`scripts/k_roster.py` groups K's forms by `flags|reads|dest` — which flags a form
writes, which it reads, and whether its destination is a register, memory, or
neither. That key is derived from K's own rule text and it is the right key for
what it was built for: it puts forms with the same flag discipline together.

**It is not a key on the WORK.** Family 7 has 116 forms and contains the
conditional branches *and* `leaveq`, `lods`, `movs`, `nop`, `pdep`, `pext`,
`retq`, `stos`, `ud2` — string operations, BMI2 bit-manipulation, and stack and
miscellaneous forms — because all of them write no flag and none writes a
register. One family, at least six templates.

⇒ **The wave's cost model counted 55 templates by counting 61 families.** That
1:1 map is refuted by family 7 alone, and in the direction that matters: a
family can hide several templates, so a per-family estimate under-counts the
work in exactly the families it is easiest to call cheap. P1 batch 5 therefore
took the family's BRANCH SUBSET (99 forms) and left the other 17, which is a
deviation from the roster's own batching and is recorded here as one.

⚠️ This compounds with the pricing finding posted on the bus: the surcharge the
55-template count was multiplied by is not visible in four measured batches
either. The template term was wrong in both of its factors.

**What would fix it:** a template key derived from the MODEL — which `step` case
a form lands in, and whether that case exists yet — rather than from K's flag
disposition. That is a real change to `k_roster.py` and it is not attempted
here; the roster stays the coverage fence, which is what it is good at.

## D18 — Two of the roster's 525 forms are not instructions.

K's tree carries `jecxz_rel32.k` and `jrcxz_rel32.k`. There is no rel32 encoding
of either: `E3 cb` is rel8 only (SDM Vol. 2A, JCC). clang refuses — *"value of
297 is too large for field of 1 byte"*. K's stratification autogenerated a
`rel32` variant for every branch mnemonic without asking whether it exists, and
the roster, derived from K's filenames, inherited it.

The roster selftest asserts 13 SDM facts, and none of them is "every form can be
assembled". The **encoding cross-check** is what catches this class, and only at
the moment a vector is written for the form — which is how it was found.

⇒ **A coverage fence derived from another project's tree inherits that
project's artifacts as well as its coverage.** The 525 is a ceiling on real
forms, not a count of them, and the same autogeneration will have produced other
impossible variants further down the roster.

**Reversal cost:** none — this is a recorded fact, not a change. The two forms
are marked in the `jrcxz`/`jecxz` coverage rows.

## D19 — CMOVcc writes its destination unconditionally; only the value is
conditional.

`step`'s `.cmov` case always calls `setReg`, with the source operand when the
condition holds and **the destination's own value when it does not**.

This is not a stylistic choice. A 32-bit write zero-extends (SDM Vol. 1
§3.4.1.1), so at width `d` the two readings are observably different:
`cmovel %ecx, %eax` with ZF clear moves nothing and still clears the upper half
of RAX, while a model written as "if the condition holds, move" leaves it
intact. At widths `w` and `q` they agree exactly.

⇒ **The natural reading of the mnemonic is wrong, and wrong only on one of the
three widths.** It was implemented from the SDM and then *arbitrated by the
oracle*: ACL2 x86isa agrees across all 74 pre-states of all 32 width-`l`
vectors, 0 unexplained. That is the differential doing the job a careful reading
alone could not — the model was self-consistent under either reading, and only a
second model could say which one the machine implements.

The planted hard half (`wrongCmovSkipsWrite`) is the other reading, and deleting
the 32 width-`l` vectors makes it catch **zero**.

**Reversal cost:** low, and loud: two `Tests/Coverage.lean` assertions and one
selftest arm fail.

## D20 — SAR's CF is defined where SHL's and SHR's is undefined.

`Flags.shiftFlags` gives `.sar` its own CF branch: at a masked count at or above
the operand width, CF is the operand's **sign bit**, and no oracle bit is drawn.
`shl` and `shr` draw one there.

This is the SDM's own wording rather than a refinement. The undefined clause
names *"SHL and SHR instructions where the count is greater than or equal to the
size of the destination operand"*; SAR has no such clause, because shifting a
value right past its own width still has a well-defined answer — every vacated
bit, and the last one shifted out, is the sign.

The consequence is visible in the published coverage table: `sar`'s undefined
list has **two** entries where `shl`'s and `shr`'s have three.

⭐ **And it was arbitrated rather than argued.** The reading was implemented from
the manual, and the model would have been self-consistent under either reading —
only a second model could say which one the machine implements. ACL2 x86isa
agrees, and the planted control says so directly: flipping CF on `sar_b9/6` is
contradicted with `oracle=1`, the sign. This is the differential doing the job a
careful reading alone cannot.

**Reversal cost:** low, and loud: one selftest arm and the coverage row.

## D21 — An assertion narrower than the coverage it guards is a false alarm.

`sar_reaches_count_ge_width` quantifies over **(vector × pre-state)**, not over
vectors alone.

Its first version matched only an `.imm8` count on a vector. Deleting `sar_b9`
made it FAIL — while the differential arm it guards still caught the planted bug
(49 disagreements instead of 79), because `sarb %cl, %al` reaches the same region
whenever RCX's low five bits are ≥ 8. **The theorem reported a coverage loss that
had not happened.**

⇒ **A gate that cries wolf is one somebody eventually switches off**, so a
false-alarming assertion is not a harmlessly strict one — it spends the same
credibility the real alarms need. This is the exact mirror of D15's and D16's
over-claiming prose: there a column claimed more than the tests reached; here a
theorem claimed less.

The repair was to assert what the tests *reach* rather than what one vector
*says*, and the result is calibrated in BOTH directions — which none of the
earlier pre-state assertions (D13, D14, and batch 5's) had been:

* everything present → passes; arm catches 79
* `sar_b9` deleted → **passes**; arm still catches 49
* `sar_b9` and the `cl` forms deleted → **fails**; arm catches **zero**

⇒ **A pre-state assertion should be probed for silence as well as for noise.**
Testing only that it fires when coverage is removed leaves the false-alarm
direction unmeasured, and that is the direction that gets a gate deleted.

**Reversal cost:** low.

## D22 — A rotate's count is reduced twice, and its flags key off the first
reduction.

`Flags.rotMasked` masks to 5 bits (6 at width `q`); `Flags.rotReduced` then
reduces modulo the width for `rol`/`ror` and modulo **width + 1** for
`rcl`/`rcr`, which rotate the operand and CF together as a `w+1`-bit ring.

⚠️ **The flag rules ask about the MASKED count.** The SDM writes *"IF COUNT ≠ 0
THEN CF ← LSB(DEST)"* for `rol`, and COUNT is the masked count — so `rolb $8`
moves no data and writes CF anyway. A model asking "did the data move?" — the
reduced count — is correct on every other count and wrong on exactly the
non-zero multiples of the width. That is this batch's planted hard half.

And `rcl` is its mirror: `rclb $9` reduces modulo **nine** to zero, and its CF
is written by the rotate loop itself, so a loop that does not execute writes
nothing. Same count, same width, one opcode apart, opposite answers.

**Two further rules that hang on a line of the manual:**
* **RCR's OF is computed BEFORE the rotate, RCL's after.** The SDM writes the
  identical sentence above RCR's loop and below RCL's.
* **A rotate touches only CF and OF.** SF/ZF/PF/AF pass through untouched,
  unlike every shift.

⭐ **All four were implemented from the manual and all four came back agreeing
with ACL2 x86isa on the first differential run**, 32412 cases, 0 unexplained.
The model would have been self-consistent under any of the wrong readings; this
is the third batch running (with D19 and D20) in which a second model settled
something re-reading could not.

`Flags.rotResult` is written as bit expressions rather than the SDM's
one-bit-at-a-time loop: the loop is a specification, and a `while` in a
definitional semantics would make every characterization theorem an induction.

**Reversal cost:** low, and loud — two selftest arms, two `Tests/Coverage.lean`
assertions and thirteen anchors.

## D23 — The bit-string shape of BT/BTS/BTR/BTC is DECLINED, not approximated.

`step`'s `.bit` case takes the bit offset **modulo the operand width**, which is
what the SDM specifies for a register destination and for an immediate offset.
The four `m,r` forms of roster families 31 and 41 — a MEMORY base with a
REGISTER offset — are **not modelled and not claimed**.

With that combination the operand is not a word with a bit selected inside it.
It is the **base of a bit string**: the offset is signed, may reach far outside
the addressed operand in either direction, and the effective address moves with
it. It is a different addressing mode wearing the same mnemonic.

⇒ **Declining is the honest answer and approximating would not be.** A model
that quietly applied the modulo rule there would be self-consistent, would pass
every anchor in this file, and would be wrong in a way no test here asks about —
which is exactly the shape of defect this project exists to prevent. The gap is
named in the coverage rows (`m,r: bit-string, not modelled`), so a reader cannot
mistake 12 forms for 16.

⚠️ It is therefore also the first place the coverage table carries a **T-frame
row with an unmodelled SHAPE** rather than merely undefined bits. The tier
column says how faithful a modelled form is; it has never had to say that a
shape is absent. That the shapes column can say it, and is gated
(`mem_dest_claims_are_backed`), is what keeps this honest rather than
convenient.

**Reversal cost:** none — this is a recorded absence. Closing it means modelling
signed bit-string addressing and giving it its own vectors.

## D24 — `xchg %rax, %rax` is NOP and `xchg %eax, %eax` is not, and the assembler is the witness.

P1 batch 10 needed a vector for `xchg` with the same register twice, because
that is where "a swap of two values" and "two writes" stop being the same
statement: a 32-bit write zero-extends (SDM Vol. 1 §3.4.1.1), so
`xchg %eax, %eax` moves no data and still CLEARS the upper half of RAX.

⭐ **THE ASSEMBLER SETTLED IT BEFORE THE ORACLE DID.** `xchg %eax, %eax`
assembles to `87 c0` — the ModR/M form — and NOT to `90`, though `90` is
"XCHG eAX, eAX" in every opcode table. `xchg %rax, %rax` assembles to `90`. The
reason is that in 64-bit mode `90` is NOP, and NOP does not touch RAX; an
assembler that used it for the 32-bit spelling would silently drop the
zero-extension.

⇒ So `90` is **not this instruction** and is not in the vector table: it is the
`nop` of roster family 7. The `87 c0` form is, and it is the vector that says
`xchg` is a pair of writes.

**Reversal cost:** none. If `nop` is modelled later it takes its own row; this
decision is about which of the two spellings `.xchg` claims.

## D25 — Two shapes REFUSED rather than approximated: `xchg` at memory, `bswap` at 16 bits.

Both follow D23's rule — decline what the manual declines, and say so where a
reader is looking.

**`xchg` with a memory operand** asserts the LOCK signal whether or not `lock`
is written (SDM Vol. 2A, XCHG). That is an ATOMICITY claim, and a single-threaded
model has no vocabulary to make it or to break it. Modelling the data movement
and silently dropping the atomicity would produce a model that is right about
every observation this harness can make and wrong about the only thing that
distinguishes the instruction. Those forms are roster family 11; `step` halts.

**`bswap` at a 16-bit operand size** is undefined in the SDM — not its flags,
not some of its bits: the RESULT. ⚠️ **The undefined-bit oracle is the wrong
instrument here, and that is the useful part.** The oracle says "this model
declines to commit to these BITS", which is a claim about a value that exists.
Where the manual declines to define the value at all, drawing oracle bits for it
would dress a refusal up as a `T-frame` answer. `step` halts instead.

**Reversal cost:** low. Each is one `step` case, one anchor, and one coverage row.

## D26 — RDX carries a value in every pre-state, because until batch 10 nothing wrote it.

`mkPre` now sets `rdx := ~~~a`.

`cwtd`/`cltd`/`cqto` are the first instructions in this model to write a
register their operands do not name, and `cltd`'s write is **32 bits wide**, so
it clears RDX's upper half. A model that merged instead — the 16-bit rule,
applied to all three mnemonics off one sentence, which is exactly D20's shape —
is **indistinguishable from the correct one in every pre-state where RDX is
zero**, and RDX was zero in all seventy-four.

⇒ This is D14 arriving a second time in a different register. There the memory
window was a constant across all pre-states, so every `_rm_` form read one value
seventy-four times; here a whole REGISTER was a constant, and it was the
destination of a batch that had not been written yet. **A pre-state set is
adversarial only with respect to the instructions that already exist**, and
each batch has to ask what its own new destinations were doing before it
arrived.

Held by `pre_states_give_rdx_a_nonzero_upper_half` and probed in both
directions: deleting the line makes the `wrongCdqMerges` arm catch zero AND
makes the assertion fail (D21's calibration, applied by design rather than after
a wolf-cry).

**Reversal cost:** none — it is one field in a pre-state constructor. Nothing
reads RDX in any earlier batch, which is why it could stay zero unnoticed.

## D27 — DF was compared for ten batches and could not differ; and an adversarial list is adversarial only about the questions already asked.

`preStates` gains two families, `dfStates` and `loopCounterStates`. They are one
decision because they are the same defect twice, found in one batch, in the two
places a differential can be blind.

**Half one — a COMPONENT nothing wrote.** `df` has been a field of `Flags` since
P0, printed by `Serialize.lean` since P0, and diffed by the comparator since P0.
It was also `false` in all seventy-four pre-states, and until batch 11 **no
instruction in the model could write it**. `cld` clears DF; against a state where
DF is already clear, `cld` and a no-op are *the same function*. An unimplemented
`cld` would have passed every case, and the comparator would have reported
agreement on a bit that could not move.

⚠️ The reassuring part is what made it survive: `df` appears in `flagNames`, in
`Serialize.chk`, and in the RFLAGS word handed to ACL2. Every instrument said it
was being watched. **A component under a working comparator is not thereby
tested; it is tested only if something can change it.**

**Half two — a COMBINATION no value reached.** `addr32 loop` tests `ECX - 1`.
A model that tested `RCX - 1` instead differs on exactly the states where the low
32 bits of RCX are 1 and the upper half is not zero. `adversarial` holds `1`
(upper half zero) and `0x100000000` (low half zero) and nothing that is both, so
the bug was invisible — not because a register was constant, but because the two
halves of one register had never been asked to disagree.

⇒ **This is D14 and D26 arriving a THIRD time, and the third instance is what
says the rule is not about registers.** D14 was a constant memory window; D26 a
constant RDX; D27 is a constant flag *and* an unreached combination. The general
form: **a state component or combination that no existing instruction
distinguishes is a constant, and a gate that watches a constant reports
agreement it never tested.** Every batch must ask what its own new destinations
— and its own new *distinctions* — were doing before it arrived.

Held by `pre_states_set_df` and
`pre_states_reach_ecx_one_over_a_nonzero_upper_half`, each probed in BOTH
directions (D21): deleting either family makes its arm catch **zero** and makes
its assertion **fail**, while deleting *one of the two* DF states leaves the arm
catching (1 of 2) and the assertion **silent** — the calibration that says
neither gate cries wolf.

**Reversal cost:** none — four pre-states appended to a list. The `df` bit of
`mkPre`'s flag seed is bit 6, above every seed any existing call site passes, so
all seventy-four original pre-states are byte-identical and no earlier batch's
evidence moved.

## D28 — Two kernel ceilings raised, and the batch that tripped them contributed a seventh of the growth.

`X86.Theorems` 143 → **540** ms; `Tests.Anchors` 254 → **801** ms. Raised
deliberately, not by `--register` (which would loosen every other line at once),
which is what `scripts/kernel_ceilings.txt` asks for.

**The measurement, taken because the obvious diagnosis was available and wrong.**
Excising batch 11's blocks from both modules and re-measuring:

| module | before batch 11 | after | batch 11's share | ceiling |
|---|---|---|---|---|
| `X86.Theorems` | **122 ms** | 180 ms | **58 ms** | 143 |
| `Tests.Anchors` | **249 ms** | 267 ms | **18 ms** | 254 |

⛔ **`Tests.Anchors` STOOD AT 249 OF A 254 ms CEILING BEFORE THIS BATCH ADDED A
LINE** — 98% of its headroom, spent. `X86.Theorems` stood at 85%. The ceilings
were registered at `measured × 3` when the modules read 84.7 ms and 47.7 ms; ten
batches later the multiple had been consumed almost exactly.

⇒ 🔑 **A HEADROOM-BASED CEILING QUIETLY BECOMES A TRIPWIRE ON AN ARBITRARY
FUTURE BATCH.** It does not fire on the batch that caused the growth; it fires on
whichever batch happens to cross the line, and that batch looks like the cause.
Thirteen anchors costing 18 ms failed a gate that ten predecessors' 164 ms had
already loaded. Had this been read the natural way — "batch 11 is expensive,
optimize it" — the effort would have gone into the 18 ms and none into the 249.

This is D26/D27's shape in the cost dimension and the batch-9 scaling diagnosis's lesson a second time: **the number a gate reports is about the
crossing, not about the cause, and the two are only related by accident.**

**What is NOT claimed:** that the growth is a problem. Both modules are doing
more work than they were, most of it in `decide`-shaped anchors, which is the
work those modules exist to do. What is claimed is that nobody had looked, and
that the ceiling's design guarantees nobody looks until it fires.

**A ceiling-as-tripwire is worth keeping anyway**, because it forces exactly this
measurement at a moment when someone is already in the module. What it should
NOT do is let the measurement be skipped in favour of `--register`.

**Reversal cost:** none — two numbers. The measurement is the durable part.

## D29 — The gate CI runs and the probe the developer runs were different lists, and the comment saying they could not be was what hid it.

`main`'s no-argument `selftest` now folds over `selftestArms`. It used to be
twenty-three hand-written `driveWrong` calls, twenty-three hand-named bindings
(`a b c e f g h j k l m n p q r' t' u v w x y z a2`) and a twenty-three-term
conjunction.

**How it was found.** Batch 11 added four arms, watched all four catch under
`selftest <substring>`, ran the no-argument form as the gate — and it printed

```
harness selftest — twenty-three deliberately wrong models, each must be caught:
...
harness selftest: PASS
```

**PASS, with twenty-three arms, on a table of twenty-seven.** The four new arms
had never run. The filtered probe read `selftestArms`; the gate did not.

⛔ **THE DRIFT WAS BORN WITH THE FIX FOR D15.** Batch 10 introduced
`selftestArms` precisely so the probe and the gate could not diverge, wired the
filtered mode to it, left the full selftest alone, and wrote on the table:

> *"Named once so the filtered probe mode and the full selftest cannot drift
> apart — a probe that ran a different set from the gate would be the exact
> defect the coverage table kept making (D15)."*

The sentence describes the intended design as though it were the built one.

⚠️ **AND IT WAS BORN IN A STATE OF AGREEMENT, WHICH IS THE ONLY STATE IN WHICH A
DUPLICATE LOOKS HARMLESS.** Verified from the history rather than assumed:
`selftestArms` first appears in `3f0111e` (batch 10, one commit before this
one), and `git show HEAD:Main.lean | grep -c 'driveWrong "'` returns **23** — the
same 23 the table held. At the moment of writing, the two lists were identical,
every arm ran, the gate was honest, and the comment read as a description of
what the code did.

The divergence needed no mistake and no edit to the old list. It needed only the
NEXT batch to append one row, which is the thing the table exists to make easy.
⇒ **A duplicate created in agreement is not a latent bug that might fire; it is
one that fires on the next ordinary use, and it has already banked the
credibility of a batch in which it was correct.**

⇒ 🔑 **A REASSURING COMMENT IS NOT NEUTRAL WHEN IT IS WRONG — IT IS LOAD-BEARING
IN THE WRONG DIRECTION.** An undocumented duplicate list invites the question
"are these two the same?". A documented one answers it, incorrectly, and the
question is never asked again. This is D15's own lesson (*a claim no gate reads
is wrong wherever nobody looked*) arriving on the mechanism built to enforce it.

⚠️ **AND THE STALE LITERAL WAS THE HONEST HALF.** The banner said "twenty-three"
and there really were twenty-three; the number nobody trusts is what exposed the
comment everyone would have. The file also carried "nineteen" in its header from
an earlier era. Both literals are now READ FROM THE TABLE (`selftestArms.length`)
and the banner prints the count with the verdict, so a future divergence between
"how many arms exist" and "how many ran" cannot be written down at all.

**What this does NOT excuse.** Every green `selftest` from batch 10 onward was a
green over twenty-three arms, and batch 10's own four arms *were* in the
hand-written list, so no earlier batch's evidence is void. Only batch 11's four
were at risk, and they were caught before the commit — by the count in a banner
nobody had reason to read.

**Reversal cost:** none. The fold is shorter than the sequence it replaced.

## D30 — The same duplicate shape, found by looking for it, left OPEN with its price rather than fixed at the end of a batch.

D29 was one hand-maintained duplicate of a data table. Having found it, the
obvious next question is whether there are others. There are: **the seven flags
are enumerated by hand in three places.**

| site | what it does | how it fails if a flag is added and missed |
|---|---|---|
| `Flags.render` (`X86/Serialize.lean`) | the wire format both models are compared through | ⛔ **SILENTLY** — the flag is never emitted, so it is never compared, and every run is green about it |
| `undefinedFlags` (`X86/Serialize.lean`) | derives the undefined set by running the oracle twice | loudly — a genuinely undefined bit classifies as `spec`, a false RED |
| `flagNames` (`Main.lean`) | the classifier's "is this key a flag?" test | loudly — an undefined flag can never be explained, a false RED |

⭐ **THE ASYMMETRY IS THE FINDING.** Two of the three fail noisily and would be
fixed within the hour. The third fails exactly the way DF failed for ten batches
(D27): the component is simply absent from the comparison, and absence reads as
agreement. **The dangerous duplicate is the one on the path that reports
success**, not the one on the path that reports failure.

Nothing is wrong today — all three lists hold the same seven names, verified by
reading them. This is a latent duplicate, and D29's lesson is precisely that a
duplicate *in agreement* is the one that looks harmless.

**Why it is not fixed here.** The fix is a single traversable source — a
`Flags.toList : Flags → List (String × Bool)` that all three read — which is
about thirty lines. But `Flags.render` defines the WIRE FORMAT that both models'
records are compared through, so changing it requires demonstrating the emitted
records are byte-identical, i.e. a full differential re-run. Doing that at the
end of a batch, after the gate is already met, would put the batch's evidence at
risk to close a gap that is currently only latent.

⇒ Named, costed, and left for a batch that can carry it: **~30 lines plus one
full differential run (~10 min) to prove the records unchanged.** It is written
here rather than in a comment beside the code, because D29's whole lesson is
that a comment beside the code is what stops the question being asked again.

### DISCHARGED in P1 batch 12 — and the count above was wrong.

**There were FOUR sites, not three.** The table above misses `rflagsToLisp`
(`Main.lean`), which packs the flags into the RFLAGS image sent to ACL2 by
hand-written bit positions. It fails in a fourth way again — a flag missing there
disagrees only where some pre-state actually SETS it, so it is loud on a varying
flag and silent on a constant one, which is to say it would have been silent
about DF for ten batches (D27) and is loud about it now. ⇒ **An inherited
diagnosis is a hypothesis: the shape of D30 was right, its enumeration was
short, and the missing item was the one whose failure mode is conditional rather
than categorical.**

All four now fold over one `flagFields` table in `X86/Basic.lean`, carrying each
flag's name, projection and RFLAGS bit position.

⚠️ **AND A TABLE IS NOT BY ITSELF THE FIX** — that is exactly what D29 was. The
table is GUARDED by `flagFields_covers_Flags`, which fails to COMPILE rather
than to prove: the anonymous-constructor pattern is positional, so an eighth
field in `Flags` is an arity error before any proof is attempted; repairing the
pattern without adding a row makes the two lists differ in length and `rfl`
fails; a row with the wrong projection makes the order differ and `rfl` fails.
It is deliberately NOT a `decide` over all 128 flag states, because enumerating
`Flags` would require a FIFTH hand-written field list — a guard with the defect
it exists to prevent, reporting agreement because a missing field sits at its
default in every enumerated state.

**The byte-identical proof was done, and the first attempt at it was vacuous.**
Emitting before and after gave two identical files because `lake build` had not
rebuilt the emitter (D31). Redone against a `git stash`-ed pristine tree with the
executable explicitly built: **52 089 879 bytes of records and 115 498 260 bytes
of ACL2 cases, byte-identical.** And the table is load-bearing rather than
decorative: with the guard neutered and the `df` row deleted, `df=` vanishes from
all 80 964 record lines.

## D31 — `lake build` did not build the harness, and the probe discipline is what runs the harness.

`lakefile.toml` said `defaultTargets = ["X86"]`. A bare `lake build` therefore
elaborated the model library and built **neither executable nor the test tier**.

⛔ **THAT IS PRECISELY THE COMMAND A PROBE IS RUN AFTER.** Every deletion probe
in this repository works by editing a source file, rebuilding, and invoking
`.lake/build/bin/x86lean-diff` directly — and the binary the probe ran was
whatever the last `lake build x86lean-diff` or `run_differential.sh` had left on
disk. Batch 12 caught this the only way it could be caught: a probe that had to
go RED came back GREEN. The `df` row was deleted from the new `flagFields`
table, `lake build` reported success, and the emitted records still carried
`df=` in all 80 964 lines — because the emitter was twenty-eight minutes old.

⭐ **THE GATES WERE NEVER EXPOSED, AND THAT IS THE UNCOMFORTABLE PART.**
`scripts/run_differential.sh` builds `x86lean-diff` explicitly (line 17) and
`.github/workflows/ci.yml` names all five targets. So CI was always honest. What
was dishonest was **the instrument the seat uses to CHECK the gates** — and for
a project whose entire method is "test the claim by deleting the coverage and
watching the arm go quiet", an unreliable probe is worse than an unreliable
gate: it silently converts a discipline into a ritual.

⚠️ **AND THE FIRST REPAIR OF THIS LINE WAS ITSELF INCOMPLETE**, in the same
direction, within the same hour. It added the two executables and still omitted
`Tests` and `X86Native`, so `lake build` came back green while the entire test
tier — the coverage theorems, the anchors, the axiom gate's red-first drive —
had not been elaborated at all. That was caught by adding four mnemonics to
`rosterP0` and watching `lake build` report success when `roster_size_is_53`
could not possibly still hold. ⇒ **A partial fix to a "what does green mean"
defect reproduces the defect at a smaller radius, and it is believed more
readily the second time because it has just been repaired.**

`defaultTargets` is now exactly the CI target list, and it must stay that way.

## D32 — Two defects that cancelled: the memory-destination gate could not read `setcc`'s claim, and could not have backed it either.

`mem_dest_claims_are_backed` exists to stop the coverage table over-claiming a
memory destination. It was green. It was green because **both halves of it were
broken and the two errors cancelled.**

| half | defect |
|---|---|
| `claimsMemDest` (the shapes reader) | fired on the prefix `m(`. `setcc`'s row spells its memory write **`m8(w)`**, with the operand width between the `m` and the parenthesis — so the claim was never read |
| `isMemDestVector` (the vector finder) | had no `.setcc` case and fell into `_ => false`, answering "no vector" to a claim that has **sixteen** |

Repairing either half alone turns the gate RED — verified, both ways. The green
depended on being wrong twice.

⛔ **AND BATCH 6 WIDENED THAT PATTERN EXPRESSLY FOR `setcc`.** The comment above
the clause says so: it generalised the literal `m(rmw)` to the prefix `m(` so
that `setcc`'s write could be described honestly as `m(w)`. It missed its own
motivating row by one character, and then explained itself for six batches.

⇒ 🔑 **A GENERALISATION THAT NAMES ITS MOTIVATING CASE IS NOT EVIDENCE THAT IT
COVERS IT.** The comment is the artifact that made the question feel answered —
D29's law again, now in a gate rather than a table. The clause is now the
NOTATION'S RULE (`m`, optional width, `(`), not a spelling; and
`isMemDestVector`'s catch-all is **gone**, so growing `Op` is a compile error on
that line rather than a silent `false`.

## D33 — The selftest could not plant a bug in the refusal channel, because `driveWrong` only counted `spec`-class hits.

`classify` gives a disagreement in `refused` the class **`"refusal"`**.
`driveWrong` counted a hit as `d.cls == "spec" && d.field == expectField`. ⇒ **an
arm whose bug shows in the refusal channel could never register**, however
correctly the comparator caught it.

`ud2` — the first form in the roster whose entire meaning is a fault — is what
walked into it. Its arm plants a `ud2` that executes instead of faulting; the
comparator found all seventy-six disagreements in `refused`, and the selftest
printed *"fires on the wrong thing"* and FAILED.

⭐ **THIRTY ARMS AND NOT ONE ON `refused`.** `bothRefused` was written
specifically for this channel — it is the reason two models that both decline an
instruction count as agreeing — and the harness's own self-test could not reach
it. That is D27's shape moved up one level: not a constant in the STATE, but an
unexercised branch in the INSTRUMENT. **A test harness has coverage gaps too,
and nothing was watching that one because nothing had asked.**

The filter now excludes exactly `undefined-region` (an EXPLAINED disagreement,
which must never count as catching a bug) and `harness` (a missing field, an
instrument failure rather than a caught model bug), and admits `spec` and
`refusal`.

## D34 — `retq` and `leaveq` were UNREACHABLE, not merely untested, and the batch looked before it shipped.

Against the seventy-eight pre-states that existed before batch 12:

* the stack window's background pattern is `0x10 + i` from `0x7fe0`, so the eight
  bytes at RSP = `0x8000` read as `0x3736353433323130` — bits 63:47 are not all
  equal, so it is **not canonical** and `retq` refuses in every single state;
* RBP is `0` in all seventy-eight, so `leaveq` would set RSP to 0 and pop from an
  address outside **both** watched windows.

⇒ **A `retq` that jumped to the return address without ever popping it would have
passed the entire pre-batch state set.** Measured, not argued: with `frameStates`
removed, that arm catches ZERO and the selftest reports "the comparator does not
work". With `frameStates` present it catches exactly **2** — the two frames, and
nothing else.

⭐ **THIS IS D27's RULE APPLIED BEFORE THE FACT INSTEAD OF AFTER IT.** D14 was a
constant memory window, D26 a constant RDX, D27 a constant FLAG and an unreached
COMBINATION; this is a constant WINDOW CONTENT. Four dresses is enough to state
the rule without reference to any of them: **a gate watching something that
cannot move reports an agreement it never tested.** What changed in this batch is
the moment the question was asked — "what in the state does this form actually
read, and does anything in the state set vary it?" is now part of adding a form,
not part of the post-mortem.

⇒ 🔑 And the corollary the batch was priced by: **the cheapness of a form is a
fact about its SEMANTICS; its cost is a fact about the STATE it needs.** These
four instructions are one line of `step` apiece — `nop` does nothing, `ud2`
faults, `retq` pops, `leaveq` is two assignments — and two of them needed a new
pre-state constructor before they could be tested at all.

## D35 — `lods` is not a cheap candidate, because ACL2 x86isa does not implement it.

The batch-11 bank listed `lods` among the cheapest remaining forms. It is not a
cheap form; it is a form this project's ORACLE cannot execute.
`vendor/acl2/books/projects/x86isa/machine/catalogue-data.lisp`, section
"5.1.8 String Instructions", says in as many words: *"Unimplemented
instructions: SCAS and LODS variations."*

⇒ **A form's cost has a third component nobody had needed to name: whether the
oracle implements it.** Cheap semantics + cheap state + **no oracle** = not a
differentially validated form at all. Checking the catalogue before pricing a
group is now the first step, not the last; `retq` and `leaveq` were kept because
the same file's section 5.1.7 lists only the FAR return with immediate (`0xCA`)
as unimplemented, and section 5.1.10 lists no exclusion for `LEAVE`.

## D36 — D35 was right about the file and wrong about the machine: the oracle's catalogue is prose, and it is wrong in both directions.

D35 made "check `catalogue-data.lisp` before pricing a form" the first step of a
batch, on the strength of one `:doc` string. **P1 batch 13 ran the opcodes
instead of reading the prose, and the doc string is wrong.**

The measurement: thirty-six hand-assembled forms (every byte sequence verified
against clang first), planted at RIP in the harness's own pre-state shape, one
`x86-fetch-decode-execute` each, `refused` read off the post-state.

| the catalogue's `:doc` says | measured |
|---|---|
| §5.1.8: "Unimplemented instructions: SCAS and LODS variations" | ⛔ **`lodsb/w/l/q` and `scasb/w/l/q` ALL EXECUTE.** `lodsq` loads eight bytes and advances RSI by 8; `scasq` compares against RAX, sets the flags and advances RDI by 8. |
| §5.1.16: LZCNT is unimplemented | ⛔ **`lzcntq/l/w` EXECUTE**, and correctly: `lzcntq` of `0x123456789ABCDEF0` is 3, where a `bsr` decoding the same bytes with the `F3` ignored would answer 60. |
| §5.1.16: lists neither BLSI implemented nor unimplemented | ⛔ **`blsiq/l` EXECUTE.** The section's two lists are not a partition. |
| §5.1.16: ANDN, BEXTR, BLSMSK, BLSR, BZHI, PDEP, PEXT, MULX, RORX unimplemented | ✔ all nine refuse |
| §5.1.13: MOVBE implemented | ✔ executes, both directions, w/l/q |
| §5.1.16: SARX, SHLX, SHRX, TZCNT implemented | ✔ all execute |

⭐ **THE PROBE WAS CALIBRATED IN BOTH DIRECTIONS IN THE SAME RUN**, which is why
its answer is worth more than the doc's: nine forms refused and twenty-seven
executed, so neither "everything executes" nor "everything refuses" is a reading
the instrument could have produced by being broken.

⇒ 🔑 **A catalogue's prose is a claim ABOUT a model, not a measurement OF it** —
and D35 turned one stale doc string into this project's roster policy in a single
step, because the doc agreed with the answer that was wanted (a form dropped is a
batch made cheaper). The rule survives with its instrument replaced: **price a
form against the oracle by EXECUTING one instance of it**, which costs about five
seconds of ACL2 and is now `run/probe_drive.lsp`'s shape. `lods` and `scas` go
back on the candidate list; `lzcnt` and `blsi` join them.

⚠️ And the shape of the error is one this project has now met four times: an
inherited diagnosis, correct in outline (the oracle's coverage IS a real third
cost) and wrong in the enumeration, believed because the outline was right.

## D37 — The memory-destination gate was position-blind, and only a three-operand form could show it.

D32 repaired `claimsMemDest` twice — the literal `m(rmw)` widened to the prefix
`m(`, then widened again to "an `m`, an optional width, a parenthesis" — and both
repairs left a substring test for the literal `m,r` untouched beside them.

⛔ **BATCH 13's `sarx`/`shlx`/`shrx` ARE THE TABLE'S FIRST THREE-OPERAND ROWS.**
Their shapes read `r,r,r · r,m,r` — destination, source, count — and `r,m,r`
CONTAINS `m,r`, whose `m` is the SOURCE. `mem_dest_claims_are_backed` went RED on
a TRUE claim about forms that cannot write memory at all.

The cheap way out was to respell the shapes column until the pattern stopped
firing. That is notation bent to fit its own gate — the failure this gate exists
to catch one level up — so the repair went into the predicate: shapes are
destination-first, so **a memory destination is an `m` in the FIRST operand
position of some shape**, followed by a `,` (a further operand) or a `(` (a
parenthesised kind). A bare first-position `m` is still a memory SOURCE, which is
what keeps `push`'s `r · m · imm` out.

⭐ **AND THE REWRITE IS AUDITED BY A THEOREM, not by a script.** Rewriting a gate
is the one change that can weaken it invisibly: the old form was green and the
new form is green, and nothing says which rows changed hands. The pre-batch-13
predicate is kept as `claimsMemDestLoose`, and
`mem_dest_rewrite_changed_exactly_the_three_operand_rows` states that the rows
the loose rule claims and the tight one does not are EXACTLY `["sarx", "shlx",
"shrx"]`, and that the tight rule claims nothing the loose one did not. Stated as
the list rather than as a count, because a count is satisfied by any three rows
changing hands.

⇒ 🔑 **A pattern that has been repaired twice is trusted more than one that never
has, and a repair aimed at a spelling does not touch a defect of position.** Both
of D32's fixes were about WHICH CHARACTERS spell a memory destination; neither
asked WHERE in the shape they may appear, because with two operands the question
does not arise. **The dimension a defect can hide in is the one no existing row
varies** — which is D27's rule ("a gate watching something that cannot move
reports an agreement it never tested") moved from the pre-state set to the
NOTATION.

## D38

**An absolute kernel-time ceiling on a table-driven module is a chore, not a
gate — and it provably missed the regression a per-row one catches.**

P1 batch 13 handed batch 14 a named inherited cost: `Tests.Coverage` at
16 400 ms against a 19 560 ms ceiling (84%), of which 5 800 ms was one theorem.
Batch 14's first act was to MEASURE it rather than act on it, and both figures
were wrong: the module ran **17 900–18 400 ms across three runs (92–94%)** and
the theorem's share was **12 300 ms, not 5 800** — more than twice the handed-on
number and 69% of the module rather than 35%. ⇒ [[inherited-diagnosis-is-a-hypothesis]]
for the fifth time in this repository, and the first time the inherited number
was wrong in the *reassuring* direction on both halves at once.

⛔ **THE OBVIOUS REPAIR WAS TRIED FIRST AND FAILED.** The audit theorem was a
conjunction of two `decide`s that swept the table twice, evaluating both string
predicates on every row in both sweeps — four predicate evaluations per row for a
question about one. Rewritten as a single `filterMap` it evaluates each once and
says strictly more (the second component records WHICH rule claimed the row, so a
row changing hands the other way breaks the equality). **It saved nothing:
17.9 s before, 17.9 s after.** Measuring the two disjuncts of
`claimsMemDestLoose` separately shows why — the `m,r` infix scan costs ~6.1 s and
`looseMemDestShape` ~6.1 s, so both are full character-list sweeps of the shapes
column and the traversal count was never the driver. ⇒ **The cost is reading the
artifact in the kernel, which D15 already decided to pay.** The rewrite was kept
for being a stronger statement and for deleting a duplicated definition, not as
an optimisation — it was not one, and its comment says so.

⇒ 🔑 **SO THE UNITS CHANGED INSTEAD OF THE NUMBER.** This module's kernel cost is
LINEAR IN THE COVERAGE TABLE, which grows every batch by construction. An
absolute ceiling on it must therefore be raised every batch — batches 3 and 14
both did — and **a gate relaxed on schedule is not a gate; it is a chore that
trains its owner to raise it.** The ceiling is now registered PER ROW
(`Tests.Coverage @perRow 470.0`) and multiplied by the live row count.

⭐ **AND THE OLD FORM PROVABLY MISSED WHAT THE NEW ONE CATCHES.** Batch 13's
theorem took the module from ~90 ms/row to 293 ms/row — a **3.2× jump in cost per
row** — and the absolute ceiling did not fire (17 900 against 19 560). At the
registered headroom the per-row ceiling does. Batch 14's own 12 rows and 34
vectors then took it to **266 ms/row, DOWN from 293** while the absolute number
held flat: the gate now reads cost DENSITY, where ordinary growth is free and
only a real regression moves the number.

⚠️ The denominator is not counted by the script. It is read from the literal in
`theorem roster_size_is_N : rosterSize = N := by decide`, which `table_row_count`
pins to `tableP0.length` — so the number the ceiling divides by is one Lean
PROVES is the table's length. A missing or ambiguous literal is an ERROR, never a
default; both refusals are probed.

⚠️ **AND BATCH 10 ASKED FOR THIS AT THE RIGHT TIME AND WAS NOT HEARD.** Its note
in `Tests/Coverage.lean` says: measure per theorem, "the ceiling is untouched at
19560 with 2.4× headroom, so there is room to do that properly rather than under
pressure." Batches 11, 12 and 13 did not; batch 14 arrived at 1.09× and did it
under exactly the pressure batch 10 named. ⇒ **A deferred instruction with no
gate behind it is a suggestion, and the batch that can afford to act on it is
never the batch that has to.**

## D39

**The `undefined` column was a published claim that no gate read.**

`frame_tier_iff_undefined_bits` checked the column against the TIER — frame iff
non-empty — and nothing checked its CONTENTS. A row naming the wrong flags, or
four of the five it should, read exactly like a correct one. It is the model's
published statement of where it declines to commit and what every tier claim
rests on, and for thirteen batches it was prose.

`checkUndefinedColumn` compares the flag TOKENS each row mentions against the set
the model actually draws, measured over every emitted case, **in both
directions**: a row naming a flag the model never draws OVER-claims, and a row
missing one the model does draw UNDER-claims — the worse direction, because a
reader takes a bit for committed that the oracle chooses.

⚠️ **Tokens, not strings, and the limit is stated rather than left to be found.**
Existing rows carry real conditions (`CF (count ≥ width)`, `OF (count ≠ 1)`) that
are worth keeping in the published table, so the gate extracts the names a row
mentions and does not police the prose around them. **A row could still carry a
wrong CONDITION.** That is not checked here, and saying so is part of the gate.

⇒ 🔑 **A column no gate reads is wrong wherever nobody looked** — D15's rule
about the shapes column, arriving in the column beside it, found only because
batch 14 added the first row whose undefined region is not a flag.

## D40

**The first UNDEFINED DESTINATION, and how the leak check kept its teeth.**

`bsf`/`bsr` at a zero source leave the DESTINATION REGISTER undefined (SDM
Vol. 2A) — not a flag. Every undefined region in the model until batch 14 was a
flag, and `undefinedLeaked` could therefore be stated in one line: the two
opposite oracle runs must agree on everything that is not a flag.

Real silicon leaves the destination unmodified and AMD documents that it does.
Intel does not, and this model follows its stated source: writing the old value
back would be INVENTING A FACT in exactly the sense `X86/Oracle.lean`'s header
forbids — and it is the more tempting invention because it matches the machine on
the desk. **The differential run shows the two models parting exactly there**:
against ACL2 x86isa, which leaves the destination unmodified, there are **108
disagreements in `rax`, all in `bsf`/`bsr`**, every one of them EXPLAINED.

⛔ **THE TEMPTING REPAIR WOULD HAVE GUTTED THE LEAK CHECK.** Widening the derived
undefined set to registers and stopping there means no register can ever leak
again: an oracle bit reaching `rcx` by mistake would be re-read as "`rcx` is
undefined here", the differential would file the resulting disagreement as
`undefined-region`, and a real spec bug would be recorded as an explained one.
The check would report a pass in precisely the case it exists to catch.

⇒ 🔑 **SO THERE ARE TWO SOURCES AND THE GATE IS THEIR EQUALITY.**
`declaredUndefRegs` reads the AST and the SDM rule; `undefinedRegs` runs the two
oracles and reports what moved. A register that moves and is not declared is the
old leak. A register declared and not moving is a FALSE UNDEFINED CLAIM — the new
hazard, which would license the harness to explain away a genuine disagreement in
that register for ever. Neither direction was possible before this batch and both
are probed: declaring the destination always (378 leaks), never (78), and
**declaring the WRONG register — right count, wrong name — which also fires (78)
and is the one a count-based check would have missed.**

⚠️ **AND THERE IS NO SELFTEST ARM FOR IT, CORRECTLY.** A model writing a
different value into an undefined destination is not WRONG; `classify` files that
as `undefined-region` and `driveWrong` excludes the class by design. The claim is
held up where it can actually be seen — `Tests/Nonvacuity.lean` (the two oracles
must differ at a zero source and AGREE at a non-zero one) and `undefinedLeaked`
on every case. **An arm here would have been a probe that could only report a
pass**, which is the shape of [[a-probe-must-create-its-condition]].

⚠️ Batch 14 first probed the leak check with `selftest <arm>` and got PASS from a
deliberately broken declaration — because `driveWrong` never reads
`Report.leaks`. The count was reachable only through the no-argument selftest's
control, twenty-one minutes away. It is now in the `undefined-column` command
(32 s), because a discipline expensive to exercise gets exercised less.

## D41

**The count had a comment and survived thirteen batches; the sentence beside it
had none and did not.**

`docs/COVERAGE.md`'s per-batch narrative stopped at "12 — the near-free four"
while the count in the same paragraph already read **396**, which includes batch
13. Batch 13 updated the number and not the prose. Every gate stayed green, and
the published coverage document described a model one batch older than the one it
tabulated.

The two claims sit one line apart and are maintained by the same hand. The
difference between them is that the literal carries a comment in `Main.lean`
stating the counting rule and an `awk` line that checks it, and the sentence
carried nothing.

`scripts/check_coverage_prose.py` gates the narrative against the
`docs/DIFFERENTIAL-P1-BATCH<N>.md` files — one per batch, written by a different
step of the work for a different reason, so **the two sides of the gate are not
maintained by the same edit**. A gate whose halves move together is a gate that
agrees with itself. It is probed by replaying batch 13's actual defect (narrative
stops at 12 ⇒ RED), by removing a middle batch (⇒ RED), and by hiding the
narrative altogether (⇒ refusal, rc 2, not a pass).

⇒ 🔑 **Prose next to a gated number is the least-suspected text in a
document**: it is read every time the number is checked, and checked never.

---

## D42 — a backward step off the end of a watched window is a test that passes by construction

**P1 batch 15.** The string group is the first in this model whose operands
MOVE. RSI and RDI were 0 in all eighty pre-states — measured in the emitted
`run/cases.lsp`, not only read off `mkPre` — and address 0 lies outside both
watched windows.

That much is batch 12's `leaveq` trap again. The part that is new survives
giving the pointers a home: **off the end of a watched window, this model's
`Mem` reads 0 for an unwritten byte and the ACL2 driver renders an unmapped read
as `00`.** A pointer that decremented when it should have incremented would
therefore have the two models agreeing — on zeroes — and the DF case would have
been green without ever being tested.

The data window is widened from 32 bytes to 64 so that every access, at every
width, in BOTH directions, lands inside watched memory. Every one of the
original 32 bytes keeps its address and its contents: the two new flanks get
their own patterns rather than re-basing the existing run, which would have
moved the whole window and broken `memory_window_margin_is_fixed`.

⇒ 🔑 **An unobserved region does not report "unknown"; it reports agreement.**
Two models that both read zero off the end of the world agree perfectly, and the
gate cannot tell that from a model that is right.

---

## D43 — a probe that reports nothing has two causes, and the flattering one is that the model is right

**P1 batch 15.** A planted arm updated the string pointers through the ordinary
operand-width rule (`setReg sz`) instead of writing all 64 bits — the natural
mistake, since every other register write in this model does go through that
rule. The harness reported **zero unexplained disagreements against a
known-wrong model**, which is its own way of saying the comparator does not work.

⚠️ The arm was right; the pre-states were the problem. A merged write and a full
write differ only where the new pointer differs from the old ABOVE the operand
width — only when the update CARRIES or BORROWS across a byte or word boundary.
With RSI at `0x1fe8` and RDI at `0x2010`, `±1` and `±2` never touch bit 8, so
the wrong model IS the right model on all eighty states, at every width, in both
directions.

This is D27 in its `loopCounterStates` form: **an adversarial set is adversarial
only with respect to the questions already asked of it.** The pointer addresses
were chosen to keep every access inside a watched window — a question about
ADDRESSES. Nothing had asked about the ARITHMETIC that produces the next one.

`stringBoundaryStates` supplies both directions: forward with both pointers at
`…FF`, backward with both at `…00`, all four addresses still inside a watched
window at every width.

⇒ 🔑 **A green from a probe is evidence about the model only if the state can
express the defect.** Otherwise it is evidence about the state, and the two look
identical from the outside.

---

## D44 — a table checked in one direction is half checked, and the unchecked half is the flattering one

**P1 batch 15.** `mem_dest_claims_are_backed` has caught a coverage row claiming
MORE than its vectors deliver since batch 3. Nothing checked the reverse.

⛔ This batch would have been the first to fall in it. The string rows were
first written as `implicit [rdi] ← [rsi]` — accurate English, and containing no
first-position `m`, so `claimsMemDest` was false for `movs` and `stos` while
their vectors plainly write memory. Every gate stayed green on a coverage table
that had stopped saying what the model does.

`mem_dest_vectors_are_claimed` states the other direction.

⇒ 🔑 **An over-claim looks like a mistake and an under-claim looks like
modesty**, so the direction nobody gates is the direction nobody doubts. This is
the `undefined` column's lesson (D39) arriving in the `shapes` column one batch
later, which is what says it is a property of TABLES and not of that column.

⭐ A second-order confirmation arrived free: rewriting the shapes in the
destination-first notation gave
`mem_dest_rewrite_changed_exactly_the_three_operand_rows` its first `(_, false)`
entries. Batch 14 added that component with no row exercising it, on the
argument that a row changing hands the other way ought to break the equality.
One batch later, `cmps` and `scas` did.

---

## D45 — a positive control says nothing about the part of the subject it never touches

**P1 batch 15.** The watch windows are declared twice, in Lean and in Lisp,
because neither toolchain can read the other's source. `scripts/check_windows.py`
now compares the two literals.

⚠️ Stated honestly, the drift it guards fails LOUD rather than silent: a
mismatch makes every rendered record differ. What the gate buys is detection in
20 ms rather than after a 4-minute ACL2 run — the difference between a check
that runs before a commit and one that does not (see *make the probe cheap*).

⛔ **And the gate's first version was wrong in the way it was written to
prevent.** Its Lisp parser used a non-greedy regex that ended its capture at the
first `))` — and the last pair's closing paren IS the list's closing paren — so
it silently parsed only the FIRST window. Its selftest passed: both planted
mutations happened to fall in the first window, both went red, and both went red
for the right-looking reason.

⇒ 🔑 **A positive control proves the gate reacts to the condition it CREATES.**
It is silent about every part of the subject the control does not reach, and a
control is usually written from the same mental model as the code it checks — so
the two share their blind spot. The repair is not a better control but a
different KIND of check alongside it: the parsed window COUNT is now compared
between the two sides, which catches a dropped trailing entry even when every
value that was read agrees.

## D46 — an instruction's own address is a legal answer, and the SDM's loop is not the oracle's step

P1 batch 16 (the repeat prefixes). Every `rep`-prefixed string form in
`p1/roster.tsv` — eleven rows — is a loop, and this model takes ONE STEP at a
time. The question the batch opened with, before a vector was written, was how
`Instr.len` and RIP interact when the model must not advance.

**The measurement.** `x86-fetch-decode-execute` performs exactly one iteration
and signals "repeat" by leaving RIP alone. That much was known from batch 15's
probe. What was not known, and what this batch went to the oracle for, is where
the count is tested:

| case | RCX in | RCX out | RIP |
|---|---|---|---|
| `rep movsq` | 0 | 0 | **advanced** |
| `rep movsq` | 1 | 0 | **UNCHANGED** |
| `rep movsq` | 3 | 2 | unchanged |
| `repe cmpsq`, operands equal | 1 | 0 | **UNCHANGED** |
| `repe cmpsq`, operands differ | 3 | 2 | advanced (ZF=0) |
| `repne scasq`, operands equal | 3 | 2 | advanced (ZF=1) |

⛔ **COUNT EXHAUSTION DOES NOT ADVANCE RIP.** The count is tested only ON ENTRY.
`rep movsq` with RCX = 1 performs the copy, leaves RCX = 0, and stays at its own
address; it is the NEXT step, finding the count already zero, that falls
through. The SDM writes REP as a `while` loop, and the natural single-step
reading of a `while` loop — do the body, decrement, notice zero, leave — is the
WRONG decomposition. The right one puts the test at the top, which is what a
`while` loop actually says and what a reader in a hurry does not see.

⇒ 🔑 **A model that advanced on the decrement reaching zero is right at every
value of RCX except 1.** It agrees on 0 (no iteration in either model) and on
every value ≥ 2 (the count does not reach zero in one step). ONE VALUE OF ONE
REGISTER separates the two models across the whole eleven-row group.

That is D43's shape with the answer coming out the other way. There the planted
defect caught nothing and the pre-states were at fault; here `adversarial`
already contained 1 — put there in P0 for the flag rules, for reasons having
nothing to do with loop counts — so the sweep reached the one state that
discriminates and `wrongRepAdvanceOnCountZero` is caught. ⇒ **The batch was
lucky, and the luck is worth recording as such**: had `adversarial` been the
"interesting boundaries" list it superficially resembles — 0, powers of two,
all-ones — the whole branch would have been green and wrong.

**The second decision: `.repstrop` as its own constructor, and `stringIter`
shared for real.** An `Option RepPrefix` field on `.strop` would have been the
smaller diff and the worse one — it touches all twenty batch-15 vectors, both
memory-destination gates and every characterization lemma, so a batch that
reuses batch 15's semantics UNCHANGED would have rewritten every line naming
them. Additive instead, for the reason batch 15 widened its window additively.
But additive must not mean *copied*: `stringIter` is batch 15's body with the
RIP write lifted out, and BOTH constructors call it, because a second copy of
five subtly-ordered arms is five chances to drift.

⇒ 🔑 **A refactor is audited by a theorem, not by a diff.**
`step_repstrop_iterates_like_strop` says the prefixed form leaves the same
memory and the same flags as the unprefixed one on a non-zero count. That is the
statement that fails if the two bodies ever diverge, and it is re-runnable in a
way "I checked the diff" is not.

**The third: `repApplies` is a ROSTER partition, not an encoding fact.** It
looks exactly like `bitcntEncodable` from batch 14 and means something different,
which is the kind of resemblance that gets taken on trust. Every pair it rejects
ASSEMBLES:

* `rep cmpsq` and `repe cmpsq` are the identical bytes `f3 48 a7` — measured
  with clang — so `.rep` on a comparison would be a second name for a form
  `.repe` already covers.
* `repne movsq` (`f2 48 a5`) assembles, and x86isa **executes it as an
  unprefixed string op**: one iteration, RCX *not* decremented, RIP advanced.

⇒ The model declines it. Copying an oracle's treatment of a shape the roster
does not file would be taking a quirk for a specification — and the comment
saying so is load-bearing, because the next reader's default assumption will be
that a table shaped like `bitcntEncodable` records what has no encoding.

## D47 — a disclaimer is not a gate, and it is worse than nothing

P1 batch 16, found while sweeping for stale numbers after the coverage literal
moved 418 → 429. `README.md` — the first file any reader of this repository
opens, and it is destined to be public — carried this:

> **P1 IN PROGRESS — twelve batches landed.** The roster now stands at
> **388 of the 525 forms** … `527 vectors · 80 pre-states · 42160 cases`

Every one of those five numbers was **four batches stale**. Batches 13, 14 and
15 each moved the literal in `Main.lean`, regenerated `docs/COVERAGE.md`, and
wrote a differential record; each left this paragraph untouched. Every gate in
the repository stayed green, because none of them reads the README.

That much is D41 again — *a column no gate reads is wrong wherever nobody
looked* — arriving in a third document after the shapes column (D15/D16) and the
per-batch narrative (D41). What makes it worth its own decision is the sentence
that stood directly underneath it:

> ⚠️ **THE AUTHORITATIVE LIST IS GENERATED, NOT WRITTEN HERE.** … the numbers in
> this paragraph are a snapshot and that file is the claim.

⇒ 🔑 **THAT DISCLAIMER IS WHY THE STALENESS SURVIVED FOUR BATCHES.** It reads as
diligence — it names the real authority, it warns the reader, it looks like
exactly the discipline this repository applies everywhere else. And its effect
was to tell every reader, and every author of the next batch, *not to check
these figures*. A number nobody is expected to trust is a number nobody
corrects.

⇒ 🔑 **A wrong number under a disclaimer is worse than a bare wrong number.** A
bare one still looks wrong to somebody; a disclaimed one has been pre-explained,
so noticing it feels like pedantry rather than a finding. This is D15's rule
("a wrong claim with a reassuring comment beside it is harder to see than a bare
one") in its strongest form yet, because here the reassuring comment was not
merely beside the claim — it was *about* the claim, and it was TRUE. The
generated file really is the authority. The disclaimer was accurate and it was
still the defect.

**The repair is a gate, not better prose.** `scripts/check_readme_snapshot.py`
checks all six headline numbers in CI against sources that cannot drift in step
with them: forms/vectors/mnemonics from the GENERATED `docs/COVERAGE.md`, the
batch count from the `docs/DIFFERENTIAL-P1-BATCH<N>.md` files (the same anchor
D41 uses), and pre-states/cases from the newest of those records. It also checks
the two independent writes of the vector count against **each other** before
comparing either to the README, so it cannot validate the README against a
figure that is itself wrong.

⚠️ **And its positive control mutates every claim and one SOURCE** — D45's
lesson taken literally. Six claims over three sources needs a mutation per
claim, not per gate; and without the source-side mutation a gate that parsed the
README and compared it to itself would pass all six README arms while checking
nothing. Deleting the paragraph outright exits 2: a missing subject is not a
pass.

## D48 — a citation is an ungated claim, and it is the most persuasive kind

P1 batch 16. While writing a comment that pointed at the gate holding a claim —
the ordinary convention in this repository — the batch cited a theorem it had
not yet written. Grepping to fix its own slip turned up three that were already
there, the oldest from P1 batch 11:

| cited as | in | reality |
|---|---|---|
| loop-synonyms-are-one-encoding | `Tests/Coverage.lean` | **never existed** (batch 11) |
| bit-counting-reaches-a-zero-source | `Tests/Coverage.lean` | split in two, citation not updated (batch 14) |
| undefined-column-matches-the-model | `Main.lean` | the check is real; nothing ever carried that name (batch 14) |

Each occurred exactly once in the repository: in the comment that cited it.

⇒ 🔑 **A CITATION READS AS THE GATE IT NAMES.** These sentences are written to
answer the sceptical reader — *this is not merely asserted, here is the theorem
that holds it* — and they answer that reader whether or not the theorem exists.
Nobody greps for the name of a gate they have just been told about; the citation
is the reason not to look. This is D15's rule ("a wrong claim with a reassuring
comment beside it is harder to see than a bare one") one level up: the comment is
no longer merely reassuring, it names its own evidence.

⚠️ **And the two grades are different defects.** A citation whose name drifted
(batch 14's two) still points a reader at real work — a grep finds the
near-neighbour, and the claim IS held. One that points at nothing (batch 11's)
leaves the claim unheld while looking held. Batch 16 had reproduced the second
kind verbatim, which is what a convention does when nothing checks it: **the
pattern gets copied together with its hole.**

**The repair, in two parts.**

`scripts/check_citations.py` (CI) requires every `` `identifier` `` cited "in
<source file>" to OCCUR in that file. ⚠️ Occurrence, not declaration, and the
weaker test is deliberate: a first version demanded a declaration and fired on
"the list of `undefBit` call sites in `X86/Semantics.lean`" and "paired with
`Oracle.zero` in `Tests/Nonvacuity.lean`" — both true sentences citing a file
for a USE. **A gate that cries wolf on true sentences gets switched off**, and
occurrence is exactly the line between pointing at something and pointing at
nothing. Its control runs both directions: a phantom must be caught and a real
citation must NOT be flagged, because a gate that only proves it can go red says
nothing about why it goes green.

And batch 11's actual claim is now *held*, not merely cited: the `SYNONYMS`
table in `scripts/check_encodings.py` assembles `loope`/`loopz`,
`loopne`/`loopnz`, `repe`/`repz` and `repne`/`repnz` and requires identical
bytes. ⚠️ **It could never have been the theorem batch 11 named.** There are no
`loopz`/`repz` vectors and there must not be — a vector per spelling is one
instruction differentially tested twice — so a theorem "over the vector table"
had nothing to quantify over. The claim is about an assembler and now an
assembler checks it. ⇒ **The phantom citation was not a typo; it named a
theorem that could not exist**, and writing the name was what made the
impossibility invisible.

⚠️ **A limit, stated because it shaped the repair.** The gate cannot tell a live
citation from a quoted dead one: this batch's own post-mortem notes quote the
sentences they replace, and the gate flagged them. Weakening it to guess at
quotation would trade a real check for a heuristic in a file whose whole subject
is claims nobody verifies. The convention instead is that **a dead citation is
never written in citation form** — named in prose, never as `` `ident` ``
beside its file — which is why those notes read as they do.

---

## D49 — The handover's scope was named by FAMILY, and the families did not partition the mnemonics.

P1 batch 16's bank told batch 17 to take **"families 14/23/27/24 — `xadd`/`cmpxchg`,
`mul`/`imul`, `div`/`idiv`/`shld`/`shrd`"**. Taken literally that instruction is wrong
three ways, and running the roster query rather than reading the sentence found all
three before any code was written:

1. **Family 23 was already discharged.** It is `repe`/`repne`/`repnz`/`repz` × `cmps`/`scas`
   — eight of the eleven prefixed rows batch 16 itself had just claimed. The bank listed as
   *next* a family the same bank recorded as *done*.
2. **The families do not partition the mnemonics.** `cmpxchg` and `xadd` occupy family
   **10** (`m,r`) as well as 14; `shld` and `shrd` occupy family **40** (`m,r,cl`,
   `m,r,imm`) as well as 24. A batch scoped by family number would have claimed 18 rows
   and orphaned 6 — memory-destination rows of mnemonics it had just implemented, filed
   under families nobody would look at again.
3. Scoped by BASE NAME the same set is **24 rows**, not 18.

⇒ 🔑 **A HANDOVER'S SCOPE IS A HYPOTHESIS, AND THE FAMILY COLUMN IS A HINT.** The roster
is the authority. Batches 15 and 16 had to split ONE family with a column filter and wrote
the counting rule down for it; the lesson generalises the other way too — **a mnemonic
spans several families**, and a rule that reads the family column alone is wrong in the
direction nobody checks, because an under-claim looks like modesty.

The scope actually taken is `mul` · `imul` · `div` · `idiv`, twelve rows, counted by

```
awk -F'\t' 'NR>2 && $4 ~ /^(mul|imul|div|idiv)$/' p1/roster.tsv | wc -l   →  12
```

and those four base names occur in no other family, so the rule cannot double-count with
any earlier batch. ⚠️ The reason for this cut is not tidiness: `div` consumes exactly what
`mul` produces — one opcode group, one register pair — while `xadd`/`cmpxchg` and
`shld`/`shrd` share nothing with that mechanism and are batch 18.

---

## D50 — The danger of a form that faults was never a wrong answer; it was an answer nothing asks for.

`div` and `idiv` are the first forms in this model whose refusal depends on the
**OPERANDS** rather than the opcode. Batch 12's `ud2` refuses because of what it is;
`divq %rcx` refuses because of what RDX, RAX and RCX happen to hold, so the same vector
refuses at one pre-state and divides at the next.

**The bank's warning was that the fault would be hard to REACH.** It said to check that a
zero divisor and an overflowing quotient are both reachable "rather than assumed". They
were checked — with a 656-case oracle probe over the harness's own eighty-two pre-states,
built by patching the bytes of the emitted `mov_d` cases so the pre-states were the
differential run's and not a re-implementation of them — and the measurement said the
**opposite** of what the warning anticipated:

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

⇒ ⛔⛔ **THE FAULTS ARE NOT SCARCE, THEY ARE THE MAJORITY: 51%–84% of pre-states refuse,
and at `idiv_w` only 13 of 82 actually divide.** `mkPre` sets `RDX := ~RAX` — put there in
batch 10 for `cltd`, nothing to do with division — and a huge high half is exactly what
makes a quotient too wide.

⇒ 🔑 **A GROUP THAT MOSTLY REFUSES IS A GROUP WHOSE AGREEMENT IS MOSTLY SILENCE.** Both
models refuse, the comparator records a match, and the quotient is never examined. That is
[[unobserved-regions-report-agreement]] with the roles reversed: there a too-narrow window
positively claimed agreement about bytes nobody looked at; here a too-eager refusal
positively claims agreement about arithmetic nobody ran.

**So the batch carries an arm whose only job is to price the observation**:
`wrongDivAlwaysRefuses`, a `div` that refuses on **every** divisor. It agrees with the
oracle on every genuinely faulting case and must be caught by the rest. It is —
**145 disagreements in `refused`**, so the non-faulting path is observed, measured rather
than hoped. Two more arms attack the fault predicate from the other side
(`wrongDivNoQuotientOverflow`, which keeps only the zero-divisor sentence: 236 catches)
and the arithmetic behind it (`wrongIdivFloorDivision`, Lean's `Int` division in place of
truncation-toward-zero: 63 catches).

⚠️ **And the same measurement produced a smaller lesson with a wider reach.** The probe's
own pre-state named `ok` — RAX = 0x100, RCX = 0x1000, RDX = 1 — is a perfectly good
non-faulting state at `.w`, `.d` and `.q`, and at `.b` it is a **zero-divisor** state,
because the divisor is `CL`, the low byte of 0x1000, which is zero. `div_b/ok` came back
`refused=1` and the *name* was wrong, not the model.

⇒ 🔑 **THE FAULT CONDITION IS A FUNCTION OF THE TRUNCATED OPERAND.** A divisor list that
is "all non-zero" is not a non-zero-divisor list at every width, and a state chosen for one
width silently becomes a different state at another. That is D43's shape a third time,
and it is why the table above is per-width rather than a single figure.

⚠️ **A claim in the `shapes` column that no gate could read.** `mul`'s memory operand is a
SOURCE, so every memory-DESTINATION gate in `Tests/Coverage.lean` is blind to it: writing
`m — b/w/l/q` while shipping vectors at two widths would have been an over-claim with
nothing looking at it — D47's shape in the column beside the one D47 was about.
`muldiv_memory_vectors_are_exactly_b_and_q` is stated as an EQUALITY, so it fails in both
directions: widening the row without a vector breaks it, and adding a vector without
widening the row breaks it too.

---

## D51 — The gate that stopped needing to be raised still records a number nobody can compare.

Batch 14 changed `Tests.Coverage`'s ceiling from an absolute figure to a PER-ROW one (D38),
on the argument that "a gate relaxed on schedule is not a gate". The change worked: the
ceiling has not been raised in four batches. But the **density it gates has climbed every
one of them** — 266 → 339 → 363 ms/row across batches 14 to 16 — and each bank has handed
the figure on with a warning and no repair. Batch 17 is the fourth to receive it.

**Two things are wrong, and they are different.**

**(1) The row is not the unit.** `Tests.Coverage`'s kernel cost is linear in
(ASSERTIONS × VECTORS), and neither factor is the roster size: a batch adds theorems and
vectors faster than it adds mnemonics. Over batches 15–17 the quantity `ms / (assertions ×
vectors)` moves by a few percent where `ms/row` moves 21%.

⚠️ **And the sound repair is BLOCKED, which is why batch 17 reports the figure and does not
gate on it.** The per-row ceiling can be trusted *because its denominator is kernel-pinned*:
`roster_size_is_N` is proved equal to the table's length, so it is a number Lean checks
rather than one the script counted. A vector count could be pinned the same way. An
ASSERTION count cannot — it is a property of the file's text, not of any term in it — so
registering a ceiling in the flat unit would trade a proven denominator for a grepped one,
which is exactly what `scripts/kernel_cost.py`'s own note says makes a ceiling meaningless.
The figure is therefore printed on every run, in the unit that is flat, so the growth law is
**observed each batch instead of reconstructed from git by whoever finally hits the ceiling.**

**(2) ⛔⛔ The series cannot be extended honestly, because none of its readings records
whether the machine was idle.** `scripts/kernel_ceilings.txt` *knows* this matters: for
`Tests.Nonvacuity` it records "measured on an IDLE machine (81.8 / 81.4 across two runs)"
and notes that a reading taken during the 21-minute selftest was ~15% high. The line beside
it — the per-row figure that is actually tracked batch to batch — records nothing at all.

⇒ 🔑 **A MEASUREMENT WHOSE CONDITIONS ARE NOT RECORDED CANNOT BE COMPARED WITH A LATER ONE.**
The discipline was written down once, in a comment, for the one module where it did not
matter much, and was not applied to the number a head is asked to watch.

⚠️ **This batch caught itself doing it.** Batch 17's first two kernel-cost runs were taken
while the 56-arm selftest was running, and read **411 and 425 ms/row** — which would have
been handed on as "a fourth consecutive climb" with no note of the load. Re-measured after
the selftest finished, **two runs both read 31 200 ms = 394.9 ms/row**, at one-minute load
averages of **2.20 and 4.08**.

⇒ ⭐ **And the re-measurement corrected the folklore as well as the figure.** The ceiling
file says a loaded reading is "~15% high"; measured here, ordinary background load moves it
**not at all** (two identical readings 1.9× apart in load average) while contention with the
selftest — a CPU-saturating Lean-and-ACL2 mix — moves it **4%–8%**. The rule is not "load"
but "contention for the same resource", and only the second kind was ever observed.

The repair is that `scripts/kernel_cost.py` now prints the one-minute and five-minute LOAD
AVERAGE beside every figure it reports, so a reading carries its own conditions and the next
head can tell whether a trend is real. Batch 17's own figure, stated the way the rule
demands: **394.9 ms/row, 1.19× headroom, two runs at load 2.20 / 4.08.** Against batch 16's
362.7 (load unrecorded) that is +8.9% in the row unit and **+2.6% in the flat unit**
(688.6 → 706.6 ns per assertion × vector) — which is the evidence for (1), offered with its
own caveat: batch 16's conditions are unknown, so this is one comparable pair and not a
series.

⇒ This is [[audit-the-premise-of-a-right-decision]] exactly: the decision (report the growth
law in the flat unit) was right, and the premise inside it (411 ms/row, up from 363) was
unmeasured — a number taken under a load the previous number may not have had.

---

## D52 — An undefined value in a REGISTER is answered; an undefined value in MEMORY is refused.

**P1 batch 18.** `shld`/`shrd` mask their count to five bits (six at `.q`) and then, per SDM
Vol. 2A, "if the count is greater than the operand size, the result is undefined" — the
DESTINATION and all six arithmetic flags. A five-bit mask reaches 31 and a 16-bit operand is
16 wide, so the branch exists at `.w` and nowhere else. **It is not a corner: over this
harness's own eighty-two pre-states a CL-driven count lands above 16 in thirty-five of
them** (measured on the oracle before the constructor existed).

With a **register** destination this model answers, from the undefined-bit oracle, and batch
14's machinery carries it unchanged: `declaredUndefGPRs` names the register from the AST and
the SDM rule, `undefinedRegs` observes which registers actually move between the two opposite
oracle runs, and `undefinedLeaked` is their EQUALITY — with teeth in both directions, a leak
one way and a false undefined-claim the other.

With a **memory** destination there is no such channel. `undefinedLeaked` demands that the two
oracle runs agree on every watched byte, and `Main.undefinableFields` — the closed list of
fields the comparator may explain as undefined — is flags and register names only. Its own
comment already named the day a memory window reached the undefined set as the day it must be
widened.

⇒ **This model REFUSES that one combination** (`dshiftMemUndefined`: a memory destination, at
`.w`, with a masked count above 16) rather than widening its strongest gate as a side effect
of one batch. Everything else is answered: every width with a register destination, and `.w`
in memory with a count that is actually defined.

⚠️ **The refusal is why there is no `m,r,cl` vector at `.w`.** The oracle COMPUTES that case,
so a vector there would be a refusal-class disagreement rather than a test — which is the
self-enforcing part: the gap cannot be filled by accident, and it cannot be forgotten either,
because `step_dshift_mem_undefined_refuses` states the refusal as a theorem.

**What the repair would be, when a batch is willing to pay for it:** the memory analogue of
batch 14's two sources. A `declaredUndefMem` reading the AST and the SDM rule, an
`undefinedLeaked` that compares the windows OUTSIDE the declared span and requires the span
itself to MOVE, and a comparator that can explain a byte range rather than a field name. Two
places have to grow, and they are named here so the next head does not have to find them.

---

## D53 — The SDM's `DEST := TEMP` does not happen, and it took eighty cases at one width to see it.

**P1 batch 18.** The SDM's CMPXCHG Operation pseudo-code reads

```
IF accumulator = TEMP  THEN ZF := 1; DEST := SRC;
                       ELSE ZF := 0; accumulator := TEMP; DEST := TEMP;  FI
```

and this model was written to say exactly that. The differential run answered with **eighty
unexplained disagreements, every one of them `cmpxchg_r_l`, every one of them RCX**:
lean `0000000055555555`, oracle `5555555555555555`.

⛔ **`DEST := TEMP` IS NOT THE NO-OP IT READS AS.** In 64-bit mode a 32-bit register write
zero-extends, so writing the destination back with the value it already had clears bits 63:32.
The line is observable at `.d` and at no other width — at `.b` and `.w` the write merges, at
`.q` there is nothing above to clear, and in memory the same bytes go back.

⭐ **TWO INDEPENDENT PUBLIC MODELS SAY OTHERWISE, AND ONE OF THEM IS EVIDENCE ABOUT SILICON.**
ACL2 x86isa's `x86-cmpxchg` (`machine/instructions/exchange.lisp`) takes the else branch as
`(!rgfi-size reg/mem-size *rax* reg/mem rex-byte x86)` and nothing else — no write to the
destination at all. K's `CMPXCHGL-R32-R32`, whose rules were **learned by execution** rather
than read off the manual, is explicit in both halves: on the unequal branch the accumulator
becomes `concatenateMInt(mi(32,0), R2[32:64])` — zero-extended — while the destination becomes
`getParentValue(R2, RSMap)`, the **full 64-bit parent value, unchanged**.

⇒ The SDM's `DEST := TEMP` describes the **memory** write-back, the one that matters under
LOCK and on a write-protected page. Applied literally to a register destination it invents a
zero-extension no processor performs. This model does not model LOCK or page protection, so it
writes nothing on that branch, says so in the coverage table's shapes column, and states it as
a theorem (`step_cmpxchg_unequal_leaves_dest`).

⇒ 🔑 **A SPECIFICATION'S NO-OP IS ONLY A NO-OP AT THE WIDTHS WHERE THE WRITE IS INVISIBLE.**
Three of the four widths agreed. The batch shipped one 32-bit register vector out of seven
`cmpxchg` vectors, and that one vector is the entire evidence.

---

## D54 — …and the manual's "no operation" is not one either. The same defect, the opposite direction, the same batch.

**P1 batch 18.** SHLD/SHRD's Operation section says `IF COUNT = 0 THEN no operation`. This
model, having just been burned by reading the manual too literally, read it literally again —
and wrote nothing at a masked count of zero. The differential answered with **fifty-one more
disagreements**, again all at `.d`, again all the destination's upper half.

⭐ **K CALLS IT AN INTEL BUG IN SO MANY WORDS.** Its `SHLDL-R32-R32` rule for this case is

```
rule execinstr (shldl R, MIdest, MIsrc, MIcount, .Operands) =>
       setParentValue(concatenateMInt(mi(32,0), MIdest), R)   // Intel Bug
     requires eqMInt(MIcount, mi(bitwidthMInt(MIcount), 0))
```

— the destination IS written, zero-extended, at a count of zero. ACL2 x86isa agrees.

⛔⛔ **AND THE CODE BESIDE IT ALREADY KNEW.** `X86/Semantics.lean`'s ordinary `.shift` has had
a count-zero branch that writes the unchanged value back since P0, with a comment saying the
instruction is a read-modify-write. The batch-18 branch was written to DIFFER from it, and the
comment justifying the difference cited the SDM.

⇒ 🔑 **WHEN A NEW FORM DEPARTS FROM THE SHAPE OF THE FORM BESIDE IT, THE BURDEN IS ON THE
DEPARTURE — AND "THE MANUAL SAYS SO" IS THE WEAKEST DISCHARGE OF IT.** The manual was the
source of the error both times in this batch. The two existing models are the ones that had
executed.

⇒ ⭐ **AND BOTH DEFECTS ARE NOW ARMS.** `wrongCmpxchgSdmWriteBack` and
`wrongDshiftZeroCountWritesNothing` are the two rejected models, planted in `selftestArms`, so
a later head who "corrects" either rule back to the manual gets a red selftest in seventy-five
seconds instead of a red differential two hundred vectors later. A finding that is only written
down is a finding that has to be re-found.

---

## D55 — The probe's controls belong inside the probe, not inside the head running it.

**P1 batch 18.** Every batch since D36 has priced its forms by EXECUTING the oracle rather
than reading its catalogue, and the probe has been rebuilt from scratch each time in the
head's scratchpad. Batch 18 extended it: to find which fields x86isa fills from its
undefined generator, run the same cases twice with `create-undef` attached to two different
functions and diff the post-states.

⛔⛔ **The second attachment was `(+ 1000 (nfix x))`, and 1000 is even.** A flag is one bit,
so every one-bit undefined field kept its parity and came back identical. The table read
"zero undefined fields" for all forty forms — which looks exactly like a clean answer, and
would have sent the batch on with the belief that `shld`/`shrd` draw nothing.

⭐ **It was caught by the arm carrying no information about the subject.** `andq %rcx,%rax`
was in the run as a positive control, its AF is undefined by the SDM, and this repository's
own ACL2 driver comment records it as the instruction whose undefined AF first forced the
`defattach` to exist. It read zero too — and that is the only reason the table was not
believed.

⇒ 🔑 **A DIFFERENTIAL PROBE'S PERTURBATION MUST BE ABLE TO MOVE THE NARROWEST FIELD IT
READS.** The failure was not in the construction of the probe, which was sound, but in its
arithmetic — and a sound-looking probe reporting silence is indistinguishable from a real
negative result.

**The repair is that the control is no longer the head's to remember.**
`scripts/oracle_undef_probe.py` takes a list of `id<TAB>asm` forms and:

* assembles them with clang and patches the bytes of the harness's OWN emitted `mov_d`
  cases, so the pre-states it reports on are the differential run's rather than a
  re-implementation that can drift;
* runs ACL2 twice, with `nfix` and with `(+ 1 (nfix x))` — **odd, with this entry's
  paragraph beside the constant**;
* **appends two controls the caller cannot remove**, `andq %rcx,%rax` (AF must be undefined
  in every case) and `movq %rcx,%rax` (nothing may be undefined);
* and **exits 2 printing NOTHING ELSE if either control fails**, because a probe that cannot
  see its own control has measured its own blindness rather than the subject.

Nine seconds for forty forms. Verified in both directions: with the offset set back to 1000
the tool refuses and names the cause.

⚠️ **AND THIS VERIFICATION IS NOT IN CI, FOR THE SAME REASON THE DIFFERENTIAL RUN IS NOT:**
the ACL2 oracle is a 1.7 GB local tree that `scripts/setup_oracle.sh` builds and `/vendor/`
excludes, so nothing in `.github/workflows/ci.yml` can execute it. The control is a RUNTIME
gate inside the tool — it fires on every invocation, on the machine that has the oracle —
and not a CI gate. Said here rather than left for a reader to assume the CI badge covers it.

⇒ This is [[make-the-probe-cheap]] and [[a-probe-must-create-its-condition]] arriving
together. A discipline that has to be re-typed each batch is one that will be re-typed
slightly differently, and the difference will be in the part nobody is attending to.

## D56 — the coverage number is DERIVED, and the literal it replaced was eleven LOW

**P1 batch 19.** Until this batch the sentence "covering N of the 525 forms in
`p1/roster.tsv`" was a hand-maintained literal in `Main.lean`. Its value was a running sum
of eighteen independent `awk` counting rules, one written into a comment at the batch that
added it, and **nothing had ever checked that those rules partition the roster.** Batch 18's
handover said so plainly: it could account for only 32 of the 72 rows it believed remained,
and the other ~40 carried base names the model already implements.

`scripts/claimed_forms.py` computes the claim from two sources that are not derived from
each other, and **their agreement is the gate**:

* **SOURCE S — the vector's own text.** Each differential vector's AT&T `asm` string, the
  one clang assembles and `check_encodings.py` already gates, parsed against the roster's
  own shape vocabulary into candidate `(prefix, base, shape)` rows. It is deliberately
  GENEROUS: `%al` is offered as both `r` and `al`, `$1` as both `imm` and `one`, a symbol
  as `label`, `rel8` and `rel32`.
* **SOURCE E — the roster row's own encoding.** Every roster row is synthesised into a
  canonical instance and assembled by clang, with no reference to any vector.

A vector may claim only a row whose encoding it MATCHES. A mis-parse does not survive:
reading `andb $0x5a,%al` as the generic `r,imm` form offers an encoding with a ModRM byte
against a two-byte accumulator encoding, and the candidate dies. A vector that resolves to
NOTHING is a finding and the tool exits non-zero; it never guesses.

**The derived answer is 469 of the 525 rows, not 453.** The literal was **sixteen low**.

⇒ 🔑 **AND THE DIRECTION IS THE FINDING.** An over-claim reads as a mistake and gets
looked for; an under-claim reads as modesty and does not. Eighteen batches of arithmetic
rested on a number that no gate read in either direction, and the error it accumulated was
the one that nobody was ever going to go looking for.

⛔ **AND THE FIRST VERSION OF THIS TOOL REPEATED THE MISTAKE, BY ONE ROW.** It grouped rows
into aliases only when their skeleton sets were EQUAL *and* their roster `widths` strings
matched, so `stos m` (widths `bw`) never joined `stos -` (widths `blqw`) although `stos m`
at byte width IS the `0xaa` that vector `stos_b` assembles to. It was caught by running a
SECOND claim rule — a row is claimed iff some vector's bytes match one of its own encodings,
with no parse consulted at all — and diffing the two: they agreed on 464 rows and disagreed
on exactly that one. The claim is now the byte rule; the parse is its check, and the gate
requires that every row claimed by bytes share an encoding with a row the parse identified.
⇒ 🔑 **A CONSERVATIVE RULE IS STILL A WRONG RULE, and it is wrong in the direction that does
not announce itself.** Writing a whole batch about an unpoliced under-claim did not stop me
shipping a smaller one in the instrument built to catch it; only the second rule did.

⛔ **AND IT HAPPENED A SECOND TIME, FOR FOUR MORE ROWS.** The alias relation was still
EQUALITY of encoding sets after the first repair. But K's grammar writes some rows as a
RESTRICTION of another — `cmp m,label` is `cmp m,imm` with a symbolic immediate at one
width, `stos m` is `stos -` at `b` and `w` — so the relation is CONTAINMENT, not equality.
Worse, a symbolic-immediate row was being synthesised with an unperturbed `$NEAR`, so its
immediate bytes stayed literal zeros and were read as OPCODE, which is what stopped it
grouping with the row it is a narrowing of. Both were found by a THIRD check — a row's
skeleton may not match a canonical instance of a row it is not related to — which is the
only one of the three that can catch an OVER-masked skeleton, because under-masking makes
the held-out reading stop matching while over-masking is silent: matching MORE never makes
anything fail. 465 → **469**.

⇒ 🔑 **THREE CORRECTIONS, ALL IN THE SAME DIRECTION.** Each was an under-claim, each was
invisible to the gate that existed at the time, and each was found only by adding a check
that reached the answer by a different route. The published number is worth exactly as much
as the number of INDEPENDENT routes that agree on it — which is why the tool now carries
three and reports the one place they cannot separate (`0x90` is both `nop` and
`xchg eax,eax`; the SDM defines that byte as NOP precisely so it does not zero-extend RAX,
and no byte-level rule can tell them apart). That collision is REPORTED on every run and
becomes a FINDING only if a row is ever claimed solely through it. `--check` now gates all six published
numbers, and `--selftest` drives the comparison red with an over-claim AND with an
under-claim, because a gate that only fires on over-claims would have passed this repository
for eighteen batches.

## D57 — 143 of the 525 roster rows are alias SPELLINGS, which is why base-name counting could never partition it

Rows whose canonical instances assemble to the same FORM SKELETON are the same machine
instruction under different spellings: `jz` and `je`, `setz` and `sete`, `cmovz` and
`cmove`, `sal` and `shl`, `loopz` and `loope`, `xchg ax,r` and `xchg r,ax`, `movs -` and
`movs m,m`. clang says so, not a hand-written synonym list.

**This is the residue batch 18 could not close.** 128 roster rows carry a base name that no
vector even spells, and 108 of them are pure synonyms of forms the model tests. The model
decodes BYTES, not spellings, so a vector spelled `je` exercises the `jz` row exactly as
much — but a rule of the form `$4 ~ /^(je)$/` claims three rows and leaves three identical
ones behind, and no amount of care with the pattern repairs a rule that counts spellings
where the machine counts encodings.

⇒ The document now publishes **both** denominators: 469 of 525 rows, which are 322 of the
374 distinct machine forms those rows describe. Of the 469, **346 are spelled by a vector
and 123 are the same encoding under another spelling** — printed separately, because a
claim that rests on an alias should be visible as one.

⛔ **AND TWO ROWS DESCRIBE NO ENCODING AT ALL.** `jecxz rel32` and `jrcxz rel32` are in the
roster because K's grammar generates them; the assembler refuses both — *"value of 200 is
too large for field of 1 byte"* — because those instructions have only an 8-bit
displacement. They are not uncovered work. They are denominator that cannot be earned, and
the tool names them on every run rather than letting them sit in the 56 rows that remain.

## D58 — the perturbation that reaches every bit, and the control that shared its blind spot

The form skeleton is derived by assembling each row under perturbations that move only
operand VALUES — a different register bank, a complementary immediate, a moved branch
target — and masking every bit that changes. Three defects were found building it, and all
three are the same defect at different scales.

1. **Two register banks cannot span a three-bit field.** The first version perturbed
   registers between two banks; whichever bits happened to agree in both were frozen into
   the skeleton as though they were opcode. `and %ecx,%eax` then failed to match the
   `and r,r` row it is an instance of. Four banks now cover every bit of every operand
   position, and the table says why.
2. **A "complement" that was not one.** The displacement pair was `0x12345678` /
   `0x6dcba987` — every bit but the TOP one — so bit 31 of every displacement was read as
   opcode, and the one vector with a NEGATIVE displacement (`cmpq $0x12345678,
   -0x3fe00b(%rip)`) did not match its own row. ⚠️ **The held-out control did not catch it,
   because the held-out value was positive too and agreed with the perturbations on exactly
   the bit they missed.** The held-out values are negative for that reason now.
3. **A silently lost label.** `objdump` prints one symbol per address, so every instance
   label that shared an address with the preceding one was hidden — **4713 of 4714
   encodings vanished and were reported as "rows with no assemblable form"**, which is a
   sentence that reads like an answer. A `nop` now separates them, and `assemble` counts
   its labels and refuses rather than returning a short table.

⇒ 🔑 [[a-perturbation-must-reach-the-field]] at BIT granularity: it is not enough that a
perturbation move the field, it must move **every bit** of it, and a control drawn from the
same half of the space as the perturbation is silent about the other half. Each of the three
was found by a vector that failed to match a row it plainly belongs to — i.e. by the tool
REFUSING rather than guessing, which is the only reason they were found at all.

⭐ One more control belongs to the same family. clang accepts an UNSUFFIXED spelling and
picks a default width for it, so a reading meant to be `btw` came back as `btl`, and the
`w` and `q` readings of four `bt` rows held the `l` encoding while every `w`/`q` vector of
those rows went unresolved with nothing to say why. **A row whose roster widths are distinct
must have distinct encodings at them**; where it does not, the readings are voided and named.

## D59 — three ORDER claims that nineteen batches of green said nothing about, and the one that cannot be tested

`step` has carried three sentences about ORDER since P0:

* `.push` reads its source **before** RSP moves — "so `push rsp` pushes the OLD RSP";
* `.pop` computes its destination's effective address **after** RSP moves — "a `pop rsp`
  therefore ends with the LOADED value";
* `.call .indirect` reads its target **before** the return address is pushed.

Every one is a real architectural commitment, each cites the SDM, and **not one of them was
tested by anything.** Every push/pop/call vector in the table named an operand that does not
move with RSP — `push_r` pushes RAX, `pop_r` pops into RCX, and batch 20's own `push_m_q` and
`pop_m_q` address memory through RBX — and against all of them a model with any of the three
orders reversed is **bit-identical**.

⇒ 🔑 **A CLAIM THE VECTORS CANNOT DISTINGUISH IS NOT TESTED BY THEM**, however many of them
there are. This is D14's rule ("a form whose source operand never moves is one test reported as
seventy-four") applied not to a VALUE but to a SEQUENCE, and it is harder to see: D14's defect
shows up as an operand that is constant, which a reader can notice, while this one shows up as
nothing at all.

⛔ **It was found by asking what a GREEN run did not contain.** The 71 shape vectors of this
batch passed the differential on the first run and were predicted to — no `step` case changed —
and it is precisely that predictability which made "what can these 5822 new cases still not
see?" the only question worth asking of them.

**Two are now tested**, by four vectors (`push_rsp`, `pop_rsp`, `push_m_rsp`, `pop_m_rsp`)
paired with three arms, with the pairing checked by deleting the vectors and re-running the
arms rather than asserted. Both pop arms exist separately because one is about an ADDRESS
(showing in the stack window) and the other about WHICH WRITE WINS (showing in `rsp`); a merged
arm would have been caught by either vector and would not have said which claim was tested.

⛔ **The third cannot be tested through the differential.** `callq *(%rsp)` is the only
instance that makes it observable, and **x86isa refuses it in 80 of the 82 pre-states**,
executing only in the two frame states. Agreement where both models refuse is agreement about
nothing, so the vector is not in the table and the claim is pinned by an anchor against this
model alone — a weaker instrument, named as such here so that a reader does not count three
tested orders where there are two.

**Reversal cost:** none for the two that landed. The third closes when a pre-state family puts
RSP somewhere x86isa will execute an indirect call through.

## D60 — the claim instrument cannot see %rsp, and the exemption is gated in both directions

`scripts/claimed_forms.py` derives each roster row's form skeleton by assembling canonical
instances under register perturbations. `MBASE` deliberately excludes register index 4 (%rsp)
and 5 (%rbp): either changes an encoding's **LENGTH** — %rsp forces a SIB byte, %rbp a
displacement — and a skeleton is a fixed-length byte pattern, so an instance built on one of
them cannot be described by it. **That exclusion is correct and load-bearing.**

⚠️ **Its consequence had never been paid, because until batch 20 no vector used either base.**
`popq (%rsp)` is the only instance that can make D59's second claim observable, and it resolves
to NO roster row.

The two vectors claim nothing — their rows are claimed by the RBX-based siblings — and that is
**tested by deletion, not asserted**: re-deriving with the two removed (via the tool's own
`X86LEAN_ASM`/`X86LEAN_LEN` file mode, so no rebuild is needed) moves the vector count 775 → 773
and leaves **every published number identical** — 497 claimed rows, 373 spelled by a vector. The
exemption therefore suppresses a parse failure and not a claim. They are exempted **by id**, and
the exemption is gated in BOTH directions: an exempt id that starts
RESOLVING is a finding (the skeleton grew and the list is stale), and an unresolved vector not
on the list is a finding exactly as before. `--selftest` carries an arm for each direction,
because a hand-kept exclusion list whose staleness nothing checks is the failure mode of
[[an-unrecorded-rule-cannot-be-audited]].

⛔ **The skeleton derivation itself was NOT touched.** Extending it to cover SIB-base instances
is the "proper" fix and it is deliberately declined here: this batch already changes the
kernel-cost gate, and two instrument changes in one batch is how two defects come to cancel
(D-note, batch 19). The cost of the declined fix is two vectors that claim nothing and say so.

**Reversal cost:** low — one additional encoding per row, plus a re-derivation of all six
published numbers with the three independent routes re-diffed.

## D61 — a DECLARED unavailable-list, wrong in the direction that invents work

`claimed_forms.py --remaining` splits the residue into rows that cannot be encoded (derived),
rows the oracle cannot execute (**DECLARED, batch 18**), and available work. It named 36 rows
available. **35 were.**

⛔ **`movnti m,r` is not implemented by ACL2 x86isa** — 82/82 refused at every real pre-state.
Batch 18 measured nine BMI forms as unavailable and wrote them down; `movnti` was never
measured, and an unmeasured row falls into "available" by default.

⇒ 🔑 **A DECLARED list inherits the direction of its default.** This one defaults to
*available*, so every gap in it INVENTS work — the flattering direction, because a batch that
sets out to do work that turns out to be impossible discovers it early and cheaply, and
therefore nobody builds a gate. The mirror error (a row wrongly declared unavailable) would
have silently shrunk the roster for ever, and is the one D36 was written about.

**Two independent routes agree**, which is why this is recorded as a fact: the probe carried
`movl %ecx,(%rbx)` — identical shape, address and pre-states — and it executed 82/82 in the
same run, so the refusal is the OPCODE; and x86isa's own SSE2-cacheability section doc reads
*"The only implemented instruction here is LFENCE."* ⚠️ D36 says the catalogue is wrong in both
directions and must never be the only route; here it happens to be right, and it is the second
route rather than the first.

**Reversal cost:** none. The line moves from declared to measured the day a probe runs it.

## D62 — the repair that was blocked for three batches, unblocked, designed, and then REFUSED BY ITS OWN SECOND SOURCE

`Tests.Coverage`'s kernel ceiling has been raised twice (batches 3, 14) and had its unit changed
once. Batch 14 made it PER ROW precisely so it would stop needing raising (D38), since *a gate
relaxed on schedule is not a gate*. Batch 17 observed that the row is not the unit either, added
a line reporting **µs per (assertion × vector)** as **REPORTED, NOT GATED**, and recorded why the
sound repair was blocked:

> *"A vector count could be pinned the same way; an ASSERTION count cannot be, because it is a
> property of the file's text and not of any term in it."*

**Every sentence of that is true**, and it was carried forward unexamined for three batches.

### 1. The block was one sentence too wide
It blocks gating the module's **TOTAL** in an (assertions × vectors) unit. It says nothing about
gating **each DECLARATION** — and a per-declaration gate needs no assertion count at all, because
*dividing by the number of declarations is the only thing an assertion count was ever for*.

⇒ 🔑 **A BLOCKED REPAIR BLOCKS A DESIGN, NOT A GOAL.** The diagnosis was CORRECT, which is what
made it expensive: a wrong diagnosis gets tested by the next head, and a right one gets quoted.
[[feedback-inherited-diagnosis-is-a-hypothesis]] at its sharpest — the hypothesis worth
re-reading is not the shaky one, it is the one nobody re-reads because it was right.

**And the mechanism was there the whole time.** `lean --json -D profiler.threshold=N` emits one
`type checking took X` message per declaration carrying `fileName` and `pos.line`. ⚠️ Plain
non-JSON output carries the same timings with NO position, so a first look says attribution is
impossible; `--json` is the entire difference.

### 2. ⛔ And then the measurement refused the design
The gate was to be `no declaration may cost more than K × vectorCount`. Before installing it, the
density was measured at **two vector counts** — the same code at 700 and at 775 vectors, minutes
apart — because [[feedback-widening-a-gate-needs-a-second-source]] forbids deriving a gate's
allowance from the thing it checks. **The two points disagree, and the disagreement is
structural, not noise:**

| declaration | 700v | 775v | ratio |
|---|---|---|---|
| `mem_dest_rewrite_changed_exactly_the_three_operand_rows` | 10 100 | 10 600 | **×1.050** |
| `mem_dest_claims_are_backed` | 9 010 | 9 700 | **×1.077** |
| `vectors_cover_the_roster` | 626 | 1 030 | **×1.645** |
| `every_row_has_a_vector` | 914 | 1 210 | ×1.324 |
| `every_vector_has_a_row` | 931 | 1 230 | ×1.321 |
| *(input)* | | | *vectors ×1.107* |

* **The two declarations that dominate the module — 53% of its kernel time — are barely
  vector-driven**, and most of even that growth is the SHAPES prose this batch lengthened. A
  per-vector denominator would make them look CHEAPER every batch that adds vectors: **the gate
  would go slack exactly where the cost is**, in the direction nobody polices
  ([[feedback-under-claims-are-unpoliced]]).
* **Three declarations grow FASTER than their input.** ⭐ And the reason is in the SOURCE, not in
  the timings, which is the second route that makes this a fact rather than a reading:
  `vectorMnemonics` is `(vectors.map Vec.mnemonic).eraseDups` and **`List.eraseDups` is
  QUADRATIC**; the two theorems above then run `contains` over its result once per row.

⇒ 🔑 **THE "GROWTH LAW" REPORTED SINCE BATCH 17 IS ITSELF WRONG.** "Linear in
(assertions × vectors)" was inferred from whole-module TOTALS, and **a total cannot tell a linear
module from a super-linear one** — the flat-looking unit was two opposite errors averaging out
across a whole file. Three batches of readings in that unit were compared as though they meant
something.

### 3. What landed, and what did not
**NOT installed:** the per-declaration-per-vector gate. Its own second source refused it, and the
bus post that proposed it said in advance that this was the outcome if the two points disagreed.
**Installed:** the per-declaration measurement that refused it — printed with names and line
numbers on every run — and a corrected growth-law line that no longer asserts a linearity the
module does not have. `vectorCount` is now kernel-pinned beside `rosterSize`, so the reported
density has a proven denominator even though nothing gates on it yet.

**The per-row ceiling is RAISED, 470 → 744, and demoted in writing to a coarse tripwire.** Batch
18 predicted batch 20 would exceed it. It does not: the module measures **465.1 ms/row against
470**. ⛔ **And that pass is the reason for the raise, not an argument against it** — 1.05% of
headroom is inside this module's own measured load sensitivity, so the green goes either way on
the next machine. ⇒ 🔑 **A GATE THAT PASSES BY LESS THAN ITS NOISE HAS NOT PASSED.** The margin
is `measured × 1.6`, the convention batch 14 REGISTERED this line with (293 × 1.6 = 470), so the
allowance comes from the line's own history rather than from the thing it checks.

⚠️ The batch-18 prediction was made in the row unit, which this entry has just shown is not a
unit. That it was nearly right is not evidence that it was right for a reason.

⛔⛔ **AND THIS PARAGRAPH WAS FALSE WHEN IT WAS FIRST COMMITTED.** It was drafted while the
measurement was still running, said *"the per-row ceiling STANDS ... with headroom intact"*, and
was appended to this file BEFORE the outcome it describes existed. It was caught by re-reading,
not by a gate — nothing gates the prose in this file. ⇒ 🔑 **A DECISION WRITTEN BEFORE ITS OWN
OUTCOME IS A DRAFT, AND FILING IT EARLY IS WHAT MAKES IT READ AS A RECORD** — the same defect as
[[feedback-ungated-prose-overclaims]], committed by the head writing the entry that names it.

**Reversal cost:** the next design has the table it needs. Whatever it gates on must handle a
module with at least one quadratic declaration and a cost concentration in two prose-driven ones —
which is why the honest next step is probably to make `vectorMnemonics` linear rather than to
find a denominator that flatters it.

## D63 — the kernel's reduction cache spans a declaration and not two, and that was where the module's money was (P1 batch 21)

**Decision.** State each group of related coverage claims in ONE `decide` and DERIVE the original
theorems from it, their statements byte-for-byte unchanged. `Tests.Coverage` goes **37 900 →
22 400 ms** (−42%). Two groups: `memDestSweep` (the three mem-dest theorems) and `vectorCoverage`
(the three vector-coverage theorems).

### 1. D62's "honest fix" was priced first, and it was the smaller half
D62 closed by naming `vectorMnemonics`'s quadratic `eraseDups` as the honest next step. Priced
before it was taken, per-declaration, at load 3.0–3.2:

| probe | ms | what it isolates |
|---|---|---|
| `vectorMnemonics.length = 83` | **935** | dedup over the 775 |
| `(vectors.map Vec.mnemonic).any (· == "zzz") = false` | **69** | the same 775 projections, one compare each, NO dedup |
| `… .any (·.isEmpty) = false` | **76** | the same projections, no compare at all |

⭐ So the dedup is REAL — 93% of that list's cost — and D62's diagnosis is **confirmed by a
control at the same shape**, not merely believed. ⛔ **And it is worth 2.8 s of a 37 900 ms
module: 7%.** It was paid three times because three theorems mention it, which is the fact that
matters and is not the fact D62 recorded.

⛔ **Replacing `eraseDups` with something cheaper was priced and REFUSED.** Both dedup-free
spellings cost the same ~30 000 string comparisons the dedup does (83 rows × first-occurrence-in-775,
or 775 vectors × position-in-83), and a hand-written 83-element literal pinned by a theorem
would pay it once at the price of a list edited by hand every batch — a chore, not a gate.

### 2. What the measurement found instead
| declaration | apart | merged |
|---|---|---|
| `mem_dest_rewrite_changed_exactly_the_three_operand_rows` | 10 600 | |
| `mem_dest_claims_are_backed` | 9 720 | |
| `mem_dest_vectors_are_claimed` | 5 250 | |
| **total** | **25 570** | **11 200** |

⇒ 🔑 **THE KERNEL'S REDUCTION CACHE SPANS A DECLARATION AND NOT TWO.** A `def` naming a closed
constant already collapses the work *inside* one theorem — measured separately, the 39
`hasMemDestVector` calls in `mem_dest_claims_are_backed` cost **70 ms** of its 9 720, so
`memDestMnemonics` was reduced once there — but every new theorem mentioning it starts cold. The
note above `memDestMnemonics` claims the collapse is "asked once instead of per row"; that was
true, and it was **half** the sharing available. ⇒ 🔑 **A COST MODEL THAT ONLY KNOWS ABOUT THE
ARTIFACT CANNOT SEE THE COST OF ASKING TWICE.**

### 3. Why this cannot weaken a gate, by construction
Merging claims is exactly the move that goes silent: a conjunction is green if the kernel never
reaches a conjunct, and nothing in a green build says which of six was exercised. Two answers,
both structural:

- **The six original theorems still exist with their original TYPES**, proved from the merged one.
  A conjunction weaker than any of them would not let the derivation typecheck. Nothing here is a
  restatement — the statements are the same bytes.
- **`scripts/sharing_redprobe.sh`** plants a defect in each of the six conjuncts **alone** and
  requires the kernel to prove the conjunct `false`. ⚠️ The arms prove `= false` rather than merely
  failing to compile: an erroring `decide` could be erroring for any reason, while a proof of
  `false` is the kernel positively agreeing the defect is visible *at that conjunct*. A **positive
  control** — the unplanted shape, `= true` — runs in the same file, because six `false`s are also
  what a probe that has stopped seeing its subject would print. **7 arms, 28 s, wired into CI.**
- ⛔ **And the probe RESTATES the conjuncts, which is a duplicate born in agreement**: edit
  `memDestSweep` and the arms go on passing while testing a shape that is no longer shipped —
  green, and about nothing. So each arm's SUBJECT must OCCUR in `Tests/Coverage.lean` and a
  missing anchor **REFUSES (rc 2)** instead of passing. Occurrence, not equality: the shipped text
  carries line breaks and comments the probe cannot reproduce, and a gate that cried wolf on
  reformatting gets switched off. **Driven red** — one conjunct spelled `== (rosterSize)` instead
  of `== rosterSize` and the probe refused — and the anchor list carries its own two-way self-test,
  because a list that silently matched nothing would be the defect it exists to prevent.

⚠️ `claimsMemDestLoose` loses `private` for this, and that is a gate's requirement rather than a
convenience: the first conjunct cannot be stated without it, and the alternative was a copy of the
rule inside the probe — precisely the byte-identical duplicate batch 14 deleted.

### 4. What is NOT done
The per-row ceiling is **not lowered in this entry** — the module's row count changes in the same
batch (`cmpxchg8b`), and a ceiling set against a denominator that is about to move is a number
measured under one condition and applied under another ([[feedback-a-measurement-without-its-conditions]]).
It is re-registered at the end of the batch, from the post-`cmpxchg8b` reading, at the `× 1.6`
convention batch 14 registered this line with.

### 5. ⛔ AND THE TECHNIQUE IS NOT GENERAL — MEASURED, BEFORE IT COULD BE OVER-APPLIED
The obvious next move is "merge every group that shares a subject", and `Tests.Coverage` has an
inviting one: **nineteen theorems each reduce `preStates 1 8`**, the 86-state pre-state list —
more sharing, by count, than the six this entry merged. Measured, four of them apart and then in
one declaration, back to back so contention cancels:

    four `preStates` theorems APART    786 ms
    the same four MERGED               733 ms      — 7%

⇒ 🔑 **SHARING PAYS WHERE THE SHARED SUBJECT'S REDUCTION IS EXPENSIVE, NOT WHERE THE SUBJECT IS
MERELY SHARED.** `vectorMnemonics` is a dedup (935 ms) and `claimsMemDest` is a character sweep of
the whole table (9 400 ms); `preStates 1 8` is 86 records built from simple constructors, and
almost all of those theorems' cost is the PER-STATE PREDICATE, which no merge can share because
each predicate is different. The count of call sites predicts nothing on its own.

⚠️ This is recorded because the reading of D63 that generalises it — *merge anything shared* —
would produce a file of conjunctions, each needing its own red probe, for 7% at a time. The two
merges here were worth it because their subjects cost seconds apiece.

**Reversal cost:** small and local. Deleting the two merged declarations and restoring `by decide`
on the six restores the previous file exactly; the red probe is the only thing that would have to
be deleted with them.

## D64 — CMPXCHG8B: the last claimable row, and a branch reached by one accident (P1 batch 21)

**Decision.** Model `cmpxchg8b m64` as one constructor with **no `Size` field** and a
memory-only destination, and add four purpose-built pre-states so its two branches are both
exercised deliberately. Roster 497 → 498 of 525; **AVAILABLE WORK 0**.

### 1. What was measured BEFORE the constructor existed
`cmpxchg8b (%rbx)` (`0f c7 0b`, clang) run on the oracle over the 82 inherited pre-states, with
`cmpxchg %ecx,(%rbx)` as a control in the same run:

| | executes | equal branch (ZF=1) | flags that EVER move |
|---|---|---|---|
| `cmpxchg8b (%rbx)` | 82/82 | **1** | `zf` |
| `cmpxchg %ecx,(%rbx)` (control) | 82/82 | 22 | `cf pf af zf sf of` |

⭐ **THE FLAG RULE IS THE OPPOSITE OF ITS NEIGHBOUR'S, AND THAT IS WHY IT WAS MEASURED.**
`cmpxchg`'s flags are the whole comparison (`Flags.sub`); `cmpxchg8b` moves ZF alone. Two forms
in one family with opposite rules is where a reader assumes. The control is what makes the first
column mean something: a form that moved no flag at all would look identical if the harness had
stopped watching flags.

⚠️ `Flags.sub` is **not** the rule here even though the two agree on ZF — ZF is set by an
EQUALITY, and the subtraction would be a false description of what the instruction computes.

### 2. The branch that one accidental state reached
`mkPre` puts `~a` in RDX and `c` in the eight bytes at RBX, so `EDX:EAX` is `(~a)[31:0]:a[31:0]`
and the comparison succeeds only where `c = a` **and** `a`'s high half is the complement of its
low half. That is `a = 0x00000000ffffffff` — one entry of `adversarial`, and there by accident.
⇒ **A BRANCH REACHED BY ONE ACCIDENTAL STATE IS A BRANCH NOBODY IS MAINTAINING** —
`carryBoundary`'s finding (batch 2) in a control-flow shape: reorder `adversarial` and the equal
branch leaves the run with every gate still green. `cmpxchg8bStates` makes it deliberate: the
equal branch is now reached in 3 of 86 cases, 2 of them on purpose.

### 3. ⛔ AND A GATE REFUSED THE FIRST DESIGN, WHICH WAS THE CHEAPER ONE ARRIVING
The states were first built by writing the wanted value into the eight bytes at RBX.
`memory_operand_mirrors_rcx` refused them: batch 3 made `[0x2000] = RCX` an invariant of EVERY
pre-state, and that invariant is the only reason a memory operand sweeps instead of being a
constant wearing its shape (D14). Setting **EDX:EAX** instead reaches the same four comparisons
and weakens nothing — no exemption, no widened window, no gate to re-probe.
⇒ 🔑 **A GATE THAT REFUSES A NEW PRE-STATE IS USUALLY NAMING A CHEAPER WAY TO BUILD IT.** The
reflex is to exempt; the exemption would have cost a both-ways probe and bought nothing.

### 4. ⛔⛔ AND THE COMMENT JUSTIFYING THE OTHER TWO STATES WAS FALSE
The two unequal states differ from the accumulator pair in ONE half, for the defect of comparing
one half. The comment shipped with them said *"no inherited pre-state is such a state."*
**Counted rather than believed: 21 of the 82 inherited states already agree in the low half and
differ in the high half, and 11 do the reverse** — because `mkPre`'s diagonal has `RCX = RAX`,
so the low halves match there by construction. Both half-width arms are caught with or without
these states.
⇒ 🔑 **A STATE ADDED FOR A DEFECT IS NOT EVIDENCE THAT THE DEFECT NEEDED IT.** The plausible
sentence about a new pre-state is the one claiming it was necessary, and it costs one count to
check. The states are kept for `carryBoundary`'s reason — they are the only DELIBERATE ones —
and the comment now says that instead.

### 5. The arms, and a gap named rather than discovered
Five arms, all caught: always-stores (79 disagreements — the unequal branch is reached),
never-stores (**3** — the equal branch is reached, and 2 of the 3 are this batch's states),
EAX-only comparison (22 in `zf`), merge-instead-of-zero-extend (71 in `rdx`, D53's defect in this
form), stored halves swapped (3).

⛔ **NAMED GAP: EBX is 0x2000 in every pre-state this harness has**, since RBX is the fixed
data-window pointer, so the low half of the value stored on the equal branch is a CONSTANT.
Swapping the halves is still caught (ECX sweeps) and so is storing any other register; what no
state here can catch is a model that stores the literal 0x2000 in that half by some other route.
Making EBX sweep means moving RBX, which moves every memory vector's address at once — a second
instrument change in the same batch, which is how two defects cancel.

**Reversal cost:** one `step` case, one constructor, one coverage row, one vector, four
pre-states, five arms.

## D65 — the unavailable list stops being DECLARED (P1 batch 21)

**Decision.** `scripts/oracle_availability.py` MEASURES which mnemonics the oracle refuses, by
executing one form per mnemonic over the real pre-states with two positive controls, and gates
the answer **in both directions**. `claimed_forms.py` imports that table instead of carrying its
own; the six rows declined by decision are declared beside the DECISION that declined them.

### 1. Why: D61 was recorded in two prose files and in zero gates
D61 measured `movnti` UNAVAILABLE at batch 20 — 82/82 refused, with an identical-shape control
executing 82/82 in the same run — and wrote it into `docs/DECISIONS.md` and `docs/COVERAGE.md`.
The hard-coded set in `claimed_forms.py` was never touched, so `--remaining` went on printing
`movnti` under **AVAILABLE WORK** for a whole batch while two documents said the list had been
corrected. The next head is invited by that line to start work that cannot be done.
⇒ 🔑 **A CITATION IS AN UNGATED CLAIM**, and D61's own closing line — *"the line moves from
declared to measured the day a probe runs it"* — is the repair nobody ran.

### 2. Both directions, because they are not symmetric
A mnemonic declared unavailable that starts executing shrinks the roster's residue silently
(D36's error). A mnemonic declared available that refuses INVENTS work — and that direction is
unpoliced precisely because it is discovered cheaply by whoever tries. The gate reports both, and
`--selftest` drives three red arms: every "refuses" form flipped must be reported, every
"executes" form flipped must be reported, and an EMPTY run must be reported by all twelve forms
rather than read as agreement. **~6 seconds**, which is the point — a discipline expensive to
exercise gets exercised less.

### 3. The residue, partitioned and checked
    27 = 2 no encoding (DERIVED) + 19 oracle-unavailable (MEASURED) + 6 declined (D23, D25)
       + 0 AVAILABLE WORK
The four buckets are now required to sum to the residue, and a DECLINED entry that no longer
names an unclaimed row is reported as stale. ⚠️ The batch-20 handover gave this partition as
`27 = 2 + 19 + 6 + 1`, which sums to 28, describes a state where `movnti` had already been
declared (it had not), and disagreed with its own row count. Three of its four terms were wrong.

### 4. And the six DECLINED rows are recorded as EXECUTES, on purpose
A bucket called "declined by a recorded decision" is only honest if the decline is a DECISION and
not an oracle limitation wearing a decision's name. Measured in the same run: `btl/btsl/btrl/btcl
%ecx,(%rbx)` and `xchgl %ecx,(%rbx)` all execute **86/86**. So oracle support is not what stops
them, and a later reader cannot quietly re-derive "declined" as "unsupported".

⛔ **AND THAT IS NOT AN ARGUMENT TO UN-DECLINE EITHER OF THEM.** D23's decline is about modelling
honesty — `step`'s `.bit` case takes the offset modulo the operand width, which is wrong where the
offset is signed and the effective address moves with it — and closing it is work in the
PRE-STATES, not in `step`: with RBX at 0x2000 and ECX sweeping the adversarial list the effective
address leaves the watched window, and an unobserved region reports agreement. D25's is about
VOCABULARY: `xchg` at memory asserts LOCK, and a single-threaded model can reproduce every
observation this harness makes while being wrong about the only thing that distinguishes the
instruction.
⇒ 🔑 **MEASURING THAT A CONSTRAINT IS NOT BINDING DOES NOT REMOVE THE OTHER CONSTRAINTS** — and the
measurement makes both rows look equally available when only one is honest work.

⚠️ The first run of these five rows produced **zero records for all of them**, because the
mnemonic key carries a space and the record id is read by splitting on whitespace. The gate
reported *"produced 0 records, expected 86 — a missing reading is not a refusal"* rather than
counting the silence. That branch was written on the general principle; this is the first time it
fired, and it fired on its author.

**Reversal cost:** none — deleting the script restores a hand-maintained set, which is what this
replaces.

## D66 — the demand-side census, and the kernel number that was 58% padding (desk ES, P1 seal)

**Decision.** `scripts/demand_census.py` measures the other side of coverage: not how much of a
roster the model implements, but **what fraction of the instructions in real x86-64 binaries the
model already covers**, with the mnemonics it does not cover ranked by how often they occur — the
P2 roster candidates, by demand.

    cc1        5,379,923 instructions   97.4% covered
    coreutils    873,099                95.0%
    glibc        603,554                81.1%
    vmlinux      2,781,898              98.0%   ← own column, never pooled

### 1. ⛔⛔ THE KERNEL COLUMN FIRST READ 40.7%, AND 58% OF IT WAS PADDING
`int3` was the top "instruction" in vmlinux: **3,881,051 occurrences, 58.19% of the column.**
0xCC is the inter-function padding byte, and a disassembler reports a run of them as instructions
because that is what the bytes decode to.
⇒ 🔑 **A DISASSEMBLER HAS NO CONCEPT OF "NOT CODE"**, so a static census must supply one, and the
one it supplies has to be stated. A run of two or more `int3` is PADDING and excluded; a lone
`int3` is a real breakpoint and is counted. **40.7% → 98.0%.**

⚠️ The first number was not merely wrong, it was wrong in the direction that would have driven a
decision: it said the kernel was the *least* covered corpus, when it is the *most*. A
system-mode fork argued from 40.7% would have been argued from filler.

### 2. ⭐ AND THAT INVERTS THE FORK QUESTION THIS CENSUS WAS COMMISSIONED TO INFORM
The kernel's privileged slice — `sti`, `cli`, `in`/`out`, `wrmsr`, `clac`/`stac`, `rdtsc` — is
about **1,900 instructions in 2.78 million: 0.07%.** What the kernel actually needs from this
model is not system mode at all:

| what the kernel uses that the model lacks | occurrences | share |
|---|---|---|
| ordinary instructions at a `%gs:`-relative address (per-CPU variables) | 33,463 | 1.20% |
| the `lock` prefix | 9,029 | 0.32% |
| `movabsq` (the `mov $imm64, r64` form) | 6,281 | 0.23% |
| **everything privileged, together** | **~1,900** | **0.07%** |

⇒ **A segment base in `Ea`, a LOCK vocabulary, and one more `mov` form buy more kernel coverage
than a system-mode fork would**, and each is a smaller change. The fork is the Captain's to rule;
this is the evidence, and it points the other way from the first reading.

### 3. Three more over-claims, each measured rather than footnoted
A mnemonic-level census inflates itself, and the inflation was measured before it was excluded:

- **a vector register under an integer mnemonic** — `movq %xmm0, %rax` is spelled `movq`:
  0.636% of cc1, 0.121% of glibc;
- **an `%fs:`/`%gs:` prefix** — `mov %fs:0x28, %rax` is the stack-protector load in most compiled
  functions: 0.244% of cc1, 2.655% of glibc, 0.802% of the kernel;
- **`lock`, which objdump prints on its own line** — so a naive counter scored the prefix as an
  instruction *and* scored the instruction it prefixes as covered. 9,029 in the kernel, and the
  model has no LOCK, which is exactly why D25 declines `xchg` at memory.

⛔ **AND THE SEGMENT RULE WAS FIRST TOO BROAD, WHICH IS AN UNDER-CLAIM.** It matched all six
segment registers, and the output said so: `nop (segment operand)` ranked 2nd among "uncovered"
mnemonics in three of four columns. The canonical multi-byte NOP is spelled `nopw %cs:0x0(…)` and
a string op's destination is architecturally `%es:(%rdi)` — notation, not an override. In long
mode only FS and GS are overrides.
⇒ 🔑 **AN OVER-BROAD EXCLUSION IS AN UNDER-CLAIM, AND AN UNDER-CLAIM IN A COVERAGE NUMBER LOOKS
LIKE RIGOUR.** It was found by READING the ranked list, which is the only reason the tool prints
one ([[feedback-under-claims-are-unpoliced]]).

### 4. What the number is NOT
It is a STATIC count — what a compiler emits, not what is hot — and an **UPPER BOUND on
form-level coverage**: the three exclusions above move it toward the truth, not to it, because an
addressing mode or operand shape the model lacks is still counted as covered when the mnemonic
matches. That residual error is in the flattering direction and is not measured. Said in the
generated document, not only here.

**45 selftest arms**, including the `movsbl`→`movsx`-not-`movs` trap in both directions and every
line-level rule that moved the number.

**Reversal cost:** none; the tool reads binaries it downloads and writes one generated document.

## D67 — the README's Lean example did not compile, and now it is compiled by a gate (P1 seal)

**Decision.** `scripts/check_readme_lean.py` extracts every ```` ```lean ```` block from
`README.md` and compiles it, in CI, with an 8-arm selftest.

### 1. What shipped
The example landed at the seal opened `open X86` with **no `import X86`**. A reader pasting it
got four errors, the first `unknown namespace X86`. The rest of the block was correct — the
theorem name, its arguments, the `Live` hypothesis were all checked against the source — and the
line that makes it *runnable* was the one nobody checked, because it is the line you do not think
of as content.

⚠️ **The head that wrote it had, in the same commit, corrected three errors of exactly this class
in the draft it replaced**: a CLI mode the binary does not have, a theorem name that does not
exist, and a residual list naming a row that is not in the residue.
⇒ 🔑 **CORRECTING A CLASS OF ERROR IN SOMEBODY ELSE'S DRAFT DOES NOT INOCULATE YOUR OWN.** The
only thing that would have caught it is the thing that catches it now: running it.

### 2. The rule is by INTENT, not by outcome
The README carries **shapes** on purpose — `def step (i : Instr) (s : Cpu) : Cpu` with no body,
`step i s = { s with … }` with a literal ellipsis. They are not meant to be pasted, and a gate
that compiled them would cry wolf on prose and get switched off.

⛔ **But "skip what does not compile" would be a gate that skips its own subject** — it would have
skipped the broken block. So a block that declares an `example`/`theorem`/`#eval` is offered as
runnable, and one of those **without an import is a FINDING, not a fragment**. Three classifier
arms drive exactly that separation, including the case that shipped.

### 3. ⛔ AND THE GATE'S OWN SELFTEST CAUGHT THE GATE
The `sorry` check looked for `declaration uses 'sorry'` with straight quotes. Lean emits
`` declaration uses `sorry` `` with **backticks**, so it never fired and a `sorry`-closed block
would have passed. The arm that plants one is the only reason this is known.
⇒ 🔑 **A PATTERN IS A GUESS ABOUT WORDING UNTIL SOMETHING DRIVES IT** — the same shape bench
reported on the fleet bus this morning, where a widened pattern changed nothing because the
scanner was reading the wrong line.

⚠️ **What this does not check:** that the example is interesting, or that it says what the prose
around it claims. It checks that a reader who copies it gets a file that compiles. Stated in the
script rather than left to be found.

**Reversal cost:** none; one script and one CI step.

## D68 — the per-declaration kernel ceiling: the unit problem, ended (P1 seal)

**Decision.** `Tests.Coverage` is no longer gated per ROW. Three declarations are gated at an
**absolute millisecond ceiling each**, and everything else in the module is gated as one
**absolute tail**. Neither number divides by anything.

    memDestSweep                         19360 ms
    pre_states_have_a_returnable_frame    2912 ms
    vectorCoverage                        2320 ms
    (everything else in the module)      12420 ms

### 1. Why: the care had all gone into the margin
The helm, 13:37: *"a number measured in the wrong unit and applied with care is still the wrong
number."* This batch had just lowered the ceiling 744 → 493.3 **ms/row** with a great deal of
care — the `× 1.6` convention this line was registered with, the worst of four readings, every
reading's load recorded, the direction of the contention error named. ⛔ **And D62 had already
proved the row is not this module's unit**: after D63 one declaration is half the module and is
barely row- or vector-driven. The margin was refined four times; the denominator never was.
⇒ An absolute ceiling on a NAMED DECLARATION has no denominator, so it cannot be in the wrong
unit. D62 designed exactly this and recorded it blocked; D63 removed the reason it looked hard.

### 2. ⛔ AND THE MEASUREMENT REFUSED THE NAIVE VERSION — gate every declaration
Four profiles on a quiet machine (one-minute loads 3.25 / 3.65 / 4.77 / 5.37), taken only after
the batch-21 selftest had finished:

| declaration | four readings | spread |
|---|---|---|
| `memDestSweep` | 11 800 · 12 100 · 11 900 · 11 900 | **2.5%** |
| `pre_states_have_a_returnable_frame` | 1 800 · 1 800 · 1 690 · 1 820 | **7.7%** |
| `vectorCoverage` | 1 440 · 1 410 · 1 410 · 1 450 | **2.8%** |
| `table_mnemonics_subset_roster` | 708 · 513 · … | **38%** |
| `bitcnt_encodable_forms_all_have_both_shapes` | 912 · 809 · 844 · 919 | 13% |

…and the COUNT of attributed declarations moved **26 / 27 / 28** between runs.
⇒ 🔑 **A PER-DECLARATION CEILING IS SOUND ONLY FOR DECLARATIONS BIG ENOUGH TO MEASURE.** Below
about a second the run-to-run noise exceeds any sensible margin, and a ceiling there would need
relaxing on somebody's schedule — D62's chore, one layer down. So the three above a second are
gated individually and the rest as one tail. **This is the second time a two-point measurement
has refused the obvious version of a gate on this line** (D62 was the first); the difference is
that this time it refused only the naive half, and the sound half was installed.

### 3. Four ways this gate could stop looking, each driven alone
`kernel_cost.py --selftest`, red-first in CI, planting in the CEILING FILE and never in the model:

- a declaration **over** its ceiling → reported;
- the **tail** over its ceiling → reported;
- ⛔ a gated declaration **not in the profile** (renamed, deleted, or fallen below the profiler
  threshold) → reported as `NOT FOUND`, because **a missing reading is not a zero** and a
  declaration that leaves takes its ceiling with it;
- ⛔ declarations gated with **no tail ceiling** → refused, because that is how this design could
  be used to become ungated: gate three declarations, omit the tail, and the rest is free.

Plus a **positive control** run last, which also asserts the ceiling file was byte-restored — a
probe that edits its subject can leave it edited.

**Reversal cost:** the `@perRow` mechanism is still in the parser and unused by this module; one
line restores it.

## D69 — the census document could go stale in silence, so it stamps the model it was measured against (P1 seal)

**Decision.** `docs/DEMAND-CENSUS.md` carries a machine-readable stamp naming the exact model it
was generated against, and `demand_census.py --check` — which needs **no corpus**, so it runs in
CI — recomputes that identity and refuses if it has moved.

### 1. The hole
`docs/COVERAGE.md` is generated and CI fails if it is stale, because the generator runs anywhere.
The census cannot: it needs a corpus of downloaded Debian binaries, so CI gates the **instrument**
(the mapping arms) and not the **reading**. That leaves a published document whose headline —
*"The model covers **84 mnemonics**"* — and every percentage under it are claims about a model
that can change underneath them with nothing to notice. The next batch that adds a mnemonic makes
`cc1 97.4%` a statement about a model that no longer exists, and it will still read as current.

⇒ 🔑 **A FIGURE NOT RE-COMPUTED AT THE MOMENT OF WRITING IS A FIGURE OF AN EARLIER TREE.** (The
helm ruled this on the fleet bus at 14:37 for a freeze hash; the same sentence names this
document's defect, which is why it is written down here rather than admired there.)

### 2. What the stamp is, and what it deliberately is not
The identity is a hash of the **sorted mnemonic list**, not of `docs/COVERAGE.md`:

    <!-- census-model: mnemonics=84 sha=a0f12388d24b4e9e -->

The census depends on precisely that set and on nothing else in the coverage table. So a reworded
row, a changed tier, a new SDM citation must **not** fail this gate — a gate that cried wolf on
prose would be switched off — and a **new mnemonic must**. Driven both ways.

⚠️ **It does not make a stale census correct. It makes it loud.** The document stays wrong until
somebody re-runs it with a corpus; what changes is that nobody can read it believing otherwise.

### 3. Four arms, and the one that matters is not the doctored stamp
- the SHIPPED census matches the model it names → the control;
- a stamp naming a **different** model → reported STALE;
- **no stamp at all** → refused, not read as fresh (an unstamped document is the state this gate
  was invented in, so it must not be the state that passes);
- and the real condition rather than a doctored one: **a new mnemonic planted in the generated
  coverage table** made the gate fire with `84 → 85, sha a0f12388… → 3aa14d31…`.
  ⇒ A stamp test that only ever edits the stamp proves the comparison works and says nothing
  about whether the SUBJECT can move; this one moves the subject.

Plus a byte-restore assertion, because a probe that edits its subject can leave it edited.

**Reversal cost:** none — one comment line in a generated file and one flag.

## D70 — the segment base is a MATCH, not a sum, and the reason is a heartbeat limit (P2 batch 1)

**The decision.** `Ea.addr` is

```lean
match ea.seg with
| none   => ea.offset s nextRip
| some g => s.segBase (some g) + ea.offset s nextRip
```

and not the one-line `s.segBase ea.seg + ea.offset s nextRip`, even though
`Ea.addr_eq_segBase_add` proves the two equal and the summed form is the one SDM Vol. 3A
Figure 3-5 draws.

**Why.** Written as a sum, every memory access in the model — the hundreds that carry no
override — acquires a `BitVec 64` addition of zero that the kernel must still reduce. That is
not a hypothetical: the summed form was written first, and it, together with the two new `Cpu`
fields, blew the 200 000-heartbeat limit on three inherited `bsf`/`bsr` frame proofs before this
batch had added a single instruction. Matched, the unsegmented path is byte-for-byte the old
`Ea.addr` and reduces exactly as it did, so the cost lands only where the feature is used.

**⚠️ The reading is preserved as a THEOREM rather than lost.** `Ea.addr_eq_segBase_add` states
the SDM's own form and is checked; what changed is which of the two the kernel walks.

**Reversal cost:** one definition; the theorem holds either way.

## D71 — two fields on `Cpu` blew three proofs, and the repair is not a bigger margin (P2 batch 1)

**What happened.** `fsBase` and `gsBase` are read by nothing in this batch except `Ea.addr`.
Adding them to `Cpu` made `bitScanStep_mem`, `bitScanStep_rip` and `bitScanStep_zf` — three P1
batch 14 frame lemmas — exceed `maxHeartbeats` at once. Removing the two fields (and changing
nothing else) made all three pass again, which is how the cause was established rather than
guessed.

**The cause.** Those proofs ran `simp only [bitScanStep, Cpu.undefBit, Cpu.undefVal, …]` and
closed with `split <;> rfl` — a defeq check over a `Cpu` record eight updates deep. `undefBit`
has had frame lemmas (`undefBit_mem`, `undefBit_rip`, …) since P0; `undefVal`, added in batch 14
alongside these very proofs, never got them, so there was nothing for `simp` to push a projection
through and `rfl` did the whole record instead.

**The decision.** Give `undefVal` the five frame lemmas its sibling has (plus the two new fields
on both), and let the three proofs be `simp` rather than `rfl`. A `set_option maxHeartbeats`
bump on the three would have been one line and would have left the next field to find the limit
again.

⇒ 🔑 **THE COST OF A STATE FIELD IS PAID BY EVERY WHOLE-RECORD PROOF, NOT BY THE FORMS THAT USE
IT.** The fix that matters is the one that makes the cost stop scaling with the field count, not
the one that buys room for two more fields. D8's kernel-cost discipline arriving as a design
constraint rather than as a ceiling to raise.

**Reversal cost:** none — the frame lemmas are true independently of the batch.

## D72 — the segment bases are INPUTS, so they are not in the record, and the displacements pay for that (P2 batch 1)

**The decision.** `Cpu.fsBase` and `Cpu.gsBase` are **not** emitted in the compared state record,
and are fixed (0x1fd8 and 0x1fe8) in every pre-state.

**Why not in the record.** No instruction in this roster writes either — `wrfsbase`, `wrgsbase`
and `wrmsr` are not modelled, and `arch_prctl` is a system call. D27 is the standing rule for
that situation: *a state component no instruction writes is a constant, and a comparator that
watches a constant reports agreement it did not test.* Two more always-equal fields would have
been two more lines of green about nothing.

**⛔ What that costs, and what pays for it.** If the bases are not compared directly, the ONLY
evidence that the model uses them is the address they produce — so every vector's displacement is
chosen to make that address land inside a watched window. `%fs:0x28` with the base dropped is
address 0x28, which is outside both windows, where our `Mem` reads 0 and the ACL2 driver renders
an unmapped byte as `00`. A vector whose access lands there is batch 12's `leaveq` trap and batch
15's backward string step a third time: **both models unobserved, and agreement that tested
nothing.** `fsBase = 0x1fd8` puts the real displacement 0x28 on the swept operand at 0x2000; the
`mov_fs_base_q` vector carries `-0x1fd8` for the same reason.

**⚠️ And the two bases DIFFER by 0x10 rather than being equal.** With one value for both, a model
that read GS's base for an FS access would agree in every case and half the addition would ship
untested. `X86.Seg` has two constructors and a pre-state that cannot tell them apart tests one.

**What is NOT closed, named rather than left to be found.** x86isa's `ea-to-la` requires the
resulting LINEAR address to be canonical and faults if it is not, for segmented and unsegmented
accesses alike. This model checks canonicity on branch targets only (D9) and on no data address.
This batch does not widen that gap — the bases are fixed and small — and does not close it.

**Reversal cost:** two fields and eight vectors.

## D73 — the completeness check cost 4 200 ms, and the ceiling named a build that costs nothing (P2 batch 1)

**What was there.** `segEas` reads an instruction's AST and returns its segmented effective
addresses. A `match` with a `_ => []` default is the shape whose gaps all fall the silent way — a
constructor it forgot would make the batch's two sweeps EMPTY, and an empty sweep is green — so it
shipped with a companion theorem comparing its answer against the **encoded bytes** (`64`/`65`
prefixes) over all 784 vectors. A real second source, and it worked.

**What it cost.** 4 200 ms of kernel time: the second most expensive declaration in
`Tests.Coverage`, behind `memDestSweep`, and enough to take the module's `@tail` ceiling from
12 420 to 12 770 and fail the gate.

**Measured rather than assumed.** Split into halves and timed standalone: the byte side **7.9 s**,
the AST side **0.4 s**. The whole cost is `String.toList` reducing 784 string literals in the
kernel. Nothing about the claim was expensive; the representation was.

**The decision — two pieces, neither of which is a raised ceiling.**

1. `X86.opOperands` is **exhaustive over all thirty-six `Op` constructors, with no wildcard arm.**
   The completeness question is now answered by the COMPILER on every build. That is strictly
   stronger than the theorem it replaces, which could only ever have caught a constructor some
   VECTOR already used; a thirty-seventh constructor is now a compile error that forces whoever
   adds it to say whether it can carry a segment.
2. The byte side became `seg_findings` in `scripts/check_encodings.py`, where an assembler is
   already running, and grew a THIRD source while it moved: the hand-written AT&T text, the
   assembler's prefix byte, and the AST's `seg` field must agree **per vector and per segment** —
   because reading GS's base for an FS access is one of this batch's four planted defects. Its
   red-first arms doctor each of the three sources alone, plus a control, on every invocation
   rather than behind a flag.

⇒ 🔑 **A CEILING THAT REFUSES NAMES A CHEAPER BUILD, AND THE CHEAPER BUILD IS USUALLY STRONGER.**
The obvious repair was `@tail 12420 → 13500`. What the refusal actually bought was a compile-time
completeness guarantee and a third independent source, for zero kernel time. This is D62's shape
(a blocked repair blocked one DESIGN, not the goal) arriving in a cost gate rather than a unit
problem.

**Reversal cost:** one function's arms and one Python block.

## D74 — the gate that polices stale literals had a stale literal in its own selftest (P2 batch 1)

`scripts/claimed_forms.py` exists because a published number was a hand-maintained literal and was
ELEVEN LOW for eighteen batches (D56). Its `--selftest` plants a defect in each README claim and
requires the gate to catch it. One of those plants was the string `"84 mnemonics in 776"`.

P2 batch 1 took the form count from 776 to 784, and that arm reported **ANCHOR MISSING** — the arm
had gone stale, and had it been one of the arms whose absence is quiet rather than announced, the
selftest would have shrunk in silence.

⇒ 🔑 **A GATE IS NOT EXEMPT FROM THE DEFECT IT POLICES**, and the exemption is granted by nobody
reading the gate's own body. The plant now DERIVES its anchor from the shipped sentence
(`_mnem_anchor`) and perturbs the count it finds there, so it cannot go stale again; a README that
stops carrying the sentence still reports ANCHOR MISSING, which is the honest answer rather than a
pass.

⚠️ **The failure mode was announced here and is not everywhere.** This arm printed `[ANCHOR
MISSING]`. That behaviour is what made a five-minute finding out of it, and it is worth naming as
the reason the pattern is safe: an arm that had simply not matched would have counted as a pass.

**Reversal cost:** two helper functions.

## D75 — a probe that edits the tree makes `git add -A` a race, and this batch lost it (P2 batch 1)

**What happened.** Commit `afcde4a` — this batch's own commit — shipped
`scripts/kernel_ceilings.txt` carrying `Tests.Coverage @decl vectorCoverageXX 2320`: a ceiling on
a declaration that does not exist. That string is not a typo. It is exactly what
`kernel_cost.py --selftest`'s **third arm plants**, and it was in the working tree because
`git add -A` ran while that selftest was mid-arm. The probe restores the file when it finishes; it
had not finished. The commit was pushed to both tiers before the selftest returned, so CI on
`afcde4a` is expected RED on the kernel-cost step, and that red is understood.

⇒ 🔑 **A PROBE THAT EDITS THE TREE MAKES `git add -A` A RACE**, and the window is invisible:
nothing in the probe's output mentions the tree, `git status` during the window looks like ordinary
work in progress, and the planted line is one character from a legitimate one.

**The repair, in the order it matters.**

1. **The seam.** `CEIL_FILE` is now read from `X86LEAN_CEIL_FILE`, and `--selftest` writes each
   mutation to a file in a temp directory and points the child at it. The probe no longer writes
   inside the repository at all — the same move P1's seal made for `sharing_redprobe.sh` (a467a22)
   for the neighbouring reason: *a cleanup that only runs on a clean exit is not cleanup*. Here
   the failure needed no crash, only a concurrent `git add`.
2. **The control keeps its byte check**, which is now trivially true. That is deliberate: it is
   the regression guard if the seam is ever removed, and it says so.

⚠️ **What this does NOT fix.** `check_readme_snapshot.py --selftest` and
`claimed_forms.py --selftest` also mutate tracked files in place and restore them. They are
correct as written and are not touched here, but they carry the same race. Until they take the
same seam, the standing rule is: **never stage while a probe that writes the tree is running.**

**The receipt, measured in the condition the seam exists for.** With the seam in place, the
tracked `scripts/kernel_ceilings.txt` was sampled **30 times over 60 s while `--selftest` was
running**: `differed=0`, with a `lean` child alive in **23 of the 30** samples — so the sampling
was inside the arms rather than between them. Before the seam the file was mutated for the WHOLE
of each arm, so all 23 of those samples would have differed. That is the positive control on the
observation, not merely on the result.

⚠️ **And a probe-subject defect of my own, found while taking that receipt.** The first version of
this check counted occurrences of `vectorCoverageXX` in the file — and found one, because the
sentence you are reading QUOTES the planted string. `read_ceilings` does `line.split("#")[0]`, so a
`#`-prefixed line yields nothing and the quote is inert; but the probe could not tell a quotation
from a plant. It counts ACTIVE (non-comment) lines now, and compares the file's sha against a
snapshot rather than grepping for a string. *A probe that greps for the defect's TEXT cannot tell
the defect from a description of it.*

**Reversal cost:** one environment variable.

## D76 — the P2 roster claimed the LOCK vocabulary would unblock six rows; it unblocked two (P2 batch 23)

**The false sentence, in a GENERATED and byte-gated document.** `docs/P2-ROSTER.md` said:

> the LOCK vocabulary — D25 declines `xchg` at memory and the six `bt`-family memory forms
> BECAUSE there is no LOCK vocabulary to state their atomicity in. The addition unblocks those
> declined rows as a side effect, which is why it is worth more than its occurrence count says.

Three errors, all in the direction that flatters the item:

| the sentence | the repository |
|---|---|
| "the six `bt`-family memory forms" | there are **four** — six was the TOTAL of declined rows |
| "D25 declines … the `bt`-family" | **D23** declines them |
| "for want of a LOCK vocabulary" | their reason is signed **BIT-STRING addressing** (D23), which no LOCK vocabulary touches |

⇒ **The addition unblocks 2 rows, not 6.** The claimed-row count moved 498 → 500, which is the
measurement that settles it.

**⚠️ WHY IT SURVIVED, AND THIS IS THE PART WORTH KEEPING.** `docs/P2-ROSTER.md` is generated by
`scripts/p2_roster.py` and CI re-derives it BYTE-FOR-BYTE. That gate proves the file matches what
the script emits and says nothing about whether the script tells the truth — and a hand-written
paragraph inside a generated document reads as generated. **A derivation gate is a wrapper a
false sentence can sit inside.**

**The decision.** The paragraph is DERIVED from `claimed_forms`'s tables, which already record one
decision per declined row, and the two tables are gated in opposite directions:

* `DECLINED` — what is still declined and by which decision;
* `LOCK_UNBLOCKED` — the rows this addition unblocked, and `--check` requires every one of them to
  be in the CLAIMED set. Shrinking the residue is now a claim that fails loud rather than a
  deletion nobody checked.

`p2_roster.py --selftest` drives it four ways: an extra unblocked row must move the count, a
still-declined row re-labelled as atomicity-blocked must be reported as REMAINING, an empty
unblocked set must say ZERO rather than fall back on a plausible number, and the tables must be
restored.

**Reversal cost:** one function and two tables.

## D77 — the LOCK vocabulary: a flag on the effective address, a transcribed list, and one guard (P2 batch 23)

**The decision.** `Ea.lock : Bool`, `Op.lockable` (the SDM's list, transcribed), and ONE
well-formedness test in `step` before its match.

**Why the flag lives on `Ea` and not on `Instr`.** The SDM (Vol. 2A, "LOCK") permits the prefix
*"only to those forms of the instruction where the destination operand is a memory operand"*. On
`Ea`, `lock` without a memory operand is **unrepresentable** rather than a runtime check somebody
has to remember to write. ⚠️ It also could not go on `Instr` cheaply: `Instr` is built with the
anonymous constructor `⟨op, len⟩` in 799 vectors, and Lean's `⟨…⟩` requires every explicit field
even when the trailing one has a default — measured, not assumed.

**⛔ THE LIST IS TRANSCRIBED FROM THE MANUAL, NOT INFERRED FROM THE MODEL.** `CMPXCHG16B` is on it
and is not in this roster; **`MOV` is not on it**, is in this roster, and is the form a reader most
expects to be lockable — `lock movq %rax, (%rbx)` looks exactly like the atomic store somebody
wants. A list derived from "the memory-destination forms we have" would have admitted `mov`, the
shift group and every `cmp`/`test`: all #UD on silicon.

**What the model does NOT claim.** A single-step, single-threaded semantics has no observation that
distinguishes an atomic read-modify-write from a non-atomic one. `Ea.lock` **records** that the
access is architecturally atomic; it verifies nothing about concurrency, and `TRUSTBASE.md` says so
where a reader is looking. Having the vocabulary is exactly what D25 said the model lacked, and it
is what un-declines `xchg` at memory.

**⛔ THE BATCH HAS NO ARITHMETIC, AND THAT SHAPED EVERY ARM.** `lock addq` and `addq` are the same
function here, so no arm can catch a model that "ignores LOCK" in the value channel. What is
observable is the two EDGES — which forms the prefix makes #UD, and the form the vocabulary
un-declined — and all four planted arms live on them, two of them moving the lockable list in
OPPOSITE directions so that a widened list and a narrowed one are caught by different vectors.

**The cost, paid once.** `step`'s guard sits before the match, so every characterization theorem
acquires a side condition. Marking the operand walk and the two predicates as `simp` definitions
discharges it structurally for the register-only forms — 61 sites down to 20 — and the remaining
20 gained `(hl : ea.lock = false)` or `(hl : o.locked = false)`. ⚠️ Those hypotheses are not
bookkeeping: for `mov m,r` the theorem was making a claim that is now FALSE for a locked operand.
Narrowing a claim that had become too wide is the honest repair.

**Reversal cost:** one field, one list, one `if`.

## D78 — the coverage table said its six numbers "ARE DERIVED"; they are written there and CHECKED elsewhere (P2 batch 23)

`docs/COVERAGE.md`'s roster line carries six numbers and the sentence *"⭐ ALL SIX NUMBERS ARE
DERIVED, by `scripts/claimed_forms.py`, and gated in CI"*. The second half is true. The first is
not: the numbers are **literals in the generator's string**, and `claimed_forms.py` DERIVES the
same six from two independent sources and fails CI if they disagree.

The distinction matters exactly where this repository's history says it does. A derived number
cannot be stale; a gated literal can be stale for as long as it takes somebody to run the gate,
and the whole point of D56 was that a literal nobody derived was ELEVEN LOW for eighteen batches.
Calling a gated literal "derived" invites the reader to skip the gate.

⇒ The sentence now says GATED, names both sources, and says plainly that the numbers are written
there and checked here. **Reversal cost:** one sentence.

## D79 — objdump prints `f0` as its own instruction, and the encoding gate had to be taught otherwise (P2 batch 23)

`objdump -d` disassembles `f0 48 01 0b` as **two lines** — `f0  lock`, then `48 01 0b  addq
%rcx,(%rbx)` — so `scripts/check_encodings.py`, which maps a vector's label to the instruction at
that address, read every locked vector as a **one-byte** instruction.

⛔ **And the direction is what makes it worth a decision.** The `Instr.len` check would have failed
loudly on 4-vs-1 — but a model that had silently DROPPED the prefix would have agreed with that 1.
A harness that reads a prefix as a separate instruction cannot see a model that ignores prefixes.

**The decision.** A single-byte `f0` line is FOLDED into its successor: same start address, bytes
concatenated. That is what the machine does — a prefix is part of the instruction (SDM Vol. 2A
§2.1.1) — and what `Instr.len` means. Everything else objdump splits (REX, the operand-size
prefix) it already keeps on one line; `f0` is the only one this table has met that it does not.

**And the fold is GATED rather than trusted**, by the same three-source shape the segment override
uses: the AT&T text's `lock` token, the assembler's `f0` prefix byte, and the AST's `Ea.lock` must
agree per vector, with an arm that doctors each source alone plus a control, on every invocation.
The third arm sets the first byte to something other than `f0` — which is precisely the unfolded
read — so the fold cannot quietly stop happening.

**Reversal cost:** ten lines.

## D80 — D74's repair fixed one plant and left its two neighbours; this batch found them the same way (P2 batch 23)

D74 (P2 batch 1) found that `claimed_forms.py --selftest` — the gate that exists because a
published number was a hand-maintained literal — planted the literal `"84 mnemonics in 776"`, and
that it had gone stale on the first batch to move the figure. The repair derived that plant from
the shipped sentence.

**It left the two plants beside it alone.** P2 batch 23 moved the declined-row count (6 → 4) and
the residue total (27 → 25), and both arms reported `[ANCHOR MISSING]` — the same defect, in the
same table, two lines away.

⇒ 🔑 **NAMING A DEFECT IS NOT THE SAME AS LOOKING FOR ITS SIBLINGS.** D74's note said "a gate is
not exempt from the defect it polices" and then fixed exactly one instance of it. The question the
repair should have asked — *what else in this table is a literal?* — was not asked, and the answer
was: everything else in this table.

Every plant is derived from the shipped sentence now (`_num_anchor` / `_num_perturbed`), so the
table has no literal left to go stale.

⚠️ **And the failure mode is still the good one.** Both arms printed `ANCHOR MISSING` rather than
silently not matching, which is what made this a two-minute finding rather than a selftest that
quietly shrank from 13 arms to 11.

**Reversal cost:** two helper functions.

## D81 — X86.Theorems' ceiling raised 540 → 1100, and it is the THIRD option (P2 batch 23)

`step` tests `Op.lockIllegal` before its match (D77), so every one of the module's ~200
characterization theorems must reduce that guard. Measured **733 ms against a 540 ms ceiling** on a
module that had never been near it.

**Two cheaper builds were taken first**, in the order this repository's own history recommends
(D68, D71, D73):

1. the predicate was rewritten from THREE list passes (`filterMap` + `++` + `any`, through
   `Op.eas`) to ONE — `Op.anyLocked`, a direct 36-arm match whose equality with the `opOperands`
   walk is a **compiler-checked theorem**, so the duplicate cannot drift. **733 → 684 ms, 7%.**
2. the operand walk and the two predicates are `simp` DEFINITIONS, which discharges the side
   condition structurally for every register-operand theorem. Without it, 41 more theorems would
   carry a hypothesis and the module would cost more, not less.

⛔ **WHAT IS LEFT IS THE FEATURE'S PRICE, NOT AN ACCIDENT OF REPRESENTATION.** A guard at the head
of `step` is work every theorem about `step` has to do. The only design that avoids it is not
having the guard — and not having it means a locked `mov` executes instead of faulting, which is
the one thing this batch is for.

⇒ **So the ceiling is raised, and this note is what makes that honest.** D71 says the repair that
matters is the one that stops the cost scaling, not the one that buys room; that was true there
(a `rfl` whose cost grew with the field count) and is not true here (a constant guard per
theorem). Registered at measured × 1.6 on the 684 reading — 1 094 → **1100**.

⚠️ **Conditions, because a figure without them cannot be compared.** One-minute load 5.03,
five-minute 4.54 — ABOVE the 2.2–4.1 band this script measured as having no effect. Both readings
were taken minutes apart under the same conditions, so the COMPARISON between them is the safe
part; the absolutes are loose and a quiet re-measurement can tighten this.

**Reversal cost:** one line, and the two cheaper builds stay either way.

## D82 — a ceiling that PASSED at 97.6% is a gate about to fire, and the control is what showed it (P2 batch 23)

`X86.Syntax` read **121 ms against a 124 ms ceiling** — the plain gate said CLEAN. The
`kernel_cost.py --selftest` **control** — the arm that re-runs the shipped ceilings LAST, after
four measurements, under contention this script itself measures at 4%–8% — went OVER.

⇒ 🔑 **A PASS AT 97.6% OF A CEILING IS NOT HEADROOM, IT IS A GATE THAT WILL FIRE ON THE NEXT LINE
SOMEBODY ADDS.** The gate's job is to catch a regression; a gate three milliseconds from its limit
catches the next edit instead, whatever that edit is, and the seat that meets it will read a real
red as noise. The batch added `Op.lockable`, `Op.anyLocked` and its equality theorem to this
module, which is the whole of the 104 → 121 move.

⚠️ **And the finding belongs to the CONTROL, not to the gate.** The control exists to prove the
gate can pass; here it did the opposite of its usual job and proved the gate can *barely* pass.
That is worth naming because the temptation was to read it as self-contention noise and move on —
which it also was: the same reading alone is CLEAN. **Both are true, and the useful one is the
tighter one.**

Registered at measured × 1.6 on the 121 reading: 194 → **200**.

**Reversal cost:** one line.

## D83 — the encoding gate silently dropped the last byte of any ten-byte instruction (P2 batch 24)

`scripts/check_encodings.py` parsed objdump's byte column with
`(?:[0-9a-f]{2} )+` — each byte followed by a **space**. objdump pads that column
to a fixed width, so for every instruction this repository had ever carried the
final byte was followed by padding and the pattern worked.

**`movabsq $imm64, %r64` is ten bytes**, the first form here wide enough to fill
the column exactly. Its final byte abuts the **tab** before the mnemonic, and the
gate read the instruction as **nine** bytes.

⇒ 🔑 **AND THE DIRECTION IS THE FINDING.** The gate reported `model says len=10,
assembler says 9` — loud, because the model was right. Had the model been wrong
in the same way the parser was, the two would have agreed: **a harness that
truncates its own reading cannot see a model that truncates the same way.** The
defect has been latent since P0 and no shorter form could expose it.

**The decision.** The pattern is `[0-9a-f]{2}(?: [0-9a-f]{2})*` followed by
whitespace-or-end, which does not care what separates the bytes from the
mnemonic. Both call sites (the vector table and the synonym check) are fixed
together; they were the same literal.

⚠️ **What this says about the class.** A parser that has only ever seen padded
input has not been tested on unpadded input, and column-filling is a property of
the WIDEST datum — so the widest datum is where a column parser gets its first
real test. This repository now has one ten-byte instruction; the next parser
written against a padded column deserves a deliberately-widest case before it
ships.

**Reversal cost:** one regex, two call sites.

## D84 — `movabs` is a batch that changes no semantics, and says so (P2 batch 24)

P2 addition 3. `Operand.imm` has carried a full `BitVec 64` since P0 and the
decoder is trusted to have performed any extension (`X86/Syntax.lean`'s header,
`TRUSTBASE.md`), so `movabsq $imm64, %r64` and `movq $imm32, %r64` reach `step`
as the same shape with different values. **Not one line of `X86/Semantics.lean`
changed**, and the roster does not move: K files `mov r,imm` as one row with six
variants, and `mov_ri` already claims it.

⛔ **So what a green run here does NOT contain has to be said, which is P1 batch
20's rule.** It contains no evidence about immediate extension, because there is
no extension in this model to be wrong about. What it does contain:

1. **the length path.** Ten bytes is the longest encoding in the table; a wrong
   `Instr.len` is a wrong RIP on every case, and the model cannot check it about
   itself. This is what found D83.
2. **the decode-trust boundary**, at the one place re-derivation is tempting.
   `movabs_lo32_ones` (`0x00000000ffffffff`) and `movabs_hi32_ones`
   (`0xffffffff00000000`) carry values no 32-bit immediate sign-extends to, so
   the single plausible wrong decoder — one that reused the `imm32` path — is
   caught, and every other `mov r,imm` vector is unaffected by that arm because
   truncate-and-sign-extend is IDENTITY on them.
3. **the demand**, measured: 3,791 occurrences, 0.41% of the uncovered gap.

⚠️ **The arm is keyed on the VALUE and not on `i.len`.** Keying on the length
would plant a defect in the decoder's output rather than in a model of it, and
would be indistinguishable from a typo.

**Reversal cost:** three vectors and one arm.

## D85 — the vector register file exists before any vector semantics, and its claim is narrow (P2 vector wave, batch 0)

**The decision.** `Xmms` (sixteen named 128-bit fields) and one `Cpu.xmm` field; sixteen `xmmN=`
fields in the differential record; the same sixteen produced by `x86l-xmms` in the ACL2 driver;
XMM values carried into the oracle's pre-state through the case record; a cross-check across the
language boundary; and one planted arm. **No vector instruction, and no vector semantics.**

**Why now, and why not at P0.** `X86/State.lean` has said since P0 that XMM is *"ABSENT AT P0, ON
PURPOSE … at P0 they would be fields that no instruction reads and no test constrains — a phantom
that reads as coverage."* That was right, and it expired when the oracle-availability run measured
what actually blocks P2: the oracle EXECUTES the vector forms, and `x86l-post` reported 16 GPRs,
RIP, the flags and two memory windows.

⇒ 🔑 **"THE ORACLE EXECUTES IT" IS NOT "THE HARNESS CAN SEE THE ANSWER."** A vector form run on
both sides would have been compared on NONE of its results, and an unobserved region does not
report "unknown" — it reports AGREEMENT. The first vector batch's `unexplained=0` would have been
a statement about the harness.

**⚠️ WHAT THIS BATCH CLAIMS, STATED NARROWLY BECAUSE D27 IS WATCHING.** No instruction writes XMM,
so the registers are CONSTANTS, and a comparator that watches a constant reports agreement it did
not test. The claim is exactly: *the channel exists, both models report it, they agree on it, and a
planted difference in it is CAUGHT.* Only the last clause has teeth — `wrongXmmClobbered` zeroes
`xmm3` and is caught in 64 746 cases.

**Three design decisions worth their reasons:**

1. **One `Cpu` field, sixteen registers nested inside it.** D71 measured that two fields on `Cpu`
   blew three inherited proofs, because a whole-record `rfl` costs O(fields). Sixteen flat fields
   would have cost eight times that. Nested, every existing record proof pays for one more
   projection. ⚠️ And the frame lemmas were written the day the field was added, not when a proof
   needed them — which is precisely what `undefVal` did not get, and D71 is the bill for that.
2. **The pre-state pattern is not zero.** All-zero on both sides is the unobserved-region trap in
   its purest form: a model reporting the wrong register, a constant, or nothing at all would agree
   in every case. Each register gets `(a+i) : (c XOR i·0x1111…)`, so no two are equal and none is
   constant across cases.
3. **The leak check widened on the same day.** The two opposite oracle runs must now agree on every
   XMM register, with **no declaration channel** — because nothing draws an oracle bit into a
   vector register yet, and the honest rule while that is true is the absolute one. The day a form
   legitimately leaves one undefined, this and `undefinableFields` are the two places that grow.

**Reversal cost:** one field, one renderer on each side, one gate.

## D86 — a CR4 gate that was already GREEN measured a call site no differential run uses (P2 vector wave, batch 1)

`scripts/oracle_availability.py --p2` has carried a two-arm CR4 gate since the P2 roster run. It
declares every candidate vector form under **both** CR4 settings, it rides a refuse-always control
and an MMX form that needs no CR4 bit, and it is green: `movdqa` executes at `CR4=0x600` and
refuses at `CR4=0`. The comment above it even records the finding that produced it — the first
availability reading said "P2 has no oracle" because `(ctri 4 x86)` read **0**.

**And the differential path was still passing `nil`.** `measure_cr4()` builds its own
`init-x86-state-64` call. The call site that actually feeds the comparator —
`x86l-run-case` in `scripts/x86isa_driver.lisp` — took its `ctrs` argument as `nil` from P0 until
this batch. So the repository held a *correct, gated, twice-armed* measurement of the oracle's SSE
capability, taken on a path no differential run has ever executed.

⇒ 🔑 **A CAPABILITY MEASURED ON A BYPASS PATH SAYS NOTHING ABOUT THE PATH THAT SHIPS.** Two call
sites into the same oracle; the probe answered *"x86isa can do SSE"*, which is true, and it was
read as *"the differential can do SSE"*, which was false. The gate was not wrong — it was
**about something else**, and nothing in its output said so.

⚠️ **The near-miss worth naming.** This one would have failed loudly: with `ctrs` nil every SSE
form raises `#UD`, the oracle's post-state carries `refused=1`, and `refused=` is a field the
comparator reads. The dangerous sibling is the quiet one — a form the oracle declines for a reason
the harness attributes to the MODEL. The reason it stayed invisible this long is that
*nothing had ever asked the shipping path a question only SSE could answer.*

**The decision.** One `defconst` on the side that owns it:

```lisp
(defconst *x86l-ctrs* (list (cons #.*cr4* #x600)))   ; OSFXSR | OSXMMEXCPT
```

passed as `init-x86-state-64`'s fourth argument. **Not** a `:ctrs` field in the emitted case, which
was the drafted design, and the departure has three reasons, each checked rather than argued:

1. **Lean has no CR4.** `X86/State.lean` models no control register, so an emitted `:ctrs` would be
   a constant serialised 69,144 times with nothing on the Lean side to disagree with — a
   cross-language duplicate that no gate could hold together. The `:fsbase`/`:gsbase` precedent
   sends values across the boundary because the model *has* those values and they *vary*.
2. **It would have grown the emitted record**, and `oracle_availability.py`'s `rewrite()` still
   reads `:bytes` off `c[1]` **by position** — the bet this repository has already lost twice
   (the `:mem` line, P2 batch 2).
3. **Several scripts `ld` this driver** — `run_differential.sh`, `oracle_availability.py` and
   `oracle_undef_probe.py` when the decision was taken, and `check_driver_cr4.py` makes another the
   moment this batch lands. A constant inside the driver reaches every one of them; an emitter field
   reaches only what the emitter feeds.

   ⚠️ That sentence began life as *"three scripts `ld` this driver"*, and the gate this same batch
   added made it four before the commit was written. **A COUNT BESIDE A LIST goes stale while the
   list stays right** — which is the exact defect this batch repaired in `.github/workflows/ci.yml`
   an hour earlier, reproduced in the decision note that recorded the repair. Naming a class does not
   confer immunity from it; the list is written out and carries no total.

**The gate: `scripts/check_driver_cr4.py`, through `x86l-run-case` itself.** Six forms × six real
pre-states, run twice: once with the driver **exactly as shipped**, once with `*x86l-ctrs*` planted
back to `nil` — which is byte-for-byte the pre-batch driver. SSE must execute in the first and
refuse in the second; `movl %ecx,(%rbx)` must execute in **both** (so the OFF arm is a reading about
SSE and not about a dead run) and `movnti` must refuse in both. The plant is **derived from the
shipped file**, and the probe **refuses** if the defconst is absent rather than running two
identical arms and reporting agreement. 19 seconds.

⚠️ **The selftest's first draft was a tautology and is worth recording as a defect, not a footnote.**
It asked whether each measured value differed from the *inverted* declaration — which, once the
shipped table is green, is true by construction for every form. It printed two ✔ red arms and
proved nothing. The fix routes the plant through `report()` itself, so the arm exercises the code
that does the reporting; probed by blinding `report()`, by flipping a shipped declaration, and by
renaming the defconst — **each produces a red**.

⚠️ **What this batch does NOT claim.** That any vector form is *differentiable*. Nothing on the Lean
side writes XMM yet, so D85's narrow claim stands unchanged: the channel exists and a planted
difference in it is caught. This batch removes the oracle's `#UD`, which is a **precondition** for
vector semantics, not a step of them. It changes no semantics and adds no roster row.

⚠️ **And a modelling choice, stated so it can be held against us:** x86lean assumes SSE is ENABLED
and does not model the `#UD` a real `CR4.OSFXSR=0` would raise. Recorded in TRUSTBASE.md.

**Reversal cost:** one `defconst`, one argument, one gate.

## D87 — editing a shell script while bash is executing it forked the run, and the batch's own receipt was the casualty (P2 vector wave, batch 1)

**What happened.** This batch's first differential run finished with a clean report —
`cases=69144 matched=49258 explained=28774 unexplained=0 oracle-leaks=0 missing=0` — and then
printed one more line that belonged to no gate in this repository:

```
at: garbled time
EXIT=1
```

`x86lean-diff compare` returns 1 only on `unexplained`, `missing` or `leaks`, and all three were 0,
so the failing command was not the comparison. It was `at`. **The Unix `at` scheduler**, which this
repository has never invoked.

**The cause, and it was mine.** `scripts/run_differential.sh` was being executed by bash when this
batch inserted its new `check_driver_cr4.py` step near the top of the file. **bash reads a script
incrementally, by byte offset**, not into memory: it had the compare command in hand, but its saved
offset for "what to read next" was an offset into the OLD file. The insertion moved every later byte
down by about 700, so when bash resumed it landed one byte inside

```sh
cat > run/drive.lsp <<LSP
```

and executed **`at > run/drive.lsp`** with the heredoc as its input — an `at` invocation with no time
specification, which answers `garbled time` and exits 1. The exact error and the exact exit code are
both accounted for by a one-byte shift.

⇒ 🔑 **A RUNNING SHELL SCRIPT IS AN OPEN FILE HANDLE, NOT A LOADED PROGRAM.** Editing it mid-run does
not schedule the change for next time — it splices new bytes into the *current* execution at an
offset nobody chose. The failure is not a syntax error at the edit site; it is an arbitrary command
assembled from the middle of unrelated text, executed with the privileges and the working directory
of the run.

⚠️ **THE SIBLING, AND THE REASON THIS IS A NOTE AND NOT A FOOTNOTE.** D75 is the same class one file
over: *a probe that edits the tree makes `git add -A` a race.* This is *a run that reads the tree
makes an EDIT a race.* Both hazards are invisible in `git status`, both windows are opened by
ordinary batch work — writing the next gate while the current run finishes — and in both the
corrupted artifact looks almost right. This one was loud only because `at` happens to exist and to
refuse; a shifted offset landing inside a `grep` or an `echo` would have produced a plausible line
and a zero exit.

**What was actually damaged, stated exactly.** Nothing in the model, and nothing in the numbers: the
oracle ran to completion under the patched driver, the comparison read all 69,144 cases, and the
report printed before the splice. What was damaged is the **receipt** — a run whose exit status is 1
for a reason unrelated to its subject cannot be shown as a green batch seal. It was re-run clean,
with no edit to any file the run reads, and the second run is the one recorded.

⚠️ **AND THE NUMBERS ARE HELD AGAINST A BASELINE, NOT ASSERTED.** `c693ab7` recorded
`cases=69144 matched=49258 explained=28774`; this batch reproduces all three **digit for digit**,
which is the batch's actual claim: `CR4.OSFXSR` is inert for the 804 existing scalar vectors. Two
identical readings normally deserve the suspicion that one arm is wearing two names — here the
identity is the *prediction*, because OSFXSR gates SSE decode and this corpus contains no SSE form,
and it is corroborated by an independent measurement that CR4 *does* reach the oracle
(`check_driver_cr4.py`, where planting it back to `nil` flips four forms to `refuses`).

**The rule.** While a run is in flight, edit nothing it reads — not the script, not the driver it
`ld`s, not the Python gates it invokes. Docs are free. If a gate must be written while a run is out,
write it in the scratchpad and move it in afterwards.

**Reversal cost:** none — this is a process finding; the code change it damaged was re-run, not
rewritten.

## D88 — `ci.yml` had not parsed for forty-nine commits, and an unparseable workflow reports a failure rather than an absence (P2 vector wave, batch 1)

**What was found.** Every push since `aa11e35` (09/02) produced a `ci.yml` run whose conclusion was
`failure` **with zero jobs**, and whose `createdAt` and `updatedAt` are the same second. GitHub had
not run a step; it had refused the file. Forty-nine commits, the whole back half of P1 and the whole
of P2 to date.

```
$ gh api repos/jyh/x86lean/actions/runs/33835447015/jobs --jq .total_count
0
$ gh run view 33835447015
X This run likely failed because of a workflow file issue.
```

**The cause is one unquoted colon.**

```yaml
- name: Fetch the K semantics (sparse: `semantics/` only, 15 MB of 2.8 GB)
```

`sparse: ` inside an unquoted YAML scalar opens a mapping where a mapping is not allowed, so the
document does not parse — *the whole file*, not the step. Local confirmation:
`mapping values are not allowed in this context at line 186 column 44`. Quoting the name is the
entire repair, and the file then parses to one job of twenty-five steps.

⇒ 🔑 **AN UNPARSEABLE GATE FILE REPORTS A FAILURE, NOT AN ABSENCE — AND THE TWO LOOK NOTHING ALIKE
IN A LIST AND IDENTICAL IN A GLANCE.** A red tick beside a commit is read as *"a check ran and did
not like it"*, which invites diagnosis. What was actually true is *"no check exists"*, which invites
nothing. Worse, it was **instant**: a zero-second run does not even look like a job that tried. The
signal that something is wrong was present on every push and carried the wrong meaning on every one.

⚠️ **AND IT IS THE STRONGEST FORM OF THE REPOSITORY'S OWN RECURRING DEFECT.** D65 wrote *a citation
is an ungated claim*; D41 and D74 wrote that a number beside a list goes stale. This is the whole
CI file as an ungated claim: twenty-five steps naming twenty-five gates, every one of them a true
description of a script that exists and works, and none of them running. `ci.yml`'s own header
comment reasons carefully about *which* gates cannot run on a runner without an oracle — a paragraph
about the boundary of a job that was not executing at all.

⚠️ **What this does NOT mean.** The gates themselves are fine: all ten fast ones were run locally at
this batch and are green, the oracle-dependent ones run beside the differential every batch, and the
**Scrub** workflow — the commit-trailer gate that the fleet's hygiene doctrine rests on — is a
*separate file*, parses, and has been green throughout. The hygiene gate never lapsed. What lapsed is
every correctness gate's *automation*; they have been running only where a seat remembered to run
them.

**The decision.** Quote the name, and say why in the file so the next editor does not unquote it. No
gate is weakened or trimmed to make the first run green: which steps are too expensive for CI is a
question the first real run should answer, and trimming them now would be choosing, unmeasured, which
checks matter — a declared list inheriting the direction of its default (D61).

⚠️ **THE FIRST RUN WILL BE LONG, AND THAT IS THE NEXT HEAD'S FIRST READING.** Step 7 is the full
harness selftest: **83 arms**, measured at ~2.6 min per arm marginal (~48 arms in 2h05m before it was
stopped), so **≈3.6 hours** — against the "twenty minutes" its own comment still claims, written when
there were 23 arms and 46,320 cases. Arms grew 3.6× and the corpus 1.5×; the total grew ~10×.
⇒ **A whole-job total cannot tell growth in the work from growth in each unit** (D-note on profiling
per part at two sizes). Steps 8 and 11 are also long. Whether this job fits GitHub's six-hour limit is
now a measurement to take, not a guess — and it could not have been taken while the file did not parse.

⚠️ **A method note, recorded because it cost two hours here.** The full selftest was launched piped
through `tail -4`, which hid all 83 per-arm lines until the process ended: a long job's progress
output must not be piped, or a run with no signal is indistinguishable from a hang. Its cost was
recovered instead from the arm NAMES that survived the pipe — and the first cost estimate taken from
a standalone one-arm invocation (5m41s) was **wrong by ~2×**, because a filtered run re-pays the
whole startup; the marginal per-arm figure is the one that predicts a batch.

**Reversal cost:** two quotation marks.

## D89 — D83's defect, one disassembler over: GNU objdump wraps its byte column at seven (P2 vector wave, batch 1, CI repair)

**What the first CI run in forty-nine commits found.** With `ci.yml` parsing again (D88), step 8 —
the encoding cross-check — failed on **24 of 804 forms**, every one of them reported as **exactly
seven bytes**:

```
cmp_rip_q      model len=11  assembler says 7   48813df51fc0ff
movabs_q       model len=10  assembler says 7   48b88877665544
mov_fs_abs_q   model len= 9  assembler says 7   64488b04252800
```

**Diagnosed from the data alone, with no Linux machine.** Every reported byte string is a strict
**prefix** of the model's, cut at a constant 7 — `movabs_q` is `48b8 8877665544 | 332211`. A cut that
does not vary with the instruction is a **column width**, not an encoding disagreement: the assembler
emitted the same bytes and the *reader* stopped. **The model is right; the harness truncates.**

**The cause.** GNU objdump (binutils, on the x86-64 CI runner) wraps its hex dump at seven bytes per
line and continues on the next line with an address and **no mnemonic**; LLVM objdump (Apple, on the
arm64 developer machine — `Apple LLVM version 21.0.0`) puts them all on one line. The parse matched
bytes on ONE line, so on Linux every instruction over seven bytes lost its tail.

⇒ 🔑 **D83's OWN RULE, ONE PLATFORM OVER, PLUS THE HALF IT DID NOT SAY.** D83 wrote *a harness that
truncates its own reading cannot see a model that truncates the same way*, and *column-filling is a
property of the widest datum*. What it missed is that **the column belongs to the TOOL, not to the
data** — so the widest datum has to be tried against every tool the project will use. Here that is
not a hypothetical second tool: CI is deliberately x86-64 because that is the lane plan v1 §4.4's
hardware co-simulation runs on.

⚠️ **And the direction is the dangerous one again.** The gate reported `len=7` for a ten-byte
instruction, so a model that had truncated to 7 would have **agreed with it**. It fired only because
the model is right — the same reason D83 fired.

⚠️ **AND IT WAS INVISIBLE FOR FORTY-NINE COMMITS BECAUSE OF D88.** This is a live gate failure that a
non-parsing workflow file had been hiding. The two findings compound: an absent CI does not merely
fail to catch new defects, it **conceals the ones already present**, and it conceals them behind a
red tick that looks like a check with an opinion.

**The decision.** One `parse_objdump(text)` used by **both** call sites — D83's lesson was that the
two are the same literal and a repair applied to one half-lands. A byte line whose bytes are followed
by nothing is a continuation and is appended to the instruction it continues, guarded by **address
arithmetic**: a continuation must begin exactly where the previous instruction's bytes ran to, and a
label resets the chain. This is the same treatment the `f0` LOCK prefix already gets in this file.

**The gate runs on EVERY invocation, not behind `--selftest`.** It is pure string processing —
microseconds — and it is the only thing on an arm64 Mac that can hold the Linux path, because macOS
objdump cannot produce a wrapped sample. A check this cheap should not be skippable.

⚠️ **The third sample exists because the first two could not see the guard.** With the
address-arithmetic condition deleted, the GNU and LLVM samples both still passed: every neighbouring
line in them carries a mnemonic, so nothing was ever swallowed, and **a control drawn from that half
of the space is silent about over-eager folding**. `_GAP_SAMPLE` puts a mnemonic-less line at a
non-contiguous address; without the guard `gap_q` reads five bytes instead of three. Probed both ways:
folding off ⇒ `movabs_q` truncates to 7 (the CI defect, restored); guard off ⇒ the gap arm fires.

**Reversal cost:** one function, two call sites, three samples.

## D90 — the first vector semantics, and the arm that did not fire (P2 vector wave, batch 2)

**What landed.** `Op.vmov` and `Op.vbin`: `movdqa`/`movdqu` register-to-register and the eleven
packed integer operations `paddb/w/d/q`, `psubb/w/d/q`, `pxor`, `pand`, `por`. Sixteen vectors, 13
new mnemonics, no memory forms. This is the batch that makes batch 4's channel **non-vacuous** —
until now nothing in the roster wrote an XMM register, so by D27 the comparator was watching sixteen
constants and agreeing about them.

### 1. Three design decisions, each with its reason

**`movdqa` and `movdqu` are ONE constructor with an `aligned` flag, and two roster rows.** They are
different *opcodes* (`66 0f 6f` against `f3 0f 6f`), so unlike `sal`/`shl` they are not one encoding
under two spellings and the model must not print one name for the other. Between registers the flag
is inert, because the alignment rule is stated of a **memory** operand — a claim about the
architecture, so it is a theorem (`vmov_aligned_irrelevant`) and not the comment that first stated
it. It becomes load-bearing the day the memory forms land, which is the day the two stop agreeing.

**The lane WIDTH is in the kind; the lane COUNT is derived from it.** `Size` in this model means the
width of one value, and a packed operation has two widths that are both essential and neither of
which is that one. A first draft of `vlanes` took the count as an argument — `vlanes 32 (·+·) a b 4`
— which is a width and a count side by side, i.e. two sources for one fact, where the wrong pair is a
silently truncated register rather than a type error. `128 / w` cannot disagree with `w`.

**The packed forms name no `Operand` and claim no P1 roster row.** `Operand` is the GPR/memory/
immediate vocabulary; an XMM register is a different register *file*. And `docs/P1-ROSTER.md` is
**derived** from K's tree with an exclusion that has read, since P1, *any operand `xmm`/`ymm`/…: SIMD,
plan v1 §5 P2* — so there is no `paddd` row there to claim and there never was. The alternative was
considered and refused: admitting SIMD to the P1 roster edits a derived artifact's exclusion rule,
which moves the 525-row denominator and therefore every coverage percentage this repository has
published, in a batch whose subject is semantics. A denominator change is its own batch. The sixteen
vectors are exempted **with that reason recorded**, gated in both directions like every other entry.

### 2. ⛔ THE FINDING: AN ARM THAT DID NOT FIRE, AND A COMMENT THAT SAID IT WOULD

`wrongVmovFixedRegisters` makes every `movdqa`/`movdqu` move xmm1 into xmm0 whatever it encodes. Run
against the first sixteen vectors it was **not caught**:

```
⛔ movdqa/movdqu ignore their register fields: comparator reported ZERO unexplained
   disagreements against a KNOWN-WRONG model. The comparator does not work.
```

Both `vmov` vectors moved xmm1 into xmm0, so the wrong model was **bit-identical** to the real one on
every vector in the table. **`Op.vmov`'s register fields were decoded by nothing**, and the
differential's `unexplained=0` said nothing whatever about them.

⚠️ **And the arm's own comment asserted it was covered** — by `paddd_x2x3`, which is a `.vbin` and
cannot exercise `vmov`'s operands at all. The pairing was *claimed in prose* and was false.

⇒ 🔑 **P1 BATCH 20'S RULE, IN THE VECTOR WAVE: ASK WHAT A PREDICTED GREEN DOES NOT CONTAIN.** Three
order claims went nineteen batches untested there because every vector named an operand that could
not distinguish them; here two vectors shared a register pair and one line of decoding went untested
from the moment it was written. The repair is `movdqa_x4x5` and `movdqu_x4x5`, and **the pairing is
proven by the failure rather than asserted**: the arm demonstrably did not fire before they existed
and fires in 164 cases after — the deletion experiment, run in the only direction that needs no
faith.

⚠️ A second, smaller instance in the same arm: with the vectors added it was caught but **in the
wrong field** — 328 disagreements, none in the declared `xmm2`, because the new vectors write `xmm4`.
The arm requires the disagreement *in the field the bug is in*, and that precision is what turned a
green into a correction.

### 3. ⚠️ The arm that COULD have passed silently, and did not

A wrong **lane width** is invisible unless some lane actually carries across its boundary: if every
xmm lane in the pre-state pattern were small, `paddd` and `paddq` would agree on every case and the
run would report agreement about a rule it never tested. `wrongVbinLaneWidth` computes every packed
add and subtract at 64-bit lanes and is **caught in 355 cases**, so batch 4's deliberately non-zero,
non-constant pre-state pattern does exercise the lane boundary. That is why the batch is not sealed
on `unexplained=0` alone.

`psub computes SRC - DEST` is caught in 328 cases (the adds and the bitwise trio are commutative and
cannot see it, which is why it is a separate arm). `a packed operation writes ZF` is caught in 696 —
"Flags Affected: None" is on every SDM entry in the group, and reaching for `BinKind`'s flag
machinery by analogy is the easiest way to get a packed operation wrong.

### 4. What this batch does NOT claim

No memory form. They need a 128-bit memory path (`readMem`/`writeMem` are defined at `Size`, which
stops at 64) **and** they are where `movdqa` and `movdqu` stop being the same instruction — an
unaligned `movdqa` is #GP. That is a semantic question of its own and it gets its own batch rather
than riding in on this one.

**Reversal cost:** two `Op` constructors, one combinator, sixteen vectors, four arms.

## D91 — the oracle does not implement `movdqa`'s alignment check, so the model's most interesting new rule has no second source (P2 vector wave, batch 3)

**What landed.** `Op.vload` and `Op.vstore`: the memory forms of `movdqa`/`movdqu`, a 128-bit memory
path, and the point at which those two mnemonics **stop being the same instruction**. `aligned` was
inert in `vmov` because between registers there is no address; here it decides whether the access
happens at all.

### 1. The measurement that shaped the batch

An unaligned `movdqa` is **#GP(0)** in hardware (SDM Vol. 2B, MOVDQA). Before writing a vector for
it, the oracle was asked — by execution, not by reading its source:

```
movdqa (%rbx),%xmm0   @0x2000 aligned        -> executed
movdqa 8(%rbx),%xmm0  @0x2008 UNALIGNED      -> executed      ⛔
movdqu 8(%rbx),%xmm0  @0x2008 unaligned      -> executed
movdqa %xmm0,8(%rbx)  @0x2008 UNALIGNED      -> executed      ⛔
movl %ecx,(%rbx)      (control)              -> executed
```

**ACL2 x86isa does not implement the alignment check.** It executes the form that hardware faults on.

### 2. ⇒ The decision, and why it is not the comfortable one

The model **faults** — `byDesign`, the same class `lockIllegal` uses, because the claim is *"this
model says: it faults"* and not *"this model cannot say"*, and that distinction decides a coverage
tier (D34).

⛔ **And therefore no unaligned `movdqa` vector is shipped.** One would produce a **one-sided
refusal** in every pre-state; `classify` correctly calls that the `refusal` class and counts it
**unexplained**. The run would go red about a model that is right.

⇒ 🔑 **THE ORACLE IS EVIDENCE, NOT THE SPECIFICATION — AND THIS IS THE FIRST TIME IN THIS PROJECT
THAT THE DIFFERENCE HAS COST SOMETHING.** Batch 18 found the SDM *wrong* twice and followed x86isa
and K against it. Here the arrow reverses: the oracle is **incomplete**, and following it would make
the model silently compute a result where hardware raises #GP — the exact direction TRUSTBASE exists
to prevent. Agreement with an oracle that does not implement a rule is not evidence about that rule.

**So the rule is carried by theorem instead of by run:** `vload_unaligned_faults`,
`vstore_unaligned_faults`, and — the half that makes the pair mean something —
`vload_unaligned_movdqu_runs`, which says `movdqu` at the *same* address does **not** stop. Without
that second theorem, "movdqa faults" is consistent with "every unaligned access faults", and the
flag would not be doing the discriminating.

⚠️ **Stated plainly, because it is the weakest claim in the repository:** this rule has **no second
source**. It rests on the SDM and on a Lean proof that the model implements what I read there. It is
recorded in TRUSTBASE.md and it is a concrete, named item for the hardware co-simulation lane, where
real silicon **is** the oracle for it — a better argument for that lane than the BMI group the
co-sim design was commissioned on and priced at a rounding error.

### 3. ⛔ An arm deliberately NOT added

The obvious arm — *"`movdqa` ignores its alignment requirement"* — cannot be caught, because no
unaligned `movdqa` vector exists or can. Adding it would place a **permanently silent entry** in a
list whose entire value is that every entry fires.

⇒ 🔑 **AN ARM NO VECTOR CAN DISTINGUISH IS NOT A WEAK TEST; IT IS A FALSE ENTRY IN THE GATE'S OWN
INVENTORY** — the same defect as D90's arm that did not fire, except that there the repair was a
vector and here no vector is possible, so the honest move is to leave it out and say why.

The three arms that *can* fire are shipped: a load that reads only eight bytes, a store that writes
only eight, and **`movdqu` applying `movdqa`'s check** — which is what `movdqu_load_unal` exists for,
being the table's only vector at an address that is not 16-byte aligned.

### 4. Two smaller decisions

**`vload`/`vstore` rather than one constructor over a `VOperand` pair.** An operand type admitting
both `xmm` and `mem` on either side can represent `movdqa (%rax), (%rbx)`, which no encoding
produces — the model would then need a well-formedness *check* where it can instead have a type that
cannot say it. `Op.mov` is stuck with `wellFormed2`; these are not.

**`readMem128` composes two 64-bit reads rather than opening a new byte recursion.** `readMem` is the
path every memory vector since P0 has exercised and its endianness is settled by 500 roster rows of
evidence; a second recursion beside it is a place for the two to disagree.

⚠️ And the vector stores exposed that `claimsMemDestLoose` is **vocabulary-bound**: its literal is
`m,r`, so it is blind to `m,x`. Recorded in `memDestSweep` rather than repaired — that function
exists only to be compared against, and teaching it `x` would erase the divergence the theorem is
there to pin down.

**Reversal cost:** two constructors, two memory helpers, five vectors, three arms.

## D92 — sharding the harness selftest, and the seam that sharding creates (P2 vector wave, batch 4)

**The measurement.** D88 said the first real CI run should answer whether step 9 fits inside a CI
job rather than guessing. It answered: **it dominates.** Two runs sat inside the harness selftest for
hours while every other step finished in minutes. The cost is **arms × vectors**, and *both* grow
every batch — 23 arms over 46,320 cases at P1 batch 14, **90 arms over 70,950 cases** here, ~2.6 min
per arm marginal. Its own comment still says "twenty minutes".

**The decision: shard it, and trim nothing.** The arms are independent by construction, so
`selftest-shard k n` runs the arms whose index is `≡ k-1 (mod n)` and the CI matrix runs `k = 1..6`
in parallel. Every arm still runs on every push; they merely run beside each other.

⚠️ **STRIDE, NOT CONTIGUOUS BLOCK.** Arms differ in cost — the string group's are dearer than the
flag singles' — so a contiguous split leaves the wall-clock decided by whichever shard inherited the
expensive neighbours.

### ⛔ The real content: sharding a coverage gate is how a coverage gate stops covering

If the split is wrong, some arms run twice (harmless) or **never** — and the failure is invisible,
because every shard that *does* run reports PASS and the job is green. That is this repository's
recurring defect introduced into the instrument that finds it. Two things stand against it:

**1. The partition is arithmetic, computed from `selftestArms.length` and written down nowhere.**
Adding an arm cannot leave it uncovered. `selftest-shards n` proves shards `1..n` name every arm
**exactly once** — it runs no arm, costs milliseconds, and is in the `build` job beside the shards it
describes. Probed by planting an off-by-one in the selection: `shards 1..6 name 75 arm slots for 90
arms`.

⚠️ **Its first draft was a tautology, and that is worth recording because it is the SECOND time in
one session.** The gate recomputed `i % n == j` for itself, so it agreed with the shard because both
had been written from the same sentence and would have gone on agreeing if the shard's rule changed
underneath it. Exactly the defect in `check_driver_cr4.py`'s first selftest (D86). ⇒ **Naming a class
confers no immunity from it.** Fixed by one `shardIndices`, two callers.

**2. The seam the arithmetic cannot reach is the ORCHESTRATOR.** The divisor `6` is written in
`ci.yml` twice — the length of `matrix.shard`, and the command's argument — and if they disagree the
arithmetic stays perfect while whole residue classes never run. A matrix of `[1,2,3]` against a
command saying `6` runs half the arms, and **every shard log says PASS, because each shard really did
pass.**

⇒ 🔑 **SHARDING MOVES THE COVERAGE QUESTION OUT OF THE CODE AND INTO THE ORCHESTRATOR, WHERE NONE OF
THIS REPOSITORY'S OTHER GATES CAN SEE IT.** `scripts/check_ci_shards.py` is the gate for that one
seam, and it is probed four ways, each a distinct way the seam fails:

| plant | caught |
|---|---|
| matrix `[1,2,3]` against divisor 6 | `[4, 5, 6] would never run` |
| a literal `k` instead of `${{ matrix.shard }}` | every job runs the same shard and all pass |
| partition gate asserting a different `n` | the gate describes a different split |
| a gap in the matrix (`[1,2,3,4,5,7]`) | `[6] would never run` |

**Cost.** The Lean build now happens in two jobs rather than one, which is the price of the
parallelism and is paid in machine time, not in coverage.

**Reversal cost:** two commands, one gate, one matrix.

## D93 — the differential found a defect in ACL2 x86isa, and K is what settled it (P2 vector wave, batch 5)

**Forms.** `movd` and `movq` across the register files — rank 4 (3.05%) and rank 8 (2.05%) of the
measured demand list, the highest-demand forms this model did not have, and the first here whose two
operands live in **different register files**.

### 1. The run went RED, and the model was right

Five vectors were written. The differential returned **159 unexplained `spec` disagreements**, all of
them in exactly two vectors:

```
movd_to_x   81 of 86      movq_to_x   78 of 86
movd_to_x/18  lean=…000000aaaaaaaa   oracle=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
movd_to_x/14  lean=…000000000000000   oracle=00000001000000000000000100000000
```

The oracle preserved the destination's upper bits and wrote only the low 32 (or 64). **ACL2 x86isa
merges where the specification says clear.**

⚠️ **And that is precisely the wrong model this batch had already planted as an arm** — *"movd/movq
into XMM merge instead of clearing the upper bits"*, which fired in 151 cases against the Lean model.
The arm and the oracle implement the same mistake.

### 2. ⭐ It is not this repository's word against the oracle's — K settled it

`vendor/k-x86-64`, public and already relied on for the P1 and P2 rosters, gives:

```
movd r32 -> xmm :  concatenateMInt( mi(96, 0), extractMInt(R1, 32, 64) )
movq r64 -> xmm :  concatenateMInt( mi(64, 0), getParentValue(R1) )
movq xmm -> xmm :  concatenateMInt( mi(64, 0), extractMInt(R1, 192, 256) )
```

Ninety-six (or sixty-four) **zero bits** and then the datum. SDM Vol. 2B, MOVD/MOVQ: `DEST[127:32] ←
0`. ⇒ **Two independent public models and the manual agree with this model; x86isa is alone.**

⇒ 🔑 **THE THIRD SOURCE IS WHAT TURNS A DISAGREEMENT INTO A FINDING.** With two models, a red run
says only *"one of you is wrong"*, and the tempting reading — the oracle has 500 roster rows of
credibility behind it — is the wrong one here. K costs nothing to consult and it decides the
question. D91 had no third source and had to say so; this one has one and uses it.

⚠️ **The defect is DIRECTIONAL, and that sharpens rather than softens it.** x86isa gets
`movq %xmm1,%xmm0` right (it zeroes the upper quadword) and gets both out-of-XMM directions right.
Only GPR → XMM is wrong. A model that were simply "vague about upper bits" would have failed all
five; failing exactly two is the signature of a specific defect, and it is why the other three
vectors stay in the table and remain differentially validated.

### 3. The decision, and the coverage it costs

The two into-XMM vectors are **removed**; the semantics and the roster rows stay. The rule is carried
by `vmovg_to_xmm_zeroes_upper` — and the arm that guarded it is **removed with them**, because with
no vector it could never fire again, and *an arm no vector can distinguish is a false entry in the
gate's inventory* (D91), not a weak test.

⚠️ **Stated as a cost, not a tidy ending:** this repository now has **two** rules its oracle cannot
check — the `movdqa` alignment fault (D91, oracle *incomplete*) and this one (oracle *wrong*). Both
are proved and neither is differentially validated.

⭐ **Both point at the same next mechanism.** Removing a vector stops the test **permanently and
silently**: if x86isa is fixed tomorrow, nothing notices. A *declared known-divergence channel* — a
per-(vector, field) list carrying its third-source citation, gated in **both** directions so it fires
when the divergence disappears — keeps the 164 cases running and deletes itself when the oracle
catches up. **That is my recommendation for the next batch**; it is not done here because it changes
`classify`, the most load-bearing instrument in the repository, and that deserves its own red-first
batch rather than riding in on this one.

### 4. What survives, and what it proves

`movd_from_x`, `movq_from_x` and `movq_xx` remain and agree with the oracle. Their arms fire:

| arm | caught in |
|---|---|
| `movq xmm,xmm` copies all 128 bits instead of zeroing the upper quadword | 76 (`xmm0`) |
| `movd` out of XMM does not zero-extend its 32-bit GPR write | 35 (`rcx`) |

⭐ Out of XMM needed **no code at all**: `Cpu.setReg` already zero-extends at `.d`, and that the rule
applies unchanged across a register-file boundary is the reason there is nothing here to read.

⚠️ Neither arm fires in all 82 of its cases, and that is **correct rather than a shortfall** — the
adversarial value list contains zeros, and where the bits a wrong model fails to clear were already
zero the two models genuinely agree. A count equal to the case count would have been the suspicious
reading.

**Reversal cost:** two constructors, three vectors, two arms, two roster rows.

## D94 — prose in a field the kernel walks character by character, and a ceiling measured against a ±2× quantity (P2 vector wave, batch 6)

**Found by CI**, on the first run in which step 11 had ever executed: `kernel-cost selftest: FAIL (1
of 5 arms)` — and the arm that failed was the **control**, *"the shipped ceilings PASS"*. All three
red arms fired correctly; the gate was working and the tree was over.

### 1. The cause was mine, and it is D72's lesson in a new place

```
memDestSweep    30700 ms    ceiling 19360    OVER ⛔
```

`claimsMemDest` walks `Row.shapes` **character by character** (`memDestFromShapeStart` recurses on
`r.shapes.toList`), and `memDestSweep` reduces it over every row in a kernel `decide`. Batches 3 and
5 wrote *explanatory prose* into that field — the longest was **285 characters** — because the
caveats felt worth recording:

> `"r,x — 32 bits ACROSS the register files, out of XMM, where the GPR write zero-extends to 64. The
> x,r direction is MODELLED and PROVED (…) but has NO VECTOR: x86isa MERGES where the SDM and K both
> say CLEAR, so it cannot be differentially validated — D93"`

⇒ 🔑 **A COMMENT IN A STRING THE KERNEL REDUCES IS NOT A COMMENT — IT IS A COST.** D72 recorded the
same shape (an AST walk costing 4,200 ms, "almost all of it `String.toList` over 784 literals") and
the repair there was to stop reading strings in the kernel. Here the strings stayed and I made them
longer. The shapes column is a **shape list**; every caveat in it belongs in the decision note where
it already was. Shortened to ≤118 characters: `memDestSweep` **30,700 → 15,400 ms**.

### 2. ⚠️ And the gate is measuring a quantity that swings by 2×

Three readings, same tree, same machine:

| | run 1 | run 2 | run 3 | ceiling |
|---|---|---|---|---|
| `memDestSweep` | 30,700 ⛔ | 17,900 | 15,400 | 19,360 |
| `X86.Theorems` | — | 1,300 ⛔ | 753 | 1,100 |
| `Tests.Anchors` | 469 | 929 ⛔ | 463 | 801 |
| module total | 44,600 | 34,500 | 29,500 | |

Run 2 reported **three modules over** that run 3 clears by a factor of two, on a tree that differed
only in string literals which cannot affect `Tests.Anchors` at all.

⇒ **The prose fix is real and the run-2 overages were noise, and telling those apart needed a third
reading — not an argument.** Had I raised three ceilings after run 2, I would have permanently
widened a gate to accommodate a busy laptop. *A number is worth as many independent routes as agree
on it*, and a timing figure carries no conditions with it.

⚠️ **Recorded as an open weakness, not repaired here:** a fixed ceiling against a ±2× measurement
will fire spuriously, and CI runners are noisier than this machine. The honest repairs are a best-of-N
reading, or ceilings stated with a stated noise margin, or a re-run policy — each a decision, none of
them "raise it until green". What must NOT happen is a ceiling raised to fit whichever reading
someone took first.

⚠️ **A diagnosability gap, worth one line:** the control arm prints only *"control: the shipped
ceilings PASS"* and discards the plain run's output, so the CI log said a control failed and never
said which declaration was over. The local re-run is the only reason this was diagnosed. The arm
should print `r.stdout` on failure.

⚠️⚠️ **CORRECTION, on six readings rather than three — the "±2×" above is TOO STRONG.** Three further
readings taken back-to-back on the same tree:

| | run 4 | run 5 | run 6 | spread |
|---|---|---|---|---|
| `memDestSweep` | 18,000 | 17,700 | 17,800 | ±1% |
| `X86.Theorems` | 728 | 711 | 724 | ±1% |
| `Tests.Anchors` | 464 | 480 | 477 | ±2% |
| module total | 31,900 | 31,700 | 31,500 | ±0.6% |

The measurement is **stable to a few percent**. Run 2 was a single outlier taken under load, and I
generalised from it to "a quantity that swings by 2×" — a claim three readings could not support and
six readings refute. ⇒ **A number is worth as many independent routes as agree on it, and that
applies to my own conclusions as much as to the repository's.** The *specific* judgement that run 2's
overages were noise was correct, and so was refusing to raise ceilings on it; the *general* claim
about the gate was not.

⇒ **And the corrected picture changes the diagnosis.** Every local reading sits comfortably under its
ceiling while CI fails the same step twice — so CI is **systematically slower**, not noisy, and a
noise margin is the wrong remedy for it. A ceiling calibrated on one machine cannot be enforced on
another at all; the principled repairs are to calibrate on the CI machine, or to make the gate a
RATIO against a reference declaration measured in the same run, which cancels machine speed. The
choice waits on CI's actual numbers (D94's diagnosability fix, `d45804f`, is what will supply them).

**Reversal cost:** fifteen string literals.

## D95 — the known-divergence channel: keeping a test alive when the ORACLE is the one that is wrong (P2 vector wave, batch 6)

**The problem this repays.** Twice the differential has been right and the oracle wrong — `movdqa` at
an unaligned address, which x86isa does not fault on (D91, oracle *incomplete*), and `movd`/`movq`
into an XMM register, which x86isa merges where the SDM and K both say clear (D93, oracle *wrong*).
Both times the remedy was to **delete the vector**, and D93 said plainly what that costs:

> Removing a vector stops the test **permanently and silently**: if x86isa is fixed tomorrow, nothing
> notices.

### 1. What it is

`knownDivergences` names a **vector-id prefix**, **one field**, an **independent source**, and the
decision note. A disagreement matching an entry is classified `oracle-divergence` — **not matched and
not explained**, its own class, counted in the header of every run:

```
cases=71380 matched=51335 explained=28774 unexplained=0 oracle-divergence=159 oracle-leaks=0 missing=0
```

The two into-XMM vectors are **back in the table** and compared on every run.

### 2. ⛔ Why this is the most dangerous list in the repository, and the three things that make it safe

A place to put disagreements is a place to hide red. So:

**It is gated in the OTHER direction.** An entry that produces *no* disagreement is a **failure**:

```
⛔ DECLARED ORACLE DIVERGENCES THAT DID NOT OCCUR:
   mov_q / rax (PROBE) — declared divergent against: FABRICATED for the probe
   Either the oracle was FIXED (delete the entry …) or this model has drifted into
   agreeing with a known-wrong answer.
```

Without that arm, an entry whose divergence had gone would excuse a field forever, invisibly —
nothing prints a rule that never fires.

**Every entry carries its third source, and that is the admission price.** A two-model disagreement
names no culprit (D93). An entry asserts that an *independent* public authority — K by file, the SDM
by section — agrees with **this** model against the oracle. Without that, the list is just somewhere
to put red.

**It is narrow by construction:** one vector prefix, one field. It cannot excuse a whole vector, nor
a field it did not name.

⚠️ **And the scoping matters more than it looks.** `classify` takes the list as a **parameter**, and
`driveWrong` passes `[]`. A declared divergence is a statement about this model against the *oracle*;
the selftest compares this model against a deliberately wrong copy of *itself*, where an oracle's
defect is irrelevant. Passing the same list to both would have let a declared oracle divergence
quietly excuse a **planted bug** — and the planted bug here, `wrongVmovgPreservesUpper`, is *exactly*
the mistake x86isa makes.

### 3. Probed in both directions

| plant | result |
|---|---|
| a declared divergence that does not occur | `rc=1`, names the stale entry and both causes |
| a real entry deleted | `rc=1`, `unexplained=81` resurfaces as `spec`, `oracle-divergence=78` |

The second is the one that proves the entries do real work rather than decorate: delete one and the
red comes straight back.

⭐ **The arm that was removed at batch 5 is restored with its vectors.** D93 removed it because an arm
no vector can distinguish is a false entry in the gate's inventory; the vectors are back, so the arm
has a subject again.

**Reversal cost:** one structure, one list, one parameter, one gate.

## D96 — the unpack group: an operation that computes nothing and only chooses (P2 vector wave, batch 7)

**Forms.** `punpckl{bw,wd,dq,qdq}` and `punpckh{bw,wd,dq,qdq}` — eight mnemonics, ~4% of the measured
gap (ranks 13, 18, 21 and neighbours). The first vector operations here that are a **permutation**
rather than lane-wise arithmetic.

**The rule, generalised once rather than eight times.** For lane width `w` the result is
`128 / (2w)` pairs, pair `i` being `dst[base+i] : src[base+i]` with the destination in the **low**
half of each pair — `base = 0` for `punpckl`, `base = pairs` for `punpckh`. As with `vlanes`, the
**count is derived from the width** and never passed, so a width and a count cannot disagree.

⭐ **Checked by evaluation before the oracle was asked.** Five hand-computed cases (`punpcklbw`,
`punpckhbw`, `punpcklqdq`, `punpckhqdq`, `punpckldq`) on a byte-ramp pre-state, all `true` — seconds,
against thirty minutes for a differential run. objdump prints the interleave in its own disassembly
comment (`xmm0 = xmm0[0],xmm1[0],xmm0[1],xmm1[1],…`) and K's `punpcklbw_xmm_xmm.k` gives the same
order, so the expected values came from two sources rather than from my reading of one.

### ⚠️ An arm that measures the PRE-STATES rather than the model

`punpckl` and `punpckh` read **disjoint halves** of their inputs. So a pre-state whose two halves
happened to agree could not tell them apart, and a green run would say nothing about which half is
read. That is a property of the XMM pattern, not of the rule, and it was written into the AST comment
as a *worry* — then measured:

| arm | caught in |
|---|---|
| `punpckl` and `punpckh` read each other's half | **656** = 8 × 82, every case |
| an unpack interleaves source-first instead of destination-first | **656**, every case |

Both fire in **all** their cases, so batch 0's pre-state pattern distinguishes the halves everywhere.
⇒ **The worry is now a measurement.** Writing it down as a caveat would have been the cheap move;
running the arm turned it into a fact, and had the number come back small *that* would have been the
finding.

**Reversal cost:** eight kinds, one combinator, eight vectors, two arms.

## D97 — a machine-calibrated gate cannot be enforced on another machine, and the repair is WHERE it runs, not HOW LOOSE it is (P2 vector wave, batch 8)

**The measurement, at last.** D94's diagnosability fix (`d45804f`) made the control print its
reading, and CI answered twice:

| module | CI-1 | CI-2 | local (×6) | CI/local |
|---|---|---|---|---|
| `X86.Syntax` | 418 | 436 | ~145 | **3.0×** |
| `X86.Theorems` | 1530 | 1640 | ~721 | **2.3×** |
| `Tests.Anchors` | 928 | 1030 | ~474 | **2.2×** |
| `memDestSweep` | 27,400 | 29,800 | ~17,800 | **1.7×** |
| `vectorCoverage` | 5,590 | 5,860 | ~1,900 | **3.1×** |
| total | 61,400 | 66,100 | ~31,700 | 2.1× |

Every module over, on a tree that passes locally with ~1% spread. **A fact about the hardware, not
about the tree.**

### 1. ⛔ Two designs were refuted by this table before either was written

**A calibration reference** — a fixed declaration measured in the same run, ceilings as multiples of
it, so machine speed cancels — requires the machines to differ by ONE factor. They differ by
**1.7× to 3.1×**. A single constant would leave `memDestSweep` 2× slack while still failing
`vectorCoverage`. ⇒ 🔑 **A NORMALISATION IS ONLY VALID IF THE DENOMINATOR VARIES THE SAME WAY AS THE
SUBJECT** — an empirical claim about the data, not a property of the arithmetic, and easy to skip
because the formula looks principled either way. (Normalising by the *total* would have been worse
still: a defect that scales numerator and denominator is invisible to every percentage.)

**Raising the ceilings to CI's scale** was the other candidate, and this file's own history refutes
it: `kernel_ceilings.txt` records a ceiling being *lowered* 744 → 493 because *"a tripwire with 2.4×
headroom will not notice a doubling"*. Ceilings at runner scale are ~2× slack on the machine where
batches are actually developed.

⚠️ **I nearly reached the opposite conclusion by a category error**, and it is worth recording: I
argued CI-calibrated ceilings would have missed my own `memDestSweep` regression — comparing a
*local* measurement against a *CI* ceiling. A regression is measured on the machine that holds the
ceiling, so the ratio is preserved. The argument was wrong; the conclusion happened to survive on
other grounds.

### 2. The decision: change WHERE it runs

`kernel_cost.py` is **removed from `ci.yml`** and named in that file's header beside the
oracle-dependent gates — for a *different* reason, stated as such: those cannot run without an
oracle, this one cannot run without **the machine its ceilings were registered on**. The evidence
table is in the header so the next reader does not re-derive it.

**No ceiling is touched.** The gate keeps the tightness that caught a real 1.7× regression three
batches after it entered the tree.

### 3. ⭐ And the actual gap was never the ceilings — it was the schedule

The session that added the whole P2 vector wave ran `run_differential.sh` **six times** and
`kernel_cost.py` **not once**, until CI complained. The regression had been sitting in the tree for
three batches.

⇒ **A gate whose schedule is "somebody will think of it" is D65's ungated claim wearing a habit.** So
it now runs on the same trigger as the differential — the **batch** — appended to
`run_differential.sh`: ten minutes against the thirty that script already costs, running **last**,
when the oracle is done and the machine is quiet, which is the condition the ceilings were registered
under.

**Reversal cost:** one CI step removed, one line added to the batch runner.

## D98 — the census's staleness stamp caught the model moving and said nothing about the MAPPING that did not (P2 vector wave, batch 9 — OPEN, closed by D99)

**Found by CI**, on step 13, another step that had not run in 49 commits:

```
⛔ THE CENSUS IS STALE. docs/DEMAND-CENSUS.md was generated against a model of 84
   mnemonics (sha a0f1…); the model is now 107 (sha b7d0…).
```

The anti-staleness stamp is correct and it fired for the right reason: the vector wave took the model
from 84 mnemonics to 107.

### 1. The regeneration, and what it showed

The corpus was rebuilt from the recipe in the document — 10 Debian packages plus 9 debug packages,
`vmlinux` carved out of the `vmlinuz` xz payload, vlc split into its `codec` and `video_chroma`
columns (52 and 19 objects, matching the document's own counts). `demand_census.py --corpus --debug`
ran clean.

⭐ **Every column's instruction TOTAL reproduced exactly** — `cc1` 5,379,923, `coreutils` 879,551,
`vmlinux-kernel` 2,781,898, all eleven identical to the cached JSON. The corpus is reproducible from
the recorded recipe, which is the document's central claim about itself.

⛔ **AND EVERY COVERAGE PERCENTAGE WAS UNCHANGED — +0.0 IN ALL ELEVEN COLUMNS.** After the model
gained `movdqa` (12.85% of the measured gap), `paddd`, `movdqu`, `movq`, `movd` and eighteen more,
the census reported *exactly* the same coverage. The regenerated `.json` is byte-identical to the
committed one.

### 2. Why: a second list, ungated

```python
def to_roster(m):          # objdump mnemonic -> roster name
    ...
    return None            # anything outside EXACT / SUFFIXED / STRING / REPS / cc-families
```

Every vector mnemonic maps to `None`, and `covered = (r is not None and kind == "plain" and r in
model)` — so they are counted as **not covered whatever the model says**. `to_roster` is a
hand-maintained allow-list that has to grow when the roster grows, and nothing checks that it did.

⇒ 🔑 **AN ANTI-STALENESS GATE OVER TWO COUPLED ARTIFACTS REPORTS ONLY ABOUT THE ONE IT HASHES.** The
stamp hashes the MODEL. The mapping is the other half of the derivation and is invisible to it — so
the gate fired, I regenerated, and the regenerated document is still wrong. **A stamp that forces a
regeneration can make a stale number look freshly computed**, which is worse than the stamp not
existing, because the regeneration reads as diligence.

⚠️ **And the direction is the unpoliced one.** The census UNDER-claims: it reports the model covering
less of real binaries than it does. An over-claim looks like a mistake; an under-claim looks like
modesty, and nobody audits modesty.

### 3. ⛔ Why this is recorded OPEN rather than fixed

The repair is not one line. `to_roster` needs a fallback for mnemonics the roster already names — but
`_split` *also* routes any non-`plain` operand kind to `outscope`, and that rule exists to stop the
census claiming `movq %xmm0, %rax` through the roster's scalar `mov`. That exclusion was **correct**
when the model had no vector forms; it is wrong now, but only for the forms actually modelled
(register-to-register, out-of-XMM, and the memory `movdqa`/`movdqu`), and relaxing it carelessly
produces an **OVER-claim** — the direction the whole `kind` mechanism was built to prevent (its
comment records 28,019 instructions once counted as two opposite residues at once).

⇒ It is a batch: the mapping must grow with the roster, and the out-of-scope rule must distinguish
vector forms the model now covers from those it does not. Rushing it at the end of a session would
trade a known under-claim for an unknown over-claim.

**The regenerated document is deliberately NOT committed.** Its stamp would read 107 while its numbers
still under-claim — a green gate over a wrong document. The red is accurate: the census *is* stale in
the sense that matters, and it should stay loud until the mapping is fixed.

**Reversal cost:** none — nothing was changed.

## D99 — the covered/not-covered test had THREE inputs and only one was coupled to the model (P2 vector wave, batch 10)

D98's repair, taken as a batch. The inherited diagnosis was **right and incomplete**, and testing it
before acting on it is what found the rest.

### 1. The handed-on cause, verified — and then measured wider

`to_roster()` returning `None` for every vector mnemonic is real: driven over the model's own roster,
**22 of the 107 mnemonics the model has cannot be produced by the mapping at all** (`movdqa`, `movdqu`,
`movd`, the four `padd*`, the four `psub*`, `pand`, `por`, `pxor`, the eight `punpck*`). Five more
(`jcc`, `setcc`, `cmovcc`, `movsx`, `movzx`) are roster names objdump never prints and are not a gap.

But the decision it feeds has **three conjuncts**:

```python
covered = (r is not None and kind == "plain" and r in model)
#          └─ the mapping    └─ the operands    └─ the model
```

and the middle one was never in the diagnosis. `kind != "plain"` was written when the model had no
vector registers, no segment base and no LOCK vocabulary. **All three have since landed** (P2 batches
1, 2 and 3, and 4–9), and the rule did not move. So the census was also refusing:

- **76,591 instructions** carrying an `%fs:`/`%gs:` prefix — P2 addition 1 put that base on `Ea`;
- **20,053 instructions** spelled `movabsq`, which nothing mapped at all — P2 addition 3 landed the
  form and changed no semantics, so the model has always been able to execute it;
- **53,822 instructions** of `movq` between an XMM register and a GPR or memory — a P2 batch-5 row.

⇒ 🔑 **AN INHERITED DIAGNOSIS IS A HYPOTHESIS AND SO IS ITS SCOPE.** The named cause was true; the
handed-on repair — "make `to_roster` see the model, relax `_split`" — would have left the segment and
`movabs` gaps in place, and there is nothing in a green run that would have said so.

### 2. What the fix is, in each of the three places

**The mapping** gains an identity rule, LAST, after every rewrite rule: a mnemonic the model names
maps to itself. That is the vector allow-list, DERIVED — the list cannot go stale because there is no
list. `movabsq`/`movabs` join `EXACT` as `mov`.

**The one collision is resolved by the operands, not by a guess.** `movq` is two instructions: the
64-bit GPR move (roster `mov`) and the SSE2 move (roster `movq`). Resolving it by mnemonic alone must
be wrong about one of them, so `to_roster` now takes the ISA bucket `isa_bucket` already computed —
not a second reading of the operand string, which would be a second rule that can disagree.

**The scope rule** becomes `EXT_SCOPE`, a **total partition** of the ISA buckets into what the model's
state can represent and what it cannot, and `form_in_scope` **refuses** on a bucket nobody has ruled
on. An allow-list would send an unclassified bucket to COVERED and a deny-list to NOT COVERED; both
are a default, and a default is how this document came to report +0.0. The GPR buckets are derived
from `GPR_EXT` rather than restated.

⛔ **`lock` stays out of scope, as a REFUSAL rather than an absence.** P2 addition 2 landed, so the
model does execute locked forms — but only the SDM's nineteen, and that predicate is `Op.lockIllegal`,
which none of this tool's inputs publish. Claiming a locked form by MNEMONIC would credit the model
with `lock movq %rax,(%rbx)` — `#UD` on silicon, and the form a reader most expects to be lockable.
Cost of the refusal, printed rather than swallowed: **9,945 instructions, 0.07% of the corpus**. The
refusal names the cheaper build (export the predicate) instead of asking for an exemption.

### 3. The result, and the independent route that checked it

| column | before | after |
|---|---|---|
| cc1 | 97.4% | 98.8% |
| coreutils | 95.0% | 97.1% |
| glibc | 81.1% | 85.6% |
| dav1d | 46.9% | **60.6%** |
| ffmpeg | 89.6% | 93.2% |
| vlc-codec | 94.8% | 97.2% |
| vlc-video_chroma | 52.2% | **75.6%** |
| vpx | 60.2% | **84.1%** |
| x264 | 78.3% | 84.8% |
| vmlinux-kernel | 98.0% | 99.5% |

The uncovered gap the P2 roster is priced against goes **918,395 → 534,576**, and `movdqa` — ranked
**#1, 12.85% of the gap** — leaves the candidate list, along with `paddd`, `movdqu` and `movq` at
ranks 2, 3 and 4. The census was telling P2 to implement what P2 had already implemented.

⛔ **A jump that large in the flattering direction is exactly when not to believe the instrument**, so
the numbers were checked against a source that is not this tool: raw `objdump` over the ffmpeg column.
`paddw` with an `%mm` operand: **2,303** — the census's excluded MMX count, to the instruction.
`paddw` with `%xmm`: **6,754**, and 6,754 + 2,303 is exactly the 9,057 by which the `paddw` residue
fell. `movdqa`: **27,450**, exactly the newly-covered count. Two independent origins, agreeing per
mnemonic ([[feedback-two-readings-are-not-two-witnesses]] — this time they are two).

⚠️ **And the residues that GREW are a reclassification, not a leak.** An MMX `paddw` used to be
"a mnemonic this tool cannot map"; it is now "a mnemonic the model HAS, in a register file it does
not" — the accurate residue, and the one the P2 join needs. The conservation identity
`covered + uncovered == total` holds in every column before and after.

### 4. The stamp, which could not have seen any of the above

The stamp hashed the model. It now carries a second sha over **the mapping's behaviour**: every
decision `_decide` makes over a domain that needs no corpus — every mnemonic any table in the file can
rewrite, crossed with every bucket `EXT_SCOPE` rules on. Behaviour, not source text, so a reworded
comment does not fail it and a changed ANSWER does. The failure message now names **which half moved**,
because D98 was a red that said "the model moved" about a document whose numbers could not move.

⛔ **And the arm that proves the stamp can go red was itself stale.** The selftest planted a
DIFFERENT model by writing a stamp as a literal in the old two-field format — so when the stamp grew
a third field the substitution matched nothing, wrote nothing, and the arm was testing a document with
no stamp at all. The plant is now DERIVED from the shipped stamp by flipping one hex digit of the half
under test, and there is a second plant for the mapping half — D98's own case, gated.

### 5. Three more defects the batch surfaced

⛔ **`ext_table` carried a second copy of the covered/not-covered test.** `_split`'s docstring has
claimed since D66 that it is "the one place the decision is made"; forty lines below it, the loop that
builds the P2 candidate list re-implemented the same three conjuncts. It agreed for twenty-two batches,
which is why nobody looked, and it would have diverged on *this* edit — leaving the headline repaired
and the candidate list computed by the old rule. Both now call `_decide`, and a **conservation arm**
(covered + the ext buckets == the column total, exactly) makes any future second implementation
observable rather than a matter of reading.

⛔ **A justification outlived the condition it was true of.** The header comment read *"Both now count
as NOT COVERED, so the headline number is honest by construction"* for twenty-two batches after both
had stopped being true, and the published preamble listed *"four ways a mnemonic-level count
over-claims are excluded"* when two of the four were no longer excluded. Prose explaining why an
exclusion is rigorous **reads as a reason not to look at it**.

⛔ **The P2 roster's arm was gated in one direction.** It asserted that each of the three additions
names a bucket the census emits — true exactly while the addition is *undelivered*. It went red when
two of them landed. The honest reading is not that the arm broke: a delivered item still showing as a
gap is the same defect as a stale census, so the arm now requires ABSENCE for an addition in scope and
PRESENCE for one still refused. And because a bucket that vanishes because the model GAINED it reads
identically to a bucket nobody needed, the census now records its **covered** buckets too, and the
document prints "LANDED — *n* instructions now counted as covered" instead of a bare zero.

### 6. A finding about the probe, not about the code

Two new red-probe mutations came back **"selftest still PASSES — THE ARM IS BLIND"**. One was: the
mutation replaced `return EXT_SCOPE[ext]` with `.get(ext, False)` — a line only reachable after the
refusal above it has already fired. The mutation was **inert**, and an inert mutation accuses the arm
in language indistinguishable from a real finding.

⇒ 🔑 **A MUTATION THAT CHANGES NO BEHAVIOUR IS A FINDING ABOUT THE MUTATION.** Both were re-anchored
on the refusal itself — the only line that can express either direction — and the probe now runs **26
mutations, every one caught**, including one per excluded register file, both directions of the
partition's default, the stamp welded back to one half, and the `ext_table` duplicate restored.

⚠️ **A measurement carried forward without its conditions:** the batch inherited "census regeneration
≈ 25 min". It is **32 seconds** on a warm page cache and about three minutes cold. Nothing was
designed around the wrong figure, but a probe priced at 25 minutes is a probe run once.

**Gates:** census selftest **138 arms PASS** (was 109) · red probe **26 mutations, all caught** (was 15)
· staleness gate CLEAN on both halves · p2-roster selftest 34 arms PASS · `--check` byte-identical ·
citations, coverage-prose, readme-snapshot, readme-lean, windows, ci-shards all green.

**Reversal cost:** the mapping and the partition are one file each; the documents regenerate in
32 seconds from a corpus the recipe rebuilds.

## D100 — a join on a key that had dropped a field priced one instruction set with another's demand (P2 vector wave, batch 10)

Found immediately after D99, by reading the candidate list D99 had just made trustworthy: **rank 9 was
`movq`, a mnemonic the model HAS.**

### 1. Why a covered mnemonic was still ranked

The census keys a vector residue as `` `movq (vector operand)` `` — by the mnemonic objdump printed,
which D66 chose deliberately so the P2 join has a word to look up in K's tree. But that key **drops
the register file**. `p2_roster.demand()` pools it under `movq`, joins it against K's `movq` shapes —
`mx`, `rx`, `xm`, `xr`, `xx` — and prints a row worth 11,109 instructions.

Measured, by walking the assembly-class corpus and splitting each uncovered residue by its ISA bucket:

| roster row | of its demand, MMX |
|---|---|
| `pmaddwd` | 454 of 21,239 — 2% |
| `psubusw` | 37 of 17,214 — 0% |
| `psrad` | 222 of 12,394 — 2% |
| **`movq`** | **11,109 of 11,109 — 100%** |

⛔ **Rank 9 is a PHANTOM ROW.** Every non-MMX `movq` form the census can see is already covered (P2
batch 5); what remains is `movq %mm0,%mm1`, and **none of the five K shapes that row advertises would
close a single one of those instructions.** The demand was real and the supply was real and they were
not the same instructions.

⇒ 🔑 **A JOIN ON A KEY THAT DROPPED A FIELD PRICES ONE THING WITH ANOTHER'S DEMAND — and the result
reads as an ordinary row.** Nothing about rank 9 looked wrong; it had a plausible mnemonic, a
plausible count and a plausible list of shapes.

⚠️ **The defect is older than D99 and D99 made it visible rather than causing it.** Before the repair
the same key pooled the XMM `movq` demand in as well, so the row was *larger* and its MMX fraction
*lower* — the mis-pricing was diluted to invisibility. Concentration is what exposed it.

### 2. The repair, both halves in one batch

The mnemonic and the bucket are both facts the census's residue loop already has; only the join was
lossy. `report()` now emits `miss_by_ext` — the same residue keyed `{mnemonic: {bucket: count}}` —
and the roster prints the MMX share of every row, marking a row above 99.5% as a **PHANTOM ROW** and
one above 10% with a warning.

⛔ **It is emitted AND consumed in the same batch.** A field written and never read is the shape this
repository has already paid for once (a renderer defined and never called), and a column computed and
never printed would be exactly that.

**Arms:** `mmx_note` is a function so its three bands can be driven — six arms including both edges
(1 of 10,000 prints `0%`, not `—`, because a nonzero share must never render as absent; a row with no
demand at all prints `—`). And the two keyings are gated against each other on the real data: for
every mnemonic in every assembly column, the per-bucket totals must equal that mnemonic's entry in the
flat map. A residue counted twice, or a bucket lost, fails there rather than in a reader's judgement.
p2-roster selftest 34 → **52 arms**.

⚠️ **What this does NOT do:** it does not re-rank. The MMX share is printed beside the demand rather
than subtracted from it, because subtracting would require deciding whether an MMX form is out of P2's
scope forever or merely out of its current wave — a roster question for the Captain, not a rendering
one. What the batch guarantees is that the next batch's rank 1 cannot be a phantom without saying so.

**Reversal cost:** one field in the census JSON and one column in a generated table.

## D101 — a roster that prices demand does not price buildability, and the two look the same in a ranked table (P2 vector wave, batch 11)

The relight handed on a candidate list described as "trustworthy for the first time" — D99 had just
repaired the covered/not-covered test and D100 had just marked the phantom rows. Rank 1 was
`pmaddwd`, rank 3 `psubusw`, and **the oracle refuses both**.

### 1. The knowledge existed; the join did not

`scripts/oracle_availability.py` has held the nine refusing SSE mnemonics since P2 batch 1, measured
by executing, gated in both directions, with an always-executes and an always-refuses control in
each CR4 arm. Re-measured live before acting on it — nine seconds, both controls behaving — and the
reading stands.

`p2_roster.py` joins **demand** (`docs/DEMAND-CENSUS.md.json`) against **supply** (K's tree) and
consults **no third artifact**. So a form the differential cannot ask about is priced exactly like
one it can, and the ranked list a fresh head is handed carries the omission forward. The roster's
own text said K coverage was "a CATALOGUE reading" and that a batch was "runnable pending an
oracle-availability run" — both true, and together a reason not to look: the run had been made.

⇒ 🔑 **A ROSTER THAT PRICES DEMAND DOES NOT PRICE BUILDABILITY.** It is D100 on the other side of
the same join — there the demand belonged to another instruction, here the supply is one no oracle
can execute.

### 2. ⛔ The first version of the repair reproduced D100 exactly, in the under-claiming direction

Keyed by mnemonic alone, the new column printed ⛔ **REFUSES** against `vpaddw` — a row of 11,682
AVX2 `%ymm` instructions — on the strength of a probe that is `vpaddw %zmm1,%zmm2,%zmm0`, AVX-512,
which this oracle cannot execute at all. One mnemonic, two register files, one verdict borrowed
across them.

⇒ 🔑 **A VERDICT MUST BE JOINED ON THE SAME KEY THE DEMAND IS COUNTED BY.** The census already
counts the gap per (mnemonic, ISA bucket) — `miss_by_ext`, D100's own repair — so that is the key,
and the bucket names are the census's own strings, because two vocabularies for one partition is the
second source that goes stale.

⚠️ **The failure direction is the one nobody polices.** Marking a buildable row unbuildable reads as
caution, not as a mistake: it would have quietly removed a rank from the next head's list with a
reason that looked measured. It was caught by reading the OUTPUT of the fix rather than its intent —
`vpaddw` is not a form this batch cares about, and the row was inspected anyway.

### 3. What landed

`measured_availability()` returns `{(mnemonic, bucket): verdict}` and **refuses on a conflict**
rather than picking; `probe_bucket()` reads the register file off the probe's OPERANDS, because the
mnemonic cannot say it (`movq` is three instructions in three files) and the label is a tag, not a
datum. The roster looks each row up on its **dominant** bucket. Three values, not two: a mnemonic
the probe does not name reads **not measured**, never "available" — a declared list inherits the
direction of its default, and `available` is the default that invents work.

Arms: the three bands of `oracle_note`, six `probe_bucket` cases including the GPR control that must
return `None`, **every probe bucket must be a census bucket** (a vocabulary drift would fail
silently, printing "not measured" on every row — the reassuring direction), and **the join must
actually land** on ≥20 census mnemonics, because a join that matched nothing looks like honest
modesty. p2-roster selftest 52 → **64 arms**.

### 4. ⭐ And the arm count itself was a hand-summed literal

The selftest reported its own size as
`len(arms)+len(key_arms)+1+4*len(asm)+len(ADDITIONS)+len(lock_arms)+6` — correct when written, and
it does not grow with the arms. This batch added twelve and the gate went on printing **52**.

⇒ 🔑 **A HAND-ACCUMULATED TOTAL CANNOT SEE ITS OWN PARTS**: it can only be recomputed, never
corrected, and it fails in the reassuring direction — under-counting reads as a smaller gate rather
than as a broken one. Every arm prints a line, so the count is now the count of printed lines:
**64 = 64**, and the number cannot drift from the work again.

### 5. ⛔ And one of the new arms was a DRIFTING THRESHOLD that this batch broke within the hour

The arm proving the join is not vacuous — *"a join that matched nothing would print 'not measured'
everywhere"* — was first written as `hits >= 20`, the count of census mnemonics the join resolves.
It passed at 23.

Then the batch that wrote it landed, `movaps`/`movups`/`movss`/`movsd` became COVERED, those four
left the uncovered residue, the count fell **23 → 19**, and the arm went red about nothing at all.

⇒ 🔑 **A THRESHOLD ON A QUANTITY THE WORK CONSUMES IS A CHORE, NOT A GATE.** Every landed batch
shrinks the residue, so that number can only fall and the gate can only be relaxed — and a gate
relaxed each batch stops being read. The repair is to state the arm's CLAIM instead of a number: it
exists to catch a join that matched NOTHING, so it now asserts that **at least one of the forty rows
the document actually prints resolves to a measured verdict** (13 of 40 today), which has no literal
to maintain and fails exactly when the join breaks.

⚠️ Driven both ways before it was believed: planting `dominant_bucket → None` takes it to **0 of 40**
and the selftest FAILS; reverted, 64 arms PASS.

### 6. ⭐ And the batch's price was confirmed by an independent origin

Regenerating the census against the new 111-mnemonic model moved the uncovered gap **534,576 →
474,736 — a fall of exactly 59,840**, which is the number the roster had quoted for these four rows
from the other side of the join. The roster reads K's tree and ranks demand; the census walks the
corpus and splits covered from uncovered.

⚠️ **These are two ORIGINS, not two readings of one artifact** — the distinction this repository has
already paid for once. A single artifact read twice agrees with itself when it is wrong; here the
supply-side price and the demand-side split were computed by different code from different inputs
and met at the instruction.

⚠️ And the corpus itself was verified before it was believed: it survives only in an old session's
scratchpad and **two candidate directories exist**. A model change must move the covered/uncovered
SPLIT and nothing else, so the corpus-side totals are the invariant — all **11 columns' instruction
totals came back byte-identical**. Picking the directory the bank named and checking nothing would
have been a guess wearing a citation.

**Reversal cost:** one column in a generated table and one function in each of two scripts.

## D102 — the coverage table's `shapes` column is a kernel-walked field, so prose in it is a cost (P2 vector wave, batch 11)

`scripts/kernel_cost.py` refused this batch: `memDestSweep` measured **19,900 ms** against a
19,360 ms ceiling registered at P1 batch 21 as `12,100 × 1.6`. The declaration has grown **62%**
across the P2 wave; this batch is the one that crossed.

⚠️ **Load was not available as an excuse, because the tool prints its own conditions.** Its line
records that the 2.2–4.1 load band has no measured effect on this module (four runs within 1%), and
the run sat inside that band. That is what a measurement carried with its conditions buys.

### 1. Where the money is, measured

A whole-module total cannot see its parts, and this file has mis-attributed its own money once
already (D62 named the smaller of two costs "the honest fix"). So the declaration was split and
re-profiled rather than reasoned about:

| conjunct | kernel ms |
|---|---|
| the loose-vs-strict string sweep over `Row.shapes` | **~18,800 of 19,600 — 96%** |
| `hasMemDestVector`'s 854-vector sweeps | ~800 |

The cost is in walking `Row.shapes` **character by character**, twice per row. The four new rows
carried ~340 characters of explanatory prose and **1,500 ms** with it.

⇒ 🔑 **A FIELD A KERNEL-REDUCED PREDICATE READS IS NOT A PLACE FOR PROSE.** The explanation was not
deleted — it moved to the AST docstrings, which nothing reduces. Trimmed: **18,400 ms**, three
readings within 1%, gate CLEAN.

⛔ **AND THIS IS NOT A NEW LESSON, IT IS A REPEAT, WHICH IS THE PART WORTH RECORDING.** D94 recorded
it in the SAME declaration and the SAME field — `claimsMemDest` walking `Row.shapes`, 30,700 ms
against this ceiling, repaired by shortening the strings — and the seat's own memory carries a card
that says, in as many words, *"before writing prose into a data field, ask whether any `decide`
reduces that field."* Four rows of explanatory prose went into that exact field anyway.

⇒ 🔑 **IN AN EDITOR A STRING LOOKS LIKE A COMMENT; THE KERNEL REDUCES IT.** The lesson was known,
written down, and re-paid. What is new here is only the DECOMPOSITION — that 96% of the declaration
is the string sweep and not the 854-vector sweeps beside it — which is what makes the next repair a
design question rather than another trim.

⚠️ **One inherited figure is corrected by this run.** D94's note recorded the reading as swinging
±2× on the same tree. Under the conditions this gate now prints for itself — the 2.2–4.1 load band,
which it measured as having no effect — three readings came back **18,500 / 18,400 / 18,400**, inside
1%. The ±2× was real under contention and is not the spread in this band; a spread quoted without its
conditions is as unusable as a timing quoted without them.

### 2. ⛔ And the pass is thin, which is the part that must not be silent

18,400 of 19,360 is **95% of the ceiling**. Read the margin, not the verdict.

The next batch crosses again, and the answer then is **not a looser number**. It is that
`claimsMemDestLoose` — an artifact kept only to be compared against — walks a documentation field,
and the disagreement list it exists to pin down **would change** if it stopped: stripping the prose
from all 106 shapes strings was tried, and `memDestSweep` failed loudly, which is the gate working.
So the cheaper build is real but it changes the subject of a historical comparison, and that is a
design question rather than a margin question. It is priced here so the next head inherits the
measurement instead of the surprise.

**Reversal cost:** four strings in `X86/Coverage.lean`.

## D103 — the coverage table's `shapes` column mixed data with prose, and a kernel predicate was reading both (P2 vector wave, batch 11)

D102 recorded that `memDestSweep` costs ~5 ms per character of `Row.shapes` and closed with the
margin rather than a repair: 18,400 of a 19,360 ceiling, and *"the next batch crosses again."* It
did — immediately. Padding ten rows by thirty characters each, the size of the next batch's ten
coverage rows **however terse their shapes**, takes the declaration to **20,000 ms**. The packed
shift group was blocked before a line of it was written.

### 1. The repair, and why it is not a trim

`Row` gains a `note : String` field. `shapes` carries the operand vocabulary a kernel-reduced
predicate reads; `note` carries the prose, and **no predicate reads it**. `renderTable` rejoins the
two with the same ` — `, so **`docs/COVERAGE.md` is byte-identical across the change** — which is the
check that says this was a refactor and not an edit to a published claim.

```
shapes column   4,577 -> 1,370 characters   (30%)
memDestSweep   18,500 -> 4,400 ms           (4,400 / 4,330 / 4,320 / 4,280, four readings)
Tests.Coverage 33,100 -> 18,600 ms
```

### 2. ⛔ The first attempt was wrong, and the way it was wrong is the finding

The obvious rule — *split at the em dash* — is wrong, because in this column the em dash does
**two** jobs: it separates a shape list from its prose, and it separates a shape from its WIDTHS
(`m(rmw) — all of b/w/l/q`). Splitting `neg`, `not` and `pop` at the first one moved real shape
vocabulary out of the predicates' sight and **silently dropped three memory-destination claims**.

⇒ 🔑 **A SEPARATOR THAT MEANS TWO THINGS IS NOT A BOUNDARY.** The gate caught it — `memDestSweep`
went red — but it caught it by luck of coverage, not by construction. So the split point is chosen
per row as the **earliest em dash that leaves `claimsMemDest` unchanged for that row**: an invariant,
computed over all 106 rows *before* the edit and enforced by the gate *after*.

### 3. ⭐ And the split found a real defect in the artifact it was moving

Exactly one row of 106 changes classification: **`bt`**. Its column read

```
"r,imm · r,r · m,imm — w/l/q (m,r: bit-string, not modelled)"
```

`claimsMemDestLoose` searches for the infix `m,r` **anywhere**, and found one — inside a parenthetical
saying that shape is **NOT MODELLED**. The loose and strict rules therefore AGREED about `bt` for a
reason that is the exact opposite of the truth, and the pinned disagreement list was one row short of
honest. With the prose out, loose correctly disagrees and `bt` joins the list.

⇒ 🔑 **A PREDICATE OVER A FIELD THAT MIXES DATA WITH PROSE IS READING BOTH — AND PROSE IS WHERE A
CLAIM'S NEGATION GETS WRITTEN.** The cost was the reason to look; the correctness defect is what
looking found.

### 4. The ceiling is re-registered DOWNWARD, and the next constraint is named

`memDestSweep` 19,360 → **7,040** (worst of four readings × 1.6, the file's own convention, conditions
recorded). ⚠️ A tightening, not an allowance: raising a ceiling from the thing it measures stays
forbidden, but a ceiling with 4.4× headroom detects nothing.

⛔ **`vectorCoverage` IS NOW THE BINDING CONSTRAINT, AT 98%** — 2,280 against 2,320. Its cost is
`vectorMnemonics`'s dedup, |rows| × |vectors| string comparisons (111 × 854), so it grows with
**both** and crosses at roughly two more vectors. Its cheaper builds were priced and refused at P1
batch 21: every dedup-free spelling costs the same cross product, and a hand-written literal trades
it for a list edited every batch. ⇒ Stating "these two sets are equal" without a cross product a
kernel must reduce is a DESIGN question, and it is the next head's first obstacle — named here with
its growth law rather than left to be met as a red gate.

### 5. ⚠️ And the gate's own warning line had gone stale in the same breath

`kernel_cost.py` printed *"ONE declaration (memDestSweep) is ~half the module"* as a LITERAL. This
batch made it 23% and the sentence went on saying half. The share and the declaration's name are
DERIVED from the profile now. A tool's output is prose too, and prose nobody re-reads is the ungated
claim this repository keeps paying for.

**Reversal cost:** one field, one line in `renderTable`, one entry in a pinned list.

## D104 — the CI step that had never run to success, and the two gates that were hiding behind it (P2 vector wave, batch 12)

The relight's order named one defect: master CI red at the step *"Fetch the K semantics (sparse)"*,
`scripts/setup_k_roster.sh` failing with

```
fatal: 'LICENSE.md' is not a directory; to treat it as a directory anyway, rerun with --skip-checks
```

diagnosed as *"an environment change under a working script"* — the runner's git 2.55 — with two
repairs offered: `--skip-checks`, or no-cone mode. Both halves of that diagnosis are wrong, and each
was wrong in a way that changed the work.

### 1. The cause: not the environment, and not a script that used to work

`git sparse-checkout set` in **cone** mode takes DIRECTORY prefixes; a file argument has been fatal
since long before 2.55. Local **git 2.48.1** reproduces it in three commands:

```
git init r && cd r && mkdir semantics && touch LICENSE.md && git add -A && git commit -m i
git sparse-checkout set semantics LICENSE.md      # fatal: 'LICENSE.md' is not a directory
```

So why did nobody see it? Because **nothing had ever executed that branch.** The script's clone
branch runs only where no tree exists; every developer box takes the `[ -d "$DEST/.git" ]` branch
instead, and this seat's `vendor/k-x86-64` is a **full 2.8 GB clone** whose `sparse-checkout list`
answers `fatal: this worktree is not sparse` — made by hand, not by this recipe. In CI the step has
never passed. ⇒ 🔑 **THE BRANCH THAT ONLY A FRESH ENVIRONMENT TAKES IS THE BRANCH NOTHING HAS
EXECUTED**, and its comment header — "15 MB of 2.8 GB, a fifteen-second job" — was prose about a
code path with no witness anywhere.

### 2. The repair is smaller than either form that was offered

In cone mode the repository ROOT's files are materialised **unconditionally**. A fresh
`clone --sparse` of the K repository therefore already carries `LICENSE.md` **before any pattern is
set**, and `sparse-checkout set semantics` leaves it in place. The pattern was **redundant, not
merely wrong**: neither `--skip-checks` nor no-cone mode is needed, and both would have kept a
pattern that does nothing. ⇒ 🔑 a gate that refuses names a cheaper build — read the refusal for the
design before reaching for the flag that silences it.

Measured against the real repository at K `592380ae`, the first time this branch has run to success:

```
clone --filter=blob:none --sparse --depth 1     1.3 s   (2.3 s in the vendor path, cold)
working tree                                    21 MB  = semantics 15 MB + .git 5.8 MB
tests/ present                                  no
```

The two properties the recipe promises are now **asserted** rather than assumed — `semantics/
registerInstructions` exists (as before) and `LICENSE.md` is non-empty (new: this repository READS an
NCSA source and `PROVENANCE.md` cites that file). Both driven red-first against a real fetched tree,
with the untouched tree as the positive control in the same run:

```
fresh clone                    rc 0      idempotent re-run          rc 0
LICENSE.md removed             rc 2      semantics/ removed         rc 2
```

### 3. ⛔ The scope was wrong too, and that is the larger finding

The order said *"RED on every run since 12:17Z"* (four commits). `gh run list --workflow=CI --branch
master --limit 200` answers **36 runs, 36 failures** — every CI run master has ever had, back to
09/03 16:04 and the D88 quoting repair that first made GitHub create jobs at all. The 11:47 run did
not even reach the K step; it failed earlier, at the census-staleness selftest. So the K fetch was
never "the" defect: it was the **frontier**, and behind it sat gates that no run has ever reached.
Two of them are red at `161500b`, found by running the remaining steps locally against the freshly
fetched sparse tree:

* **`docs/P2-ROSTER.md` is stale.** `f1b698d` probed the twelve packed-shift forms and updated
  `scripts/oracle_availability.py` without re-deriving the document that reads it: eight mnemonics
  (`psrlw`, `psraw`, `psrldq`, …) still say ⚠️ *not measured* where the measurement says ✔, and the
  summary band under-reports — EXECUTES 26 → **34**, probed demand 39.4% → **43.4%**. Regenerated;
  `--check` byte-identical.
* **Sixteen batch-10 vectors claim no roster row and were never exempted.** `movaps`/`movups`/
  `movss`/`movsd` — the P1 roster excludes xmm operands *by derivation*, so a SIMD vector must be
  listed in `CLAIMS_NO_ROW`, and every earlier vector batch listed its own. Batch 10 did not, so
  `claimed_forms.py --check` fails at HEAD with sixteen unresolved vectors and its **control arm**
  red. Added; `--check` rc 0 with the claimed-row count unmoved (500 of 525, as the rule predicts),
  `--selftest` 13 of 13.

⇒ 🔑 **A GATE NOBODY HAS EVER SEEN RUN IS NOT A GATE.** Both of these were written to fail loudly and
both did — into a log that stopped being read three steps earlier. A failing step does not merely
report its own defect; it **launders every gate behind it into silence**, and the silence reads
exactly like green in a bank that lists gate names. The bank for batch 10 listed twelve gates as
CLEAN; these two are not on that list, and *not on the list* is where a red hides.

⚠️ Under this, "the CI is red on the K fetch" and "the CI is red" are different claims with different
costs, and only the second is true. The order's exit — *verify by a green run on master* — is
therefore the right exit for a reason it did not state: it is the only check that can see what is
behind the frontier.

**Reversal cost:** one word deleted from a git command; two `test` lines; one regenerated document;
sixteen dictionary entries.

## D105 — the kernel was searching where it could have been checking, and four cheaper spellings were refuted before the fifth was built (P2 vector wave, batch 12)

`vectorCoverage` — the declaration proving that the differential vectors exercise exactly the
coverage table's mnemonics — cost **2 250–2 370 ms against a 2 320 ms ceiling**. D103 named it as
the next head's first obstacle, forbade raising the ceiling (the number would come from the thing
it checks), recorded one refuted route, and left an instruction: **profile the declaration's PARTS
before optimising it.** This is that profile, the four refutations it produced, and the design that
came out of them.

### 1. The parts, measured (each its own declaration, one file, same run)

```
the traversal alone   (854 `Vec.mnemonic` projections, no dedup)            104 ms
the table's own map   (111 rows -> 111 mnemonics)                          < 50 ms
the DEDUP alone       (`vectorMnemonics.length == rosterSize`)             1 700 ms
inclusion sweep 1     (dedup + rows looked up in the deduped list)         1 970 ms
inclusion sweep 2     (dedup + the deduped list looked up in the rows)     2 080 ms
the whole shipped declaration                                             2 260 ms
```

⇒ **The dedup is three quarters of it.** And the part of the dedup that matters is not the
duplicates: `eraseDups` over the **111 DISTINCT mnemonics alone** — a list from which nothing can be
removed — is **801 ms**, half the dedup's cost. The comparison count model that every previous
attempt reasoned from counts the wrong comparisons.

### 2. ⛔ Four cheaper spellings, each REFUTED by measurement

* **Hoist `tableP0.map Row.mnemonic` out of the inner lambda.** The shipped sweep rebuilds it once
  per element, which reads like an obvious 111× waste. Measured: **2.08 s → 2.01 s, nothing.** The
  map is under 50 ms and the kernel was already sharing it. *This was my hypothesis, and it was the
  most confident one.*
* **Drop the dedup; sweep the raw lists both ways.** Measured **6.1 s — 2.7× WORSE.** The dedup pays
  for itself by making the outer loop 111 long instead of 854.
* **Collapse adjacent duplicates before the dedup** (batch 11's route, reverted there at 7% measured
  module-to-module). I re-ran it **declaration to declaration**, expecting the per-declaration gate
  to see a bigger share: **2.32 → 2.13 s, eight per cent.** The previous head's number and its
  revert were both right, and my re-reading of them was wrong. ⇒ 🔑 **a REFUTED route re-derived
  from a better denominator is still refuted** — the denominator was not the defect.
* **`mergeSort`, an O(n log n) dedup.** `decide` fails outright: the `String` order's instance does
  not reduce in the kernel. The design died before it was written, for 30 seconds of probe.

### 3. ⭐⭐ What worked: stop the kernel searching, and let it CHECK

`Tests/VectorRuns.lean` is **generated** (`lake exe x86lean-diff runs`) and gated byte-for-byte in
CI exactly as `docs/COVERAGE.md` is. It names, for each **run** of equal mnemonics in the vector
table, the **index of the coverage-table row** that run exercises — 181 runs over 854 vectors and
111 rows. `vectorCoverage` then checks four things and searches for none of them:

```
1. every run's mnemonic IS the mnemonic of the row its index names   (181 string compares)
2. every row index 0..rosterSize-1 is named by some run              (Nat)
3. no run names an index outside the table                           (Nat)
4. the runs name exactly rosterSize distinct rows                    (Nat)
```

```
in isolation, same run   shipped 2 260 ms   certificate 990 ms
in the module            2 370 ms  ->  962 · 1 010 · 1 020 · 1 100 ms (loads 3.7-5.7)
ceiling                  2 320     ->  1 760   (worst of four x 1.6, the file's convention)
Tests.Coverage           19 300 ms ->  17 900 ms
```

⚠️ **A cost model, marked as INFERENCE and not as measurement.** Dividing each arm's time by the
comparison count its shape implies gives ~0.13 ms per **string** comparison and ~0.037 ms per **Nat**
comparison, consistently across six arms — which would mean the certificate trades roughly 17 000
string comparisons for 181 of them plus Nat work. Every figure in that sentence is arithmetic ON the
timings above with an assumed comparison count, not a thing this repository measured; it is written
down because it PREDICTS the next batch's cost (~+60 ms, not ~+200), which is the form in which it
can be found wrong. What IS measured is the arm table and the module total.

The growth law changes with the design: the string half is linear in the RUNS (181, not 854) and the
coverage half is Nat work over rows × runs, where the old shape was |rows| × |vectors| in strings.

### 4. ⛔ A certificate is only worth the check, and the check is red-first

`scripts/sharing_redprobe.sh` gains a fourth `vectorCoverage` arm and its first arm is now the
important one: **r4 plants a LYING certificate** (every run pointed one row along) and requires the
kernel to prove the equality FALSE. r5 removes every run naming row 0 (a row with no vector), r6
adds a run naming a row that does not exist, r7 takes the distinct count one short. Seven arms and a
positive control at the same shape, all in one run; the anchor list that ties each arm to a string
occurring in the shipped declaration was updated in the same edit, and it REFUSES rather than
passing when it cannot find one.

⛔⛔ **AND THE VOCABULARY CHANGE OPENED A HOLE, WHICH IS CLOSED BY PROOF AND NOT BY COMMENT.** Every
conjunct speaks about the RUNS, and the runs come out of `collapseAdjacent`. The old spelling swept
every vector's mnemonic directly and so could not have this defect; the new one would go on holding
if that function ever DROPPED a mnemonic rather than collapsing repeats of it — an observation
narrower than the claim it supports, which is the failure this repository keeps finding in its own
gates. So `mem_collapseAdjacent` proves, for all lists, that collapsing loses no member, and
`every_vector_mnemonic_is_in_the_table` reassembles the original published statement — *every
mnemonic the vectors exercise is one the table names* — from the four conjuncts plus that lemma. ⚠️
Neither is a `decide`: they are proofs about a function and a chain, so they cost the kernel nothing
that grows with the tables.

⚠️ **The three published theorems changed VOCABULARY, and that is the risk this batch carries.**
`every_row_has_a_vector` no longer mentions vectors: it says every row index is named by a run. It
means what it used to mean **only through the bridge** (conjunct 1), so the bridge is now stated as
its own theorem, `vector_runs_name_their_rows`, and each docstring says so. A reader who takes the
index facts without the bridge is reading arithmetic about a list of numbers.

### 5. The deadlock that had to be designed around, and the alternative that was refused

The generator lives in `x86lean-diff`, which imports `Tests.Vectors` and **never** `Tests.Coverage`.
That is load-bearing: a stale certificate makes `Tests/Coverage.lean` fail to BUILD (it is imported
by the model tier, unlike `docs/COVERAGE.md`), so if the generator needed the module it invalidates,
a fresh checkout with a stale file could not regenerate it.

⛔ **The cheapest design measured was refused on other grounds.** Comparing the collapsed runs
directly against the table's mnemonics — no certificate at all — costs **165 ms**, but it requires
the vector table's mnemonics to be CONTIGUOUS and in table order (they are 181 runs over 111
distinct today). Reordering 854 hand-authored vectors would scramble thirteen comment blocks that
explain why particular vectors sit where they do ("these four exist because the harness selftest
FOUND their absence") and would make every future batch an insertion rather than an append. A 165 ms
declaration is not worth a file whose comments no longer point at their subjects.

**Reversal cost:** one generated file, one generator arm, one theorem's four conjuncts, four probe
arms, one ceiling line.

## D106 — a duplicated objdump parser, and the first master CI run that a gate had never been seen to run (P2 vector wave, batch 13)

**The Actions billing wall cleared (desk FH) and the first master CI run in this repository's life
came back RED.** Not on the commit under it: on a parser copied months earlier.

```
⛔ control: the repository as it stands
    ⛔ 1 vector(s) resolve to NO roster row
claimed-forms selftest: FAIL (1 of 13 arms)
```

### 1. The message named nothing, and that cost the diagnosis

The failing arm is the CONTROL — *the repository as it stands*. On the developer machine both
`--check` and `--selftest` pass at `f45aa6c`, rc 0, verified in a clean worktree before anything was
touched. So the red was **Linux-only**, and all the runner said was a count.

⇒ 🔑 **A GATE THAT REFUSES MUST SAY WHAT IT SAW.** Every other finding in that same list names its
subjects; this one printed `1 vector(s)` and stopped. A remote red that names nothing turns into a
local re-run that measures a different machine. It now prints the id, the bytes, and the byte COUNT
— and with that alone the answer fell out in one command.

### 2. The cause is the DUPLICATE, not the parse

`scripts/claimed_forms.py` carried its own copy of the objdump byte-column parse. `check_encodings.py`
has `parse_objdump`, written for exactly this defect and repaired TWICE — D83 (the final byte
abutting the tab) and its Linux follow-up (**GNU objdump wraps its hex dump at seven bytes**,
continuing on a line carrying an address and no mnemonic). The copy received neither.

⇒ 🔑 **A DUPLICATE BORN IN AGREEMENT DIVERGES ON THE NEXT ORDINARY REPAIR, AND THE ONE THAT MATTERS
IS THE ONE ON THE PATH THAT REPORTS SUCCESS.** The fixed copy sat in a gate green for weeks; the
stale copy sat in the gate master CI had never reached (D104's frontier). This repository had already
written that law down — for `looseMemDestShape`, *"two definitions that agreed at birth, one of them
unreachable"* — and then paid it again three files away. ⇒ **Naming a defect is not finding its
siblings**: the sibling was found by grepping for the parse SHAPE, and it should have been grepped
for when D83 was written.

### 3. Measured on the runner's actual tool, not inferred

The developer machine's `objdump` is Apple LLVM and cannot produce a wrapped sample, so rather than
repair on a hypothesis, GNU binutils was installed and the format taken from it directly:

```
GNU objdump (GNU Binutils) 2.47              Apple LLVM objdump
  7: 48 b8 88 77 66 55 44   movabs ...         7: 48 b8 88 77 66 55 44 33 22 10  movabsq ...
  e: 33 22 11                                  (all ten bytes on one line)
```

With GNU objdump on PATH and the tree otherwise untouched, the stale copy read `cmp_rip_q` — eleven
bytes — as its first seven:

```
⛔ 1 vector(s) resolve to NO roster row: cmp_rip_q (48813df51fc0ff78563412, 11 bytes)
```

**Exactly the runner's count.** ⛔ `cmp_rip_q` is the ONLY non-exempt vector of 854 at eight bytes or
more; the other eleven wide vectors are all `CLAIMS_NO_ROW`-exempt and could not expose it. ⇒ 🔑 **A
COLUMN PARSER IS TESTED BY ITS WIDEST DATUM**, and this table had exactly one — which is why
forty-nine commits of local green said nothing.

### 4. The repair, and the check a pair of passes cannot give

`claimed_forms.py` imports `parse_objdump`. **No third parser was written**: the original folds
continuations under an address-arithmetic guard and carries an always-on selftest over a GNU sample,
an LLVM sample, and a third readable only by the guard.

```
claimed_forms --selftest   GNU: PASS 13/13 (the arm CI failed)    LLVM: PASS 13/13
claimed_forms --check      GNU: rc 0                              LLVM: rc 0
check_encodings            GNU: rc 0                              LLVM: rc 0
```

⭐ And the stronger statement: the two tools' full `--check` output is now **byte-identical**, and
stable across repeated runs. Two greens side by side would not have shown that the reading had
stopped depending on the tool ([[two-defects-that-cancel]]); an equality does.

⚠️ **A false residual, recorded because it will recur.** A `500 vs 501` difference between the tools
was briefly read as a remaining defect. It was an ORDER EFFECT: `--check` regenerates
`docs/COVERAGE.md`, so the first run moved the file the second compared against. Settled runs agree
exactly. A gate with a side effect cannot be A/B-ed by running it twice in sequence.

### 5. What this adds to D104

D104: *a gate nobody has ever seen run is not a gate.* The half this adds: **the first time such a
gate runs, it may fail for a reason that has nothing to do with the commit under it.** A red on the
first-ever run of a step is evidence about the STEP's history, not about the change beneath it — and
reading it the other way would have sent this seat looking through batch 12.

**Reversal cost:** one import, one deleted parse block, one message widened to name its subject.


## D107 — the packed shifts: a count that does not wrap, and a guard whose real reason is a crash (P2 vector wave, batch 13)

Ten roster rows — the eight encodable lane-wise packed shifts and the two whole-register byte shifts
— at three count shapes, 39 vectors, no new state. `docs/DIFFERENTIAL-P2-BATCH11.md` carries the
batch's own account; this records the three decisions.

### 1. The oracle was measured before the model was written, because the handover asserted it

The batch arrived with *"the saturating-count rule measured IMPLEMENTED"* and **no artifact in the
tree said so**. An oracle with no rule for out-of-range counts agrees with any model over vectors
that stay in range, so the sentence had to become a measurement
([[the-oracle-is-evidence-not-the-specification]], [[inherited-diagnosis-is-a-hypothesis]]). Three
models — the SDM's, count-modulo-lane-width, and count-truncated-to-a-byte — against x86isa:
**42 rows, 42 agree with the SDM, 20 of them DISCRIMINATING.** The other 22 are printed as pricing
NOTHING rather than counted as support: at an in-range count all three models agree, so those rows
say the harness runs, not that the rule holds.

### 2. The guard has two reasons and only one is a theorem

`vshiftLane` refuses to shift at `cnt ≥ w`. The SDM's rule is asserted in
`vshift_saturates_rather_than_wrapping`. The second reason is not statable in Lean:

```
x <<< (4294967299 : Nat)  ⇒  INTERNAL PANIC: Nat.shiftl exponent is too big
```

— in the interpreter **and in the kernel**. 2³²+3 is a count `psllw %xmm1,%xmm0` reads whenever the
count register holds it, which the pre-state sweep produces in quantity. ⛔ **A declaration that
panics does not fail to elaborate; it kills the process**, so this cannot be a red arm inside Lean
and is `scripts/shift_guard_redprobe.sh` instead, which plants the unguarded spelling.

⇒ 🔑 **THE ASYMMETRY IS THE DEFECT'S COVER.** Lean's two right shifts saturate correctly at any
count, so removing the guard leaves every `psrl`/`psra` vector passing and takes the build down only
on `psll` at a large register count. The probe therefore carries a **held-out arm** asserting the
right shifts stay quiet: without it the probe would demonstrate a crash and not the fact that makes
it hard to find.

### 3. The AST departs from `VBinKind`, and the departure carries the burden

`VBinKind` puts the lane in the kind because it has **no hole**. The shifts have two — no packed byte
shift, and no `psraq` outside AVX-512 — so they are a product with a `vshiftEncodable` table, and the
declined set is stated **as the four pairs, not as a count**: `sra` at `w64` is the pair a reader
will get wrong, since `sll` and `srl` both exist there, and it is exactly the one a count hides.
Gated in both directions, because a spare `psraq` roster row is an over-claim the forward direction
cannot see ([[under-claims-are-unpoliced]], inverted).

### 4. Two routes disagreed by 2,822 and the third fact reconciled them exactly

The census's gap fell **474,736 → 441,854**, i.e. by 32,882, against the roster's 35,704 for the
group. The difference is **2,822 MMX-register-form instructions** which this model, having no MMX
register file, correctly does not claim — measured directly, per mnemonic, and independently
reproducing the roster's own *"of it, MMX"* column. `35,704 − 2,822 = 32,882`, exact.

⇒ The batch is published at **32,882**, not at the rank the roster shows. A demand figure and a
coverage gain are different quantities whenever the model declines a register file.

### 5. `x,m` was built rather than declined, and the reason is a number

The census counts by mnemonic, so declining the memory-count shape would have been counted at 100%
of the group's demand while covering **0.85% less** (305 of 35,704, measured on both candidate
corpora, agreeing exactly and matching the census per-mnemonic 10 of 10) — an over-claim no gate here
could see. The oracle was measured on that shape first, since **12 of 12 does not license the 13th**
and no row of `oracle_availability.py` had ever asked it.

**Reversal cost:** four AST constructors, two combinators, one encodability table, ten table rows,
39 vectors, two pre-states, seven theorems, four selftest arms, one probe script, one CI step.


## D108 — the oracle reads the packed-shift count from 128 bits where the SDM and K read 64, and it contradicts itself two shapes over (P2 vector wave, batch 13)

The batch's differential came back with **8 unexplained disagreements out of 78,584**, all on the
register-count shape, all at ONE pre-state. This is the third time the differential has been right
and ACL2 x86isa wrong (after D91's missing alignment fault and D93's merging `movd`), and it is the
first one the oracle refutes ITSELF on.

### 1. What the run said

```
cases=78584 matched=58052 explained=29435 unexplained=8 oracle-divergence=163 oracle-leaks=0
  [spec] psllw_x/79 (psllw) xmm0: lean=5550…8890  oracle=0000…0000
  [spec] psrad_x/79 (psrad) xmm0: lean=f555…0222  oracle=ffff…0000
  … eight in all, one per encodable lane-wise shift, at pre-state 79 alone
```

Pre-state 79 is one of this batch's two `shiftCountStates`, and it is the only state in the sweep
whose `xmm1` has a **small low quadword and a non-zero upper one**: `aaaaaaaaaaaaaaab_0000000000000003`.
The model shifted by 3. The oracle saturated.

⚠️ **The pre-state transports correctly**, which was checked before anything was concluded:
`mov_d/79` and `paddb_xx/79` report identical `xmm0` on both sides. The disagreement is about the
SEMANTICS, not about the harness.

### 2. Isolated to a single bit

```
psllw %xmm1,%xmm0,  xmm0 = aaaaaaaaaaaaaaaa_1111111111111112

  count operand                          oracle answer          SDM
  0x0000…0000_0000000000000003           shift by 3             shift by 3   ✔
  0x0000…0001_0000000000000003           all zeros              shift by 3   ⛔
  0xaaaa…aaab_0000000000000003           all zeros              shift by 3   ⛔
  0x0000…0000_0000000000000040 (control) all zeros              all zeros    ✔
```

One bit of the count register's **upper quadword** — a bit SDM Vol. 2B says is not part of the count
(`COUNT ← COUNT_SOURCE[63:0]`) — flips the answer completely. The control at a true count of 64
saturates correctly in the same run, so the oracle's saturation machinery is not broken; its notion
of where the count ENDS is.

### 3. ⭐⭐ The third source, and then a better one: the oracle contradicts itself

D93's rule is that a two-model disagreement names no culprit. K's `psllw_xmm_xmm.k` is explicit —
the saturation test is

```
ugtMInt( extractMInt( getParentValue(R1, RSMap), 192, 256), mi(64, 15))
```

and bits 192..256 of the 256-bit parent are exactly `SRC[63:0]`; the upper quadword is never read.
K agrees with this model and with the manual.

⛔ **AND THEN THE STRONGER FACT, WHICH NEEDS NO INTERPRETATION AT ALL.** The same mnemonic's
MEMORY-count shape, given the SAME 128-bit count value, returns the SDM's answer:

```
psllw %xmm1, %xmm0    count 0xbfbebdbcbbbab9b8_0000000000000003  ⇒  0000…0000   (wrong)
psllw (%rbx), %xmm0   the same 128 bits, in memory              ⇒  5550…8890   (right)
```

⇒ 🔑 **AN ORACLE THAT DISAGREES WITH ITSELF ACROSS TWO SHAPES OF ONE MNEMONIC HAS A DEFECT, NOT A
READING.** x86isa's own memory path already implements the 64-bit rule its register path does not,
so no appeal to the manual is needed to say which of the two is the mistake. This is a better class
of evidence than D93's, and it was available only because the batch built **both** count shapes —
had `x,m` been declined as the 0.85% it is worth, the finding would have been a bare disagreement
with the more credible model.

### 4. The resolution, and what is deliberately NOT declared

Eight `knownDivergences` entries — one per encodable lane-wise shift, field `xmm0`, each carrying
its K citation. The vectors keep running and keep being compared; if x86isa is fixed, the channel
fails and says so.

⛔ **`vshiftm` IS NOT DECLARED.** It agrees, and an entry that never diverges is a failure in this
channel by design. ⛔ **AND THERE IS NO WILDCARD**: eight entries, each naming one vector prefix and
one field, so a future disagreement about a lane width or a sign fill is not absorbed by a broad rule
written for the count's width.

⚠️ **The cost, stated plainly.** An entry excuses field `xmm0` for that vector at EVERY pre-state, so
a real defect of this model in the same field would now be absorbed. Three things stand against that
and none is the channel: the saturation rule is a theorem
(`vshift_saturates_rather_than_wrapping`), the two wrong models are planted as selftest arms, and
`driveWrong` passes the EMPTY divergence list — the arms compare this model against a wrong copy of
itself, where the oracle's defect is irrelevant, so declaring a divergence cannot weaken them.

**Reversal cost:** eight list entries; delete them the day x86isa's register path reads 64 bits.

---

## D109 — the permute group's shape: a selection whose COUNT comes from the selector

**P2 batch 14.** `pshufd`/`pshuflw`/`pshufhw` are one opcode (`0F 70 /r ib`) under three
mandatory prefixes, and they are the first operations in this model that read a source and write a
destination **without combining them**: no lane of the result is a function of the destination's old
value, and no lane is a function of more than one source lane.

**The AST carries no lane width, and the absence is the decision.** The reflex from `VShiftW` is to
put `w16`/`w32` beside the kind, and it would be wrong twice: `lw` and `hw` are not one function at
two widths — they consume DISJOINT halves of the source, as `punpckl`/`punpckh` do — and `d` is not a
third width of the same function, because it replaces the whole register where both word forms COPY
the untouched quadword through. The width is a consequence of the kind and is derived in
`vshufApply`.

⛔ **THE COUNT IS DERIVED FROM THE SELECTOR, NOT FROM THE LANE WIDTH, AND THAT IS THE ONE PLACE THIS
GROUP DEPARTS FROM `vlanes`.** `vlanes` folds `128 / w` lanes. A permute folds **four** — an 8-bit
immediate holds exactly four 2-bit fields — which is four of four at `w = 32` and four of **eight** at
`w = 16`. Taking the `vlanes` reflex (`128 / 16 = 8`) permutes the whole register and silently
destroys the half the SDM says to preserve. That wrong model is planted as
`wrongVshufWholeRegisterWords`, and ⚠️ **it leaves `pshufd` completely untouched**, because there
`128 / 32` and `8 / 2` are both 4 — which is why the word forms carry vectors of their own rather
than riding on the doubleword's.

**`pshufw` is declined by register file, not omitted.** It is the same opcode's fourth prefix (none),
takes MMX operands, and this model has no MMX register file. Measured over the census's `asm` class:
**642 of 642** occurrences are MMX-register forms — the same decline D107 made for the shifts' 2,822,
and stated here because a mnemonic absent from a kind is an absence, and an absence falls the way the
default points.

**Reversal cost:** one inductive of three constructors, one combinator, two `Op` constructors.

---

## D110 — the packed shifts' memory form had no alignment check, and the comment said the absence was the rule

**P2 batch 14, and the finding is in what the batch INHERITED.** `Op.vshiftm` (P2 batch 13) carried:

> *"NO ALIGNMENT CHECK, unlike `vload`. The SDM states no alignment requirement for the shift forms,
> so there is no `#GP` branch to write — the absence is the rule."*

### 1. The SDM settles it in three lines, and none of them is a recollection

```
PSHUFD   Other Exceptions: … Table 2-21, "Type 4 Class Exception Conditions"
PAND     Other Exceptions: … Table 2-21, "Type 4 Class Exception Conditions"
MOVDQU   Other Exceptions: … Table 2-21, "Type 4 Class Exception Conditions"
MOVDQU   "the operand may be unaligned to any alignment WITHOUT causing a
          general-protection exception (#GP) to be generated"
MOVUPS   the same sentence, the same table
```

⭐ **AN EXEMPTION IS PROOF OF THE RULE IT EXEMPTS FROM.** MOVDQU and MOVUPS sit in Type 4 and are
given an explicit licence to be unaligned; an exemption from a requirement that does not exist is
vacuous. So Type 4 carries a 16-byte `#GP` for every member not exempted — and `psrlw xmm,m128`,
`pshufd xmm,m128,imm8` and `pand xmm,m128` are all unexempted members.

**x86isa agrees in its own source, independently of the manual.** `logical.lisp` implements the
legacy `pand`/`por`/`pxor` check literally (`:memory-address-is-not-16-byte-aligned`) and disables it
for the VEX form with the comment *"There is no alignment checking (see Intel Manual Volume 2
Table 2-21)"* — exactly the legacy/VEX split Type 4 encodes.

### 2. ⛔⛔ Why it survived a green run of 78,584 cases — and the first answer was WRONG

**The first draft of this decision said "no vector could construct the violation, because every
memory vector addresses `(%rbx)` = 0x2000, which is aligned." That is false**, and it was written
into four files before the differential refuted it.

```
psraw_m_disp   psraw 0x8(%rbx), %xmm5     ← 0x2008. NOT 16-byte aligned.
```

The vector exists. **P2 batch 13 added it in the same commit as the defect**, pointed straight at the
rule — and it PASSED, at all 88 pre-states, inside a run that reported `unexplained=0` over 78,584
cases. Repairing `.vshiftm` is what surfaced it: the differential came back **264 unexplained**, every
one of them this single vector (88 pre-states × `xmm5`, `rip`, `refused`), and no other.

⇒ 🔑 **IT PASSED BECAUSE THE MODEL'S MISSING CHECK AND THE ORACLE'S MISSING CHECK ARE THE SAME
OMISSION.** x86isa implements the 16-byte rule in exactly one file of its whole tree
(`logical.lisp`) and not in `pshift.lisp`. The differential compared a model that should have faulted
against an oracle that also does not fault, and reported agreement.

⇒ 🔑 **TWO DEFECTS THAT CANCEL SURVIVE EVERY GREEN RUN THAT COMPARES THEM TO EACH OTHER.** A
differential is blind to exactly the errors its two sides share, and **nothing inside it can report
that**. What broke the tie was not a vector and not the oracle: it was the SDM read for a DIFFERENT
group one screen away, plus x86isa's own source contradicting its own behaviour. That is a worse fact
about the method than the one this decision first recorded, and it is the one worth keeping: the
strongest instrument in this repository has a blind spot shaped exactly like its two sides'
agreement.

⚠️ **How the false claim got written.** The vectors being ADDED were checked for alignment, and the
property was generalised to the vectors already there without grepping the table for a displacement.
It was the load-bearing half of the explanation — the reason offered for the defect surviving — and
it sat in the incidental half of a finding whose main half is sound
([[audit-the-premise-of-a-right-decision]]).

**The repair to the vector.** `psraw_m_disp` moves to `0x10(%rbx)` = 0x2010: still displaced, still
inside the watched window, still a constant count, so everything it was written to test it still
tests. ⛔ The unaligned form is NOT re-added under the known-divergence channel — that channel is for
an oracle that computes a WRONG VALUE with a third source naming the right one (D95), and this is an
omitted FAULT, which is D91's case and D91's answer is no vector.

### 3. The oracle contradicts itself across one exception class

88 pre-states, one run, all at `8(%rbx)`:

```
pand   8(%rbx),%xmm0    refused 88 of 88   ← POSITIVE CONTROL: the refusal IS visible
pand    (%rbx),%xmm0    refused  0 of 88   ← negative control, same opcode, aligned
pshufd 8(%rbx),%xmm0    refused  0 of 88
psrlw  8(%rbx),%xmm0    refused  0 of 88
movdqa 8(%rbx),%xmm0    refused  0 of 88   ← D91's reading, reproduced
```

`grep -rln 16-byte-aligned` over x86isa's instruction tree returns **one file**.

⇒ 🔑 **THE ORACLE'S ALIGNMENT BEHAVIOUR IS A PROPERTY OF THE FILE THAT IMPLEMENTS THE INSTRUCTION,
NOT OF THE INSTRUCTION'S CLASS.** D108 found the oracle disagreeing with itself across two SHAPES of
one mnemonic; this is the same defect across three MNEMONICS of one class. ⛔ **D91's sentence is
amended in place**: *"ACL2 x86isa does not implement the alignment check"* is true of `movdqa` and
false about the oracle, and it was the sentence that told the next reader not to look
([[a-justification-outlives-its-condition]]).

### 4. The resolution, and the gate that was driven red

The rule is written into `.vshufm` and into `.vshiftm`, and is asserted by four theorems
(`vshufm_unaligned_faults` / `vshufm_aligned_runs` / `vshiftm_unaligned_faults` /
`vshiftm_aligned_runs`), because no vector can validate it — the oracle executes where this model
faults, so a vector would be a one-sided refusal counted UNEXPLAINED (D91's position, re-measured for
this group rather than inherited).

⛔ **Each branch was DELETED in turn from the shipped `Semantics.lean` and the tree rebuilt**: the
shift deletion went red at `vshiftm_unaligned_faults` and the permute deletion at
`vshufm_unaligned_faults`, **each at its own theorem and no other** — so these are two independent
gates, not one wearing two names ([[two-arms-that-agree-to-the-case]]).

⭐ **And the class HAS a measured route to differential validation**, which D91 did not: `pand`/`por`/
`pxor` at a memory operand, where the oracle does check. `Op.vbin` is register-only today, so
building its memory shape is the priced first item of the next batch — the rule then stops resting on
the manual for at least one member of its class.

**Reversal cost:** two `if !aligned16` branches and four theorems.

---

## D111 — the kernel-cost ceiling accused a batch of a regression that was the machine

**P2 batch 14.** The gate's first reading with the batch applied: `@tail` **13,160** against a
12,420 ceiling — 740 ms over, and **+1,490 ms** against batch 13's recorded 11,670, which would have
made it the most expensive batch in the project's history.

### 1. The matched measurement, which is the only kind that means anything here

Alternating the two trees in ONE session on ONE machine:

```
PARENT COMMIT 144e9a3 (batch removed)   12,970 · 13,030 · 13,060   loads 5.2 · 6.7 · 7.3
THIS BATCH APPLIED                      13,040 · 13,160 · 13,680   loads 6.6 · 6.5 · 7.9
ceiling                                 12,420
the same parent, measured earlier the same day                     11,670
```

**The parent commit is itself 550 ms over the ceiling**, before the batch exists. The two bands
overlap (13,040 < 13,060). ⚠️ They are not identical and this record does not claim they are — the
batch's three readings average ~230 ms above the parent's — but the +1,490 ms the first single
reading implied is not there.

⇒ 🔑 **A CEILING WHOSE MARGIN IS UNDER THE MACHINE'S OWN SPREAD REPORTS THE MACHINE, NOT THE CODE.**
Margin: 750 ms (6.4%). Across-session shift at one commit: 1,320 ms (11%). Within-session spread at
one commit: ~90 ms. The gate cannot tell a batch from a busy afternoon, and it blamed the batch by
about six times the batch's own likely cost.

### 2. What is NOT done

⛔ **The ceiling is not raised.** Deriving a gate's new allowance from the thing it checks is how a
gate stops being one ([[widening-a-gate-needs-a-second-source]]), and the matched A/B is the second
source — it says the code did not grow enough to explain the reading.

⛔ **D105's arithmetic is retired, not merely falsified.** "~+200 ms per batch" and "480 ms of margin
⇒ two batches" were read off absolute figures whose machine-to-machine term is 1,320 ms. A per-batch
cost cannot be recovered from unmatched absolute readings at all.

### 3. What is done

`kernel_cost.py` now reports **UNMEASURABLE** — naming the load it saw and the band its own effect
measurement covers (2.20 / 3.42 / 3.88 / 4.08) — instead of reporting OVER, whenever the one-minute
load is outside that band. It still exits non-zero (rc 3): **a refusal is not a pass**, and the
per-declaration `OVER ⛔` markers are printed unchanged so the readings stay visible
([[a-gate-that-refuses-must-say-what-it-saw]]).

⭐ **Two new selftest arms, and the second is the held-out one.** The refusal fires on a machine
state rather than on a file, so it cannot be planted in the ceiling file like the other four; the
load is overridden instead (`X86LEAN_FAKE_LOADAVG`, printed on every run that uses it, and able only
to make the verdict stricter — never to turn a red into a pass). Arm 5 forces a load outside the band
and requires UNMEASURABLE; **arm 6 forces one inside it and requires that the refusal does NOT fire**,
without which the change is indistinguishable from switching the gate off. ### 3a. ⛔⛔ And the probe reproduced this decision's own confusion, one hour later

The positive control was first written to run at a **forced** calibrated load (`X86LEAN_FAKE_LOADAVG=
"1.00"`), on the reasoning that a control which cannot tell *"the ceilings pass"* from *"the machine
is busy"* reports the second as a failure of the first.

**That was a defect, and the selftest caught it by failing.** Forcing the load suppresses the
VERDICT but not the CONDITION: the child still profiled a busy machine, only with the refusal
disabled — so the arm asserted *"the ceilings pass"* about a reading that cannot support either
answer. ⇒ 🔑 **A SEAM THAT SILENCES A GATE'S REFUSAL DOES NOT CREATE THE CONDITION THE REFUSAL WAS
GUARDING**, and the arm that used it was making exactly the machine-reading-as-code-fact mistake this
decision exists to name. It was written an hour after the decision, by the head that wrote the
decision.

The control now runs at the REAL load and admits three outcomes, because there are three:

```
rc 0   the ceilings pass                      → the control did its job
rc 3   UNMEASURABLE at this load              → it could not, and SAYS SO in its own line
rc 1   over ceiling AT A CALIBRATED LOAD      → a real regression, and the arm FAILS
```

⚠️ The middle case is **a pass that prints its own uselessness** — it states that the control passed
WITHOUT checking the ceilings, and that the only thing verified was that the gate refused rather than
guessed. It is not an escape hatch: `rc 1`, the one outcome meaning *"the code got slower on a
machine quiet enough to tell"*, still fails.

### 4. ⚠️ The honest cost

**On a machine that is never this quiet, the gate is now silent**, and every reading in the table
above is outside the band. That is worse than a gate that works and better than one that lies. The
repair is to **gate the DELTA between two trees measured in one session** — the instrument the table
above was produced by hand — and it is a batch with its own red probes (a gate that measures two trees
has two ways to measure the wrong one), not something to smuggle into a semantics batch.

**Reversal cost:** one constant, one branch, two selftest arms.

---

## D112 — the packed binary group's memory shape: a batch that adds no coverage and removes an over-claim

**P2 batch 15.** `Op.vbinm` gives the nineteen operations of `Op.vbin` their second operand shape.
One constructor, 22 vectors, no new roster row, no new state.

### 1. The number does not move, and that is the argument

Measured over the census's `asm` class: the nineteen are **182,286** instructions, of which
**166,269** are buildable (the rest MMX-register) and **7,705 (4.63%)** take a memory source. The
census counts by MNEMONIC, so **all of them have been counted as covered since batch 7** — including
the 7,705 the model could not execute.

⇒ 🔑 **AN OVER-CLAIM IS INVISIBLE TO THE INSTRUMENT THAT PRODUCES IT.** A coverage census keyed on
mnemonics cannot see a missing operand shape, in either direction: it neither rewards this batch nor
reported the gap that made it necessary. The only defence is to price the SHAPE and not the
mnemonic, which is what `vshiftm` did at 0.85% (D107) and what this does at 4.63%.

⚠️ Stated plainly so no later reader mistakes it for a coverage win: **`docs/DEMAND-CENSUS.md`,
`docs/DEMAND-CENSUS.md.json` and `docs/P2-ROSTER.md` are BYTE-IDENTICAL after this batch** — not even
the model stamp moves, because the model gained no MNEMONIC. `demand_census.py --check` passes
without regeneration. That is the correct outcome, and it is the claim of this decision confirmed by
the instrument itself: the census cannot see what this batch did, in either direction.

⚠️ Contrast batch 14, which added three mnemonics and moved the gap by exactly 12,064. The two
batches are the same size in instructions and one is invisible to the census. **That difference is
the decision, not an accident of this batch.**

### 2. The oracle was measured at THIS shape

D108's law — oracle support is a fact about a **(mnemonic, SHAPE) pair** — applied without exception:
all nineteen are validated at the register shape, none had ever been asked at a memory source. All
nineteen execute and return this model's `vbinApply` value at all 88 pre-states, discriminating in
65–88 of them. ⚠️ `pand`'s 65 is the lowest and is recorded rather than pooled: AND against a source
sharing bits is the likeliest of the nineteen to leave the destination unchanged.

### 3. The operand order

`vbinApply k dst mem`. Eleven of the nineteen commute; `psub*` and the eight unpacks do not, and
`vbinApply`'s unpack arm takes its FIRST argument as the destination, whose lane goes low in each
pair. `wrongVbinmOperandsSwapped` is planted for it and is caught by twelve of the nineteen vectors.
⚠️ **That minority is the number to read**: an arm caught by a minority of a group's vectors is an arm
whose group needed exactly those, and pooling it into "caught" would hide which seven are carrying
nothing for this claim.

**Reversal cost:** one constructor, one step arm, three theorems, 22 vectors.

---

## D113 — the alignment rule stops being unvalidatable, and the arm D91 called impossible is written

**P2 batch 15.** For nine batches this repository has carried a rule its oracle could not check.
D91 (batch 6) stated it exactly, and was right:

> *"`movdqa` ignores its alignment requirement` cannot be caught by any vector that can exist, and an
> arm no vector can distinguish is not a weak test but a FALSE ENTRY in the gate's own inventory."*

### 1. D110 found the reason, and the reason contained the exception

x86isa implements the 16-byte `#GP` in **exactly one file of its whole instruction tree**
(`grep -rln 16-byte-aligned` ⇒ `logical.lisp`), and that file implements `pand`, `por` and `pxor`.
So the rule is unvalidatable for sixteen of the nineteen and **validatable for three**.

⭐ **THE SPLIT WAS PREDICTED FROM THE SOURCE BEFORE IT WAS MEASURED**, which is the strongest shape
this evidence can take — a claim registered in a form that could have been wrong:

```
                            predicted    MEASURED (88 pre-states)
por       8(%rbx),%xmm0     refuses      refuses    88 of 88
paddd     8(%rbx),%xmm0     executes     executes    0 refused
psubw     8(%rbx),%xmm0     executes     executes    0 refused
punpcklbw 8(%rbx),%xmm0     executes     executes    0 refused
```

⇒ 🔑 **ONE EXCEPTION CLASS, ONE OPERAND SIZE, TWO BEHAVIOURS — AND THE LINE BETWEEN THEM IS WHICH
FILE IMPLEMENTS THE INSTRUCTION.** D110 recorded that as an observation about the oracle; here it is
used as a PREDICTION, and predicting correctly is what turns it from a curiosity into a tool. The
next head can now decide in advance which rules of this class a run can check, by reading x86isa's
tree rather than by discovering it in a red run.

### 2. Three vectors in which both models refuse — and what makes them worth anything

`pand_m_unal`, `por_m_unal`, `pxor_m_unal` at `0x8(%rbx)`. Both models refuse; `bothRefused` reports
agreement; the rule is finally carried by a run.

⚠️⚠️ **AGREEMENT BY MUTUAL REFUSAL IS SILENCE.** Two sides refusing is indistinguishable from two
sides broken, and a vector whose only content is that nothing happened is worth precisely what a
planted model would cost it ([[a-refusing-form-needs-a-refuse-always-control]]). So the arm D91 called
impossible is written: `wrongVbinmIgnoresAlignment` executes at an unaligned address, disagrees in
`refused` — D33's channel, which exists because `ud2` walked into the same gap — and is caught.

⇒ **Those three vectors are worth exactly what that arm catches, and not one case more.** The claim
is not "the alignment rule is now tested"; it is "the alignment rule is now tested at three of the
nineteen, against an oracle that implements it there and nowhere else, and the observation is priced
by a planted model rather than by the absence of a disagreement."

⛔ **The other sixteen are unchanged and still theorem-only** (`vbinm_unaligned_faults`), as are
`vload`, `vstore`, `vshufm` and `vshiftm`. D91's entry is amended in scope, not retired: it named a
general truth about this oracle that has exactly one exception, and the exception is now used.

**Reversal cost:** three vectors and one arm.


---

## D114 — a denominator borrowed from the neighbouring instrument invents an explanation for its own gap

**P2 batch 15, correcting P2 batch 14.** The permute batch's record reported its second planted arm
as *"84 disagreements in `xmm2` … 84 of 88 rather than 88 because in four pre-states `xmm2` and
`xmm3` happen to permute to the same value."*

**There are no missing four.** `driveWrong` emits over `preStates seed 4`, which is **84** states;
the differential emits over **88**. The arm caught **84 of 84 — every case it ran**.

### What actually happened

Both numbers appear in every batch record, one screen apart. `88` was the one in front of me,
because the differential's line is the batch's headline receipt. The arm's `84` was then read against
it, the difference became a gap, and **a gap invites a mechanism** — so one was supplied, phrased
exactly like a measurement (*"in four pre-states … happen to permute to the same value"*) and never
computed.

⇒ 🔑 **A DENOMINATOR BORROWED FROM THE NEIGHBOURING INSTRUMENT INVENTS AN EXPLANATION FOR ITS OWN
GAP.** The wrong denominator does not produce an obviously wrong answer; it produces a plausible
one, and the plausibility is supplied by the writer rather than by the data. This is
[[a-normalisation-needs-its-denominator-to-vary-the-same-way]] in its cheapest form: not a
calibration failure, just two instruments with different sample counts quoted in one paragraph.

### What caught it

**Not a gate, and not re-reading.** The next batch's alignment arm came back at **252 = 84 × 3** —
three vectors, none of which could "coincide" in the way the invented mechanism described, all
reporting the same per-vector figure. ⇒ **The second instance is what made the first one legible.**

⚠️ The correction is recorded in `docs/DIFFERENTIAL-P2-BATCH12.md` and in batch 13's record, which
now states the two denominators explicitly beside the numbers. The commit message of `4f6766b`
carries the error and cannot be edited; this decision is where it is answered.

⇒ A number that needs a story is worth reading twice. This one got a story on the first reading and
was wrong for four hours.

**Reversal cost:** none — it is a correction, not a mechanism.

---

## D115 — the residue, measured: the oracle refuses more of the gap than it executes

**P2 batch 16. No forms, no vectors, no semantics — one ACL2 run and a table.**

### 1. What was wrong with the roster

`docs/P2-ROSTER.md`'s oracle column reads `⚠️ not measured` for any mnemonic `oracle_availability.py`
does not name. D65 established what that costs:

> *A DECLARED LIST INHERITS THE DIRECTION OF ITS DEFAULT. This one defaults to available, so every
> gap in it INVENTS work.*

Thirteen non-VEX ranked rows carried that mark. **One run of 30 forms × 88 pre-states settled all of
them**, with both controls behaving (`packuswb` and `paddd` executed at all 88, `pmaddwd` refused at
all 88).

### 2. What it found

**Eighteen mnemonics the roster was ranking as available work cannot be executed by the oracle at
all** — among them the ENTIRE saturating add/subtract family (`padds{b,w}`, `paddus{b,w}`,
`psubs{b,w}`, `psubus{b,w}`), both averages, the unsigned min/max pair, four multiplies, and
**both signed packs**.

⚠️ **The batch that found this was looking for the PACK group.** `packssdw` is rank 15 at 5,613
instructions and was marked `not measured`; `packuswb` beside it executes. A group sampled at one
member would have passed, and a batch's semantics would have been written against an oracle that
cannot run it. ⇒ [[a-batch-cannot-be-sampled]], the law that made `pmaddwd` a surprise at rank 1,
**paid a second time at rank 15** — and this time the sample would have been drawn from the same
mnemonic family, which is the sampling that feels safest.

### 3. ⭐⭐ THE NUMBER THAT CHANGES P2's SHAPE

```
                         BEFORE                     AFTER
the oracle EXECUTES      34 mnemonics  84,395       41 mnemonics   92,555   21.5%
the oracle REFUSES       11 mnemonics  79,863       27 mnemonics  108,578   25.3%
probed so far            45            164,258      68            201,133   46.8%
```

⚠️ **THE FIGURES IN THIS TABLE ARE AS OF BATCH 16 AND ARE NOT THE LIVE ONES — see D118 §6.** The
census's uncovered total has since moved (417,231), so the same 108,578 refusing instructions are
**26.0%**, not 25.3%, and the executing column derives differently too. The live figures are
generated into `docs/P2-ROSTER.md` by `scripts/p2_roster.py`, which CI holds byte-identical; quote
them from there. This table stays byte-untouched because a dated decision is a record of what was
measured that day — but a bank reproduced these numbers as current, so the pointer is written here
rather than left to be rediscovered.

⇒ 🔑 **THE ORACLE NOW REFUSES MORE OF THE UNCOVERED GAP THAN IT EXECUTES**, and the crossover
happened in one run because nobody had asked. More than a quarter of what P2 has left **cannot be
differentially validated at any price** — not by working harder, and not by a better batch order.

⚠️ This is a fact about the METHOD's ceiling, not about a batch, and it was reachable at any time
since P2 batch 1 for the cost of one ACL2 run. It was not reached because the roster's default made
every unmeasured row look like work rather than like a question.

### 4. What is buildable

Seven mnemonics moved the other way and are declared `executes`: the **six packed compares**
(`pcmpeq{b,w,d}`, `pcmpgt{b,w,d}`) and `pmovmskb`. With `packuswb`, which was already declared, that
is **13,012 buildable instructions** of the `asm` class — the next batch, and it is now picked from a
measurement rather than from a rank.

**Reversal cost:** 23 rows in `oracle_availability.py`; the gate holds them to the oracle in both
directions, so a row that starts executing is a finding rather than a silent stale entry.

---

## D116 — a control can share the blind spot of the thing it controls

**P2 batch 17.** The packed compares join `VBinKind` rather than taking a kind of their own: they
are packed binary operations, and both operand shapes come free from `Op.vbin` and `Op.vbinm`
together with the 16-byte alignment rule. Six roster rows, 13 vectors, no new constructor.

### 1. The group was picked from a measurement

D115's run left the compares as the only buildable candidate of this size in the residue — every
other one refuses. **7,454 buildable instructions.** That is the first batch in this repository
chosen from a measurement of the oracle rather than from a demand rank, and it is the whole point of
D115 landing first.

### 2. ⛔ What each vector prices is not uniform

Measured per form against three wrong models, 88 pre-states (a number is how many states the WRONG
model still agrees on — lower is a sharper vector):

```
                       unsigned   boolean   swapped
pcmpeqb %xmm1,%xmm0         88         9        88
pcmpeqd %xmm1,%xmm0         88        12        88
pcmpgtb %xmm1,%xmm0         61        34         0
pcmpgtd %xmm1,%xmm0         73        53         0
pcmpeqb (%rbx),%xmm0        88         0        88
pcmpgtw (%rbx),%xmm0        15         8         0
```

⚠️ **`pcmpeq` prices nothing about signedness or operand order.** Equality is the same relation
signed or unsigned and is symmetric, so both models agree with it at all 88 **by construction**.
Reporting "six mnemonics tested" as six tests of the signedness rule would be an over-claim of
exactly half the group — the kind no gate here can see, because a gate counts vectors.

### 3. ⛔⛔⛔ THE FINDING: the register-field control is blind to the batch's own rule

`pcmpgtb %xmm3,%xmm2` exists for the reason `movdqa_x4x5` does — batch 5 found that with every
vector reading xmm1 into xmm0, a model ignoring the register FIELDS is bit-identical to the right
one. It is a correct and necessary control.

**And the unsigned model agrees with the right one at ALL 88 pre-states on it**, against 61 of 88 on
`pcmpgtb %xmm1,%xmm0`. `xmmPattern` gives xmm2 and xmm3 byte lanes that never differ in sign in a
discriminating way.

⇒ 🔑 **A CONTROL CAN SHARE THE BLIND SPOT OF THE THING IT CONTROLS.** The vector is worth exactly
what it was added for and **zero** for the rule the batch is about. Had the group carried only its
register-field control at `pcmpgtb` — the natural economy, one control per constructor — the
signedness rule would have been untested and the run green.

⚠️ **What made it visible was measuring the two vectors SEPARATELY** instead of reporting "the
`pcmpgtb` vectors". A per-form column costs nothing to print and is the only thing that can show one
member of a group carrying a rule and another carrying none of it
([[a-control-can-share-the-blind-spot]] — written down after a held-out value was drawn from the same
half of the space, and here the same shape appears in a REGISTER PAIR rather than in a value).

### 4. The two wrong models, and why neither is a strawman

**Unsigned.** Lean's `<` on `BitVec` IS unsigned. `y.slt x` is the arm; `y < x` compiles, and is
bit-identical wherever both lanes are non-negative. A model written without noticing the SDM's word
"signed" lands exactly there.

**Boolean, not mask.** A lane becomes all ones or all zeros, never 1 — and the flag model is
bit-identical in the LOW BIT of every lane, which is the bit a reader coming from `Flags` is thinking
about. Measured: it survives 34–53 of 88 at the register shape and 0–8 at the memory shape, so **the
memory vectors are carrying this arm and the register ones are barely carrying it at all.**

### 5. ⛔⛔ AND THE FILTERED SELFTEST RAN HALF THE BATCH'S ARMS AND SAID PASS

`x86lean-diff selftest "<substring>"` selects arms by substring. This batch's two arms are named
*"pcmpgt compares its lanes as UNSIGNED"* and *"a packed compare writes 1 instead of an all-ones
MASK"* — and **they share no substring**. Filtering on `"packed compare"` ran ONE of them and printed

```
harness selftest (filtered by "packed compare") — 1 of 111 arms:
  ✔ a packed compare writes 1 instead of an all-ones MASK: caught — 822 in `xmm0`
filtered selftest: PASS
```

**The arm that never ran is the signedness one — the whole subject of this decision.** A green
`filtered selftest: PASS` was printed about a subject half the size of the one intended.

⇒ 🔑 **A FILTER THAT NAMES A GROUP MUST BE CHECKED AGAINST THE GROUP'S SIZE.** The count is right
there in the header (`1 of 111`) and it is the only thing that distinguishes "the arms passed" from
"the arms I meant were not selected". The verdict line cannot: it says PASS either way.

⚠️ This is the session's own recurring shape arriving in the tool used to check for it — an
instrument reporting success about a subject smaller than the one intended, exactly as `refusal: 0`
would have, exactly as the 84-vs-88 denominator did. **The defence is the same each time: read what
the instrument says it measured, not only what it concluded.**

⇒ The batch's arms are reported here per arm and per name, with their counts, so a later reader can
see two and not a verdict.

**Reversal cost:** six `VBinKind` constructors, six `vbinApply` arms, six roster rows, 13 vectors.

---

## D117 — `packuswb`: a group one mnemonic wide, and a truncation model that a gentle vector table would have missed

**P2 batch 18.** `packuswb` joins `VBinKind`; `vpackus` is a new combinator because this is the
first NARROWING operation here — lane `i` of the result is not a function of lane `i` of the
operands, so `vlanes` cannot express it.

### 1. The group is one mnemonic wide, and that is a measurement rather than a choice

`packsswb` and `packssdw` refuse on the oracle at every pre-state (D115). `packssdw` is **roster rank
15 at 5,613 instructions** and was marked `not measured`, which the roster's default reads as
available.

⇒ 🔑 **A batch sampled at `packuswb` would have passed** — same encoding family, adjacent opcodes,
same operand shapes, executes at 88 of 88 and returns the SDM's answer. [[a-batch-cannot-be-sampled]]
again, and this time the sample would have been drawn from **the same mnemonic family**, which is the
sampling that feels safest of all. The defence was not judgement; it was measuring all three.

### 2. The saturation, and the model a gentle table would have missed

Source lanes SIGNED, result lanes UNSIGNED: a negative word saturates to 0, one above 255 to 255 —
opposite ends of the range. Against the oracle, 88 of 88 at both shapes, with three models refuted:

```
                          trunc   unsigned-source   swapped
packuswb %xmm1,%xmm0          0                32        20
packuswb (%rbx),%xmm0         0                 0        38
```

⚠️ **Truncation scores 0 of 88 here, and that number is a property of the PRE-STATES, not of the
instruction.** Keeping the low byte is bit-identical at every in-range value. A vector table of small
positive constants would have scored truncation 88 of 88 and reported a green run about a model that
does not saturate at all. What refutes it is `adversarial` reaching `0x8000`, `0xFFFF` and `0x7FFF` —
a choice made in P0 for scalar arithmetic and doing the work here.

⇒ 🔑 **A WRONG MODEL'S SCORE IS A JOINT FACT ABOUT THE MODEL AND THE PRE-STATES**, and reporting it
without saying which is doing the work invites the next head to trust a table that cannot reach the
rule.

⭐ And the unsigned-source model is refuted best by the MEMORY vector (0 of 88 against 32 at the
register shape), because the memory source sweeps where `xmm1` is a fixed pattern — so the two
vectors are not interchangeable and neither is redundant.

### 3. Both arms share a substring, deliberately

`"packuswb truncates instead of saturating"` and `"packuswb reads its source as UNSIGNED…"` both
contain `packuswb`, so one filter selects both. That is a direct response to D116 §5, where two arms
of one batch shared no substring, `selftest` ran half of them and printed PASS.

**Reversal cost:** one `VBinKind` constructor, one combinator, one roster row, 2 vectors, 2 arms.

---

## D118 — the scalar-FP group, measured; and every availability verdict in the table was a reading at zero

**P2 batch 19. No forms, no vectors, no semantics — one repaired instrument and six settled rows.**

### 1. The claim that was false, and the shape of its falsity

Batch 18's bank closed with the sentence that sets the next head's queue:

> *`pmovmskb` (453) is the only executing mnemonic left unbuilt from the probed set. Everything
> larger either refuses or is VEX — which needs VEX decoding vocabulary and is unpriced.*

The first sentence is true and is correctly scoped to **the probed set**. The second is a claim about
the **whole residue**, and it is false. `docs/P2-ROSTER.md` carried 26 rows marked `⚠️ not measured`;
18 are VEX, two (`movd`, `psubw`) are `100% — PHANTOM ROW` MMX demand whose xmm probe correctly does
not transfer — and **six are scalar SSE floating point that had never been asked about at all**:

```
mulss 5,698 · mulsd 5,482 · addss 4,696 · addsd 4,260 · movhps 3,672 · cvtss2sd 2,949
TOTAL 26,757 instructions — larger than any of the last five batches (14 was 12,064; 18 was 5,105)
```

⇒ 🔑 **A CATEGORY WITH NO SLOT IN THE SENTENCE READS AS ABSENT.** "Refuses or VEX" is a two-valued
partition offered for a three-valued residue, and the third class did not read as *unhandled*, it
read as *empty*. This is [[feedback-a-declared-list-inherits-its-default]] moved up one level: not a
list whose gaps default to available, but a **sentence** whose missing case defaults to nothing.
And it sat in a bank's closing "next" line — the one sentence a relight acts on and nobody
re-derives.

### 2. ⭐⭐ THE INSTRUMENT: every verdict in the table was a reading at ONE point of the value space

`init-x86-state-64` takes no XMM argument, so `measure_cr4` never wrote one. Every `executes` and
every `refuses` in `P2_FORMS` — 77 rows, gated in both directions, joined into the roster, and used
to pick batches 17 and 18 — was a reading taken at **xmm0 = xmm1 = 0**. Nothing declared that; it was
the default of a function with no parameter for it, which is the quietest kind of frozen dimension.

**And the frozen point can invert a verdict.** `cvtss2sd` at a zero source neither executes nor
refuses:

```
ACL2 Error [Evaluation]: The guard for (RTL::SSE-POST-COMP U MXCSR F), which is
(AND (REAL/RATIONALP U) (NOT (= U 0)) (NATP MXCSR) (RTL::FORMATP F)), is violated
by the arguments in the call (RTL::SSE-POST-COMP 0 8064 '(NIL 53 11)).
```

A guard violation produces **no reading** — a THIRD verdict the two-valued model has no slot for, and
one that surfaces as an absence. At any non-zero source the same form executes and returns the right
answer. Read at zero it looks unavailable; it is available.

⇒ 🔑 **A PROBE THAT NEVER VARIES A DIMENSION REPORTS THE DEFAULT OF THAT DIMENSION, AND THE DEFAULT
LOOKS LIKE AN ANSWER.**

### 3. What the re-measurement found, and the honest bound on it

All 77 rows re-read at non-zero operands (xmm0 = `0x4040…40`, xmm1 = `0x4020…20`, chosen so the same
bits are a NORMAL number under every FP reading — low32 3.0078f, low64 ≈32.5 — and an ordinary
non-zero integer under every packed reading; a random pattern would have been a NaN or denormal under
some reading and would have turned an availability probe into a value probe):

**77 of 77 agree with the zero reading. Zero flips. Zero crashes.**

⚠️ **So the hazard is real and has NOT corrupted the table.** That is the honest result and it is
worth stating in both halves: the freeze could invert a verdict (proved, by `cvtss2sd`), and on the
77 rows actually in the table it did not.

⚠️⚠️ **AND 77/77 IS EXACTLY WHAT A NO-OP WRITE WOULD ALSO PRINT.** The forms that agree at zero are
precisely the ones that agree everywhere, so an xmm write that silently did nothing produces an
identical green table. The first run of this measurement carried no arm that could tell those apart
and therefore established nothing; §4 is the repair.

⛔ **THE DIFFERENTIAL IS NOT AFFECTED, and the scope matters.** `scripts/x86isa_driver.lisp` sets xmm
from each case's `:xmms`, and the emitted 83,072 cases carry varying values. The frozen dimension was
only ever in the AVAILABILITY probe — the instrument that decides **which batch is next**, not the
one that validates a batch. No landed vector's validation is in question.

### 4. The operand control, and its three red arms

`p2_operand_control()` runs in the same ACL2 session as the table and requires:

| arm | requirement | what its failure means |
|---|---|---|
| `cvt_nonzero` | executes | the probe's own subject does not run; nothing it says is readable |
| `cvt_zero` | **no reading** | either x86isa repaired the guard (a finding) or operands are not arriving |
| `witness` | `packuswb` → all-ones | a zeroed xmm cannot produce all-ones, so the write did not land |

The witness is the one that **observes the write directly** rather than inferring it from an absence:
saturating `0x4040`/`0x4020` words to unsigned bytes gives `0xff…ff`, which no zero operand can
produce. All three branches were driven red before the green was believed — the write zeroed (both
`cvt_nonzero` and `witness` fire, two independent routes), the zero-crash removed, and the witness
re-pointed at `pxor` — with the shipped arms passing in the same session.

⚠️ The `cvt_zero` arm is stated as *"these two must DIFFER"* and not *"zero must crash"*, because an
x86isa that repairs the guard is a **finding about the oracle**, not a false alarm; it must fire and
be re-pointed at whatever still varies, not be silenced.

### 5. What is buildable, and what this is NOT

The roster moves:

```
                    BEFORE                    AFTER
the oracle EXECUTES 41 mnemonics   79,996     47 mnemonics  106,753   25.6%
the oracle REFUSES  27            108,578     27            108,578   26.0%
probed              68            188,574     74            215,331   51.6%
```

⛔ **"EXECUTES" IS NOT "BUILDABLE THIS WEEK", and this batch does not pretend the group is next.**
`X86/State.lean` has no MXCSR (absent on purpose, D2), and Lean's `Float` is an opaque extern type
the kernel cannot reduce — so a definitional, `decide`-checkable model of these six needs a
**soft-float IEEE-754 layer over `BitVec`** plus a new state field, and
[[feedback-a-state-field-costs-every-record-proof]] records that two fields blew three unrelated
record proofs. That is a **design block for the helm**, priced here and not started.

⇒ The measured buildable work that needs no new vocabulary is still `pmovmskb` (453).

### 6. ⚠️ A DRIFT FOUND ON THE WAY, AND NOT REPAIRED IN THE DIRECTION IT LOOKS

D115 §3 prints `executes 41 / 92,555 / 21.5%`, `refuses 27 / 108,578 / 25.3%`, `probed 68 / 201,133 /
46.8%`. The generator today derives `41 / 79,996 / 19.2%` and `68 / 188,574 / 45.2%` for the same
table, and the refusing share is **26.0%, not 25.3%** — the absolute is unchanged and the
DENOMINATOR moved (the census's uncovered total is now 417,231). D115's figures were true when
written and are left byte-untouched as a dated record; what was wrong is that the **bank reproduced
them as current**, and the standing order to print "the refusing 25.3%" beside every coverage number
therefore names a stale figure.

⇒ 🔑 **A DATED RECORD IS NOT STALE; A QUOTATION OF IT IS.** No gated artifact carried the drift —
`docs/COVERAGE.md` and `README.md` are clean — which is why nothing fired. The pointer added to D115
says where the live figures are, so the next quotation is taken from the generator.

**Reversal cost:** two constants, four lines in `measure_cr4`, six `P2_FORMS` rows, one control
function; `docs/P2-ROSTER.md` regenerates.

---

## D119 — `movhps`: the half that does not move, and an absence measured instead of asserted

**P2 batch 20; sixteenth differential record.** Two constructors, 6 vectors, one roster row, no new
state, 3,672 instructions.

### 1. Why this form and not `pmovmskb`

D118 measured six scalar-SSE-FP mnemonics the residue had been reporting as absent (26,757
instructions). The Captain's 19:21 ruling put them first. ⛔ **They do not build together, and saying
so was half the batch:** `mulss`/`mulsd`/`addss`/`addsd`/`cvtss2sd` (23,085) need a soft-float
IEEE-754 layer over `BitVec` plus MXCSR — Lean's `Float` is an opaque extern the kernel cannot
reduce, so a `decide`-checkable model cannot borrow it — and that is a design commission, posted and
not started. `movhps` is the one of the six that is a **pure data move**.

⇒ 🔑 **"EXECUTES ON THE ORACLE" AND "BUILDABLE" ARE DIFFERENT PROPERTIES, AND THE ROSTER HAS A COLUMN
FOR ONLY ONE.** That is D115's own finding one level down: there a ranked table priced demand and not
buildability; here a *measured* table prices oracle support and not the model's own vocabulary.

### 2. The content is the half that does not move

```
load  (0f 16):  dst[127:64] ← m64,  dst[63:0] PRESERVED
store (0f 17):  m64 ← src[127:64]
```

⭐ **So the plausible wrong model is the one that CLEARS the low half — the exact mirror of D93.**
There ACL2 x86isa *merged* what the SDM clears (`movd` into XMM). Here the SDM *preserves*, so the
direction of the plausible error reverses with the rule. A model that clears is bit-identical to this
one at every pre-state whose low quadword is already zero.

```
                     loads-low   clears-low   stores-low
movhps loads (xmm0)        146          152            —
movhps store (mem)           —            —          208
```

⚠️ **152 is a joint fact about the model and the PRE-STATES** ([[feedback-a-wrong-models-score-is-a-joint-fact]]).
What refutes `clears-low` is `xmmPattern` giving xmm0 a non-zero low quadword; a pre-state table that
zeroed the destination would have scored it 0 and reported green about a model that destroys half the
register on every load.

### 3. ⛔ The alignment rule is ABSENT, and the absence is measured

The memory operand is eight bytes, so SDM Exception Type 5 applies and no alignment is required.
**D110 is why that sentence is not left to a comment:** there, *"NO ALIGNMENT CHECK … the absence is
the rule"* was written about a group that DID have one, and the model's missing check and the
oracle's missing check were the same omission — two defects that cancel, invisible to the differential
that compares them.

So it was measured, with a **two-sided control in the same run**:

```
movhps, both directions, at 16- / 8- / 4-byte alignment     EXECUTES
pand 0x8(%rbx),%xmm0   [x86isa's one file that checks 16B]  REFUSES
pand (%rbx),%xmm0                                           EXECUTES
```

⇒ The harness demonstrably **can** see an alignment refusal, so `movhps`'s silence is a reading and
not a blind spot. K's rules carry no check either — a third source independent of both.

⚠️ **The unaligned vectors are at displacement 4, not 8.** Eight is still 8-byte aligned and could not
distinguish "no alignment rule at all" from "an 8-byte rule" — the control must differ in the
dimension most likely frozen ([[feedback-a-control-can-share-the-blind-spot]]). Both addresses were
checked against the watched window (`0x1fe0` + 64) rather than assumed.

⛔ **AND A CONTROL WITH THE WRONG ENCODING IS A CONTROL FOR A DIFFERENT INSTRUCTION.** The first
`pand` control EXECUTED unaligned and looked like a finding against D113 — because it was written
`0fdb…`, the **MMX** `pand`, with the `66` prefix dropped. MMX has no 16-byte rule, so the reading was
true of the instruction actually run. It fails in the direction that MANUFACTURES a finding, and the
only thing that caught it was that D113 predicted the opposite. ⇒ 🔑 **Assemble a control's bytes;
never hand-write them from memory.**

### 4. Two constructors, and deliberately not a `VMovKind`

`Op.vloadh`/`Op.vstoreh` are two for the reason `vload`/`vstore` are: an operand pair admitting `mem`
on both sides could spell `movhps (%rax),(%rbx)`, which no encoding produces. And it is **not** a
fifth `VMovKind`: that type's entire content is `VMovKind.aligned`, the 16-byte rule, and a member
whose answer to it is meaningless is a field someone reads eventually.

⚠️ ONE roster row for both directions — one mnemonic at two opcodes, unlike `movdqa`/`movdqu`, which
are two rows because a disassembler prints two names. ⚠️ Two of the six vectors use `%xmm5` for D90's
reason: batch 5's vectors all moved xmm1 into xmm0, so a fixed-register model was bit-identical to the
real one and the register fields were decoded by nothing.

### 5. Receipts, and the gate that REFUSED

```
cases=83600 matched=63068 explained=29435 unexplained=0 oracle-divergence=171 oracle-leaks=0 missing=0
```
171 oracle-divergences, unchanged; this batch adds none.

⛔ **The kernel-cost gate refused rather than reporting**, twice: one-minute load 4.61 then 4.24,
outside the band its own effect-measurement covers (0.0–4.1). The load is not this batch's — `ps`
attributes it to WebKit, a vendor updater and another seat's bus scanner
([[feedback-enumerate-is-not-attribute]]) — and it does not go quiet on this machine. That is the
pre-existing condition the batch-18 bank records, not a regression here; the gate printing readings
and withholding a verdict is the RIGHT refusal, because a machine-calibrated gate that answered here
would be reporting the machine ([[feedback-a-machine-calibrated-gate-belongs-where-it-is-calibrated]]).
⚠️ **`vectorCoverage` reads 1680 of its 1760 ceiling — 95%, and the margin is the number to read, not
the verdict** ([[feedback-a-pass-at-97-percent-is-not-headroom]]). The priced repair is unchanged and
unstarted: gate the DELTA between two trees measured in one session (D111).

**Reversal cost:** two AST constructors, one semantics clause, one coverage row, one roster row,
6 vectors, 3 arms, 6 `claimed_forms` exemptions.

---

## D120 — the census of the unprobed remainder: VEX is SPLIT, and the hole is a third

**P2 batch 21. No forms, no vectors — one ACL2 run of 18 arms and a table that moves the plan.**

### 1. Why this run happened before it was asked for

The Captain's 19:21 ruling makes arm C (a second, K-backed oracle) ripen *"when the measured buildable
list is EMPTY — post the census that proves it."* D118 is the reason that census was run **now**
rather than at the moment the list looked empty: an ASSERTED-empty queue is precisely the thing that
had just turned out to be wrong, and the assertion had survived a whole relight.

Only 74 of the residue's mnemonics had ever been asked — **51.6% of the demand. 48.4% had never been
measured at all**, and every unmeasured row defaults to *available* (D65).

### 2. ⛔⛔ VEX IS NOT ONE CLASS, AND EVERY SENTENCE HERE HAD TREATED IT AS ONE

Batch 18's bank read *"everything larger either refuses or is VEX — which needs VEX decoding
vocabulary and is unpriced"*. That sentence has two failures, and D118 only found the first. The
second is here: it treats **VEX as a single class blocked by one cause** — our decoder. Measured:

```
vmovaps  (ymm)  7,599  EXECUTES        vpmaddwd (ymm)  7,209  REFUSES
vpsubw   (ymm)  6,234  EXECUTES        vpsrad   (ymm)  6,338  REFUSES
vmovdqu  (ymm)  6,160  EXECUTES        vshufps  (ymm)  4,693  REFUSES
                                       vpbroadcastd    3,941  REFUSES
                                       vaddps   (ymm)  3,434  REFUSES
                                       vpshufb  (ymm)  2,984  REFUSES
                                       vmulps   (ymm)  2,715  REFUSES
```

⇒ 🔑 **THE VEX RESIDUE IS BLOCKED BY BOTH CAUSES AT ONCE, IN DIFFERENT PLACES.** A plan that priced
only the decoding vocabulary would have bought the *executing* half and discovered the rest at the
differential; a plan that priced only the oracle would have missed that half of it is available today
if the decoder existed. Neither number alone describes the work.

⚠️ Note the shape: the *moves* execute and the *arithmetic and permutes* refuse. That is the same
split x86isa shows at SSE, one register width up — evidence about the oracle's coverage pattern
rather than about AVX.

### 3. WHAT IS BUILDABLE TODAY THAT NOBODY KNEW WAS

⭐ **`prefetchnta` and `prefetcht0` — 466 instructions — EXECUTE, and are architecturally NO-OPS.**
They change no state this model observes.

⚠️ **That is the claim in this decision most likely to be wrong, and it is deliberately NOT yet a
semantics.** [[feedback-the-burden-is-on-the-departure]]: a spec's "no-op" is only a no-op where the
write is invisible, and the burden is on the departure — the manual has not executed, the oracle has.
It is recorded here as a MEASUREMENT of the oracle, and a batch that implements it must show the
model and the oracle agree on all 88 pre-states before the word "no-op" appears in a semantics.

⚠️ `cvtsi2sd`/`cvtsi2ss` (2,603) execute and **join the soft-float commission** rather than the
buildable list: they are blocked by this model's missing MXCSR and by Lean's `Float` being an opaque
extern, not by the oracle. The commission is 23,085 → **25,688**.

⚠️ `emms` executes and `pshufw` refuses; both are MMX and **declined by design** (no MMX register
file). Recorded so neither reads as available work.

### 4. ⭐⭐ THE NUMBER THAT CHANGES THE RULING'S ARITHMETIC

```
                    BEFORE (D118)              AFTER
the oracle EXECUTES 47 mnemonics  106,753      55 mnemonics  129,979   31.2%
the oracle REFUSES  27            108,578      35            140,534   33.7%
probed              74            215,331      90            270,513   64.8%
```

⇒ **THE KNOWN HOLE IS 33.7%, NOT 26.0% AND NOT THE ORDERED 25.3%.** It grew by a third of itself in
one run, because the refusing set was never the eighteen mnemonics the ruling names — those were
simply the refusing rows that had been *looked at*. This is the strongest available argument for arm
C, and it is an argument the ruling could not have had, because the measurement did not exist.

⚠️ **AND THE CENSUS IS NOT FINISHED.** 35.2% of the demand is still unprobed. The number above is a
floor on the hole, not its size — every further run has so far moved it in the same direction, which
is the direction that shrinks the buildable list.

**Reversal cost:** 16 rows in `oracle_availability.py`, gated in both CR4 arms; `docs/P2-ROSTER.md`
regenerates.

---

## D121 — `PREFETCHh`: a form that changes nothing, and the gate that named a cheaper build

**P2 batch 22; seventeenth differential record.** One constructor, 4 vectors, two roster rows, no new
state, 466 instructions.

### 1. It exists because batch 21 MEASURED instead of declaring

`prefetchnta` (315) and `prefetcht0` (151) were invisible until D120's census asked the oracle about
the unprobed remainder. They are the direct answer to the question *"is the buildable list empty?"* —
which had been answered "yes, except `pmovmskb`" from a list nobody had finished measuring.

### 2. ⚠️ THE CLAIM IS NARROW, AND THE NARROWNESS IS THE BATCH

`step` advances RIP and does nothing else. PREFETCHh reads no memory and **does not fault** — not on
an unmapped address, not on a misaligned one. So the differential can witness only that both models
leave every watched register, flag and memory window alone and advance RIP by the right length.

⛔ **A form that writes nothing is one whose vectors agree with almost any wrong model**
([[feedback-unobserved-regions-report-agreement]]). The two arms are what stop that agreement being
vacuous — `prefetch faults on its operand` (336 in `refused`) and `prefetch loads its operand into
rax` (292 in `rax`), both real misreadings of the SDM's word *hint*.

⚠️ The word "no-op" was NOT taken from the manual. D120 recorded it as a measurement of the oracle and
explicitly refused to write it into a semantics until a run said so; this batch is that run
([[feedback-the-burden-is-on-the-departure]]).

### 3. ⛔ NO ARM FOR THE HINT, AND THAT IS A DECISION RATHER THAN AN OMISSION

*"Prefetch ignores its locality hint"* is architecturally invisible: no vector that can exist would
distinguish it. An arm for it would be a **FALSE ENTRY in the gate's own inventory**, which is D91's
rule and a cost this repository has already paid once. The spellings are held apart by
`scripts/check_encodings.py`, which assembles each `asm` and compares bytes — **the instrument that
can actually see a `/reg` field**. ⇒ 🔑 The response to an undistinguishable claim is to move it to a
gate that can see it, never to plant an arm that cannot fire.

### 4. ⛔⛔ TWO ROWS, NOT FOUR — THE KERNEL-COST GATE NAMED THE CHEAPER BUILD

The first cut modelled all four hints. The gate refused: four roster rows put `Tests.Coverage`'s
residue **700 ms over its ceiling**, because several `decide` theorems are quadratic in the row count.
`prefetcht1`/`prefetcht2` have **zero measured demand** — absent from the census entirely — so
modelling them was completionism, not demand, which is the instinct this roster declines at `pshufw`.

⇒ 🔑 **THE REFUSAL NAMED A CHEAPER BUILD, AND THE CHEAPER BUILD WAS THE MORE HONEST ONE**
([[feedback-a-gate-that-refuses-names-a-cheaper-build]]). It weakens nothing. Shortening the `note`
strings — prose the kernel walks character by character — was the other half, and moved `X86.Syntax`
204 → 200 ([[feedback-prose-in-a-kernel-reduced-string-is-a-cost]], re-paid a third time).

### 5. ⭐⭐ D111's METHOD, RUN FOR THE FIRST TIME, AND WHAT IT FOUND

The gate could not return a verdict in four attempts (one-minute loads 3.60, 5.85, 6.20, 6.38 against
a band of 0.0–4.1; `ps` attributes the load to WebKit, a vendor updater and another seat's bus
scanner). So D111's priced-and-unstarted repair was applied **as a measurement**: parent and current
tree, profiled back to back in one session.

```
                          parent 873a4d9      this batch      delta
X86.Syntax                     206.0 ⛔           205.0        ~0
Tests.Coverage (residue)      12540  ⛔          12900        +360
```

⛔ **THE PARENT IS ALREADY OVER BOTH CEILINGS WITH NONE OF THIS BATCH IN IT.** And across four runs of
substantially identical code `X86.Syntax` read **204, 205, 206 and 244** — a 20% spread.

> ⛔⛔ **CORRECTION, D122, and it is against this section's own method.** The parent readings above were
> taken OUT OF BAND (load 6.07). An IN-BAND profile of the same parent tree (load 3.90) reads
> `X86.Syntax` **198.0 — UNDER its ceiling**, and only `Tests.Coverage`'s residue (12610) is genuinely
> over. So the sentence "the parent is already over BOTH ceilings" is **half wrong**: it is true of the
> Coverage residue and false of `X86.Syntax`, whose 206 was load noise.
>
> ⇒ 🔑 **I USED AN OUT-OF-BAND READING TO ARGUE THAT OUT-OF-BAND READINGS CANNOT BE TRUSTED.** The
> conclusion of §5 survives — the ceilings are load-sensitive and the delta is the only meaningful
> reading — but one of its two supporting facts did not, and it was the one I did not re-measure
> because it agreed with what I already believed. A gate's own refusal applies to the evidence you
> gather to indict it. See D122 §2 for the in-band delta and for what the `X86.Syntax` margin really
> is: the parent sits at **198 of 200**, so the ceiling cannot absorb even one AST constructor.

⇒ 🔑 **A CEILING WHOSE MARGIN IS UNDER THE MACHINE'S OWN SPREAD REPORTS THE MACHINE, NOT THE CODE**
([[feedback-match-the-gate-units-to-the-growth-law]]), and the delta is the only reading here that
means anything. **No ceiling was raised**: deriving a gate's new allowance from the thing it measures
is the move with no second source ([[feedback-widening-a-gate-needs-a-second-source]]). The
authoritative reading is CI's, on a Linux runner, and this tree is not pushed. ⚠️ **This is the first
evidence that the absolute per-module ceilings are unusable on this machine for ANY commit, not just
for a batch that grows the table** — which promotes D111's repair from a nicety to the next
infrastructure item.

**Reversal cost:** one `PrefetchHint` type, one `Op` constructor, one semantics clause, two coverage
rows, two roster rows, 4 vectors, 2 arms, 4 `claimed_forms` exemptions.

---

## D122 — the in-band delta, a correction to D121, and a ceiling that cannot absorb one constructor

**P2 batch 23 (`pmovmskb`) is COMPLETE AND NOT MERGED TO master.** It lives on `p2-batch23-pmovmskb`.
Its differential is green; the kernel-cost gate returns a RED VERDICT in band, and a red verdict is a
stop where a refusal was not.

### 1. ⛔ THE CORRECTION, AND IT IS AGAINST MY OWN METHOD

D121 §5 says *"the parent is already over BOTH ceilings with none of this batch in it"*, from a parent
profile taken at load 6.07 — **out of band**. Re-measured in band (load 3.90):

```
parent 0f7baee, IN BAND      X86.Syntax  198.0  ok        Tests.Coverage residue  12610  OVER ⛔
parent 873a4d9, OUT OF BAND  X86.Syntax  206.0  OVER ⛔    Tests.Coverage residue  12540  OVER ⛔
```

Half of that sentence was true (the Coverage residue) and half was load noise (`X86.Syntax`).

⇒ 🔑 **I USED AN OUT-OF-BAND READING TO ARGUE THAT OUT-OF-BAND READINGS CANNOT BE TRUSTED.** D121's
conclusion survives — the gate is load-sensitive, the delta is the only meaningful reading — but one
of its two supporting facts did not, and it was the one I never re-measured **because it agreed with
what I already believed**. [[feedback-audit-the-premise-of-a-right-decision]]: a reason inside a
correct decision is the least-inspected kind, and here the decision was right and the reason was
manufactured by the very effect the decision names.

### 2. ⭐⭐ THE IN-BAND DELTA, WHICH IS THE READING THAT COUNTS

> ⛔⛔ **SUPERSEDED BY MEASUREMENT — D123 §3, the same day.** Both figures in this section were taken
> **one reading per side**. Re-measured on the identical `.lean` diff with **three repeats per side,
> alternated base/head in one session**: `X86.Syntax` **+2.0** (within-side spread 8.0) and
> `Tests.Coverage` residue **−60.0** (spread 500). Neither reproduces, and the batch below merged
> CLEAN under the delta gate (D125). The CONCLUSION of this decision — that an absolute ceiling
> inside the parent's own spread is not a gate — stands and is strengthened; the two numbers offered
> as its evidence do not.

```
                          parent 0f7baee     batch 23      delta      ceiling
X86.Syntax                     198.0 ok        206.0 ⛔      +8         200
Tests.Coverage (residue)      12610  ⛔        13190 ⛔     +580      12420
```

⛔ **THE `X86.Syntax` CEILING HAS TWO MILLISECONDS OF HEADROOM ON master.** The parent passes at
**198 of 200 — 99%** — and one AST constructor costs +8. So this is not a fact about `pmovmskb`: **the
next batch that adds any constructor will cross it too**, whatever it is.
[[feedback-a-pass-at-97-percent-is-not-headroom]] — the margin was the number to read, and nobody read
it while the verdict said `ok`.

⚠️ And `Tests.Coverage`'s residue is over **on master already**, in band. Two ceilings, two different
stories, and the whole-module refusals of D121 could distinguish neither.

### 3. WHY THE BATCH IS NOT MERGED, AND WHY NO CEILING WAS RAISED

D121's gate REFUSED (no verdict, machine out of band); this one FAILED in band. A refusal and a red
are not the same evidence, and treating them alike is how a project starts merging over a gate it has
stopped reading. So `pmovmskb` waits on the branch.

⛔ **No ceiling was raised.** Deriving a gate's new allowance from the quantity it measures has no
second source ([[feedback-widening-a-gate-needs-a-second-source]]), and doing it *in the batch the
gate just stopped* is the worst available moment. The two legitimate routes are both open and both
belong to whoever takes this next:
1. **D111's delta gate** — gate the change between two trees in one session, which is the only reading
   this machine can produce. D121 showed the method works; this decision shows it discriminates.
2. **A second source for the ceilings** — CI's Linux runner, which has never scored this tree.

⚠️ Until one of them lands, **every batch that adds a constructor is blocked by a 2 ms margin**, which
makes this an infrastructure item ahead of the next form, not behind it.

### 4. THE BATCH ITSELF, for whoever merges it

`pmovmskb`: `dst[i] ← MSB(src.byte i)`, bits above 15 zero. ⭐ **No `Size` field, on two independent
sources**: K gives `pmovmskb_r32_xmm.k` and `_r64_xmm.k` the same value, and the assembler emits the
**same bytes** (`660fd7c1`) for `%eax` and `%rax` — REX.W buys nothing when the result is
zero-extended. A width field would be one no encoding can set and no semantics can read.

```
differential   cases=84128 unexplained=0 oracle-divergence=171 (unchanged)
arms (3 of 121, shared substring `pmovmskb`)
  reads the LOW bit of each byte           83
  reverses the lane order                  51
  merges instead of clearing 63:16         46
```
⚠️ The last two score low **for reasons about the pre-states, not the instruction**: a reversed mask is
invisible on a palindrome, and a merging model is invisible unless the destination already holds bits
above 15. Both are joint facts ([[feedback-a-wrong-models-score-is-a-joint-fact]]).

**Reversal cost:** one `Op` constructor, one semantics clause, one coverage row, one roster row,
2 vectors, 3 arms — all on the branch.

---

## D123 — the VEX-128 bucket, and a census that is not finished when every mnemonic has been named

**P2 batch 24. One ACL2 run of 11 arms.** Taken under the helm's 21:42 ruling: *finish the census*.

### 1. ⛔⛔ WHY ROWS STAYED `not measured` AFTER A RUN THAT NAMED THEM

Batch 21 probed `vpsubw` at **ymm** and it EXECUTES — and the roster went on printing `⚠️ not
measured` for `vpsubw`. That is the join working CORRECTLY: its demand is dominantly **VEX-128**, and
`dominant_bucket` refuses to carry a ymm reading across to an xmm row.

⇒ 🔑 **A CENSUS IS NOT FINISHED WHEN EVERY MNEMONIC HAS BEEN NAMED. It is finished when every
(mnemonic, BUCKET) the demand actually occupies has been asked.** Eleven ranked rows and 48,525
instructions were still unmeasured after batch 21 for exactly this reason, and the caution was earned:
`vpaddw` — **rank 4, 11,682 instructions** — had never been asked at the width where its demand lives.

```
EXECUTE  vpaddw 11,682 · vpsubw 6,234
REFUSE   vpmulhrsw 5,010 · vmovq 3,430 · vpunpcklwd 3,630 · vpunpckhwd 3,352
         vpmaddubsw 3,048 · vpackssdw 3,026 · vsubps 2,795
```
Both controls behaved (`vpxor` at VEX-128 executed, `movnti` refused).

### 2. ⚠️⚠️ AND THE INSTRUMENT NOW ERRS IN **BOTH** DIRECTIONS

```
the oracle EXECUTES  55 mnemonics  129,979  31.2%
the oracle REFUSES   42            164,825  39.5%   <- the hole
probed               97            294,804  70.7%
```

The hole moved 33.7% → **39.5%**. But `executes` did not move at all, and it should have: `vpaddw`
executes at xmm. It is counted as REFUSING because `p2_roster`'s verdict is per **mnemonic**, and a
conflict between two buckets collapses to `refuses` — a rule written to stop double-counting demand,
which here **condemns 11,682 instructions of executable work on the word of a `zmm` probe**.

⇒ 🔑 So the two errors now point OPPOSITE WAYS, and neither is visible in the total:
* an **unprobed** (mnemonic, bucket) pair defaults to *available* and **under-states** the hole;
* a **collapsed** verdict lets one refusing width condemn every width and **over-states** it.

⚠️ **39.5% is therefore the best current figure and it is not a clean floor** — the claim D120 made
about 33.7% needs this qualification. It is a floor with respect to the 29.3% still unprobed, and an
over-estimate with respect to at least one row. Both halves are stated because an under-claim looks
like modesty and goes unpoliced ([[feedback-under-claims-are-unpoliced]]).

⛔ **NOT REPAIRED HERE, and the reason is scope**: splitting `vec[mn]` per bucket changes the
denominator of every published coverage number, and doing that inside a census batch would move two
things at once. It is a named item for the next head, with `vpaddw` as its worked example and its
red-first arm.

**Reversal cost:** 9 rows in `oracle_availability.py`, gated in both CR4 arms; the roster regenerates.

## D123 — the delta gate: a control set already in the record, and two numbers that did not reproduce

**P2 batch 25**, on the helm's ruling of 2026-09-04 21:42: *"the absolute ceilings are retired as a
MERGE GATE and kept as READINGS printed beside every merge; D111's delta method is the gate — you set
the per-batch delta budget from your own batch history (print the last ten batches' deltas; budget = a
stated multiple of their median, with the reason), register it in the repo's CI as the check that
runs, red-first driven (a planted constructor that doubles the delta must fail)."*

All four parts are built. The one that changed what I believe is the history, and it is a finding
against the premise of the batch that ordered it.

### 1. ⛔⛔ THE COST ESTIMATE THAT MADE THE HISTORY LOOK UNMEASURABLE WAS WRONG BY TWO ORDERS

The bank handing this on priced the walk as *"each historical point needs a checkout plus a full
`lake` rebuild (hours, not minutes)"*, said *"I did NOT measure that history"*, and offered **two**
real data points where the ruling asked for ten.

Measured, before anything else was written:

```
a full clean `lake build` in a fresh worktree     33 s
one full profile pass (19 modules + per-decl)     57 s
⇒ twelve commits x two sweeps                    ~32 min, in the background
```

⇒ 🔑 **AN INHERITED COST ESTIMATE IS A HYPOTHESIS, AND ONE INSTANCE TESTS IT.** A ruling had been
shaped around a number nobody had timed, and the shape it took was *"budget them from a real ten
before quoting one"* — advice that reads as caution and functions as a reason not to look.

### 2. ⭐⭐⭐ THE TEN BATCHES, MEASURED — AND FIVE OF THE ELEVEN COMMITS CHANGED NO LEAN AT ALL

`scripts/kernel_delta_history.py` walks one detached worktree through twelve commits, twice —
forward, then in reverse so a load that drifts through the run biases the two sweeps in OPPOSITE
directions — and differences adjacent readings. 24 readings, ~32 minutes.

⭐ **The control set was already in the history and is not synthetic.** Five of the eleven commits in
the window touch **no `.lean` file whatever**: `3769ea0` (b16, the residue measured), `762da1a`
(b19, the FP group measured), `873a4d9` (b21, the census), `e57c99f` (D122) and `5c01599` (b24, the
VEX-128 bucket). Whatever this instrument reports for them, it reported about nothing.

```
Tests.Coverage @residue (ms)      six commits that CHANGED Lean   five that changed NONE
                                  +130 +185 +220 +250 +285 +415   −270 −140 −140 −50 −15
X86.Syntax (ms)                   +0.5 +0.5 +4.5 +4.5 +8.5 +10.5  −7.0 −4.5 +1.5 +3.5 +4.5
```

⇒ 🔑 **THE SEPARATION IS THE INSTRUMENT'S CHARACTER, MEASURED RATHER THAN ASSUMED.** On the residue
the two populations do not overlap at all — every real batch positive, every control negative or
flat. On `X86.Syntax` they overlap: a commit that changed nothing produced **+4.5 ms**, which is the
MEDIAN of the six real batches.

### 3. ⛔⛔ NEITHER OF D122'S TWO NUMBERS REPRODUCES, AND I TWICE ALMOST SAID OTHERWISE

D122 held P2 batch 23 off master on two readings taken **one per side, in band**: `X86.Syntax`
**+8 ms** and `Tests.Coverage`'s residue **+580 ms**. This gate measured the same `.lean` diff with
**three repeats per side, alternated**:

```
                          base(master)   head(batch 23)   delta   within-side spread   budget
X86.Syntax                     198.0          200.0        +2.0          8.0            37.0
Tests.Coverage @residue      13 130         13 070         −60.0        500.0          1825.1
Tests.Coverage               21 100         21 300        +200.0        500.0          1519.2
```

⇒ 🔑 **BOTH OF D122'S NUMBERS WERE SINGLE-READING ARTEFACTS.** `+8` reproduces as `+2` against a
spread of `8`; `+580` reproduces as `−60` against a spread of `500`. Batch 23's true kernel cost is
below this instrument's resolution on both units. The batch was held off master for two hours by two
readings that a repeat does not support.

⛔⛔ **AND I ALMOST WROTE THE OPPOSITE, TWICE, IN THIS SAME DECISION.**

1. I first drafted this section as *"the premise of D122 survives"* — reasoning that `+8` exceeds all
   five zero-Lean controls (worst `+4.5`) and matches batch 22's own constructor delta (`+8.5`). Both
   of those comparisons are sound. **They compare D122's number with my controls; they do not
   re-measure D122's number**, and when I did, it was `+2`.
2. Earlier I read the planted-constructor arm as `+6 ms` off two pass lines of a four-pass run. Its
   summary said `+16.0`.

⇒ 🔑 **A NUMBER YOU DID NOT TAKE YOURSELF IS NOT EVIDENCE ABOUT THE THING IT NAMES; IT IS EVIDENCE
ABOUT THE RUN THAT PRODUCED IT.** Twice in one batch I built a careful argument on top of one
somebody else's single reading and one of my own pass lines, in a batch whose entire subject is that
a single reading of this quantity means nothing.

⇒ **What the ruling got right, and for a reason better than the one D122 gave — and here is the
sharpest form of it, measured tonight.** `master` was profiled twice this evening by two different
runs of the same gate, five minutes apart:

```
22:45  the batch-23 gate, master side, median of 3     X86.Syntax  198.0   UNDER the 200 ceiling
22:50  the identical-trees control, base side, med 2   X86.Syntax  216.0   OVER  the 200 ceiling
```

⇒ 🔑 **ONE COMMIT, ONE EVENING, ONE BOX, TWO OPPOSITE VERDICTS FROM THE SAME GATE.** Across the whole
window `X86.Syntax` reads 184–213. A threshold inside that spread does not report the commit; the
gate now prints exactly which side of each ceiling the BASE sits on, so a reader can see it without
being told.

### 3a. THE ESTIMATOR ARGUMENT THAT DID NOT SURVIVE ITS OWN TEST

Contention noise is one-sided — another process can only make a reading slower — which is a good
argument for taking the MINIMUM of the repeats rather than their median. Scored against a ground
truth the code itself guarantees (the coverage table only GROWS across this window: `rosterSize`
121→134 and `vectorCount` 893→954, both monotone, checked commit by commit), the argument is not
supported:

```
estimator   negative deltas on Tests.Coverage, which cannot fall
  median    2 of 11        min   2 of 11        max   3 of 11
```

⇒ The median is kept. An argument about the shape of the noise is still an argument
([[feedback-inherited-diagnosis-is-a-hypothesis]]: a cause you thought of yourself gets the same
credulity as one you inherited).

### 4. THE BUDGET, AND THE FOUR GENERATED RULES THAT WERE READ AND REFUSED

`scripts/kernel_delta_budget.txt` is **generated**, with its whole derivation inside it — a
hand-accumulated number with no per-step rule can only be recomputed, never corrected, and this
repository carried a coverage total that was eleven low for eighteen batches for exactly that reason
(D56).

```
candidate_u = max( median historical relative delta,
                   worst relative delta on a commit that changed NO .lean file,
                   worst measured within-commit relative spread )
budget_u    = MULT x candidate_u,  floored at @floor absolute milliseconds
```

The three terms are three different things and the `max` is deliberate: the first says what a batch
costs, the second says what a commit that changed NOTHING appeared to cost, the third says what the
instrument can resolve. Set below any one of them, the gate is not a gate.

⛔ **FOUR GENERATED RULES WERE READ AND REFUSED BEFORE THIS FILE SHIPPED**, and all four failures
are the same shape — a statistic taken over the wrong population, or of the wrong quantity:

1. **`@floor` = the worst absolute control delta over ALL units** generated **800 ms**, which is
   `Tests.Coverage`'s noise in milliseconds handed to `X86.Syntax`, a module whose entire reading is
   191 ms. That is a borrowed denominator wearing a floor's name
   ([[feedback-a-borrowed-denominator-invents-its-own-gap]]). Restricted to the units under 50 ms it
   read **2 ms**.
1b. **And that second rule was wrong too, in a third way.** The gate's refusal compares a budget
   against the run's own **SPREAD**; the floor was derived from a **DELTA**. Different statistics of
   the same readings, and the spread is systematically larger — **5.30 ms** on `X86Native` against a
   2 ms delta-derived floor, which would make the gate REFUSE on small modules whenever an ordinary
   run was as noisy as this walk already was. ⇒ 🔑 **A THRESHOLD MUST BE DERIVED FROM THE STATISTIC IT
   WILL BE COMPARED AGAINST.** Registered at **6 ms**, with no extra multiple: a run noisier than the
   worst this walk saw SHOULD refuse rather than pass.
2. **`MULT` = the smallest multiple at which every batch passes, rounded up** generated **1.4**
   against a needed **1.40** — a gate with ZERO headroom on the unit that binds it
   (`Tests.Coverage @decl vectorCoverage`), so the next batch costing what `0f929e3` cost fires it.
   Registered at **2.0**, which buys **1.43×** margin over the worst batch in the window; both
   numbers are printed in the file so neither can hide.
3. **`@default` = MULT × the LARGEST candidate** would hand every future module the allowance of
   `Tests.VectorRuns`, a 0.3 ms file with 58% spread. It is the median candidate now — and every unit
   that falls to it is LISTED by the gate on every run, so a module landing there by accident is
   visible rather than silently free.

⚠️ **WHAT THE RESULTING GATE CAN AND CANNOT SEE, STATED IN MILLISECONDS.** `X86.Syntax`'s budget is
18.7% of 191 ms ≈ **36 ms**, which is about **four and a half AST constructors**. That is not a
tight gate and it is not pretended to be one: it is what a box whose within-commit spread on that
unit is 9.3% can support. The gate catches a batch that multiplies a module's cost; it does not
catch one constructor, and no repeat count available in a merge gate would make it.

### 5. ⭐⭐ WHY THIS GATE CAN BE REGISTERED IN CI WHEN `kernel_cost.py` COULD NOT

`.github/workflows/ci.yml` spends thirty lines refusing to run the ceiling gate on a runner, and the
refusal stands: the same tree profiled there reads **1.7×–3.1× slower DEPENDING ON THE MODULE**, so
no single calibration constant exists, and ceilings loosened to fit would be ~2× slack on the box
where batches are developed.

⇒ 🔑 **THE MEASUREMENT THAT REFUTES A PORTABLE CEILING IS WHAT MAKES A PORTABLE RATIO WORK.** That
factor is a property of *(machine, unit)*. This gate profiles two trees on ONE machine and gates the
ratio of the difference to the base, so the factor sits in the numerator and the denominator and
divides out exactly — whatever it is, and however much it varies between modules. Every budget in
`scripts/kernel_delta_budget.txt` is therefore a percentage.

⚠️ **AND THAT IS A PREDICTION, NOT A MEASUREMENT.** It follows from the factor being multiplicative
and stable within a session, which the CI table supports for ABSOLUTE readings and which nothing has
tested for a matched DELTA on two machines: this account's runner refuses every job for billing (desk
FH), so no delta has ever been measured anywhere but here. The first delta CI prints is the test of
this paragraph, not its confirmation.

### 6. THE RED-FIRST DRIVE, AND THE ONE CONSTRAINT THE PLANT COULD NOT WORK AROUND

The helm asked for *"a planted constructor that doubles the delta"*. It is literally that, with a
constraint stated rather than quietly evaded:

⛔ **A constructor cannot be planted in `Op`.** Adding one leaves `opOperands`, `Op.anyLocked` and
`Op.mnemonic` non-exhaustive in `X86/Syntax.lean` and breaks ~30 further match sites in five other
files. The tree would not build, and a probe whose subject does not build measures nothing.

⭐ **`PrefetchHint` is the one inductive in the repository that can carry it.** It is matched in
exactly one place — `PrefetchHint.mnemonic` — so N constructors and their N arms compile, change no
other module, and put their whole cost in `X86.Syntax`: the unit whose real margin was two
milliseconds. The plant is a real constructor addition to a real inductive, which is why it was
preferred to a synthetic block of `decide` theorems, and the probe REFUSES if the shape it edits is
no longer there rather than silently planting nothing.

⛔⛔ **AND THE FIRST PLANT SIZE DID NOT CREATE THE CONDITION, WHICH IS THE MOST USEFUL THING THE ARM
HAS DONE SO FAR.** 48 planted constructors moved `X86.Syntax` **+16.0 ms** — 0.33 ms each — against a
**27.4 ms** budget, and the arm returned rc 0 where 1 was wanted: **it failed, out loud, instead of
reporting the gate sound while planting something the gate is right to ignore**
([[feedback-a-probe-must-create-its-condition]]).
⚠️ And the first figure I read for it was **+6 ms**, taken off two single pass lines of a four-pass
run before the medians existed. The arm's summary line is the reading; a pass line is not
([[feedback-read-what-the-instrument-measured]]).

⇒ 🔑 **A CONSTRUCTOR ON A FRESH INDUCTIVE COSTS A THIRD OF A MILLISECOND, AND A REAL `Op`
CONSTRUCTOR COSTS SOMETHING THIS BOX CANNOT RESOLVE.** D122 put the latter at 8 ms from one reading;
§3 measures the same diff at **+2.0 ± 8**. So the honest statement is a bound, not a figure — and a
plant sized to ONE REAL CONSTRUCTOR would have been sized to a quantity nobody has measured.
The 0.33 ms figure IS measured (48 constructors, +16.0 ms, four alternating passes), which is why the
plant is sized from it.
⚠️ The plant is therefore sized to the BUDGET rather than to a real constructor, at 512 (~170 ms at
the measured rate), and the arm prints its measured delta on every run so that estimate is checked
rather than trusted.

⭐⭐ **Beside it runs the arm that could have invalidated every green this gate will ever print:
base and head at the SAME COMMIT.** Whatever the gate reports there is pure instrument. It is the
negative control the whole method rests on, and it runs in CI in its own job.

**BOTH ARMS, MEASURED UNDER THE SHIPPED BUDGET FILE:**

```
arm 1  identical trees          rc 0 (wanted 0)   worst unit delta  +60.0 ms on Tests.Coverage @residue
arm 2  512 planted constructors rc 1 (wanted 1)   X86.Syntax  205.0 → 928.0  = +723.0 against a 38.3 budget
delta-gate measured selftest: PASS (2 arms)
```

⭐ **And the estimate that sized the plant was wrong by 4.3×, which is the reason the arm prints its
delta.** At the 48-constructor rate (0.33 ms each) 512 predicted ~170 ms; it measured **+723.0**,
1.41 ms each. 10.7× the constructors bought 45× the cost — the match compiler is **super-linear in
the arm count**, so a plant sized by extrapolation is a plant sized by a model nobody checked.

⚠️ Both arms were re-judged over their SAVED readings after the budget file changed
(`--save-readings` / `--readings`), not re-measured: a second measurement would be a different
evening, and re-judging the same readings is the only way to compare a changed budget against a
fixed observation.

### 7. WHAT IS RETIRED AND WHAT IS KEPT

`scripts/kernel_ceilings.txt` is **not deleted and not raised**. Its figures ride beside every merge
as READINGS, box-stamped, printed by `kernel_delta.py` under a heading that says they are retired as
a gate. Deriving a gate's allowance from the quantity it measures has no second source, and doing it
in the batch the gate just stopped is the worst available moment (D122 §3); nothing here does it.

## D125 — batch 23 merges, under the gate it was held off master for

**P2 batch 23 (`pmovmskb`) is ON master.** It sat on `p2-batch23-pmovmskb` from 21:40 because
`kernel_cost.py` returned a red verdict in band: `X86.Syntax` 206 against a 200 ceiling, and
`Tests.Coverage`'s residue 13,190 against 12,420 (D122). The helm retired those ceilings as a merge
gate at 21:42 and made D111's delta the gate; D123 built it; this is the merge.

### 1. THE COMMIT THAT LANDS IS NOT THE COMMIT THAT WAS MEASURED, AND THE DIFFERENCE IS CHECKED

The branch was based on `e57c99f`; master had moved to `5c01599` (batch 24) and then to D123's
commit. The batch is cherry-picked forward rather than merged, so the history stays linear — and the
question that creates is whether the measured pair is the landed pair.

⛔ **It is checked rather than assumed.** Restricted to `*.lean`, the diff of the ORIGINAL pair
(`e57c99f` → `p2-batch23-pmovmskb`) and of the REBASED pair (`5c01599` → the cherry-pick) are
**byte-identical** (`git patch-id --stable` agrees, and so does `diff`). Batch 24 and D123 touch only
`docs/`, `scripts/` and `.github/`, so nothing the kernel reads moved. The differential result
(84,128 cases, unexplained=0, oracle-divergence 171) and the kernel delta therefore carry.

### 2. THE GATE'S READING — CLEAN

Three repeats per side, alternated base/head, in one session on one box
(`yukon.lan`, macOS-26.6.2-arm64, 14 cpus, one-minute loads 3.81–5.07):

```
UNIT                                          base       head     delta   spread   budget  VERDICT
X86.Syntax                                   198.0      200.0      +2.0      8.0     37.0  ok
Tests.Coverage                             21100.0    21300.0    +200.0    500.0   1519.2  ok
Tests.Coverage @residue                    13130.0    13070.0     -60.0    500.0   1825.1  ok
Tests.Coverage @decl memDestSweep           4850.0     4940.0     +90.0     90.0    417.1  ok
Tests.Coverage @decl vectorCoverage         1470.0     1460.0     -10.0     90.0    230.8  ok
Tests.Coverage @decl pre_states_…_frame     1730.0     1770.0     +40.0    100.0    320.1  ok
X86.Theorems                                 887.0      894.0      +7.0     36.0    162.3  ok
…every other unit ok; 2 fell to @default 23.3% (Tests, X86 — both read 0.0 ms)
delta gate: CLEAN
```

### 3. ⛔⛔ AND THE TWO NUMBERS THAT HELD IT OFF MASTER DO NOT REPRODUCE

D122's readings were taken **one per side**. Three repeats give:

```
                          D122 (1 reading/side)    this gate (3/side, alternated)    spread
X86.Syntax                      +8 ms                        +2.0 ms                   8.0
Tests.Coverage @residue        +580 ms                       −60.0 ms                 500.0
```

The batch's true kernel cost is **below this instrument's resolution on both units**. It waited two
hours on two numbers a repeat does not support. D123 §3 carries the full account, including the two
places I nearly repeated the same mistake while writing it up.

### 4. THE ABSOLUTE READINGS, BOX-STAMPED, BESIDE THE MERGE (retired as a gate, 09/04 21:42)

`kernel_delta.py` prints them under a heading that says they are not a verdict, and DERIVES the
sentence that used to be a literal:

> The BASE — the tree this change is a change to, with none of it applied — is over **1** of these
> ceilings: `Tests.Coverage @residue` (13,130 against 12,420); the head is over **1**: the same one.

`X86.Syntax` reads **200.0 against a ceiling of 200** on the head — the razor's edge D122 named,
which is the whole reason an absolute ceiling here reports the afternoon.

### 5. WHAT THE MERGE DOES NOT SETTLE

⚠️ **The differential was not re-run.** It does not need to be — the `.lean` diff is byte-identical to
the one that produced `84,128 cases, unexplained=0, oracle-divergence=171` on the branch — but that is
an argument from the diff, not a re-run, and it is stated as one.
⚠️ **CI has still never run any of this.** GitHub Actions refuses every job on this account for
billing (desk FH). The local gates are the receipt this box can produce.

## D124 — the census counts a mnemonic as probed by NAME and reads its verdict by KEY

**P2 batch 25.** Batch 24 established the rule — *a census is not finished when every MNEMONIC has
been named; it is finished when every (mnemonic, BUCKET) the demand occupies has been asked* — and
applied it BY HAND to eleven rows. `scripts/p2_roster.py --unprobed` applies it to all of them, and
the first thing it reports is that `docs/P2-ROSTER.md` answers the question two different ways.

### 1. THE TWO ACCOUNTINGS, IN ONE DENOMINATOR — AS THE INSTRUMENT FOUND THEM

The roster's summary table counts a mnemonic as probed if `oracle_availability.py` NAMES it, at any
width. Each ROW's oracle column looks the mnemonic up at the bucket its own demand lives in
(`dominant_bucket`). Over one set of rows with one occurrence count:

```
NAMED anywhere in the availability table   268,979   64.5% of the 417,231-instruction gap
ASKED at the bucket its demand lives in    218,333   52.3%
⇒ probed by NAME but never asked at its BUCKET  50,646   12.1%
```

⚠️ **The difference is computed over ONE set with ONE `occ` on purpose.** The published *"probed so
far 294,804 / 70.7%"* is a THIRD accounting (`vec[mn]` over join keys); subtracting one from another
would be a difference of two denominators, which invents its own gap
([[feedback-a-borrowed-denominator-invents-its-own-gap]]).

⇒ 🔑 **A CENSUS CAN BE FINISHED IN ONE ACCOUNTING AND UNFINISHED IN ANOTHER, IN THE SAME DOCUMENT,
AND NEITHER NUMBER LOOKS WRONG.** 328 (mnemonic, bucket) pairs carrying 161,026 instructions — 38.6%
of the gap — have never been asked, against a published figure that reads 70.7% probed.

### 2. `vpaddw` IS THE WORKED EXAMPLE AND IT DISAGREES WITH ITSELF

The bank handed this on as a diagnosis and it was TESTED rather than believed
([[feedback-inherited-diagnosis-is-a-hypothesis]]). It holds, with one correction to its wording:

* `vpaddw` is probed at **zmm** (refuses, AVX-512 — this oracle cannot execute it at all) and at
  **xmm** (executes, batch 24).
* The SUMMARY's per-mnemonic collapse sees a conflict and takes `refuses`, so **11,682 instructions
  are counted inside the 39.5% hole on the word of an AVX-512 probe**.
* The ROW's oracle column looks up `(vpaddw, AVX2/AVX (ymm))` — its dominant bucket — finds nothing,
  and prints `⚠️ not measured`.

One mnemonic, two verdicts, both published. The bank called it *"counted as REFUSING"*, which is the
summary's answer; the ranked table says `not measured` on the same row.

### 3. WHAT IS DONE AND WHAT IS NOT

⛔ **The per-mnemonic collapse is NOT repaired here, and the reason is the one the previous head
gave**: splitting the summary's `vec[mn]` per bucket moves the NUMERATOR's provenance (`vec` sums
join keys; `per_ext` sums `miss_by_ext`), and a census batch must not move a published number's
source at the same time as it moves the number.

⭐ **What IS done is the instrument that makes the remainder finite and ranked** — `--unprobed` prints
every unasked pair with the demand it would resolve and the exact key `oracle_availability.py` has to
be extended by — and the accumulation both callers used is now ONE function (`per_ext_map`), because
a third copy was about to be written and two copies born in agreement diverge on the next append.

### 4. WHAT THIS BATCH ASKS, AND WHAT IT LEAVES

Twenty-five (mnemonic, bucket) pairs — the top of `--unprobed` — were assembled by clang, declared
provisionally, run on the oracle, and then written back at the twelve values the oracle actually
produced. Second run: **CLEAN in both CR4 arms, both controls behaving.**

```
                                       before        after
asked at the bucket its demand lives in   52.3%        69.8%
unasked remainder            328 pairs / 38.6%   303 pairs / 21.2%   (161,026 → 88,333 instructions)
probed by NAME but not by KEY   50,646 / 12.1%    7,335 / 1.8%
the roster's measured hole (REFUSES)      39.5%        43.1%   (executes 31.2% → 34.6%)
```

⭐ **THE HOLE ROSE, AND THAT IS THE INSTRUMENT WORKING.** Twelve of the twenty-five execute and
thirteen refuse; the refusing ones were previously counted as *available by default*, which is the
direction an unprobed pair errs in. A census that only ever lowers the hole is a census measuring
its own optimism.

⭐ **MMX EXECUTES WITH CR4 = 0.** `movd %mm1,%eax`, `psubw`, `punpcklbw` and `pxor` at `%mm` run in
BOTH arms — MMX uses the x87 state and is not gated by `CR4.OSFXSR`, exactly as the SDM says and
unlike every SSE form in this table. Four rows that would have read as "the oracle has no MMX" now
say the opposite, and the model's MMX gap is a decision of this repository's, not the oracle's.

⛔⛔ **AND `vpaddw` IS STILL INSIDE THE 43.1% HOLE, NOW AGAINST TWO EXECUTING WIDTHS.** It is probed
at zmm (refuses — AVX-512, which this oracle cannot execute at all), at xmm (executes, batch 24) and
now at ymm (executes, this batch). The summary's per-mnemonic collapse still takes `refuses`, so
**11,682 instructions sit in the published hole on the word of an AVX-512 probe alone.** Adding a
second executing width did not remove them; only §3's repair will.

⚠️ One cosmetic defect found and fixed on the way: the conflict list was a `list` that was appended
to once per disagreeing PROBE, so a mnemonic measured at three widths printed as
`['vpaddw', 'vpaddw']` — a count of probes wearing the name of a count of mnemonics. It is a set now,
rendered as prose.

⛔ **The census is NOT finished and this record does not say it is.** The instrument's contribution is
that the remainder is a LIST rather than a search: every unasked pair, ranked by the demand it would
resolve, with the exact `(mnemonic, bucket)` key `oracle_availability.py` has to be extended by. The
next head can work down it without re-deriving which bucket to probe.

## D126 — a CI gate has been red for five batches, and no record in those five says so

**Found while running the CI `build` job's gates locally on the tree that merged P2 batch 23.**
`scripts/demand_census.py --check` fails:

> ⛔ THE CENSUS IS STALE — the MODEL and the MAPPING have both moved.
> `docs/DEMAND-CENSUS.md` was generated against a model of **131** mnemonics; it is now **135**.
> Every coverage percentage in that document is against the older pair.

### 1. IT IS NOT THIS MERGE, AND THE COMMIT WHERE IT STARTS IS MEASURED, NOT INFERRED

The first instinct was that batch 23 broke it — it adds `pmovmskb` to `rosterP0`, which moves the
model's identity. ⛔ **That was tested rather than believed**, by checking out each commit in the
window into a worktree and running the gate:

```
762da1a  P2 batch 19   demand-census staleness gate: CLEAN (131 mnemonics)
a5326fd  P2 batch 20   ⛔ STALE   ← the first red
873a4d9  P2 batch 21   ⛔ STALE
0f7baee  P2 batch 22   ⛔ STALE
5c01599  P2 batch 24   ⛔ STALE     (the tree this life inherited)
ff5b59c  D123          ⛔ STALE     (no `.lean` change of mine)
```

**Batch 20 (`movhps`) took `rosterP0` from 131 to 132 and the census document was not regenerated.**
Five batches have landed on top of it. Two further CI steps — the census `--selftest` and
`census_redprobe.py` — fail as a consequence, because their planted arms cannot distinguish "the
model moved" from "the mapping moved" once both already have; so **one stale artifact reds three of
the workflow's twenty-five steps**.

### 2. ⛔⛔ WHY FIVE BATCHES OF RECORDS SAY "GATES GREEN"

* **GitHub Actions refuses every job on this account for BILLING** (desk FH), so no CI run has ever
  executed this step. Master CI has never been green — 36 of 36 runs — and that is recorded.
* **The per-batch local discipline runs the gates named in `scripts/run_differential.sh`**, which is
  a SUBSET of `.github/workflows/ci.yml`. Nothing compared the two lists.

⇒ 🔑 **A GATE THAT LIVES ONLY IN CI, ON AN ACCOUNT WHERE CI CANNOT RUN, IS A GATE NOBODY HAS.** D104
found two gates hiding behind a failing step and repaired *them*; the repair it did not make was to
give a head one command that runs the whole workflow on the box that exists. "Gates green" in five
banks meant "the gates I ran are green", and the sentence cannot tell the difference.

### 3. WHAT IS DONE, AND WHAT IS DELIBERATELY NOT

⭐ **`scripts/ci_local.py` runs a CI job's steps on this box, DERIVED from `ci.yml` rather than copied
from it.** A hand-written roster of CI steps is a duplicate born in agreement — it matches the day it
is written and diverges on the next append, silently. This parses the workflow, runs each `run:`
block in order, NAMES the `uses:` steps it skips as runner setup, and prints the failing step's own
output rather than only its name. `--list` shows what it would run; it parses the `build` job's 25
steps and the two new `kernel-delta` jobs.

⛔ **THE CENSUS IS NOT REGENERATED HERE, and that is a decision rather than an omission.**
Regenerating needs the corpus re-downloaded (ten Debian packages plus nine debug packages, the
recipe is in the document) and **it moves every published coverage percentage in this repository** —
`docs/DEMAND-CENSUS.md` feeds `p2_roster.py`, which feeds the hole this same batch has just
re-measured at 43.1%. Moving a denominator and a numerator in one batch, at the end of a life, is how
a number gets published that nobody can attribute. It is the next head's FIRST item, with its
first-red commit and its blast radius named here rather than left to be rediscovered.

⚠️ And a caution the next head should carry: `ci_local.py` runs on **arm64 macOS**; CI's runner is
**x86-64 Linux**, where this tree has been measured 1.7×–3.1× slower per module. A green here is not a
receipt for the runner. It is, however, the first time in five batches that anything has asked.

## D127 — the census regenerated, every moved instruction attributed, and three false figures a byte-for-byte gate could never see

**D126's first item, discharged.** `docs/DEMAND-CENSUS.md` was five batches stale (stamped against
131 mnemonics, the model at 135); three of the `build` job's twenty-five steps were red because of
it. The corpus was rebuilt from the recipe in the document, the census re-run, and the P2 roster
re-derived. `ci_local.py --job build` now reads **25 of 25 GREEN** — the first fully clean local
`build` this repository has had.

### 1. ⭐⭐ THE CONTROL WAS ALREADY IN THE RECORD, AND IT IS AN EXACT ONE

D126's stated risk was that regenerating "moves every published coverage percentage", so a number
gets published nobody can attribute. That risk is real only if the corpus or the disassembler moved
underneath the document as well. **Both were pinned by a control that cost nothing to read: the
document's own instruction totals.** They are a function of the corpus and the tool ALONE — the model
does not enter them — and they are printed per column in every version of the document.

```
column              published (HEAD)      re-measured today
cc1                    5,379,923            5,379,923   ✔
coreutils                879,551              879,551   ✔
glibc                    603,554              603,554   ✔
dav1d                    303,830              303,830   ✔
ffmpeg                 3,116,986            3,116,986   ✔
vlc-codec                151,688              151,688   ✔
vlc-video_chroma         112,104              112,104   ✔
vpx                      722,331              722,331   ✔
x264                     377,330              377,330   ✔
vmlinux-kernel         2,781,898            2,781,898   ✔
```

**Ten of ten, exactly.** So the corpus and the disassembler are the same ones the published
percentages were measured with, and every number that moved, moved because the MODEL moved.

⚠️ **The disassembler is not recorded anywhere in the document, and it decides these totals.** It is
`objdump` off `PATH`, which on this box is **Apple LLVM objdump (Apple LLVM version 21.0.0)** —
GNU binutils 2.47 is installed but keg-only and unlinked, so it is not what runs. That the tool was
constant across the whole document history was established the same way: the totals above are
byte-identical in all nine regenerations from `50dcfa7` (09-03 13:27) through `320cb45`
(09-04 16:27), a window that spans the binutils install at 11:48. ⛔ **A future head who regenerates
on a box where GNU objdump is first on `PATH` will get different totals and nothing in the document
will say why** — D89 measured that difference in another gate (GNU wraps its byte column at seven).
Recording the tool in the stamp is docketed and deliberately NOT done here: hashing it would red the
gate permanently on the x86-64 Linux runner, which is a gate nobody can ever have.

### 2. ⛔ THE CORPUS RECIPE HAS A GAP, AND IT COST 6,452 INSTRUCTIONS

The first rebuild reproduced **nine** of the ten totals; `coreutils` read **873,099** against the
published **879,551**. That was not a repo defect — it was mine. The recipe says to `ar x` + `tar xf`
each package into "one subdir of `$CORPUS` per column"; I cherry-picked `usr/bin` and so dropped
`usr/sbin/chroot` and `usr/libexec/coreutils/libstdbuf.so`.

⛔ **The mechanism was measured, not assumed.** Those two files alone, run through this same census as
their own column, count **6,452** instructions — and `873,099 + 6,452 = 879,551` exactly. The corpus
was rebuilt from whole trees and all ten then matched.

🔑 The value of the control is what it did here: it turned a silent 0.7% error in one column into a
number with a name, before anything was published. A regeneration with no reproduced control cannot
tell "I rebuilt the corpus wrong" from "the corpus changed" from "the model changed" — and all three
look like a plausible new reading.

### 3. ⭐ THE GAP MOVED BY 4,591, AND ALL 4,591 ARE ACCOUNTED FOR — BY THREE INDEPENDENT ROUTES

```
the uncovered gap (assembly class)   417,231  ->  412,640     -4,591
  the oracle EXECUTES                144,535  ->  139,944     -4,591
  the oracle REFUSES                 179,651  ->  179,651          0   (raw count UNCHANGED)
the roster's measured hole             43.1%  ->    43.5%
  ⇒ the hole did not grow. Its NUMERATOR did not move at all; the denominator shrank.
```

The model gained four mnemonics since the census's stamp — `movhps`, `pmovmskb`, `prefetchnta`,
`prefetcht0`. Their demand in the OLD uncovered bucket sums to **4,631**, which is **40 more** than
the gap actually moved. The 40 were chased rather than rounded: they are `pmovmskb (vector operand)`
in ffmpeg (15) and x264 (25) — a bucket batch 23's `pmovmskb` does not cover, so they correctly
stayed uncovered. `4,631 - 40 = 4,591`. ⭐ And the strongest arm: of the **1,346** other
(column, uncovered-key) pairs, **1,346 are byte-identical** old to new. Nothing else moved at all.

⇒ 🔑 **A DENOMINATOR AND A NUMERATOR MAY MOVE IN ONE BATCH IF EVERY INSTRUCTION OF THE MOVE IS
ATTRIBUTED.** D126 was right that doing it blind publishes an unattributable number; the repair is
not to avoid the batch but to make the move add up, per instruction, against a control the reading
did not supply.

### 4. ⛔⛔ THREE FIGURES IN A GENERATED, GATED DOCUMENT THAT WERE FALSE THE DAY THEY WERE WRITTEN

`docs/P2-ROSTER.md` is generated, and `p2_roster.py --check` re-derives it byte-for-byte in CI. That
gate was **CLEAN** on a shipped document which said, four lines under its own table:

```
prose:  "...it is rank 4 in the demand list, 2.31% of the whole gap..."
table:  | 1 | `pmaddwd` | 21,239 | 5.09% |          <- rank 1, not 4; 5.09%, not 2.31%
prose:  "The nine the oracle does not have are `...`"   <- followed by 49 names
table:  | the oracle REFUSES | 49 | 179,651 | 43.1% |
```

**Two of the three were false in the very commit that introduced them** (`00dd9ea`, the first
oracle-availability run: the table said REFUSES **11** and ranked `pmaddwd` **5th** while the prose
already said "nine" and "rank 4"). The third, `2.31%`, was true at birth and had drifted to 5.09%.
They survived because they were literals inside the generator's f-string, so the document is a
faithful rendering of the script and the gate has nothing to complain about.

⇒ 🔑 **A BYTE-FOR-BYTE DERIVATION GATE PROVES `file == script`. IT CAN NEVER PROVE `script == true`.**
A hand-written number inside a generated document is invisible to that gate for as long as the
document exists — and, worse, it *reads as generated*, so no human checks it either. Its own
neighbours were derived and correct the whole time.

**The repair** is not a new gate but the removal of the thing a gate cannot see: all three figures are
now taken from the same objects (`b["joined"]`, `rf_names`, `b["total_uncovered"]`) that print the
table beside them, so the prose and the table cannot disagree again. They now read `rank 1`, `5.15%`
and `The 49`, agreeing with the table and with the 49 names actually listed (checked by counting
them, not by trusting the field).

⚠️⚠️ **AND THE SIBLING SEARCH I SAID I HAD RUN WAS SCOPED TOO NARROWLY — CORRECTED WITHIN THE HOUR.**
This paragraph first read *"these three are the only hand-written figures in either generator's prose
blocks"*. That sentence is TRUE and it is not the claim that mattered: I had grepped the two
GENERATORS, and the same three figures were sitting in a **code comment** in a third file,
`scripts/oracle_availability.py:340` — *"AND THE NINE THE ORACLE DOES NOT HAVE … `pmaddwd` is rank 4
in the demand list — 21,239 occurrences, 2.31% of the whole gap"*. I found it on the NEXT task, by
opening that file for an unrelated reason.

⇒ 🔑 **A SIBLING SWEEP INHERITS THE SCOPE OF THE FILE THE DEFECT WAS FOUND IN.** The card says to grep
*the same file for the same shape*; the defect's shape here was not "a literal in a generator" but
"a hand-written figure about a table that regenerates", and that shape has no reason to respect file
boundaries. The repo-wide grep that found it (`rank [0-9]+ in the demand`, `2.31%`, `the nine the
oracle`) took one command and should have been the FIRST move, not the second.

⛔ And the comment is the worse hiding place of the two: a figure in a generated document is at least
re-rendered next to the truth on every regeneration, where a reader might catch it. **A figure in a
comment is invisible to every gate there is** and is re-rendered never. The repair therefore does not
restate the figures at all — it names where they are derived (`docs/P2-ROSTER.md`, from `b["joined"]`
and `rf_names`) and records that all three drifted, so the next reader is sent to the live number
instead of being handed a stale one.

### 5. WHAT THIS BATCH DELIBERATELY DID NOT DO

- **The per-mnemonic collapse (D124 §3) is untouched.** It moves a published numerator's provenance
  and remains its own batch, with `vpaddw` as the worked example.
- **No ceiling and no budget was touched.** `kernel_ceilings.txt` and `kernel_delta_budget.txt` are
  unchanged; this batch changes no `.lean` file at all, so the delta gate has nothing to judge.
- **Nothing was pushed.** Local only, both tiers.
- **The historical figures in this file are left standing as written.** D115's, D124's and D126's
  `417,231` and `43.1%` were true on their dates and are dated records, not live claims; rewriting
  them would destroy the only evidence of what each batch actually saw.

### 6. THE CORPUS, IDENTIFIED

19 Debian `amd64` packages, every recipe URL re-probed and resolving `200` with no version redirect
before the download. The sha256 of each is recorded in the bank so the next regeneration can tell a
moved pool from a moved model; `coreutils_9.10-1_amd64.deb` is
`6e39a854a50bdfb912f5afc7ffa920d83093b33a2394fa5ece4771adf9b40dbc`.

### 7. THE CENSUS AFTER THE MOVE

```
census stamp        131 / 6d5c44858342796c / c6278134749d11c1
                ->  135 / 756af18bbd2a48a9 / 2d8eaea351934cb1
asked, per KEY               69.8%  ->  69.5%
the unasked remainder    303 pairs / 88,333 / 21.2%  ->  304 pairs / 88,373 / 21.4%
  (+1 pair, +40 instructions: the `pmovmskb (vector operand)` bucket of §3, now visible as unasked)
ci_local.py --job build      24 of 25  ->  25 of 25 GREEN
```

## D128 — the availability table is keyed by the column that does not run, and measured through the column that does

Found while preparing the next probe batch, by asking what would validate the twenty-three new
encodings I was about to write. Nothing would have.

### 1. THE TWO COLUMNS

Every row of `P2_FORMS` in `scripts/oracle_availability.py` carries an `asm` string and an `hx`
string, and they are consumed by different code for different purposes:

* **`hx` is written into ACL2's memory and IS THE INSTRUCTION THAT EXECUTES** — `measure_cr4` emits
  it as `(#x<addr> . #x<byte>)` pairs. The oracle never sees the `asm`.
* **`asm` is never assembled by anything** — but `measured_availability()` keys the entire
  availability table by `asm.split()[0]`, and deliberately so: a probe LABEL is a tag
  (`movq_xmm`, `paddw_mmx`), and D100's phantom row came from recovering a mnemonic by stripping a
  suffix off one.

⇒ 🔑 **THE KEY COMES FROM THE COLUMN THAT DOES NOT RUN, AND THE MEASUREMENT COMES FROM THE COLUMN
THAT DOES.** One mistyped hex byte publishes a verdict *about* `pmaddwd` that was *measured on*
whatever those bytes decode to. It is D100's phantom-row family arriving through the one column no
reader checks, because a hex string is not readable by eye. `docs/P2-ROSTER.md` prints those verdicts
in its oracle column, and `p2_roster.py --unprobed` decides what to work on next from them.

The gate is `oracle_availability.py --check-encodings`, registered in CI: every row's `hx` must be
what `clang -target x86_64-unknown-linux-gnu` assembles from that row's own `asm`. It needs no ACL2,
so it runs with the model gates rather than behind the oracle. **The shipped table passes: 133 of
133.** The gate's value is not this reading — it is that the next twenty-three rows cannot be wrong.

### 2. ⛔⛔ THE PARSER WAS THE HARD PART, AND IT FAILED ON EXACTLY ONE ROW — WHICH READ AS A DEFECT IN THE TABLE

The first parser matched `([0-9a-f]{2} )+`, requiring a space after every byte. That space is
**padding**, and objdump only emits it after instructions narrower than the column. The table's
widest row is `movabsq $0x123456789abc, %rax` at ten bytes, whose last byte abuts the tab — so its
final `00` was dropped, and **132 of 133 rows agreed while one disagreed.**

⚠️ I nearly filed that one as a finding against the shipped table. What stopped it was shape rather
than suspicion: `48b8bc9a7856341200` is a strict PREFIX of the declared `48b8bc9a785634120000`, and a
prefix at one length is a column width, not a disagreement — the diagnosis
[[feedback-a-column-parser-is-tested-by-its-widest-datum]] was written for. **The instrument was
wrong and the subject was right**, in a run whose green would have been reported as a repo defect.

### 3. ⭐⭐ AND THE TWO DISASSEMBLERS DISAGREE ABOUT THE DELIMITER — BOTH ARE NOW EXERCISED HERE

D89 found that GNU objdump wraps its byte column at seven bytes where LLVM does not, and recorded
that it **could not be tested on the dev machine, which had only one disassembler**. That is no
longer true — GNU binutils 2.47 is installed (keg-only, so it is not what `objdump` resolves to) —
so this gate runs against both and requires both to agree:

```
LLVM   `   0: 48 b8 .. 00 00<TAB>movabsq<TAB>$0x...`     space after the colon
GNU    `   0:<TAB>48 b8 .. 34 <TAB>movabs $0x...`        TAB after the colon,
       `   7:<TAB>12 00 00 `                             and WRAPPED at seven
```

Neither delimiter is a space, and the second parser — written to fix the first — returned **empty for
every GNU line**, because splitting on the tab put the bytes in a different field. The shipped parser
drops the address, splits on tabs, and takes the leading run of fields that are nothing but hex byte
pairs. `133 forms, 0 disagreements` under **both**.

### 4. THE RED ARMS, AND WHY THE SECOND ONE IS THE ONLY ONE THAT MATTERS

```
✔ one byte flipped in an ordinary short form
✔ the WIDEST row (`ADD3:movabsq`, 10 bytes) truncated by its LAST byte
✔ a row carrying a DIFFERENT real instruction's encoding (`pxor` given `paddd`'s bytes)
```

⛔ **Arms 1 and 3 would BOTH have passed against the padding-dependent parser this gate was born
from.** They perturb short forms, and short forms are exactly where that parser was correct. Only arm
2 differs in the dimension a column parser can be frozen in
([[feedback-a-control-can-share-the-blind-spot]]) — and it is generated from the shipped table
(`max(P2_FORMS, key=len(hx))`), not from the literal `movabsq`, so it follows the widest row if a
wider one is ever added ([[feedback-a-gate-is-not-exempt-from-its-own-defect]]).

### 5. ⚠️ A BUCKET THE PROBE TABLE CANNOT EXPRESS, MEASURED RATHER THAN ASSERTED

`probe_bucket()` reads a form's ISA bucket off its OPERANDS (`%mm`, `%zmm`, `%ymm`, `%xmm`) and
returns `None` for anything else. The census emits **eighteen** buckets; a probe form can produce
**five**. The other thirteen — `AVX (state)`, `x87 (st)`, `PREFETCH`, `LOCK prefix`, `CPUID`, `BMI2`,
`XSAVE`, the fences, and the rest — are **unaskable**: a probe written for one is silently dropped
from `measured_availability()`, so the pair stays on the unasked list forever no matter how often it
is probed.

⛔ There IS a gate here and it runs **one way only**: it checks that every probe bucket is a census
bucket (a stray-probe / over-claim direction) and never that a census bucket is reachable by a probe.
The unpoliced direction is the one that reads as modesty
([[feedback-under-claims-are-unpoliced]], [[feedback-probe-gates-both-ways]]).

⚠️ **The live cost is one pair, and I am not inflating it to thirteen buckets' worth.** Measured
against today's residue: of the 304 unasked pairs / 88,373 instructions, **303 pairs / 87,132 (98.6%)
are askable** and **1 pair / 1,241 (1.4%) is not** — `vzeroupper`, `AVX (state)`, which will sit near
the top of the ranked list indefinitely and quietly refuse to be retired. The vocabulary gap is
thirteen buckets; the demand behind it today is one row. Both numbers are stated because the gap can
grow silently as coverage moves and nothing would say so.

### 6. WHAT THIS BATCH IS NOT

**It adds no probe form and moves no published number.** The twenty-three new forms this gate was
built for are the NEXT batch, deliberately: the gate that makes their encodings trustworthy has to
land before them, which is the red-first discipline applied at the level of a batch rather than an
arm. `ci_local.py --job build` reads **26 of 26 GREEN** (the step count rose from 25 because
`ci_local` derives its list from `ci.yml` rather than carrying one).

## D129 — P2 BATCH 26: the top of the unasked list, asked; and five predictions wrong in one direction

The order's item 1, taken with D128's encoding gate already under it. **Twenty-three (mnemonic,
bucket) pairs asked** — ranks 1–24 of `p2_roster.py --unprobed`, minus rank 21.

### 1. WHY RANK 21 WAS SKIPPED, AND WHY THAT IS NOT A GAP IN THE BATCH

`vzeroupper` (1,241 instructions) sits in bucket `AVX (state)`, and D128 §5 measured that
`probe_bucket()` cannot express it: a probe written for it is dropped from
`measured_availability()`, so the pair would stay on the unasked list **after being asked**. Probing
it would have produced a form that runs, a verdict that is discarded, and a list that does not move —
the most expensive kind of nothing. It is named here so the next head does not rediscover it by
spending a probe on it.

### 2. ⛔⛔ THE PREDICTIONS WERE RECORDED BEFORE THE RUN, AND FIVE WERE WRONG — ALL ONE WAY

Each form's verdict was predicted and written into the table *before* ACL2 saw it, so the run
measures my model of the oracle and not only the oracle. **Eighteen of twenty-three held. Five did
not, and all five failed in the same direction — predicted `executes`, measured `refuses`:**

```
vpunpckldq    VEX-128    predicted executes   MEASURED refuses
vpunpcklqdq   VEX-128    predicted executes   MEASURED refuses
vpunpckhqdq   VEX-128    predicted executes   MEASURED refuses
vpunpckhdq    VEX-128    predicted executes   MEASURED refuses
pinsrw        SSE-legacy predicted executes   MEASURED refuses
```

**Four of the five are the VEX-128 unpacks — and their SSE-legacy siblings all EXECUTE.**
`punpckldq`, `punpcklwd`, `punpcklbw` and `punpckhwd` are declared `executes` a few dozen lines above
them in the same table, measured in earlier batches. I inferred the VEX verdicts from those siblings
without saying so, and every one of the four inferences was wrong.

⇒ 🔑 **THE SAME OPERATION HAS DIFFERENT ORACLE SUPPORT AT DIFFERENT ENCODINGS.** That is precisely
why the census key is `(mnemonic, BUCKET)` and not a mnemonic — and it is the same shape as
[[feedback-a-batch-cannot-be-sampled]], one level up: there the eighth member of a group broke a
verdict drawn from seven; here a whole BUCKET broke a verdict drawn from another bucket of the same
name. A sibling in another bucket is not evidence about this one, and the direction of the error is
the one that invents work.

⚠️ **A prediction that is never written down cannot be scored.** Had I filled the declarations in
from the run, this batch would have published twenty-three correct rows and learned nothing; the
5-of-23 is only visible because the guess was committed first and the run was allowed to refute it.

### 3. THE MOVE, AND IT ADDS UP EXACTLY

```
asked at the bucket its demand lives in      69.5%  ->  77.2%
the unasked remainder    304 pairs / 88,373 / 21.4%  ->  281 pairs / 56,676 / 13.7%
probed so far      111 mn / 319,595 / 77.5%  ->  133 mn / 350,167 / 84.9%
  the oracle EXECUTES  62 / 139,944 / 33.9%  ->   68 / 147,867 / 35.8%
  the oracle REFUSES   49 / 179,651 / 43.5%  ->   65 / 202,300 / 49.0%
```

⭐ **Both accountings agree to the instruction**: the 23 pairs' own demand sums to **31,697**, and the
unasked remainder fell by `88,373 − 56,676 =` **31,697**; pairs fell by exactly **23**.

⛔ **The hole GREW, 43.5% → 49.0%, and that is the batch working, not failing.** Sixteen of the
twenty-three are refusals, so asking moved demand out of *unknown* and into *known-unsupported*. A
batch of this kind can only make the published hole larger or leave it alone; a head who reads a
rising REFUSES number as a regression will stop asking, which is the one thing that would keep it
looking small.

### 4. ⚠️ THE MNEMONIC COUNT ROSE BY 22, NOT 23 — D124 §3, UNCHANGED AND UNCONCEALED

The summary table counts MNEMONICS, and its `verdict` map is keyed by `label.split("_")[0]`, so
`packuswb_mmx` collapses into the `packuswb` already measured at SSE-legacy. Their verdicts agree
(both execute), so nothing is hidden by the collapse this time and no conflict is raised. **This is
D124 §3's known discrepancy and this batch neither repairs nor worsens it** — the row-level oracle
column is still looked up per bucket while the summary counts per mnemonic. It stays its own batch
because it moves a published numerator's provenance.

### 5. THE ENCODINGS

All 23 came from `clang -target x86_64-unknown-linux-gnu`; none was typed. D128's gate re-derives
every one of the now-**156** rows on **both** disassemblers at every CI run, so the `hx` that ACL2
executes is the assembly of the `asm` that keys the table. `ci_local.py --job build`: **26 of 26
GREEN**.

## D130 — one key, two subjects: a probe tag that shared a reading, and a decision number that shares a section

Found by batch 27's pre-flight, before a single new row was measured. A uniqueness assertion over
`P2_FORMS` refused, and the duplicate was already in the shipped table at `961653e`. Chasing its
shape through the repository turned up a second instance of the same defect in a different medium.

### 1. ⛔⛔ TWO ROWS SHARED A LABEL, SO TWO PUBLISHED VERDICTS CAME FROM ONE READING

`measure_cr4` emits one ACL2 form per row, each printing `P2RESULT tag=<tag_of(label)> …`, and
collects them with `got[tag] = verdict`. Two rows carried the label `vpsubw`:

```
("vpsubw", "vpsubw %ymm1, %ymm2, %ymm0", "c5edf9c1", …)   AVX2/AVX (ymm)
("vpsubw", "vpsubw %xmm1, %xmm2, %xmm0", "c5e9f9c1", …)   VEX-128 (v… xmm)
```

ACL2 printed two records under one tag; the dict kept the **last**; both rows were then scored
against that one reading. Those are two **different census keys**, both published in the
availability table. The ymm key had never been measured — its verdict was the xmm row's reading
wearing the ymm row's name.

That is not a technicality, and b26 is why. Batch 26 measured four VEX-128 unpacks that **refuse**
where their SSE-legacy siblings **execute** — which is the whole reason the census key is
(mnemonic, BUCKET) and not a mnemonic. A verdict borrowed across buckets is the exact error the key
exists to prevent.

**Why nothing caught it.** `p2_run` guards the *other* direction: `g0 is None` catches a row that got
no reading — "a missing reading is not a refusal". Nothing caught a row that got *somebody else's*.
And a shared reading is not anomalous to read: both rows print a ✔ against it. ⇒ 🔑 **identical
verdicts in identical fields is what confirmation looks like, and is also what one arm wearing two
names looks like.**

**And why it lived here and nowhere else.** The repository's other two measurement paths COUNT
records per tag and compare the count to the number of pre-states: `measure` stores
`res[tag] = (e, r)` and `report` refuses on `e + r != n`; `check_driver_cr4.verdict` does the same. A
collision there surfaces at once as *2n records, expected n*. `measure_cr4` is the one path that
collapses a tag to a single verdict **by assignment**, so a second record does not increment a count
— it overwrites, erasing the first. ⇒ 🔑 **the collision is undetectable exactly where the collector
stopped counting.**

**The repair and its receipt.** The VEX-128 row is relabelled `vpsubw_v`; the key is unaffected
because the mnemonic comes from the `asm` column, not the label (D100, D128). `--p2` then measured
the ymm form for the first time:

```
✔ vpsubw    vpsubw %ymm1, %ymm2, %ymm0   refuses  executes
✔ vpsubw_v  vpsubw %xmm1, %xmm2, %xmm0   refuses  executes
```

It agrees. **The published verdict was right — by luck, not by measurement.** The borrowed reading
came from a sibling x86isa implements through the same semantic function
(`x86-vpsubb/vpsubw/vpsubd/vpsubq-vex` serves both the VEX-128 and VEX-256 entries), so the coin
landed the right way up. The defect was real and its live consequence was nil; the gate is what makes
that not a coin toss next time. **Stating the consequence as nil is not the same as calling the
defect nil**, and the temptation to round one into the other is why this paragraph is here.

**The gate.** `p2_structure_check` refuses on any tag emitted by more than one row. It runs from
`--check-encodings` — the entry point CI actually runs, since ACL2 is not on the runner — and again
at the top of `--p2` before ACL2 is paid for. Two red arms, both required to fire, plus a control:

- two rows sharing a LABEL outright (the live shape, spottable in principle);
- two rows whose LABELS DIFFER but whose TAGS collide, because `tag_of` squashes every
  non-alphanumeric to `_`: `X:y` and `X_y` are one tag. This table already carries `CONTROL:mov` and
  `ADD1:mov %gs:`, so that collision is reachable and **invisible in the source**. ⇒ an arm drawn
  only from the visible half would have been silent on it.

**What it deliberately does not flag.** Two rows may legitimately share a (mnemonic, bucket) KEY:
`psrad $0x3, %xmm0` (0F72 /4) and `psrad %xmm1, %xmm0` (0FE2) are different opcodes at one census
key, as are `psrlw_i`/`psrlw_x`. Their labels are distinct, so they are measured independently, and
`measured_availability` already refuses if they disagree. That design is correct and untouched — but
the fold is now **printed**, because a reader of the table could not otherwise tell that two rows
collapse into one published verdict.

### 2. ⛔ THE SAME DEFECT IN PROSE: `D123` HEADS TWO SECTIONS

Numbering this note required knowing the next free number, and the count did not match: **126
headings, 125 distinct.** `D123` heads both batch 24's VEX-128 bucket (`5c01599`) and the delta gate
(`ff5b59c`) — two decisions, one number, landed the same day, and nothing in the repository checked.

A D-number is a **citation**: `ci.yml` says "the kernel-time delta gate (D123)", `kernel_cost.py`
cites it twice, and DECISIONS.md cross-references it five times. All seven resolve to the delta gate,
so the other section is **unreachable by number** — it is published and uncitable.

**Recorded, not renumbered.** Renumbering the referenced one breaks `ci.yml` and `kernel_cost.py`;
the unreferenced one has no free in-sequence number to move to, D124 having been taken by the next
batch the same day. So the collision stays in the history and is FROZEN in
`check_citations.py`: the assertion is `KNOWN_DUPLICATE_D == {"123": 2}`, **exact and not a
tolerance**, with a red arm proving a *third* `D123` still fails — because an exemption that absorbs
more of the thing it exempts is not an exemption, it is a hole. This gate lives in
`check_citations.py` because that file exists for one sentence — *a citation is itself an ungated
claim* — and a decision number is a citation whose target nobody greps.

⚠️ While confirming the inbound references, `kernel_cost.py` was seen to label D123 as
"P2 BATCH 25", where batch 25 is D124 (`fd4a8ba`). That is a stale figure in a comment — D127's
lesson, unrepaired here because it is a different defect from this one and is docketed, not
forgotten.

### 3. 🔑 WHAT THE TWO INSTANCES SHARE

Both are a **key that names one thing while two things stand behind it**, and in both the failure is
silent because the collapse happens in a container that cannot represent the collision: a `dict`
assignment in one, a document's heading namespace in the other. Neither was found by review — the
probe table's by an assertion written while adding rows, the document's by needing the next number.
⇒ **a uniqueness invariant that is never asserted is not an invariant, it is a habit**, and habits
are kept until the first day they are not.

## D131 — P2 BATCH 27: the prediction route replaced, and 23 of 23 — priced, not believed

> ⛔⛔ **CORRECTED BY D132, the same sitting.** This section calls x86isa's instruction listing **"a
> second source"** and reads 23 of 23 as a model of the oracle beating naive baselines. It is **not a
> second source**: `machine/dispatch-creator.lisp` includes `inst-listing` and builds the opcode
> dispatch from it, so the slot the route reads is the datum that *decides* the machine's behaviour.
> The listing and the machine are **one source read two ways**. The score below is real and the
> baseline comparison stands as a measure of how much information the read carries — but it is
> evidence that the READING IS FAITHFUL, not that a model is good. §2's framing is the error; §3, §4
> and §5 are unaffected. D132 carries the correction and what it turned out to buy.


Twenty-three (mnemonic, bucket) pairs asked: **ranks 2–24** of `p2_roster.py --unprobed`. Rank 1
`vzeroupper` / `AVX (state)` was skipped, again and deliberately — `probe_bucket` reads the bucket
off the OPERANDS and that bucket has none, so a probe for it runs, has its verdict discarded, and
leaves the pair exactly as unasked as before (D128 §5). It is named here so the next head does not
spend a probe rediscovering it.

### 1. ⭐⭐ THE PREDICTION ROUTE WAS REPLACED, BECAUSE b26's ROUTE FAILED

b26 predicted from **sibling base rates** and got five wrong, all in the same direction, four of them
by inferring a VEX-128 verdict from an SSE-legacy sibling. So b27's predictions were read off a
**second source**: the oracle's own catalogue, `vendor/acl2/books/projects/x86isa/machine/
inst-listing.lisp`, at the entry whose **encoding matches the bytes clang produced** — VEX/EVEX
class, vector length, prefix, opcode, `/reg`. A `'NIL` semantic-function slot ⇒ predict `refuses`.

All 23 predictions, both CR4 columns, were **written down and hashed before ACL2 saw any of these
forms** (sha256 `84ec5947…`, 07:02:54Z).

⚠️ **The instrument was a suspect first, and it was guilty.** The extractor's function-slot regex was
uppercase-only, and x86isa writes some slots lowercase (`x86-vpsubb/vpsubw/…-vex`), so a lowercase
slot read as unknown and could fall through to "unimplemented" — a mis-declared `refuses`. All 23
were re-derived case-insensitively *before the run*; **every prediction was unchanged**, and the seal
verifies byte-for-byte that the amendment left the table untouched. The bug never reached this batch
— but it reached `vpsubw`, which is how it was found. ⇒ 🔑 **a new instrument is a suspect until a
case it gets wrong is exhibited**, and here the exhibit was free: an entry outside the batch that it
scored as unknown.

### 2. ⭐⭐ 23 OF 23 — AND A GREEN THAT EASY IS A SUSPECT, SO IT WAS PRICED

Every pair correct in **both** CR4 columns: 46 of 46 cells, scored mechanically against the sealed
file rather than by eye. Against b26's 18 of 23, that demands an explanation better than "the route
is good". Three naive rules were scored on the same 23 rows, on the published CR4=0x600 column:

| rule | score |
|---|---|
| "always refuses" | 17 / 23 |
| "always executes" | 6 / 23 |
| "refuse iff VEX/EVEX (v-prefixed)" | **20 / 23** ← the best baseline |
| **the catalogue route** | **23 / 23** |

It beats the best baseline on exactly three rows, and they are the three that discriminate:
`pmuldq` and `movntdq` are legacy-SSE forms the baseline calls *executes* and the oracle **refuses**
(no semantic function), and `vpcmpeqw` is a VEX.256 form the baseline calls *refuses* and the oracle
**executes**. The probe is also demonstrably not stuck: three distinct verdict patterns came back in
one run — `(executes, executes)` ×4, `(refuses, executes)` ×2, `(refuses, refuses)` ×17.

⛔ **What this does not license: the remaining 258 pairs.** A batch cannot be sampled — this is 23
asked pairs across 5 buckets, not a proof about the route. The catalogue remains a **screen** that
makes a prediction scorable; `measured_availability` still publishes only what ACL2 executed.

### 3. THE MOVE, AND BOTH ACCOUNTINGS AGREE TO THE INSTRUCTION

```
the uncovered gap                412,640   (unchanged — asking moves demand, it does not remove it)
asked at its own bucket            77.2% -> 81.9%
THE UNASKED REMAINDER   281 pairs / 56,676 / 13.7% -> 258 pairs / 37,334 / 9.0%
probed so far          133 mn / 350,167 / 84.9% -> 153 mn / 367,246 / 89.0%
  the oracle EXECUTES   68 / 147,867 / 35.8%    ->  71 / 150,084 / 36.4%
  the oracle REFUSES    65 / 202,300 / 49.0%    ->  82 / 217,162 / 52.6%
```

The 23 pairs' own demand sums to **19,342**; the remainder fell by `56,676 − 37,334 =` **19,342**,
and pairs fell by exactly **23**. The two figures come from different routes — the first from the
ranked listing, the second recomputed by the tool from the census join — so their agreement checks
the transcription and not only the arithmetic.

⛔ **The hole GREW again, 49.0% → 52.6%, and that is the batch working.** Seventeen of twenty-three
are refusals, so asking moved demand out of *unknown* into *known-unsupported*. A head who reads a
rising REFUSES as a regression will stop asking, which is the one thing that keeps it looking small.

### 4. ⚠️ THE MNEMONIC COUNT ROSE BY 20, NOT 23 — D124 §3, AND CHECKED RATHER THAN ASSUMED

Three of the batch's mnemonics were already NAMED at another bucket: `psraw`, `punpcklwd` and `psllw`
each existed at SSE-legacy and were asked here at **MMX**. So pairs rose 23 while mnemonics rose 20.
The summary table gives a mnemonic ONE verdict and takes the pessimistic one where its buckets
disagree — so whether anything is hidden is a question, not an assumption. It was **executed**, not
argued: all three agree across their two buckets (`executes` at both), as does `packuswb` from b26.
Nothing is concealed by the collapse this batch. **This is D124 §3's known discrepancy, neither
repaired nor worsened.**

### 5. THE ENCODINGS

All 23 came from `clang -target x86_64-unknown-linux-gnu`; none was typed. D128's gate re-derives
every one of the now-**179** rows on **both** disassemblers (Apple LLVM and GNU binutils) at every CI
run, so the `hx` ACL2 executes is the assembly of the `asm` that keys the table. D130's structure
gate confirms all 179 tags are distinct, so every row has its own reading.

## D132 — CORRECTION to D131: the catalogue is not a second source, it is the machine's own definition

D131 §2 called x86isa's instruction listing "a **second source**" and scored the batch-27 route
against naive baselines as though 23 of 23 measured a good model of the oracle. Chasing that green —
because a green that easy is a suspect — refuted the framing.

### 1. ⛔⛔ THE LISTING GENERATES THE DISPATCH

`machine/dispatch-creator.lisp` opens with `(include-book "inst-listing")` and builds the opcode
dispatch out of it:

```lisp
(fn-call (if (equal fn nil) unimplemented-opcode
           (let ((fn-name (car fn)) …) …)))        ; dispatch-creator.lisp
```

The semantic-function slot the route reads **is** the datum that decides whether the running machine
implements the opcode. ⇒ 🔑 **the catalogue and the machine are ONE source read two ways — statically
and dynamically.** They are not two witnesses, and artifacts of one source agree because they are the
same thing, not because they confirm each other.

**So the score means something different from what D131 said it meant.** 23 of 23, and the 163 of 163
below, are **not** evidence that a model of the oracle is good; they are evidence that **this reader
parses the listing faithfully**. A miss would have been the finding. A hit is the baseline
expectation. The route was still temporally predictive — it was written and hashed before ACL2 ran —
and the baseline comparison still measures how much information the read carries versus a naive rule.
What does not survive is the word *second*.

### 2. ⭐⭐ THE CORRECTION MAKES THE RESULT STRONGER, NOT WEAKER

If oracle support is **derivable**, then the unasked remainder can be priced with **no ACL2 run at
all**. `scripts/p2_oracle_support.py` does that. Scored first on everything already measured:

```
SCORED AGAINST THE MEASURED TABLE — 168 pairs measured
  predicted and scorable : 163      correct : 163  (100.0%)      wrong : 0
  absent from the listing under this name  : 5
  baseline "always refuses"                : 87 / 163
  baseline "always executes"               : 76 / 163
  baseline "refuse iff v-prefixed/zmm"     : 117 / 163
```

and then applied to the 258 pairs nobody has asked:

```
THE UNASKED REMAINDER, PRICED STATICALLY — 258 pairs, 37,334 instructions
  x86isa IMPLEMENTS    84 pairs / 15,119 / 40.5% of the remainder
  x86isa DOES NOT     158 pairs / 20,108 / 53.9%
  NOT RESOLVED HERE    16 pairs /  2,107 /  5.6%
```

**Those 84 pairs are the ones that can become differential vectors**, ranked by demand, and a head
can now pick a batch by what the oracle can actually validate instead of by demand order alone. That
is a better artifact than a good predictor would have been.

### 3. ⚠️ WHAT THE PROBE STILL BUYS — STATED AS A MEASUREMENT, NOT AN ASSUMPTION

A static read cannot see the ways a form fails **before** the dispatch is reached or **despite** an
implemented slot: a byte string that does not decode to that entry at all; a feature-flag or CR4
gate; an ACL2 guard violation (`cvtss2sd` at zero operands raises one — which is exactly why it
serves as the operand control). **163 of 163 is a measured statement that none of those bit on 168
pairs.** It is not a claim that they cannot, and `measured_availability` still publishes only what
ACL2 executed. ⇒ the probe's residual value is now *characterised* rather than assumed, which is
what lets a future head decide when to spend one.

### 4. ⛔ THE READER'S OWN DEFECT, FOUND WHILE CHECKING IT — AND IT WAS WRONG IN BOTH DIRECTIONS

The first version bucketed a legacy entry by its **feature flag**. Two real entries broke it:

| entry | feature | operands | truth | the reader said |
|---|---|---|---|---|
| `PSHUFW` | `:SSE` | `(P Q)(Q Q)` | MMX | SSE-legacy — **wrong bucket** |
| `PSHUFB` | `:SSSE3` | `(P Q)(Q Q)` | MMX | *no bucket at all* — `":SSSE3"` does not contain the substring `":SSE"` |

⇒ 🔑 **a legacy entry's register file is in its OPERAND LETTERS, not in its feature flag** — the SDM's
`P`/`Q`/`N` name MMX registers and `V`/`W`/`H`/`U` name XMM ones. That is the same rule
`probe_bucket` already follows, for the same reason: the mnemonic and the feature flag are labels,
the operands are the thing. Repairing it lifted scorable coverage from 156 to **163 of 168** and left
the disagreement count at **zero**, which is the shape of a reader defect rather than a source
disagreement: it moved rows from *unreadable* into *correct*, not from *wrong* into *right*.

### 5. THE RESIDUAL GAP, NAMED AND NOT GUESSED

Five measured pairs and sixteen unasked ones carry a name the listing does not use: AT&T size
suffixes (`cvtsi2sdl`, `cvtsi2ssq`), `movd`, `vpermq`, `pextrw`, `vzeroupper`. **None is resolved by
stripping a suffix**, because recovering a mnemonic by stripping characters off a label is D100's
lossy key exactly, and it is how a phantom row was published once already. They are printed as
unresolved so the next head sees a gap rather than a guess.

## D133 — P2 BATCH 28: the queue reordered by derived support, and the first batch that could have failed

Not the top of `--unprobed` by demand: **the top 23 of the 84 pairs `scripts/p2_oracle_support.py`
derives as implemented**, by demand. The fork was posted on the bus with a recommendation and taken
on it, per the standing law that nothing blocks on the Captain.

**Why reorder.** Same census progress per pair, but every pair asked here is one that **can become a
differential vector** — which is what the project is for — and it is where a probe is most
informative. D132 established that the listing *generates* the dispatch, so asking a pair the listing
calls unimplemented can only confirm the read. Asking one it calls **implemented** is different: the
machine can still refuse for reasons a static read cannot see —

- the bytes do not decode to that entry at all (a decode-level `#UD`);
- a feature-flag or CR4 gate fires;
- an ACL2 guard violation aborts the step, which yields **no reading at all** rather than a refusal
  (`cvtss2sd` at zero operands does exactly this, which is why it is the operand control).

⇒ 🔑 **this is the first batch whose predictions could be caught out by the machine.** Batch 27's
could not: every row it declared `refuses` was a row the listing said was unimplemented, and the
listing is what makes it so.

### 1. THE RESULT: 23 OF 23 AGAIN — AND THIS TIME THAT IS INFORMATION

46 of 46 cells, scored mechanically against a file hashed before ACL2 ran (sha256 `0ccb1f2a…`,
07:31:09Z, unchanged after). Fifteen `(refuses, executes)` and eight `(executes, executes)` — the
eight being the MMX forms, which need neither `OSFXSR` nor `OSXMMEXCPT`.

**None of the three divergence classes bit.** That is a measured statement about 23 implemented
forms, not an assumption that they cannot: no decode-level refusal, no feature gate, and no guard
violation — the six floating-point rows (`divss`, `mulps`, `addps`, `movddup`, `cvttsd2si`,
`cvttss2si`) were run at operands whose every lane is a normal positive float, which was recorded as
a *reason to expect no guard violation* before the run rather than claimed as one afterwards.

### 2. THE MOVE — AND THE FIRST BATCH THAT MOVES ONLY THE EXECUTING SIDE

```
THE UNASKED REMAINDER  258 pairs / 37,334 / 9.0%  ->  235 pairs / 27,271 / 6.6%
asked at its own bucket                  81.9%    ->  84.3%
probed so far          153 / 367,246 / 89.0%      ->  169 / 374,138 / 90.7%
  the oracle EXECUTES   71 / 150,084 / 36.4%      ->   87 / 156,976 / 38.0%
  the oracle REFUSES    82 / 217,162 / 52.6%      ->   82 / 217,162 / 52.6%   ← unchanged
```

The 23 pairs' demand sums to **10,063**; the remainder fell by `37,334 − 27,271 =` **10,063**, and
pairs by exactly **23**. Every previous batch grew the published hole; this one does not touch it,
because every pair asked executes. Mnemonics rose 16, not 23, because seven were already named at
SSE-legacy and were asked here at **MMX** — distinct keys, distinct labels, measured separately.

### 3. ⭐ THE PER-MNEMONIC COLLAPSE NOW HAS A MAGNITUDE — D124 §3, PRICED

Every mnemonic measured at more than one bucket was checked for agreement rather than assumed to
agree: **25 such mnemonics, 24 agree, one does not.**

```
vpaddw   demand 11,682   ymm 5,487 · VEX-128 4,434 · zmm 1,761
         measured: ymm executes · VEX-128 executes · zmm REFUSES
         dominant bucket = ymm, where it EXECUTES
         the summary counts all 11,682 as REFUSES  (pessimistic collapse)
```

The conflict itself is old and already named in `p2_roster.py`'s comments. What is new is the
**number and its direction**: the summary overstates REFUSES by **9,921 instructions — 2.4% of the
412,640-instruction gap** — and understates EXECUTES by the same. ⇒ ⚠️ **the error runs in the
direction that makes the oracle look worse than it is, which is the unpoliced direction**: an
over-claim reads as a mistake, an under-claim reads as modesty. It is left unrepaired here because
moving a published numerator's provenance is its own batch — but it is no longer an unpriced one.

### 4. ⛔ A STALE COUNT IN THE ONE SENTENCE THAT ASSERTS THE VERDICTS ARE TRUSTWORTHY

The operand control has printed *"so the **77** verdicts are readings at the declared operands"*
since batch 19. The table held 77 rows then; it holds **202** now. The same literal sat in the
control's failure message. Neither is reachable by any gate — a count written as a literal in a
message re-renders never, which is D127's lesson in its worst location: **the sentence whose whole
job is to certify that every verdict was taken at real operands was itself carrying a figure that had
been wrong for nine batches.** Repaired by deriving it from `len(P2_FORMS)`, not by updating it.

A repo-wide sweep for the same shape was run **before** this note was written, not after: the only
other literals of that family are a historical account of the D128 parser incident (`132 of 133`,
correctly frozen — it describes what happened, not what is) and two counts in
`p2_oracle_support.py`'s own docstring, which were removed in favour of the number its run prints.

### 5. THE ENCODINGS

All 23 came from `clang`; none was typed. D128's gate re-derives every one of the now-**202** rows on
both disassemblers each CI run; D130's structure gate confirms all 202 tags are distinct.
`ci_local.py --job build`: **26 of 26 GREEN**.

## D134 — the coverage number was counted per mnemonic and consumed per bucket; both are now published, and their difference is computed

D124 §3 named this discrepancy and left it as its own batch because it moves a published numerator's
provenance. D133 priced one instance of it (`vpaddw`, 9,921 instructions). This is the whole of it.

### 1. THE MEASUREMENT, AND THE CONTROL THAT LICENSES IT

The summary table gives each **mnemonic** one verdict and counts that mnemonic's **whole** demand
under it. The row-level oracle column, and the differential that depends on it, ask a different
question: does this demand have a verdict **at the bucket it lives in**?

⚠️ The first attempt to measure the gap reproduced *348,011* where the document publishes *374,138* —
a **borrowed denominator**, built from the join's occurrences instead of `vec`'s. Nothing was reported
from it. Rebuilt on the generator's own `vec`, the reproduction is exact:

```
CONTROL — my reproduction vs the PUBLISHED table
   EXECUTES   87 / 156,976      (published: 87 / 156,976)
   REFUSES    82 / 217,162      (published: 82 / 217,162)
   probed    169 / 374,138      (published: 169 / 374,138)   -> REPRODUCES EXACTLY
```

⇒ 🔑 **reproduce the published figure before perturbing it, or the delta is a fact about your
reconstruction.** Only after that control passed was the difference attributable:

```
BY MNEMONIC     EXECUTES 156,976 (38.0%)   REFUSES 217,162 (52.6%)   probed 374,138 (90.7%)
BY (mn,BUCKET)  EXECUTES 128,234 (31.1%)   REFUSES 169,877 (41.2%)   probed 298,111 (72.2%)
                                                    not asked at its own bucket 114,367 (27.7%)
```

**76,027 instructions — 18.4% of the 412,640-instruction gap — are attributed on a reading taken at a
different bucket than the demand lives in.** `movdqa` measured at SSE-legacy carries its ymm demand
with it. The published coverage headline was **90.7%** where the demand-weighted answer is **72.2%**.

### 2. THE SPLIT IS EXACT, AND THAT IS CHECKED RATHER THAN ASSUMED

`per_ext_map`'s per-bucket demand sums to `vec`'s per-mnemonic demand for **all 564 mnemonics —
412,478 both ways, delta zero**. So nothing is rescaled and the two tables share a denominator *by
measurement*. `attribute_by_bucket` refuses if that ever stops being true, because a shared
denominator assumed rather than measured is how a gap gets invented.

Both tables are now printed, with **their difference computed in the document**, so it can never
again drift unnoticed. A total cannot see its parts; two totals that must agree can.

### 3. ⛔ THE PARAGRAPH THAT SAID THIS WAS IMPOSSIBLE

The section carried: *"the census pools an MMX and an SSE spelling of `paddw` under a single key, so
its demand **cannot be split** between the batches by mnemonic at all."* `per_ext_map` — in the same
file — splits every mnemonic's demand by bucket exactly, and has since D124. `paddw`'s census demand
is `{MMX (mm): 4166}`, entirely one bucket. ⇒ 🔑 **a justification outlives its condition**: prose
explaining why something cannot be done reads as a reason not to try, and survives the arrival of the
capability that refutes it. The pessimistic collapse was never forced by the data; it was a choice
that a stale sentence kept looking like a constraint.

### 4. ⛔ MY OWN RED ARM WAS THE OTHER ARM WEARING A SECOND NAME

Two arms were written for `attribute_by_bucket`: "break the denominator" and "break conservation".
The second **fired the denominator branch** — moving a by-mnemonic total breaks that check first — and
printed a ✔ for a gate it never reached.

And the reason it cannot be reached is worth stating rather than papering over: once the denominator
check passes, every bucket's demand sums to its mnemonic's and the loop adds each exactly once, **so
conservation is implied, not independently testable from data**. The assertion stays as a guard
against a future edit to the *loop* — a stray `continue`, a bucket counted twice — and is deliberately
**not** claimed as a second red arm.

Arm 2 was replaced with the condition that *is* data-reachable and that arm 1 cannot see: a
**positive control on the unattributed pile**. If `avail` ever answered for a pair it has not measured
— a default in place of a `None` — unasked demand would land silently in a verdict, over-reporting
coverage in the direction that reads as progress. The arm answers for one unasked pair and requires
the numbers to move: `endbr64`/CET-IBT shifts 16,488 instructions out of unattributed and into
executes. A pile that could not be made to move would be a pile nothing was ever added to.

### 5. WHAT IS NOT DONE HERE

The by-mnemonic table is **kept**, not deleted: it answers a real question (how many mnemonics has the
oracle been asked about) and other prose counts mnemonics. What changes is that it is no longer
presented as the coverage number, and the demand-weighted figure now sits beside it with the
difference spelled out. `ci_local.py --job build`: **26 of 26 GREEN**.

## D135 — P2 BATCH 29: the FP-heaviest batch, and the guard violation that did not fire

The next 23 pairs the derived support calls implemented, by demand — and deliberately the batch with
the most floating point in it, because that is where the one divergence class a static read cannot
see is most likely to bite.

### 1. WHY THIS BATCH WAS WORTH RUNNING RATHER THAN DERIVING

Eleven of twenty-three rows are floating point: `sqrtss`, `sqrtsd`, `cvtss2si`, `cvtsd2si`,
`minss`/`minsd`, `maxss`/`maxsd`, `ucomiss`/`ucomisd`, `subps`. An **ACL2 guard violation** is the one
outcome that is neither verdict — it aborts the step and yields **no reading at all** — and it is
known to be reachable here: `cvtss2sd` at zero operands raises one, which is exactly why it serves as
the operand control.

⚠️ **The risk was priced before the run, not explained after it.** At `xmm0 = 0x4040…40` and
`xmm1 = 0x4020…20`, every single-precision lane is `0x40404040` = 3.0078125 and `0x40204020` =
2.5039…; every double lane is 32.25 and 8.2539…. All normal positive: no NaN, no denormal, no zero
divisor, no negative operand to a square root, and both conversions land far inside int32. So no
guard violation was expected — and the prediction was recorded that way so that a firing would read
as the finding it is rather than as a surprise to be rationalised.

**Result: 23 of 23, both columns, 46 of 46 cells** (sealed `be7f80e5…`, 07:46:52Z, unchanged after).
No missing readings. No guard violation fired. Nineteen `(refuses, executes)` and four
`(executes, executes)`, the four being MMX.

### 2. THE MOVE, IN BOTH ACCOUNTINGS — WHICH IS WHAT D134 BOUGHT

```
THE UNASKED REMAINDER   235 pairs / 27,271 / 6.6%  ->  212 pairs / 23,532 / 5.7%
asked at its own bucket             84.3%          ->  85.2%

BY MNEMONIC   EXECUTES  87 / 156,976 / 38.0%  ->  107 / 160,182 / 38.8%
              probed   169 / 374,138 / 90.7%  ->  189 / 377,344 / 91.4%
BY (mn,BUCKET) EXECUTES 65 / 128,234 / 31.1%  ->   88 / 131,648 / 31.9%
              probed   153 / 298,111 / 72.2%  ->  176 / 301,525 / 73.1%
              not asked at its own bucket 114,367 -> 110,953
```

The 23 pairs' demand sums to **3,739**; the remainder fell by `27,271 − 23,532 =` **3,739**, and pairs
by exactly **23**. This is the first batch reported in both accountings, and the pair of them is the
point: the by-mnemonic headline moved +0.7 points while the demand-weighted one moved +0.9 — the two
do not track each other, which is precisely why publishing only the first was a mis-statement.

⚠️ Three mnemonics (`psllq`, `psrad`, `pcmpgtb`) already sat at SSE-legacy and were asked here at
**MMX**: distinct keys, distinct labels, measured separately.

### 3. WHAT FOUR BATCHES OF THIS NOW SAY, AND WHAT THEY DO NOT

Batches 27, 28 and 29 scored 23 of 23 each, 138 of 138 cells, against declarations hashed before ACL2
ran. Batches 28 and 29 were the ones that **could** have failed — every row declared `executes` off a
static read, with three divergence classes able to refute it. None did.

⛔ That is a measured statement about **69 implemented forms**, not a licence. A batch cannot be
sampled, and the classes remain live: the operand control exists because one of them fires on a form
already in this table. What it does support is the reordering itself — asking implemented pairs first
costs no more per pair and yields forms the differential can actually use.

`ci_local.py --job build`: **26 of 26 GREEN**. All 23 encodings from `clang`; D128's gate re-derives
all **225** rows on both disassemblers; D130's structure gate confirms 225 distinct tags.

## D136 — P2 BATCH 30: the implemented remainder exhausted in one batch, and the demand it moved counted two ways

Batches 27–29 asked 23 pairs each off the derived support read. This batch asks **all 38 that
remained** — every (mnemonic, bucket) pair `scripts/p2_oracle_support.py` reads as IMPLEMENTED in
x86isa's instruction listing. After it the derived-support queue holds **no implemented pair that
has never been asked**: the tool now prints `x86isa IMPLEMENTS 0 pairs / 0 / 0.0% of the remainder`.

### 1. WHY ONE BATCH AND NOT TWO, WHICH IS AN ARGUMENT ABOUT COST AND NOT ABOUT CONFIDENCE

The costs here scale with BATCHES, not rows: one ACL2 run (16.6 s for the whole 263-row table, not
per row), one `ci_local --job build` (2m25), one roster regeneration, one decision entry, one
commit. The costs that scale with ROWS — a spelling chosen, an encoding taken from `clang`, a
verdict predicted — are identical however they are grouped. Splitting 38 into 23 + 15 would have
paid the fixed cost twice and bought nothing.

⛔ **And it does not weaken the test.** Every row is scored independently against a declaration
hashed before ACL2 ran. 38 rows that could each fail is a strictly stronger run than 23 that could.

### 2. THE DECLARATION WAS SEALED BEFORE THE ORACLE RAN

```
sha256(the 38 rows) = 6e8474ff4f07771264068577b88644d49e94954752cecf2d5d1815c2609ff942
sealed 2026-09-05T20:02:18Z — verified byte-identical in the file BEFORE the run and again AFTER
```

Predictions: 29 `(refuses, executes)` for the SSE/VEX/AVX rows, 9 `(executes, executes)` for the MMX
rows — MMX does not go through CR4.OSFXSR, so the CR4=0 arm is not a refusal for them.

**RESULT: 38 of 38, both columns, 76 of 76 cells. No missing reading. No guard violation.**
`ci_local.py --job build`: 26 of 26 GREEN.

### 3. ⭐ THE CR4=0 ARM IS DEMONSTRABLY NOT FROZEN, AND THIS BATCH IS ITS OWN CONTROL

A column that reads `refuses` on every row cannot be distinguished from a column that is not being
set at all — the failure mode of [[feedback-a-dimension-with-no-parameter-is-frozen]], where 77 verdicts
turned out to be readings at zero. This batch carries the discriminator **inside itself**: the nine
MMX rows declare `executes` at CR4=0 where the twenty-nine others declare `refuses`, and all
thirty-eight matched. Measured inside batch 30: `{(executes, executes): 9, (refuses, executes): 29}`.
Had the CR4=0 arm been stuck at `refuses`, nine rows would have gone red. It is a positive control
that cost nothing because the batch's own composition supplies it.

The operand control ran as always and reports the write LANDS and the verdict DEPENDS on it, so
these are readings at the declared operands rather than at zero.

### 4. THE FP RISK WAS PRICED BEFORE THE RUN, NOT EXPLAINED AFTER

Nine rows do FP arithmetic (`addpd`, `subpd`, `mulpd`, `divpd`, `divps`, `maxps`, `minps`, `sqrtps`,
`cvtpd2ps`). An ACL2 guard violation is the outcome that is NEITHER verdict — it yields no reading
at all. Every result was computed first: double lanes 32.501960784313724 and 8.125246051728084,
single lanes 3.0039215087890625 and 2.5039138793945312, giving add 40.627207 · sub 24.376715 ·
mul 264.086429 · div 4.00012 (pd) / 1.199690 (ps) · max 3.003922 · min 2.503914 · sqrt 1.582376 ·
cvtpd2ps 8.125246 — all normal, no NaN, no denormal, no Inf, no zero divisor, no negative root.
So none was expected, and a firing would have read as the finding it is.

### 5. THE MOVE, IN BOTH ACCOUNTINGS

```
THE UNASKED REMAINDER   212 / 23,532 / 5.7%  ->  174 / 22,215 / 5.4%
   of which x86isa IMPLEMENTS   38 / 1,317   ->    0 /      0     <- the seam
BY MNEMONIC     EXECUTES 107 / 160,182 / 38.8%  ->  138 / 161,256 / 39.1%
                probed   189 / 377,344 / 91.4%  ->  220 / 378,418 / 91.7%
BY (mn,BUCKET)  EXECUTES  88 / 131,648 / 31.9%  ->  126 / 132,909 / 32.2%
                probed   176 / 301,525 / 73.1%  ->  214 / 302,786 / 73.4%
                not asked at its own bucket   110,953 / 26.9%  ->  109,692 / 26.6%
```

By (mnemonic, bucket) the pair count moved by **exactly 38** and the demand by **exactly 1,261** —
and 1,261 is the number I computed independently from `per_ext_map` for these 38 pairs before
reading the regenerated roster. Two routes, one number.

### 6. ⛔ AND THE NUMBER THE QUEUE TOOL PRINTED FOR THIS BATCH WAS 1,317, NOT 1,261

`p2_oracle_support.py` priced this batch at **1,317** instructions; the roster credited **1,261**.
The 56-instruction difference is not noise and not a rounding: it decomposes exactly across seven
VEX/AVX mnemonics whose demand straddles two buckets — `vmovups` 17 · `vpaddq` 26 · `vmovupd` 4 ·
`vmovmskps` 2 · `vmovapd` 4 · `vandps` 1 · `vxorpd` 2 = 56.

That is **D134's defect, in the tool written the same sitting as D134's repair**: a pair priced with
its MNEMONIC's whole demand while labelled and consumed at ONE bucket. It is repaired in D137, which
also names the sibling in `p2_roster.unprobed()` — the ranker that ordered batches 27–30 — because
naming a defect is not finding its siblings.

⚠️ It changes nothing about *this* batch's verdicts, which are measurements, not estimates. What it
touched was the PRICE and the ORDER, and both are stated here at the corrected figure.

## D137 — the queue rankers priced a pair at its mnemonic: D134's defect at the site D134 did not sweep

### 1. HOW IT WAS FOUND, WHICH IS THE PART WORTH KEEPING

Not by reading the code. By **two numbers for one batch that should have been the same one**.
`p2_oracle_support.py` priced P2 batch 30's 38 pairs at **1,317** instructions; the regenerated
roster credited **1,261**. 56 apart. That is small enough to round away and exactly the size that
gets rounded away — and it decomposed, with no remainder, across the seven mnemonics in the batch
whose demand straddles two buckets:

```
vmovups 17 · vpaddq 26 · vmovupd 4 · vmovmskps 2 · vmovapd 4 · vandps 1 · vxorpd 2  =  56
```

`vpaddq` was priced at **54** where its VEX-128 demand is **28** — nearly double.

### 2. THE DEFECT

D134 established that a mnemonic's whole demand must not ride on a reading taken at one of its
buckets, and repaired the published coverage table. **Both queue rankers kept doing it.**
`unprobed()` here and the remainder pricing in `p2_oracle_support.py` each walked
`build()["joined"]`, took `dominant_bucket(mn)` as the pair's key, and then priced that pair with
`occ` — the mnemonic's total across *every* bucket.

⚠️ **The prose was already correct; only the arithmetic was wrong.** `unprobed()` printed its total
under the label *"ASKED at the bucket its demand lives in"* while summing the quantity that is
explicitly not that. A label naming the right number is not a gate on it
([[feedback-a-citation-is-an-ungated-claim]]).

⇒ 🔑 **The error is an OVER-claim, which is the direction that reads as value.** A split pair is
ranked by demand that asking it cannot resolve, so inflated rows sort *upward* and the queue spends
its next batch on them first. This is `[[feedback-a-join-on-a-lossy-key]]` — one thing priced with
another's demand, arriving as an ordinary row.

### 3. WHAT THE CORRECTED NUMBERS ARE

```
THE UNASKED REMAINDER      22,215  ->  18,224 instructions   (3,991 was other buckets' demand)
   x86isa DOES NOT         20,108  ->  16,119
   NOT RESOLVED             2,107  ->   2,105
ASKED at the bucket its demand lives in
                          353,019  -> 282,908   (a 70,111-instruction over-claim, 17.0% of the gap)
```

Both tools now report **18,224** by independent routes. The witness the selftest names is
`vmovdqa`: **16,813** instructions of demand, **9,409** of them at `AVX2/AVX (ymm)` — the other
**7,404** sit where that pair cannot answer.

### 4. THE GATE, AND BOTH PLANTS DRIVEN RED

`unasked_walk()` is factored out of `unprobed()` so the selftest gates **the ranker's own output**
rather than re-deriving the walk beside it — a gate that rebuilds its subject can agree with the
code while both are wrong ([[feedback-two-readings-are-not-two-witnesses]]). Three arms:

- **a vacuity guard first.** If no mnemonic's demand were split, the two prices would agree and the
  arm would pass while testing nothing. It asserts the distinction has a live instance.
- **the witness arm:** a pair is priced strictly below its mnemonic's total.
- **the red arm:** run the *same walk* under the pre-D137 rule and require both the total **and the
  ordering the queue consumes** to change.

⛔ **Both reversions were planted and both went red**, each through the arm meant for it:

```
plant 1 — bucket_demand reverted   -> ⛔ "D137 arm is VACUOUS…"                    rc=1
plant 2 — unasked_walk reverted    -> ⛔ "22,215 -> 22,215 and does NOT reorder"   rc=1
restored                           -> PASS (69 arms)
```

Plant 2 is the one that matters: it leaves `bucket_demand` correct and reverts only the caller,
which is the actual defect this entry repairs.

### 5. ⛔ THE FIRST RED ARM I WROTE WAS A TAUTOLOGY

It set `_pre_d137 = _tot` and then tested `if _pre_d137 < _tot`. That is `_tot < _tot` — false by
construction, so the arm printed ✔ on every possible input and could not have failed for any reason.
It was written in the same hour as, and directly beneath, a comment citing
[[feedback-an-implied-assertion-is-not-a-second-gate]].

⇒ 🔑 **A red arm whose planted value is computed from the thing it is compared against is not a
control, it is a restatement.** The repair was to give the arm a subject that actually runs — the
ranker — and then to prove it fires by planting the reversion rather than by arguing it would.

### 6. WHAT THIS DOES NOT CHANGE

No measured verdict moves: availability is read by executing, and D136's 38 of 38 are measurements.
`docs/P2-ROSTER.md` is **byte-unchanged** by this commit — the published coverage tables were
already per-bucket, which is exactly why the discrepancy showed up as a disagreement between the
rankers and the roster rather than as a wrong published number. What moves is the **price** of the
remaining work and the **order** it will be done in.

## D138 — the sixteen "absent under this name" pairs: eleven were never absent, and the reader was dropping 169 entries

The council's item 2 was *"the 16 NOT-RESOLVED names, each found by ENCODING"*. Resolving them
found that the pile had two different things in it and that its label was wrong for most of them.

### 1. ELEVEN OF THE SIXTEEN NAMES WERE IN THE LISTING ALL ALONG

The first check was the cheapest one and it should have been run when the pile was created:
grep the listing for each name. Eleven of sixteen are there. So `"absent under this name"` — the
tool's own words — was false for eleven pairs, and the real cause was that the catalogue READER
discarded their entries. `entries()` computes a bucket, and `if bucket is None: continue`; a
dropped entry leaves no trace, and the pair then reads as a *name* problem downstream.

⇒ 🔑 **A pile named for one cause collects everything with that symptom.** The name of a bucket is
a hypothesis about its contents, and nothing was gating it.

### 2. TWO READER DEFECTS, MEASURED RATHER THAN ESTIMATED

```
INST entries in the listing            3,184
dropped by the reader (bucket = None)  1,777   55.8%
  EVEX — out of scope BY DESIGN          927        0 implemented
  legacy, genuinely non-vector           437      378 implemented  (correctly excluded)
  legacy, no ARG list (mostly non-vector)244       30 implemented  (correctly excluded)
  ⛔ VEX with :LIG / :LZ / :L0           161        8 implemented  ← DEFECT
  ⛔ vector operand present, not in OP1    8        0 implemented  ← DEFECT
```

⚠️ The first cut of this table said *"445 entries lost to the OP1 regex"*. That was wrong: it
lumped 437 ordinary GPR instructions — correctly excluded from a **vector** census — in with the 8
real misses. **The in-scope loss is 169 entries, not 850 and not 1,777.** A breakdown that mixes a
correct exclusion with a defect over-states the defect, and the over-statement is the flattering
direction when you are the one reporting it.

**Defect A — the width is not always spelled `:128`/`:256`.** x86isa marks VEX lane width with six
tokens: `:128` 306 · `:256` 277 · `:LIG` 70 · `:L0` 36 · `:LZ` 28 · `:L1` 27. The reader knew two.
`:LIG`/`:L0`/`:LZ` are the **scalar VEX** forms — `vaddss`, `vmovsd`, `vcomiss`, `vcvttss2si` and
their kin, every one encoded with VEX.L = 0 and keyed by the census at VEX-128. Eight of the
sixteen unresolved names were this class.

**Defect B — the ARG regex read only the first operand.** It was
`\(ARG\s(.*?)\)\s*\n` — non-greedy to the first `)` at end of line — and an ARG list is written one
operand per line. On `pextrw` it captured `":OP1 '(G D"`: a GPR, no vector register, bucket `None`.
⇒ **every instruction whose vector operand is not first was invisible** — `pextrw`, `pextrd/q`,
`pinsrd/q`, `extractps`: the extract-and-insert family, which is exactly the family whose
destination is a GPR or memory. Replaced by a balanced-paren reader.

With both repaired, `NOT RESOLVED` fell 16 → 6 pairs and the ten that moved all landed in
`DOES NOT` — independently agreeing with the encoding resolution done by hand first.

### 3. THE SIX THAT REALLY WERE NAME DIFFERENCES, RESOLVED BY ENCODING

`scripts/resolve_names.py` keys on what the machine dispatches on — opcode map, opcode byte,
mandatory prefix, VEX.L — recovered from bytes `clang` emitted:

```
cvtsi2sdq  #xF2A   :F2  f2480f2ac0      -> cvtsi2sd    executes   ← 178 instructions, ASKABLE
cvtsi2ssq  #xF2A   :F3  f3480f2ac0      -> cvtsi2ss    executes   ←  14 instructions, ASKABLE
pextrd     #xF3A16 :66  660f3a16c001    -> pextrd/q    refuses
pinsrd     #xF3A22 :66  660f3a22c001    -> pinsrd/q    refuses
pinsrq     #xF3A22 :66  66480f3a22c001  -> pinsrd/q    refuses
vzeroupper #xF77   -    c5f877          -> vzeroupper  executes   ← 1,241, NOT askable
```

⛔ **And this is why the rule is "by encoding, never by name."** A suffix-stripping rule gets
`cvtsi2sdq → cvtsi2sd` right and then must invent `pextrd → pextrd/q` — and *no edit of the string
`pextrd` produces `pextrd/q`*, because that name is two widths sharing one entry, not a spelling of
one mnemonic. D100 paid for the general form of this with a phantom row.

⚠️ `vzeroupper` resolves and **is implemented**, and is still unaskable: the census keys it at
`AVX (state)`, one of the buckets `probe_bucket` cannot express (D128 §5). Resolving the name buys
the verdict and nothing askable — 1,241 instructions this route cannot reach.

### 4. ⛔ THE RESOLVER'S OWN GATE WAS WRONG TWICE, AND BOTH WERE FOUND BY PLANTING

**(a) It refused, and the refusal was right.** The first run failed with
*"vzeroupper: 2 listing names ['vzeroall', 'vzeroupper'] — ambiguous, not picked"*. Both sit at
opcode `0F 77` with no prefix and are told apart by **VEX.L alone**, which my key did not carry.
The gate declining to choose is what exposed the omission; a resolver that picked the first name
would have published `vzeroall`'s verdict under `vzeroupper`.

**(b) It was silent, and the silence was a circular test.** The spelling arm accepted
`head in (mn, name)` — where `name` is the listing name **derived from those very bytes**. So it
asked whether the disassembly agrees with what the bytes decoded to, which is true by construction.
Planting `addpd %xmm1, %xmm0` as the spelling for `cvtsi2sdq` resolved it to `addpd` and the gate
printed **CLEAN**.

⇒ 🔑 **A check whose expected value is computed from its subject is not a check.** The repair
compares against `mn` — the census mnemonic, the one datum in the row that does not come from the
bytes — allowing only the operand-size suffix the two spellings disagree about. Re-planted after
the fix: `⛔ … the spelling is not this instruction`, rc 1.

### 5. P2 BATCH 31 — THE TWO PAIRS THE READER WAS HIDING

Declaration sealed before ACL2 ran (`a32e3399…`, 2026-09-05T20:33:02Z), verified unchanged after.
**2 of 2, both columns.** `(refuses, executes)` each — measured now, not predicted.

⚠️ The source operand is a **GPR, a dimension this probe does not vary**, so it was checked instead
of assumed: `measure_cr4`'s `init-x86-state-64` sets gprs `((0 . #x400000) (3 . #x2000))`, so
RAX = 4,194,304 = 2²² — non-zero and exact in both float and double. Had it been 0 these would
convert 0 → 0.0 and risk the `SSE-POST-COMP` guard violation that yields **no reading at all**.

### 6. WHERE THE QUEUE STANDS

```
THE UNASKED REMAINDER   174 / 18,224  ->  172 / 18,032
  x86isa IMPLEMENTS       3 /  1,433  ->    1 /  1,241   (vzeroupper alone, and unaskable)
  x86isa DOES NOT       171 / 16,791  ->  171 / 16,791
  NOT RESOLVED            0 /      0  ->    0 /      0
```

**Every implemented pair that can be asked has been asked.** What is left is 171 pairs x86isa does
not implement and one it does that no probe can express — a *design* item (widen `probe_bucket`),
not a queue item. D136's headline `IMPLEMENTS 0 pairs` was true of the reader and false of x86isa;
it is corrected here, and the correction was worth 192 instructions of measured coverage.

## D139 — the soft-float commission, opened: its premise tested, its price re-derived, and one of its own kill-checks refuted

The council's item 2(c) put the soft-float commission on this repository's queue as P3, *"a design
commission with its own freeze + refuter pass when paris reaches it"*. The two items ahead of it
(D136, D138) are discharged, so it is opened here. `docs/SOFT-FLOAT-COMMISSION.md` is the freeze and
`docs/QUEUE.md` is the queue it sits on — the first time this repository's queue has been a file
rather than bank prose, which is §2's whole lesson.

### 1. THE PREMISE WAS INHERITED, SO IT WAS TESTED

The commission has been carried since batch 19 on *"Lean's `Float` is an opaque extern type the
kernel cannot reduce"*. Run at `v4.32.0-rc1`, it is confirmed and **stronger than stated**:

```
(2.0:Float) + 2.0 = 4.0  by rfl          ⛔ not definitionally equal
#print Float                              structure Float where val : floatSpec.float
#print floatSpec                          opaque floatSpec : FloatSpec   ← nothing to unfold
                         by native_decide ⛔ failed to synthesize Decidable (2.0 + 2.0 = 4.0)
CONTROL, same run:  (2#8) + (2#8) = 4#8 by decide   ✔ depends on NO axioms
```

There is no route through `Float` **at any axiom price** — not merely no kernel route. The escape
hatch usually available (`native_decide`, at the cost of `ofReduceBool`) does not apply, because
propositional equality on `Float` has no `Decidable` instance at all.

### 2. THE PRICE HAD DRIFTED 44% WHILE THE ROW SAT DOCKETED

The commission's size has been quoted as **25,688 instructions over 7 mnemonics** since batch 19.
Re-derived from the current measured availability table: **40 pairs, 36,925 instructions.** Batches
29, 30 and 31 measured twenty more FP mnemonics as executing, and every one of them joined a block
whose price was a sentence in a bank.

⇒ 🔑 **A cost carried in prose does not move when the world does.** Nothing was wrong when written;
what was missing is that no gate and no generator owned the number, so eleven days of measurement
went past it. That is why the price now names the tool that prints it.

### 3. K1 — VERIFIED, WITH A CONTROL

`ucomisd`'s comparison rule, over Lean-core `BitVec`, no mathlib, decided by the **kernel**, with
`#print axioms` reporting `[propext]` — inside the three standard axioms. Seven cases pass,
including the four a raw bitvector compare gets wrong (`+0 = -0`, negative ordering, NaN unordered).

⛔ And a planted-wrong expectation was refuted by the kernel (*"decide proved that the proposition …
is false"*), because seven passing `decide`s prove nothing about propositions that might be vacuous.

### 4. ⛔ THE REFUTER PASS KILLED ONE OF MY OWN KILL-CHECKS

K2 said sub-group B *needs rounding, therefore MXCSR* — as a property of the block. Attacked by
asking whether any member is exact for every input:

```
cvtss2sd   binary32 -> binary64 : 199,489 patterns   non-exact 0
cvtsi2sdl  int32    -> binary64 : 200,000 values     non-exact 0
CONTROL cvtsi2sdq  int64 -> binary64 : non-exact 198,824   <- the instrument sees rounding
CONTROL cvtsi2ssl  int32 -> binary32 : non-exact 193,067
```

binary64 has an 11-bit exponent against binary32's 8 and 52 mantissa bits against 23, so every
binary32 value widens exactly; every int32 fits in a 53-bit significand. **3,437 instructions leave
the rounding-dependent block**, and the immediately-buildable group doubles: 3,182 → 6,619, from
8.6% of the commission to 17.9%. A third group separated itself on the way — `cvttsd2si`/`cvttss2si`
truncate, and truncation is fixed by the opcode rather than chosen by MXCSR.RC.

⇒ 🔑 **A block named for a shared blocker is a hypothesis about every member of it.** `cvtss2sd` has
sat inside this commission since batch 19 as one of its original five, and it cannot round. The
grouping was made from the *instruction class* rather than from the *question* — can this result be
inexact? — and no gate reads a class.

### 5. WHAT IS RECOMMENDED, AND WHAT IS DELIBERATELY NOT PRICED

Take sub-group A (6,619 instructions, no new state field) as an ordinary P2-shaped batch. Leave B
frozen until K3 and K4 are **measured** — K3 because a `Cpu` field is not known to be cheap
([[feedback-a-state-field-costs-every-record-proof]]: two fields once blew three unrelated record
proofs), K4 because a 52×52 mantissa multiply in the kernel is not obviously affordable under the
delta gate.

⛔ **B's price is left blank on purpose.** Inventing one would be the third inherited figure in this
commission's own history, and §2 is a record of what that costs.

## D141 — the delta gate's refusal grew with the repeats it asked for: a gate whose only remedy was a box it could not have

> ⚠️ **D140 IS NOT MISSING.** It is P2 batch 32's own entry, written on
> `p2-batch32-fp-compares` and not yet merged. This repair lands FIRST and on
> `master` deliberately: it is the instrument that will score that batch, and an
> instrument judged in the same commit as the thing it judges cannot be judged at
> all. The gap closes when the batch merges.

Batch 32 has sat on `p2-batch32-fp-compares` since 15:33 on 09/05, held off `master` by a delta
gate that returned `UNMEASURABLE`. The bank handed that on as *"blocked on a quiet box"*, and the
box was not quiet at the next boot either (load 10.46/11.12/11.06). Before waiting for a third
afternoon I read the instrument. **The refusal was honest and its stated remedy was arithmetically
impossible.**

### 1. THE DEFECT, IN ONE LINE OF THE GATE'S OWN SOURCE

`kernel_delta.py` refused when `budget < spread`, and printed *"re-run with more `--repeats` or on
a quieter box"*. `spread` was

```python
spread = max((max(bs) - min(bs)) if len(bs) > 1 else 0.0,      # the RANGE of a side's readings
             (max(hs) - min(hs)) if len(hs) > 1 else 0.0)
```

⛔ **A RANGE GROWS WITH THE NUMBER OF READINGS.** The quantity actually gated is a difference of
MEDIANS, whose uncertainty falls as `1/sqrt(n)`. So of the two remedies the gate offered, the one
under the seat's own control made the refusal STRICTLY MORE LIKELY, and only the one outside its
control could ever help. Driven through this file's own `verdict()` on synthetic readings — a true
delta of 1,000 ms, per-reading sigma 1,400 ms, the real 1,778 ms budget, 400 trials a cell:

```
n:                          2      3      4      6      8     10     16     24
REFUSE rate:              60%    84%    96%   100%   100%   100%   100%   100%
mean spread (max-min):   2257   3053   3528   4210   4579   4915   5501   6024
sd of the gated estimate:1445   1313   1035    946    846    748    613    504
```

⭐ The two DIRECTIONS in that table are bounds 8 and 9 of `delta_band_calibration.py --check`, so
the finding is re-derivable rather than quoted — a paragraph is where a claim's negation gets
written. ⚠️ They are asserted about the STATISTICS and call nothing in `kernel_delta.py`; the
REFUSE row is bound 6, which does read the shipped rule.

⇒ 🔑 **THE INSTRUMENT GOT MONOTONICALLY BETTER AND THE GATE GOT MONOTONICALLY MORE CERTAIN THAT IT
COULD NOT SEE.** Spending machine time on this gate bought refusals. The one act a seat could take
was the one act that could not work, and the gate said so in the same paragraph as the verdict.

### 2. THE HALF THAT IS WORSE, BECAUSE IT IS A FALSE VERDICT AND NOT A MISSING ONE

The same rule on a QUIET box (sigma 200 ms) refuses nothing — and on a commit sitting exactly ON
its budget it returned `ok` **50%** of the time and `OVER BUDGET` **50%**, over 4,000 trials. A
coin flip, delivered as a verdict, on precisely the commits a budget gate exists to judge. A small
range says the readings agreed with each other; it never said the delta was far enough from the
budget to call. The two failures are one mistake: **`spread` answered a question about the
READINGS where the gate needed one about the ESTIMATE.**

⛔ And a third face of it, found by an arm whose own NAME had been carrying the defect for nine
batches. `--selftest` asserted that `{M: 100} → {M: 900}` with jitter 80 against a 50 ms budget
must REFUSE — *"a REFUSAL outranks an over-budget red"*. That is a delta **sixteen times** its
allowance and five standard errors clear of it, refused because the box's noise (80) exceeded the
budget (50). The arm's name stated a principle that is true only when the run genuinely cannot
tell, and the arm made the blindness look like scruple. It is now split in two: a straddling band
still refuses, **and a delta far over budget is CONVICTED even when the box's noise exceeds that
budget.**

### 3. WHAT REPLACES IT — A BAND, NOT A THRESHOLD

Each unit's delta carries the uncertainty of its own estimator, from this run's readings alone:

```
se(unit) = 1.2533 * sqrt( s_base^2 / n_base + s_head^2 / n_head )
delta - K*se > budget  ⇒ FAILED  ·  delta + K*se < budget  ⇒ ok  ·  else UNMEASURABLE
```

with **K = 2**. The refusal now depends on how far the delta is from the budget, not merely on how
loud the box is, so a commit nowhere near its allowance is decided cheaply and only a commit near
the line is expensive — which is a fact about the commit.

⛔ **K WAS NOT CHOSEN BY WHAT IT SAYS ABOUT BATCH 32.** Deriving a gate's free number from the
commit under test is the move this file already forbids for the budget, and it would have been
easy here: K=1 decides batch 32 in about a third the repeats. K was fixed on the two error rates,
swept over sigma in {200, 1000, 2000} ms and n in {3, 6, 10, 16, 24}, 4,000 trials a cell,
identical draws for every rule:

```
                                        OLD range      BAND K=1      BAND K=2
false PASS  (`ok` at a true 2x budget)      0.0%          2.7%          0.5%
false RED   (`FAILED` at a true zero)       0.0%          3.0%          0.5%
a commit exactly ON its budget, refused    0-100%          67%           92%
a harmless commit, sigma 1000, n=3..24    33%→0% ok    79%→100% ok   49%→100% ok
```

The OLD column's zeroes are bought by refusing 95-100% of everything; they are the numbers of an
instrument that does not speak.

⛔ **And the first draft of this table, and of the docstring it summarises, said `≤ 0%` for both of
K=2's figures and `≤ 2%` for K=1's false pass.** Those came off the exploratory probe, which
printed integer percentages; the calibration script then computed 0.5%, 0.5% and 2.7% and the
prose was never reconciled with the gate written to check it. **An over-claim by the width of a
truncation, in the paragraph whose whole job is to report a measurement** — and the gate did not
catch it, because it asserts `≤ 1.0%` while the prose claimed something stricter than the gate.
⇒ 🔑 *a bound in prose that is TIGHTER than the bound in the gate is unpoliced in the direction
that flatters.* Corrected to the measured worst cell. ⭐ **The sweep is `scripts/delta_band_calibration.py` and it is a
GATE, not a table**: `--check` asserts all seven bounds, including the two LIVENESS bounds that a
rule refusing everything would fail, and it reads `K_SIGMA` out of the shipped gate rather than
keeping a copy — if the constant is renamed it refuses instead of testing a number nobody uses.
Driven red at K = 0.5, 1.0 (false-pass and false-red bounds break) and 4.0 (liveness breaks).

### 4. THE PRECEDENCE INVERTED WITH THE RULE, AND ONLY A REPLAY SHOWED IT

The gate returned `UNMEASURABLE` (rc 3) in preference to `FAILED` (rc 1), on the old arm's
principle that *"a refusal is not a verdict at all"*. While the refusal read `budget < spread` that
was right: the spread was a property of the RUN, so a refusal anywhere meant no verdict anywhere.

Under the band it is a property of ONE UNIT and its distance from ITS budget — and a unit marked
`OVER BUDGET` was convicted **beyond this run's noise**, which is exactly what the refused unit
says it could not establish. Found by replaying a realistic readings file through `--readings`:
`Tests.Coverage` convicted at +2,900 with a ±409 band, `Tests.Coverage @residue` refused at the
same +2,900 because its budget is 2,766 and the margin is +134. The run was reported
`UNMEASURABLE`. ⇒ **a commit that certainly breaks a budget was being filed under "we could not
tell", because a different unit was unresolved** — the reassuring direction. Now `FAILED` outranks
`UNMEASURABLE` outranks `CLEAN`; both messages still print, only the exit code ranks. A tightening,
and pinned by its own arm.

### 5. THE HOLE AT THE OTHER END, CLOSED BY THE SAME CHANGE

`max - min` of ONE reading is `0.0`, so under the old rule `--repeats 1` could **never** refuse:
the gate returned a verdict off a single pass a side with nothing whatever said about its noise.
A side with fewer than two readings now yields an infinite band and the gate refuses. Nobody was
looking at that end, because a refusal test is read as the thing that might fire too often.

### 6. THE ARMS

⭐⭐ **AND THE MEASURED SELFTEST'S OWN JUDGEMENT IS NOW DRIVEN WITHOUT ITS FOUR BUILDS.**
`selftest_measure` lives in its own CI job because it needs real trees, and **that job has never
completed on any machine** — so its decision logic was the least-exercised code in the file, and
this repair changed it. Three arms stub `measure` and hand arm 1 each of the three verdicts it can
be told: a conviction on identical trees must RED (a true delta of exactly zero convicted would
make every red this gate ever printed suspect), a CLEAN passes, and a REFUSAL passes while
reporting the box. Nothing is profiled.

⛔ **And the first version of those arms had the defect they exist to catch.** Driven red, a mutant
that quietly replaced the loud-box stub readings with quiet ones left the suite GREEN: the arm
named *"identical trees REFUSED"* was testing the CLEAN branch under that name, and the rc-3 branch
went uncovered with nothing red. Each case now DECLARES the verdict it must produce, and an arm
that fails to create its own condition says so in those words. Two of three planted defects were
caught before that fix; three of three after.

`--selftest` is 28 arms (was 18). Six planted defects, each the shape a hurried fix takes —
`K_SIGMA = 0`; `resolution()` returning the range again; a one-reading side scoring 0.0 noise;
either side of the band dropped; `se` not dividing by `n` — **all six caught.** The arms that name
the finding are a matched pair on the SAME dispersion at 3 and at 12 repeats: the readings' range
is identical (600.0 in both) while the band falls from ±614 to ±262, so the old rule's verdict
could not have moved and the new rule's does. A third arm asserts that pairing directly, because
without it the two runs are unrelated and prove nothing about the remedy.

### 7. THE REFUSAL NOW NAMES ITS PRICE, AND ITS THREE CAUSES SEPARATELY

A refusal prints, per unit, the delta, the budget, the margin between them, the band, and
`~N repeats a side would decide it` — `N = n * (K*se / |delta - budget|)^2`, labelled a projection
because it reads this run's noise forward onto a box that may not repeat it. Three causes that the
first draft of this message collapsed into one sentence are now named apart: a side with fewer than
two readings (cannot estimate its noise at all), a delta sitting exactly on its budget (no n
decides it), and a genuine straddle (buy repeats). The first draft printed *"no number of repeats
decides a delta sitting ON its budget"* for a unit whose margin was −990.

### 8. ⛔ AND THE FINDING THAT MADE ALL OF THIS COST AN EXTRA DAY

`kernel_delta.py` has taken `--out FILE` and `--readings FILE` from the start, *"because a
measurement that took eleven minutes should be re-judgeable against a changed budget in seconds"*.
**The batch-32 run did not pass `--out`.** Its readings do not exist, so the refusal that held the
batch cannot be re-judged, the sigma behind its 3,400 ms spread is an inference from a printed
range rather than a measurement, and the first thing this repair wanted — the actual numbers — had
to be replaced by a synthetic model of them. This is the seat's own banked card *"a gate that
refuses must say what it saw"*, paid on the seat's own gate, by the head that wrote the card.

### 9. WHAT THIS DOES NOT SETTLE

- **It does not score batch 32.** No tree was profiled for any number in this entry; every reading
  here is synthetic and says so. Whether the batch passes, fails, or refuses again is the next
  measurement's to say, and it will be taken with `--out`.
- **The 1.2533 factor is asymptotic** and conservative at the n this gate runs (the true ratio at
  n=3 is 1.16), and it assumes readings that are independent within a side. Drift makes `s` too
  large, hence the band too wide, hence the gate too conservative — the safe direction, stated
  rather than corrected. Correcting it would need the paired differences, and with the passes
  ordered base,head,base,head each pair carries a one-pass bias the medians do not.
- **A band of exactly zero means "these readings did not vary", which is not quite "there is no
  noise".** Lean's profiler prints three significant figures, so a module reported in SECONDS is
  quantized to 100 ms and one reported in milliseconds to 0.1 ms. Checked rather than assumed:
  `Tests.Coverage` at ~26 s carries a 100 ms quantum against a 1,778 ms budget (0.4%), and the
  smallest units are floored at 6 ms absolute, so no unit's budget is currently near its own
  quantum and a zero band cannot manufacture a conviction. It is written down because that
  relationship is not gated anywhere, and a future unit whose budget approaches its quantum would
  get a confident verdict off readings that agreed only because they were rounded.
- **`--repeats 6` in CI is a guess about a runner nobody has measured** (Actions refuses every job
  on this account for billing, desk FH). The first run that completes there prices it, and the
  number to read off is the gate's own `~N repeats` line.

## D142 — batch 32 re-measured on the repaired gate: the +2,900 that held it and the +1,000 that replaced it are the same reading

The first act of the repaired delta gate (D141) was to take the measurement the old one refused,
`--repeats 6`, **with `--out`** — the flag the first run omitted, which is why none of this could be
established by re-judging instead of re-measuring.

### 1. THE TWO RUNS, AND WHY NEITHER IS "THE" DELTA

```
                        base      head     delta    band(K=2)     range    budget   verdict
run 1  09/05 15:2x    24 700    27 600    +2 900    (±4 100)*     3 400    1 778    UNMEASURABLE
run 2  09/05 16:1x    24 500    25 500    +1 000     ±1 443       2 700    1 764    UNMEASURABLE
                                                     * reconstructed: run 1 saved no readings
```

⛔ **The two runs profiled the same trees.** Run 1's head was `42f9ebe` and run 2's `3a811fb` — two
amends apart — but the amends touched `Main.lean` and two docs, and `kernel_cost.modules()` reads
`X86/*.lean`, `X86.lean`, `X86Native.lean`, `Tests/*.lean`, `Tests.lean`. None of the three is
profiled. Same subject, two afternoons.

⇒ 🔑 **THE SAME HEAD TREE READ 27,600 AND 25,500 ON TWO AFTERNOONS, WITH NO CODE BETWEEN THEM.**
That 2,100 ms is the instrument, measured across sessions rather than argued from within one, and
it is larger than the 1,764 ms budget the two runs were arguing about. The honest statement is not
that run 1's +2,900 was wrong: it is that **+2,900 and +1,000 are the same measurement to within
the resolution of the box**, and the band is the first thing this gate has ever printed that says
so out loud.

⚠️ **And the located CAUSE that came with run 1 did not survive.** Its reading put the cost at
`Tests.Coverage @residue`, *"15,210 → 18,210, +3,000 for 8 vectors — about 375 ms per vector"*, and
the bank's order to a successor was built on it (*"cut vectors or move the coverage claim"*).
Measured at six repeats, `@residue` is **15,225 → 15,960, +735, band ±1,319, budget 2,116 — `ok`**.
The unit named as the batch's cost is the unit the gate now passes.
[[feedback-inherited-diagnosis-is-a-hypothesis]]

### 2. FIVE UNITS REFUSED, AND THEY ARE NOT ALL ABOUT THE BATCH

```
UNIT                                     delta    band     budget   ~repeats to decide
Tests.Coverage                          +1 000   ±1 443   1 764.0        22
Tests.Coverage @decl vectorCoverage       +195     ±265     266.1        84
X86.Basic                                 −1.7    ±34.7      24.6        11
X86.Semantics                             +0.8     ±6.7       6.0        10
X86.Value                                 −1.9    ±14.1       6.1        19
```

Read the deltas. **Three of the five are essentially zero** — the batch does not touch `X86.Basic`,
`X86.Semantics` or `X86.Value` in any way that a millisecond could see. They refuse because each
one's BUDGET is smaller than what this box invents between two readings of one tree. Those three
would refuse for any commit, including a commit that changed nothing.

⚠️ **Not a regression from the band.** The old range rule refused them too (`X86.Semantics` range
16.1 against a 6.0 budget). What changed is that the refusal now says which units, why, and what an
answer would cost.

⛔ **And this REFUTES the direction `docs/QUEUE.md` item 4 asserted four hours earlier**, in the
same sitting, written by me: *"a floor is a MINIMUM allowance, so this one can only be too
generous; re-deriving it can only tighten the gate."* `X86.Semantics`'s budget IS the floor (27.8%
of 15.6 ms is 4.34, floored to 6.0) and the box's band on it is **±6.7** — so a floor derived
against the band would be LARGER. ⇒ 🔑 *"it can only err in the safe direction" is a claim about a
measurement nobody has taken*, and it survives precisely because it sounds like caution.
[[feedback-conservative-is-a-direction-not-a-margin]]

### 3. THE CONTROL, AND IT SETTLES THE QUESTION AGAINST BOTH RUNS

`kernel_delta.py --base c372d80 --head c372d80 --repeats 6` — **the same commit on both sides**, so
the true delta of every unit is exactly zero. Run at 16:2x, an hour after the batch run, same box.

```
UNIT                                    base      head      delta    band     budget   VERDICT
Tests.Coverage                        27 500    25 350    −2 150   ±2 474    1 980    ok
Tests.Coverage @residue               17 680    15 650    −2 030   ±2 637    2 458    ok
Tests.Coverage @decl memDestSweep      5 715     5 830      +115     ±510      492    UNMEASURABLE
Tests.Coverage @decl vectorCoverage     1 770     1 760       −10    ±72.7      278    ok
X86.Basic                               96.6      99.6      +3.0    ±10.9     24.4    ok
X86.Semantics                           15.8      16.4      +0.7     ±2.6      6.0    ok
X86.Value                               27.5      27.7      +0.2     ±2.6      6.0    ok
```

⇒ 🔑 **THE GATE INVENTED A 2,150 ms DIFFERENCE BETWEEN TWO COPIES OF ONE COMMIT — larger than the
1,980 ms budget it was gating — AND RETURNED `ok`.** That `ok` is not a bug: the band covers the
invented delta, so "confidently not over budget" is a true statement. But it is a true statement
about the BUDGET and not about the instrument, and the number that says so — the −2,150 — is
printed by `--selftest-measure`'s arm 1 under the words *"that is what this box invents between two
copies of one commit, and every budget has to clear it"* **with nothing gating it.**

⛔ **And the same base tree read 27,500 here and 24,500 an hour earlier — 12% apart, on `c372d80`,
with no code between them.** Batch 32's whole disputed delta is +1,000. The instrument's own zero
moves by three times that between runs.

### 4. MY PREDICTION FOR THIS CONTROL WAS WRONG, AND THE WAY IT WAS WRONG IS THE FINDING

Written down before the control finished, from the batch run's bands: *"three of the five refusals
are the BOX (`X86.Basic`, `X86.Semantics`, `X86.Value` — deltas ~0, budgets under the noise) and
two the BATCH."* The control passed **all three**, with bands 3-5× smaller than the batch run's:

```
                 batch run     control
X86.Basic          ±34.7        ±10.9        budget 24.4-24.6
X86.Semantics       ±6.7         ±2.6        budget 6.0
X86.Value          ±14.1         ±2.6        budget 6.0-6.1
```

⇒ 🔑 **"THE BOX'S NOISE" IS NOT A PROPERTY OF THE BOX.** It varies several-fold between two runs an
hour apart, so no single run supports a sentence of the form *"this unit's budget is under the
box's noise"* — including the sentence I wrote into `docs/QUEUE.md` item 4 four hours earlier and
then corrected once already, in the opposite direction, on the batch run's numbers. That claim has
now been wrong twice in one sitting, in both directions, each time from one run's readings.
[[feedback-a-single-reading-is-about-its-run]]

⚠️ There is no order bias to report, and I looked: the batch run's base read LOWER than its head
(24,500 vs 25,500) and the control's read HIGHER (27,500 vs 25,350). A systematic base-then-head
effect would have pointed the same way twice. It does not, so the alternation is not indicted here
— what is left is plain, large, run-to-run variation.

### 5. WHERE THIS LEAVES BATCH 32 — NOT MERGED, AND NOT FOR "A QUIET BOX"

Not one unit's delta exceeds its budget as a point estimate, in either run. Nothing is convicted.
But the gate refuses, and the control says the refusal is honest rather than timid: on
`Tests.Coverage` this instrument cannot resolve a 1,764 ms budget at any affordable number of
repeats, because its own zero wanders by ±2,000 between runs. The refusal names 22 repeats for
`Tests.Coverage` and **84** for `Tests.Coverage @decl vectorCoverage`, whose margin is 71 ms —
and at 84 the band still lands exactly on the line, so even that price does not buy an answer.

⇒ The remedy the gate offers third is the only live one: **make the measurement cheaper to resolve,
not the verdict easier to reach.** That is now `docs/QUEUE.md` item 4, rewritten from "re-derive
`@floor`" to what the measurements actually say. ⛔ Batch 32 stays on its branch — but for a
recorded, measured reason with a named next act, which is a different thing from waiting on
a quiet box that was never going to come.

## D143 — `probe_bucket` was not a narrow rule, it was a SECOND rule, and the gate that should have seen it was checking the vocabulary

`docs/QUEUE.md` has carried *"widen `probe_bucket` — it expresses 5 of 18 census buckets"* since
D128, with `vzeroupper` (`AVX (state)`, 1,241 instructions, the only pair x86isa implements that no
probe can ask about) as the reason. Reading it for the first time rather than inheriting it: the
shape of the item is wrong.

### 1. THE CENSUS ALREADY HAS A TOTAL RULE, AND IT ALREADY ANSWERS

`demand_census.isa_bucket(mn, ops, kind)` produced the DEMAND side of the join, is total, and
returns `AVX (state)` for `vzeroupper` out of the very table the census keeps *"for operand-free
AVX state instructions: the width rules cannot see them, because there are no operands to read a
width off"*. `oracle_availability.probe_bucket` read the register file off the operands and
returned `None` for anything without one.

⇒ **Two functions for one partition**, and the join between them is the thing the whole
availability census rests on. ⛔ MEASURED over all 265 probe rows before touching anything: the two
agree on **256 of the 256 rows both classify, and disagree on none.**

⇒ 🔑 **THAT AGREEMENT IS WHY IT SURVIVED, AND WHY IT COULD NOT BE SEEN.** `p2_roster.py` already
gated this and the gate is honest about what it checks — *"every probe bucket is a census bucket"*
— which is a check on the **VOCABULARY**. It passes whenever both names exist, and would pass with
the two rules assigning the same row to different buckets. A duplicate born in agreement is
invisible to a name check and diverges on the next ordinary append to either table.
[[feedback-duplicate-born-in-agreement]]

### 2. SO IT DELEGATES, AND THE ARM TESTS THE DELEGATION AND NOT THE AGREEMENT

`probe_bucket` now calls `demand_census.isa_bucket`. Every existing bucket arm still passes — they
would pass against a second rule too, which is the point. The new arm STUBS the census's function
and requires `probe_bucket`'s answer to move with it. Driven red by re-introducing a local rule
that agrees with the census on every current row — the exact shape of the defect being removed:

```
⛔ probe_bucket IS demand_census.isa_bucket, not a rule that agrees with it
   (got 'SSE-legacy (xmm)' from a stubbed census rule — there is a second bucket rule again)
```

### 3. AND THE `None` WAS DOING TWO JOBS

`probe_bucket` returned `None` for a row with no vector operand, and `measured_availability`
skipped it. So the set of rows the availability census does not ask about was *"rows with no
`%xmm`"* — a DEFAULT wearing a decision's clothes, whose nine members each inherited an accident
rather than a ruling. Naming the bucket and deciding whether the row is a question are different
jobs; the second one now lives in `NOT_AN_AVAILABILITY_QUESTION`, a declared list with a reason per
entry, gated for orphans. [[feedback-a-declared-list-inherits-its-default]]

⛔⛔ **AND THREE OF THE NINE TURNED OUT TO HAVE MEASURED REASONS — which is what stopped this from
being a wholesale delegation.** Computing the delegated table before changing anything:

```
+ ('lock',     'GPR/other (unclassified)')   ← `asm.split()[0]` is the PREFIX, not a mnemonic:
                                               a phantom key no census row can ever match
+ ('movq',     'GPR/other (unclassified)')   ← `movq %gs:0x28, %rax`; the census buckets it by
                                               kind=segment, a datum the asm TEXT cannot carry,
                                               so it joins against ordinary `movq` demand
+ ('movabsq',  'mov imm64 / movabs (P2 addition 3)')  ← not one of the census's MISS buckets at
                                               all, so `p2_roster`'s vocabulary gate goes red
```

⇒ 🔑 **A KEY DERIVED FROM A STRING IS ONLY AS GOOD AS WHAT THE STRING CARRIES**, and `kind` is not
in it. [[feedback-a-join-on-a-lossy-key]] The other six (`endbr64`, `prefetcht0`, `prefetchnta`,
`emms`, and the two `CONTROL:` rows) map to real census buckets under the census's own rule, so
their verdicts ARE availability facts this table could carry. They stay excluded **only because
they were excluded yesterday**, and the list says so in those words rather than inventing a reason:
ruling on them widens what `measured_availability` means and moves the roster, which is a batch and
not a side effect of a bucket repair.
[[feedback-a-category-is-a-hypothesis-about-its-members]]

### 4. WHAT THIS COMMIT DOES NOT DO

`measured_availability()` returns **254 keys before and 254 after** — this is a repair of the RULE,
not of the subject. `vzeroupper` now buckets as `AVX (state)` and is therefore askable, but **no
probe for it has been run**: its `hx` must come from `clang` like every other row's and its verdict
from an ACL2 pass. Until then the unasked remainder still reads 1 implemented pair / 1,241
instructions, and the census's `AVX (state)` column is unchanged.

## D144 — P2 BATCH 33: `vzeroupper` asked at last, my declaration refuted by the run, and the availability census finished without a qualifier

`vzeroupper` has been rank 1 of `p2_roster.py --unprobed` since batch 26 and was **skipped three
times on purpose** (D128 §5, D138 §3): `probe_bucket` read the ISA bucket off the OPERANDS and this
form has none, so a probe for it would run, have its verdict discarded, and leave the pair exactly
as unasked as before. D143 delegated that function to the census's own rule, which buckets it
`AVX (state)`. The key exists, so the question can be put.

### 1. THE ROW, AND THE TWO THINGS CHECKED AT THE OBJECT RATHER THAN INHERITED

`hx = c5f877`, from `clang`, agreed by **both** disassemblers (LLVM and GNU `objdump`), and
re-derived by D128's gate at every CI run — 266 forms now.

⭐ **That x86isa IMPLEMENTS it was re-checked, not taken from D138.** `inst-listing.lisp:9040`
names `x86-vzeroupper` as the VEX.128 form's semantic function *(the VEX.256 sibling `VZEROALL`
carries `NIL` in the same column)*, and the function is **defined** at
`machine/instructions/fp/non-arith.lisp:50`. A catalogue can name a function that does not exist;
this one does. [[feedback-the-oracle-is-evidence-not-the-specification]]

### 2. THE DECLARATION WAS SEALED, AND THE RUN REFUTED IT

Declared before ACL2 ran, sha256-sealed in the source with its timestamp: **`(refuses, refuses)`**.
The reasoning: the listing gives this form `(CHK-EXC :TYPE-8 (:AVX))`, and this probe's enabled arm
sets `CR4 = #x600` — OSFXSR | OSXMMEXCPT. **Bit 18, OSXSAVE, is not among them**, so AVX cannot be
enabled and the form should refuse at the very CR4 the differential runs under.

```
⛔ vzeroupper: declared (refuses, refuses), MEASURED (refuses, executes)
```

⇒ 🔑 **THE ORACLE'S CATALOGUE DECLARES AN EXCEPTION CHECK ITS EXECUTION DOES NOT PERFORM.** The
reasoning was sound about the SPEC and wrong about the MACHINE, and the seal is what made that
visible: a prediction written after the run would have been right by construction, and the
interesting half — that x86isa does not gate this form on CR4.OSXSAVE — would have gone unrecorded.

⛔ **AND THE CONSEQUENCE IS FOR WHOEVER MODELS THE FORM, not for this probe.** An x86lean
`vzeroupper` that DOES gate on `CR4.OSXSAVE` will disagree with this oracle on a machine where AVX
is off, and the differential will report that as the MODEL's disagreement. It is the oracle's.
[[feedback-two-defects-that-cancel-survive-a-green-run]]

### 3. ⛔⛔ AND A HARDER WARNING, BECAUSE "ASKABLE" IS NOT "BUILDABLE"

`vzeroupper` zeroes `YMM[255:128]` of every register. This model has no YMM registers — the
census's own `EXT_SCOPE` says `"AVX (state)": False`, and `"AVX2/AVX (ymm)": False` beside it.

⇒ **A differential vector for `vzeroupper` against a model with no upper halves would AGREE, and
the agreement would be about the absence of the state rather than about the semantics.** Every
observable the harness compares — GPRs, flags, the xmm low quadwords, memory — is untouched by the
instruction on both sides. The vector would pass, the coverage table would gain a row, and nothing
would have been tested. [[feedback-unobserved-regions-report-agreement]]
[[feedback-a-dimension-with-no-parameter-is-frozen]] The 1,241 instructions are now ASKED; they are
not now BUILDABLE, and the gap between those two words is a register file.

### 4. THE REBUILD WAS CONTROLLED, AND THAT IS THE WHOLE RECEIPT

`docs/P2-ROSTER.md` is generated and CI requires byte equality. Regenerated, the diff is **six
lines**, and every one of them moves by exactly `+1` pair and `±1,241` instructions:

```
| the oracle EXECUTES         | 140 → 141 | 161,448 → 162,689 | 39.1% → 39.4% |
| **probed so far**           | 222 → 223 | 378,610 → 379,851 | 91.8% → 92.1% |   (asked-at-bucket table)
| the oracle EXECUTES         | 128 → 129 | 133,101 → 134,342 | 32.3% → 32.6% |
| **probed so far**           | 216 → 217 | 302,978 → 304,219 | 73.4% → 73.7% |
| not asked at its own bucket |           | 109,500 → 108,259 | 26.5% → 26.2% |
```

`the oracle REFUSES` does not move at all. Nothing outside those six lines moves. That is the
controlled-rebuild rule this repository already carries for the census corpus, applied to a
generated roster: **per-column totals accounted for, and zero rows changed but the one added.**

### 5. WHERE THE CENSUS STANDS

```
THE UNASKED REMAINDER    171 pairs / 16,791 instructions      (was 172 / 18,032)
   x86isa IMPLEMENTS       0 pairs /      0
   x86isa DOES NOT       171 pairs / 16,791
   NOT RESOLVED            0 pairs /      0
```

⭐⭐ **Every pair x86isa implements has now been asked.** D138 could only reach *"every implemented
pair that CAN be asked"* — a sentence with a qualifier doing real work, hiding 1,241 instructions
behind a limitation of the probe rather than of the oracle. The qualifier is gone.

⚠️ This supersedes D143 §4's *"until then the unasked remainder still reads 1 implemented pair /
1,241"*, which was true when it was written one commit earlier.

## D145 — the identical-trees control's own number, gated at last: a BIAS can red, a LOUD BOX only scopes

D142 measured this box inventing **−2,150 ms** between two copies of one commit, on a unit with a
1,980 ms budget, and `--selftest-measure`'s arm 1 **passed**. The arm has printed that number since
the gate was built, under the words *"that is what this box invents between two copies of one
commit, and every budget has to clear it"* — and nothing has ever compared it with a budget. A
sentence saying a number matters is not a check that it does.

### 1. TWO DIFFERENT THINGS ARE DONE WITH IT, AND CONFLATING THEM IS WHY IT WAS INERT

**(a) An assertion, and it is about the CODE rather than the box.** Identical trees have a true
delta of exactly zero, so the invented delta must sit inside the run's OWN band: `|delta| > K·se`
means the run produced a difference **its own noise model cannot explain** — a systematic
difference between the two sides, which no amount of load excuses and which would ride inside every
delta the gate reports. That is box-independent, so it may red, and it does.

**(b) A scope statement, printed and not asserted.** The budgets this box's invented delta does NOT
clear today. Those units' verdicts this afternoon are worth exactly as much as the box is quiet,
and a reader of any `CLEAN` should see that list beside it. ⛔ Asserting it would red on a busy box,
which is the defect D141 took out of this same arm — the distinction between the two halves is the
whole content of this entry.

On D142's control the two land differently and correctly: `|−2,150| < ±2,474`, so **no bias** — that
run showed noise, not a broken instrument — while the scope line would have named `Tests.Coverage`
as a unit whose budget the box's own invention exceeded that afternoon.

### 2. THE ARMS, AND THE ONE THAT CAUGHT MY OWN DECLARATION

Two cases added to the stubbed judgement suite (no tree profiled):
- a **+200 ms** difference with a **±20 ms** band — far under the 1,778 ms budget, so the gate says
  CLEAN and the old arm was happy — must RED. It is the case the old arm could not see, because it
  compared only the rc.
- a **−2,000 ms** difference inside a **±5,524 ms** band — over the budget, but the box is loud, not
  biased — must PASS, printing the scope line.

⛔ **And the second case was declared `CLEAN` in its first draft.** The condition check added one
edit earlier refused it: a ±5,524 band around −2,000 straddles a 1,778 budget, so the gate returns
UNMEASURABLE. The arm was testing a branch its own name did not describe — **the exact defect the
verdict column had just been introduced to prevent, caught on the case that introduced it.**

⇒ Each case now declares BOTH the verdict it must produce AND the LINE it must print, because the
scope list and the bias message are arm 1's real output and a case that stopped producing one would
otherwise stay green on its rc alone. Four planted defects — the assertion neutered, the bias test
made unreachable, the scope list silently emptied, and the scope threshold slipped from the budget
to the band — **all four caught**, and the last two only by the line assertion.

`--selftest` is 30 arms (was 28).

## D146 — QUEUE item 4: the heartbeat proxy is REFUTED BY A PLANT, and the counter the kernel keeps about itself is the one that measures the gated quantity

QUEUE item 4 handed this seat a lead: Lean charges HEARTBEATS for the elaborator's `whnf`, a
heartbeat count is deterministic, so a `maxHeartbeats` ceiling would be the zero-variance,
machine-independent gate the millisecond ceilings could not be (D111, D122). The item recorded its
own open question honestly — *"heartbeats are charged in the ELABORATOR, the gate is on the KERNEL,
and whether the two track each other across the changes this gate exists to catch is UNMEASURED"* —
and ordered a correlation walk over the twelve commits in
`docs/kernel-delta-history-2026-09-04.jsonl`.

**The walk was run and it is reported below, but it is not what decided this.** A correlation study
is what you run on a hypothesis that has survived a refutation attempt, and the refutation was
cheaper than the walk by two orders of magnitude.

### 1. THE PREMISE IS THINNER THAN THE SENTENCE THAT CARRIED IT, IN THREE DIRECTIONS

**(a) Back-to-back, it holds.** `Tests/Coverage.lean`, rewritten so every top-level declaration
reports `IO.getNumHeartbeats` either side of its own elaboration, run twice on one tree: **103 of
103 declarations identical, module total `4,984,106` both times.** Same at the walk's first commit.

**(b) ⛔ "Any machine" is FALSE as stated, and the counter-example costs one run.** The same tree
under `lean --threads 1` reads **`4,981,523`** — every one of the 103 declarations differs, by 2 to
30 heartbeats each, for −0.052% overall. Heartbeats are deterministic *per toolchain
configuration*, not per tree. That does not hurt a Δ gate, whose two sides run in one
configuration; it does refute the portability half of the claim, which was the half the proposal
was FOR. ⇒ 🔑 *a premise inherited as one sentence usually has two halves, and the half that
motivated the work is not always the half that was measured.*

**(c) ⛔⛔ AND NOT EVEN ACROSS MACHINE STATES — WHICH MY OWN DETERMINISM ARM COULD NOT SEE.** Two
commits in the walk change **zero `.lean` files**, so their Lean input is byte-identical:

```
  320cb45 → 762da1a   Δheartbeats  +20      Δkernel-unfoldings  0     (load 42 → 95)
  a5326fd → 873a4d9   Δheartbeats   -8      Δkernel-unfoldings  0     (load 91 → 77)
```

Identical input, a heartbeat count that moves. The cause is the same parallelism §9 is about:
Lean elaborates commands on several threads, `IO.getNumHeartbeats` is a THREAD-LOCAL counter, and a
`stop − start` around `elabCommand` therefore attributes whatever the scheduler happened to do on
that thread. Under load 95 the attribution shifts.

⛔ **The arm I wrote to prove determinism ran the two measurements BACK TO BACK**, on a machine in
the same state, and passed 103/103 — the one condition under which the defect cannot appear.
⇒ 🔑 **a reproducibility arm that repeats immediately shares the blind spot it is meant to expose;
the machine state has to differ between the two readings, and the corpus's own no-op commits are a
free way to make it differ.** [[feedback-a-control-can-share-the-blind-spot]] The kernel counter
read **exactly zero on both of those pairs**, at loads from 13 to 95, which is what a deterministic
count of the kernel's own work looks like.

### 2. ⛔⛔ THE REFUTATION, PLANTED RATHER THAN INFERRED

Two modules, ninety seconds. `Data.lean` holds `bigList : List Nat`; `Check.lean` holds
`theorem scan : bigList.all (fun n => n < 1000000) = true := by decide`. **`Check.lean` is
byte-identical across the three arms; only the DATA it reduces changes.**

```
  N=2000   heartbeats  12,084     kernel `type checking`   82 ms    tactic execution  122 ms
  N=4000   heartbeats  12,084     kernel `type checking`  229 ms    tactic execution  249 ms
  N=8000   heartbeats  12,084     kernel `type checking`  460 ms    tactic execution  520 ms
```

**The heartbeat count is not approximately flat — it is the same integer three times, while the
gated quantity grows 5.6×.**

⭐ **AND THE PROBE CARRIES ITS POSITIVE CONTROL IN THE SAME RUN**, because a flat reading is exactly
what a broken instrument prints. Hold the data at N=2000 and grow the module's SOURCE instead (eight
more theorems over the same list): heartbeats **12,084 → 225,043**, an 18.6× move. The instrument
is live; it is measuring the wrong thing. [[feedback-a-probe-must-create-its-condition]]

### 3. THE MECHANISM, WHICH IS WHY THE LEAD LOOKED SO GOOD

`decide`'s evaluation of `Decidable.decide p` is **kernel** reduction, and the kernel is not charged
heartbeats — twice over: once inside the tactic and once when `addDecl` re-checks the term. What the
elaborator IS charged for is elaborating the surrounding source: the statement, the instances, the
`match` compilation. So:

> **Heartbeats measure the size of the SOURCE being elaborated. The gate measures the size of the
> DATA being reduced.** They are two different quantities that happen to grow together whenever a
> batch does both at once, which is what made the lead survive a plausibility check.

⛔ The evidence QUEUE item 4 recorded — *"a `decide` under `maxHeartbeats 1000` fails `(deterministic)
timeout at whnf` in the elaborator"* — is TRUE and is fully compatible with this refutation: what
exceeded 1,000 was the fixed elaboration cost, not the fold. A reading can be correct and still not
be evidence for the sentence it is quoted under. [[feedback-two-readings-are-not-two-witnesses]]

### 4. THE CORPUS SAYS THE SAME THING, INDEPENDENTLY

The twelve-commit walk (`scripts/deterministic_cost.py`, one deterministic pass per commit — a
deterministic instrument needs no repeats, which is the one economy the proposal really did deliver):

```
commit        heartbeats        Δhb    kernel ms   Δkernel     .lean files changed
144e9a3cf      4,792,823                   19350
4f6766b9b      4,858,743    +65,920        19650      +300     8   (Coverage.lean +15/-3)
76cb51bd0      4,887,300    +28,557        20150      +500     8
3769ea0c1      4,887,300         +0        19900      -250     0
0f929e3e5      4,887,271        -29        20500      +600     7   (13 new vectors, Coverage +2/-2)
320cb4572      4,887,285        +14        20600      +100     7   ( 2 new vectors, Coverage +2/-2)
762da1add      4,887,285         +0        20650       +50     0
a5326fd04      4,939,878    +52,593        20750      +100     7
873a4d9ea      4,939,878         +0        20750        +0     0
0f7baee50      4,959,784    +19,906        21200      +450     7
e57c99fdf      4,959,784         +0        21250       +50     0
5c0159983      4,959,784         +0        20900      -350     0
```

⛔ **Batches 17 and 18 changed seven `.lean` files each and moved the proxy by −29 and +14 out of
4.9 million.** What they added was vectors — data — and the coverage theorems' source barely moved.
Batch 14 moved it by 65,920, and what batch 14 added was fifteen lines of `Tests/Coverage.lean`.
The corpus and the plant agree, from independent origins.

### 5. ⭐⭐ FIVE ZEROS, NOT ONE — AND THE REFEREE CANNOT REFEREE

`scripts/kernel_delta_history.py`'s docstring names ONE negative control, *"`e57c99f` (D122) changes
`docs/DECISIONS.md` and nothing else"*. **There are five.** `3769ea0`, `762da1a`, `873a4d9`,
`e57c99f` and `5c01599` each change zero `.lean` files. (The budget derivation was never wrong: its
code builds a `zero_lean` SET and finds all five. Only the prose under-counted — which is the
direction nobody audits. [[feedback-under-claims-are-unpoliced]])

On all five, **Δheartbeats is exactly 0**. On the same five, the kernel instrument reads
**−250, +50, +0, +50, −350 ms** — a 400 ms span of pure invention on a unit whose budget is 1,764 ms.

⛔⛔ **AND THE STATISTIC THAT MATTERS MOST FOR ANY FUTURE PROXY WORK.** Of the eleven adjacent pairs,
the kernel reference can resolve — |Δkernel| larger than the two commits' own sweep spreads —
**two.** One of those two is `e57c99f → 5c01599`, which changed **no `.lean` file at all** and reads
−350 ms. ⇒ 🔑 **the kernel walk resolves exactly ONE real pair in eleven, and "resolves" a no-op
commit as a 350 ms improvement.** A proxy cannot be validated against a referee in that state: the
REFERENCE's noise sets a floor on how unstable any ratio to it can look, so a wide spread would have
been a fact about the referee. That is why §2's plant, which needs no referee at all, is what
decided this. [[feedback-a-normalisation-needs-its-denominator-to-vary-the-same-way]]

### 6. ⭐⭐⭐ WHAT REPLACES IT: THE COUNTER THE KERNEL KEEPS ABOUT ITSELF

Found while measuring §2's mechanism. `set_option diagnostics true` makes Lean report, per
declaration, a `[kernel] unfolded declarations` table — the KERNEL's own reduction counters. On the
same three synthetic arms:

```
  N=2000   [kernel] Bool.casesOn ↦  6,002     N=4000 ↦ 12,002     N=8000 ↦ 24,002
```

**Exactly linear in the data, to the unit.** It is deterministic, it is a count and not a time, and
it is a count of the work the gated phase actually does.

On the real module, per declaration, against the kernel milliseconds measured in the SAME run
(27 declarations over 150 ms):

```
  ms per 1,000,000 KERNEL UNFOLDINGS    min 1,627   median 4,255   max 6,590    spread  4.1x
  ms per 1,000 ELABORATOR HEARTBEATS    min  2.62   median 10.97   max 165.99   spread 63.5x
```

and a good part of the 4.1× is the millisecond column's own ±25–50% run-to-run noise, which is on
both ends of it.

**Determinism on the real module, asserted before any commit-to-commit number was believed:**
`Tests.Coverage` measured twice on one tree, **103 of 103 declarations identical, module total
`6,311,170` both times**. Of 6.31 M unfoldings, **10** are unattributed to any declaration, and the
tool prints that number rather than folding it into a total.

⭐⭐ **AND THE FULL WALK SEPARATES THE TWO PROXIES EXACTLY WHERE THE MECHANISM SAYS IT SHOULD.**
Twelve commits, both columns from ONE pass each (a deterministic instrument needs no repeats — the
one economy the proposal really did deliver: this walk is 12 passes where the millisecond gate at
`--repeats 6` is 12 profile passes for ONE commit pair):

```
commit        heartbeats      Δhb    kernel unfoldings       Δku   kernel ms   what changed
144e9a3cf      4,817,186                   6,311,170              19350
4f6766b9b      4,883,740  +66,554          6,410,419   +99,249    19650  +300  batch 14 (+15 src ln)
76cb51bd0      4,912,750  +29,010          6,485,433   +75,014    20150  +500  batch 15
3769ea0c1      4,912,750       +0          6,485,433        +0    19900  -250  NO .lean file
0f929e3e5      4,912,738      -12          6,666,666  +181,233    20500  +600  batch 17 (13 vectors)
320cb4572      4,912,752      +14          6,697,891   +31,225    20600  +100  batch 18 ( 2 vectors)
762da1add      4,912,772      +20          6,697,891        +0    20650   +50  NO .lean file
a5326fd04      4,964,997  +52,225          6,740,241   +42,350    20750  +100  batch 20
873a4d9ea      4,964,989       -8          6,740,241        +0    20750    +0  NO .lean file
0f7baee50      4,985,436  +20,447          6,799,095   +58,854    21200  +450  batch 22
e57c99fdf      4,985,436       +0          6,799,095        +0    21250   +50  NO .lean file
5c0159983      4,985,436       +0          6,799,095        +0    20900  -350  NO .lean file
```

⛔⛔ **Batch 17 added thirteen vectors. Heartbeats moved by TWELVE, downwards. The kernel's own
counter moved by 181,233 — and the millisecond reading for that same commit, +600 ms, sits INSIDE
its own ±1,000 ms band and says nothing at all.** Batch 18 is the same shape one order smaller.
Three instruments separated on one row.

**Scored over the whole walk:**

```
                              no-op commits reading    sign agreement on    ms per 1k unit
                              EXACTLY ZERO             the pairs that moved (6 live pairs)
  KERNEL unfoldings           5 of 5                   6 / 6                2.36 – 7.65   (3.2x)
  elaborator heartbeats       3 of 5  (+20, -8)        5 / 6                -50000 … +7143
```

⚠️ And the 3.2× is an UPPER bound on the kernel counter's own scatter, not a measurement of it: the
denominator resolves 2 of 11 pairs (§5), so most of that spread is the referee's noise sitting in
the ratio. Saying "3.2×" without that sentence would be quoting the referee as if it were the
subject. [[feedback-a-normalisation-needs-its-denominator-to-vary-the-same-way]]

⚠️ **WHAT IS MEASURED AND WHAT IS NOT.** Measured: exact linearity in data on a plant; determinism
on the real module; a 4.1× cross-declaration ratio spread against heartbeats' 63.5×; the six walk
rows above; a cost of ~2× elaboration wall-clock with `diagnostics true` (30 s → 62 s on
`Tests.Coverage`). **Not measured: machine independence**, which is a prediction until a second
machine reads it — the same status `ci.yml` already gives the portability of its ratio budgets —
and **no budget has been derived**, which needs the full walk as its second source and not these
rows. ⛔ Do not gate on it before that. [[feedback-widening-a-gate-needs-a-second-source]]

### 7. ⛔ TWO DEFECTS OF MY OWN, BOTH CAUGHT BY ARMS I WROTE FOR THE PURPOSE

**(a) The rewriter wrapped prose.** `Tests/Coverage.lean` carries two doc-comment lines that begin
with the word `theorem` at column 0 (*"theorem does not compile, which is how it is known to have
teeth"*, *"theorem names NEITHER"*). A regex for a declaration matched both; the wrapper landed
INSIDE the comment, where it is inert; the module still compiled; and two declarations would have
gone unmeasured in a table that looked complete. **It was caught only because `read_messages`
refuses when a wrapped name never reports** — not by a parse error, not by a count that looked
wrong. The rule a regex cannot have is now a comment-and-string scanner, with six arms including a
positive control (the same names OUTSIDE a comment must still be wrapped) and a report of what was
excluded. [[feedback-a-tool-has-no-concept-of-not-applicable]]

**(b) My own sign statistic counted silence as agreement.** `sign agreement: 8/11` — with
`(dh > 0) == (dk > 0)`, the five pairs where the proxy read EXACTLY ZERO scored three agreements,
because `False == False` whenever Δkernel happened to be ≤ 0. **The pairs that most damn the proxy
were being counted in its favour.** Over the six pairs where the proxy moved at all it is 5/6, and
only one of those six is resolvable by the referee, so the statistic was close to vacuous in both
directions. It now excludes and names the silent pairs. ⇒ 🔑 *a summary statistic must exclude the
cases where the instrument said nothing; "no reading" and "a reading that agrees" are the same
number to every naive comparison.*

### 8. THE FIVE PREDICTIONS, SEALED ON THE BUS BEFORE THE WALK REPORTED, SCORED

1. deterministic at the first commit — **RIGHT AS ASKED, AND THE QUESTION WAS TOO EASY** (103/103
   back to back). Two no-op commits later in the same walk moved the count by +20 and −8 on
   byte-identical Lean input (§1c). I sealed the prediction my own arm was shaped to confirm.
2. the no-op pair reads exactly 0 — **RIGHT, and understated**: there were five no-op pairs, all 0.
3. the ratio spans more than 3× — **RIGHT IN VERDICT, WRONG IN KIND.** I predicted an unstable
   ratio; the truth is that the proxy reads ZERO on data-only batches, so the ratio is not unstable
   but undefined. A prediction can be scored correct and still have described the wrong world.
4. fewer than half the pairs resolvable — **RIGHT, and by more than I expected**: 2 of 11, one of
   them a no-op commit.
5. sign agreement ≥ 8/11 — **RIGHT ON THE NUMBER AND THE NUMBER WAS BROKEN** (§7b). ⛔ This is the
   one to remember: I sealed a prediction against a statistic I had not audited, it came out exactly
   as predicted, and the agreement was manufactured by a defect. **A confirmed prediction is not a
   checked statistic**, and a sealed forecast protects against hindsight, not against a bad ruler.

### 9. THE THIRD ROUTE, RECORDED AND NOT YET MEASURED

The profiler's cumulative block for one `Tests.Coverage` run reads `tactic execution 47.8s` against
`type checking 26.2s`, and `user` time is 2× `real`: **Lean elaborates this file's commands in
PARALLEL, and every gated number is a per-task WALL-CLOCK reading taken while those tasks contend
with each other and with whatever else is on the box.** `scripts/kernel_cost.py` never passes
`lean -j/--threads`, so it takes the default. Pinning `--threads 1` changes how the SAME quantity is
measured rather than which quantity is gated, and it is an A/B in one interleaved session. It is not
run here and it is not claimed to work; it is the cheapest untried thing and it belongs to the next
sitting.

**Tools.** `scripts/deterministic_cost.py` (17 arms), which measures both candidate proxies in ONE
pass — they must be measured together, because `diagnostics true` adds bookkeeping the elaborator is
charged for (+25,408 heartbeats, +0.51%), so a heartbeat count taken without it cannot sit in the
same row as an unfolding count taken with it.

## D147 — the duplicate-D gate could not see four of its own subject's headings, and its printed count was the only place that showed

Found by running `scripts/check_citations.py` over this sitting's edits and reading the line it
prints on success rather than its exit code:

```
  ✔ decision numbers: 142 headings, 141 distinct
```

`docs/DECISIONS.md` has **146** headings and **145** distinct numbers.

### THE CAUSE

`check_decision_numbers` matched `^## D(\d+) ` — **with a trailing space**. Four entries put their
title on the line BELOW the heading:

```
## D38

**An absolute kernel-time ceiling on a table-driven module is a chore, not a gate …**
```

so their heading line ends at the digit and the pattern misses it. D38, D39, D40 and D41 have been
outside this gate's census since it was written.

### WHY IT MATTERS MORE THAN FOUR ROWS

The function exists to do ONE thing: refuse when two sections claim one decision number, because
*"a number that names two decisions is a citation that resolves to whichever the reader finds
first"*. For those four numbers it could not have refused. A second `## D38` would have passed
silently, and the `✔` line would have said `141 distinct` with the same confidence it says it now.
⇒ 🔑 **a gate that cannot see part of its subject reports agreement about the part it can see, and
its own printed denominator is the only place the gap is visible** — which is exactly why the count
is printed, and exactly why nobody had read it against the file.
[[feedback-unobserved-regions-report-agreement]]

### THE REPAIR, AND WHY IT IS TWO CHANGES AND NOT ONE

**(a)** The pattern accepts both shapes: `^## D(\d+)(?=\s|$)`.

**(b)** ⭐⭐ And the gate now REFUSES when any line beginning `## D<digits>` is not matched by that
pattern, naming the lines it could not read. Fixing only (a) would repair today's four and leave the
NEXT heading shape to drop out of the census in the same silence. A pattern is a claim about a file
that changes; the refusal is what makes a mismatch loud. [[feedback-a-declared-list-inherits-its-default]]

**(c)** ⛔⛔ **AND THE FIRST REPAIR BROKE ON THIS ENTRY, WHICH IS THE HALF WORTH READING.** The
paragraph above documents the bare shape by SHOWING it, inside a fence. The widened pattern read
that quotation as a second claimant and the gate refused — *a gate that fails whenever the file
explains the gate*. The census now skips fenced blocks. ⇒ 🔑 **widening a pattern moves the error
from false-negative to false-positive; both directions have to be armed, and the input that finds
the second one is the documentation of the first.** [[feedback-measure-a-gates-error-rates]]

⚠️ And skipping fences opens its own hole — an UNTERMINATED fence would swallow every heading after
it, in exactly the silence this entry is about, one layer down. An odd number of fence lines is
therefore itself a refusal.

Six red arms, all planted **in a copy of the shipped file** rather than a fixture: a duplicate of an
ordinary number; a third `D123` (the frozen exemption is exact, not a tolerance); a duplicate in the
BARE heading shape; a `## D9999:` heading in a shape the pattern does not know; a heading quoted
inside a fence, which must NOT count — **with its control beside it**, the identical heading outside
a fence, which must still be caught, or the fence rule has merely switched the census off; and an
unterminated fence. The bare arm SKIPS with a warning if the shipped file ever stops using that
shape, so it cannot pass by having no subject.

`check_citations.py` now reads `147 headings, 146 distinct`.

## D148 — the corpus never supported the kernel-unfolding proxy the way the table said: a sign statistic a null model matches, and a referee that was a SECOND rule looser than the gate it refereed

D146 refuted the heartbeat proxy with a plant and named the kernel's own `[kernel] unfolded
declarations` counters as the live candidate. Its evidence came in four parts, and the entry was
careful about two of them — *"NOT measured: machine independence, and no budget has been derived"*.
This entry is about the other two, which were presented as corroboration and are not.

⚠️ **Nothing here revives heartbeats and nothing here convicts the kernel counter.** Two of D146's
four legs stand exactly as measured. What falls is the CORPUS leg, which is the one a reader would
have quoted as "and it tracks the real thing on twelve real commits".

### 1. THE SIGN STATISTIC IS MATCHED BY A NULL MODEL, SO IT CARRIES NO EVIDENCE

The walk reported **sign agreement 6/6** over the pairs where the proxy moved, against heartbeats'
5/6, and D143's law was already applied to it: pairs where the proxy read exactly zero are excluded,
because scoring silence as agreement is how an 8/11 was manufactured once already.

⛔ **AND THE COMPARISON ROW BORROWED THE OTHER ROW'S DENOMINATOR.** The table's header says
"6 live pairs" for BOTH metrics. Heartbeats move on **eight** of the eleven pairs, not six; scored
on its own live set the heartbeat row reads **7/8**, not 5/6. The 5/6 is heartbeats scored over the
KERNEL COUNTER's live pairs — a real quantity, but not the one the row's header names, and the two
rows are then not comparable in the column that invites comparison. Re-run
`--metric hb` and the tool now prints 7/8 with its own denominator.
[[feedback-a-borrowed-denominator-invents-its-own-gap]]

⚠️ It changes no conclusion, and that is the point worth keeping: **both rows fail the null model
anyway**, by different routes. The kernel counter is one-sided, so the tool refuses the statistic
outright; heartbeats ARE two-sided and still only match what a constant scores (7/8 either way), so
the tool's second branch fires. A gate that can only speak one way would have caught one of them.

That exclusion was right and it was not enough. **Δproxy is positive on every one of the six live
pairs** — a corpus of batches that only ever add rows has no negative to offer — so the statistic is
`sum(Δkernel > 0)` wearing the proxy's name:

```
  sign agreement over the 6 pairs where the proxy MOVED:  6/6
  NULL MODEL — the best CONSTANT-SIGN proxy scores        6/6   on the same pairs
```

A proxy that printed `+1` unconditionally scores the same 6/6. ⇒ 🔑 **A STATISTIC A NULL MODEL
MATCHES IS NOT A MEASUREMENT OF THE SUBJECT; IT IS A DESCRIPTION OF THE REFERENCE COLUMN.** The
walk now computes and prints the null model's score beside the proxy's, and says out loud when the
proxy moved in one direction only. [[feedback-a-claim-the-vectors-cannot-distinguish]]
[[feedback-refute-a-proxy-with-a-plant]]

### 2. ⛔⛔ THE REFEREE WAS A SECOND RULE, AND IT DISAGREED WITH THE GATE IN THE FLATTERING DIRECTION

The walk decided which pairs its kernel reference could resolve with a rule it invented:
`|Δkernel| > the two commits' summed sweep RANGES`. The repository already merges on a different
one — `kernel_delta.verdict`'s band, `K_SIGMA` standard errors of the difference of medians, chosen
in D141 on measured error rates. Two rules, one subject.

They disagree, and the corpus contains the pair that shows how:

```
  pair                     Δkernel  band K*se  range b+h   range rule   gate's band
  873a4d9ea→0f7baee50         +450        280        300          yes           yes   real change
  e57c99fdf→5c0159983         -350        376        300          yes            NO   NO .lean changed
```

⛔ **The second pair changes `docs/DECISIONS.md`, `docs/P2-ROSTER.md` and
`scripts/oracle_availability.py` — NOT ONE `.lean` FILE.** Its Lean input is byte-identical, so its
true Δkernel is ZERO, and the walk's own rule called it *resolved*. **A measured false positive, on
the one class of pair in this corpus whose truth is known.** The gate's band declines it (376 > 350)
and keeps the real pair, so the repair costs no resolution the corpus had.

⛔⛔ **AND THE MECHANISM IS THE PROFILER'S OWN ROUNDING, WHICH MAKES THIS NOT A ONE-OFF.** The
summed-range rule is not uniformly looser — on nine of the eleven pairs its threshold is HIGHER than
the band's (1200 vs 1078, 1000 vs 886, …), so it is usually the *stricter* rule. It becomes looser
in exactly one circumstance: **a side whose repeated readings happen to be EQUAL contributes zero
range, and the rule reads that as a noiseless side.** Here `5c01599`'s two sweeps both read
`20900.0`. Lean's profiler prints three significant figures, so a module at ~21 s is quantized to
100 ms — D146 §9 wrote that quantum down as a thing to watch, and this is it biting: two readings
agreeing to the printed digit is common, and it is not evidence of a quiet box. The band's `se`
takes the OTHER side's variance and the median factor and survives it.
⇒ 🔑 *a noise estimate that can reach exactly zero will reach it by rounding, and every rule built
on it inherits a confident verdict at that moment.*

⇒ 🔑 **A SECOND RULE INVENTED BESIDE A SHIPPED ONE DOES NOT MERELY DUPLICATE IT — IT DISAGREES, AND
THE DISAGREEMENT LANDS WHERE NOBODY IS LOOKING.** D143 caught this shape in `probe_bucket`, where
the second rule agreed on 256 of 256 rows and the danger was future divergence. Here the divergence
had already happened and was manufacturing evidence on the day it was written.
[[feedback-a-duplicate-born-in-agreement]]

**The repair is delegation, not correction.** `scripts/kernel_delta.py`'s `sys.exit(main())` is now
guarded by `if __name__ == "__main__":` — behaviour under `python3 scripts/kernel_delta.py` is
unchanged — and `deterministic_cost.resolves()` calls the gate's own `resolution()` and reads
`K_SIGMA` off the imported module at CALL time. The arm that proves it is delegation and not
agreement STUBS `kernel_delta.resolution` and requires the walk's answer to move; a second arm
drives the exact shape of the removed defect (a pair the summed-range rule resolves and the band
declines); a third requires a side with fewer than two readings to be REFUSED rather than resolved.

### 3. WHAT THE CORPUS ACTUALLY SAYS, ON THE GATE'S OWN RULE

```
                                       old rule      gate's band
  pairs the kernel reference resolves      2/11             1/11
  no-op pairs falsely called resolved       1/5              0/5
  live pairs (Δproxy ≠ 0) that it resolves  1/6              1/6
```

⇒ **The `ms per 1k proxy units` calibration rests on ONE pair.** The printed range `2.36 – 7.65`
(spread 3.2×) is computed over pairs the referee cannot resolve at all; over the resolved set it is
the single value **7.65**. QUEUE item 4b already said "an UPPER bound polluted by a referee that
resolves 2 of 11 pairs" — the caveat was attached to that column and to no other, and the sign
column beside it was read as independent corroboration. ⇒ 🔑 *a caveat attached to one column of a
table is read as not applying to the others.* [[feedback-under-claims-are-unpoliced]]

### 4. WHAT SURVIVES, STATED SO IT IS NOT LOST IN THE CORRECTION

- **Exact linearity on a plant**: `Bool.casesOn ↦ 6,002 / 12,002 / 24,002` at N = 2000/4000/8000
  with the checked module byte-identical. This is a measurement of the proxy against a change whose
  truth is KNOWN, which is precisely what the corpus cannot offer.
- **Five no-op commits at exactly zero**, at machine loads from 13 to 95 — the instrument's own zero,
  taken across differing machine states rather than back to back (D146 §1(c)'s lesson).
- Both are stronger evidence than any correlation over eleven pairs a referee resolves once.

### 5. WHAT IS STILL NOT MEASURED

- **The referee's false-NEGATIVE rate.** No pair in this corpus has a known NON-zero truth, so the
  band rule is measured in one direction only, and the walk now prints that limitation rather than
  leaving a one-sided error rate to read as an error rate. [[feedback-measure-a-gates-error-rates]]
- **Machine independence** of the kernel counter — unchanged from D146, a prediction until a second
  machine reads it.
- **A budget.** Unchanged and now more so: a calibration resting on one resolved pair is not a
  second source. Do not gate on it. [[feedback-widening-a-gate-needs-a-second-source]]

## D149 — a dead session's orphan is a term in every wall-clock gate this repository owns

At 19:29 this seat found `scripts/ci_local.py --job build` running with **ppid 1**, forty-seven
minutes old, with a live child (`oracle_availability.py --check-encodings`). It was started at
**18:42:25** — the same minute as the previous head's last file write — and it outlived the session
that launched it. Attributed by `lsof` cwd (`/Users/jyh/projects/claude/x86lean`), not by command
name, and killed BY PID. [[feedback-enumerate-is-not-attribute]]
[[feedback-a-process-filter-matches-its-own-waiter]]

**Why this is a measurement entry and not housekeeping.** This repository's merge gate is the CHANGE
in kernel `type checking` WALL-CLOCK time. D142 measured the same tree reading 27,600 and 25,500 ms
on two afternoons with no code between them and attributed the difference to "the box". Tonight a
piece of "the box" had a pid, a cwd and an owner — and **every instrument this seat has was blind to
it**, because the conditions line records LOAD. A load average says something is running; it never
says what, or whose, or that it is this seat's own work from an hour ago.

⇒ 🔑 **A GATE WHOSE READING IS WALL-CLOCK IS ROBBED BY WHATEVER SHARES ITS BOX, AND THE LIKELIEST
THIEF IS THE SEAT'S OWN PREDECESSOR.** A relight kills the session, not the processes.

⚠️ **And a banked timing died with it.** The bank says `ci_local --job build` is 2-4 minutes. Step 6
of 27 alone ran 47 minutes on the orphan and had not finished in 10 on this seat's own run, while
the 1-minute load went 39 → 52 → 282 on other seats' builds and `top` read **0.0% idle with 55-64%
in SYSTEM time**. The banked figure was taken on a quiet box and carries no record of that.
[[feedback-a-measurement-without-its-conditions]]

⛔ **A load average is the wrong conditions metric on this box, and this is the second time tonight
it misled.** At load 282 the actual CPU was ~44% user / ~55% sys with one `lean` at 160% — the
number is dominated by runnable short-lived processes, not by compute. Any future conditions line
that wants to mean something should carry **idle %** beside the load.

## D150 — QUEUE item 4c measured: `--threads 1` is not the repair, and the same passes were already carrying a per-unit quantity 14.6× tighter than the one the gate reads

Five predictions were SEALED on the bus at 19:3x with their scoring rule, before any reading, and
the run's readings are committed at `docs/threads-ab-2026-09-05.jsonl` so this entry can be
re-judged in seconds (`threads_ab.py --analyse FILE`) rather than re-measured on another afternoon
— D146 §8's scar, paid once already. Five rounds, arms `default` and `lean --threads 1`, alternated
A,B / B,A, four gated units and a two-size plant in every round, 60 readings.

**CONDITIONS, because this entry is about conditions**: 1-minute load 16.6 – 62.3 (median 27.9),
CPU idle **0.0 – 48.4%** (median 19.8), recorded per reading. The box was shared with other seats'
builds throughout. Every control passed in both arms and for all three fields (below), so the
variance figures are about the instrument and not about an instrument that stopped responding.

### 1. ⛔⛔ THE READING THAT MATTERS MORE THAN THE ARMS

Five `default` profiles of **the same tree**, `Tests.Coverage`:

```
  round        type checking     user CPU      load(before→after)   idle before
    0             51,400 ms       56.99 s        46.5 → 59.0           40.1%
    1             42,700 ms       58.05 s        42.9 → 44.8            0.6%
    2             28,900 ms       55.98 s        37.9 → 29.3           20.2%
    3             31,000 ms       56.69 s        16.6 → 24.8           24.9%
    4             42,700 ms       57.24 s        22.2 → 28.4            0.8%

  range / median      52.7%                3.6%
```

⇒ 🔑 **THE GATED NUMBER'S SPREAD ON ONE TREE WAS 22,500 ms AGAINST A 1,764 ms BUDGET — 12.8× the
allowance the gate is policing** — while the child's total CPU time for the same passes moved 2.07 s
on a 57 s median. D142 established this problem at 2,100 ms across two afternoons; an evening on a
shared box makes it an order of magnitude worse, and the two quantities were being produced by the
same `lean` invocations the whole time.

### 2. THE SEAL, SCORED ON WHAT IT NAMED

| | prediction | measured | verdict |
|---|---|---|---|
|P1| default u/r > 1.4, falling to < 1.15 under `--threads 1` | **1.17** → 0.77 | ⛔ **REFUTED** |
|P2| median `real` under `--threads 1` ≥ 1.3× | 1.62 paired / 1.39 arm-median | ✅ confirmed |
|P3| median `type checking` ratio B/A < 0.95 | 0.93 paired / 0.76 arm-median | ✅ confirmed |
|P4| CV of `type checking` under `--threads 1` < 0.5× default | **0.73** | ⛔ **REFUTED** |
|P5| `user` CPU quieter than the gated number in BOTH arms | **12 of 12** | ✅ confirmed |

⛔ **P1 IS THE INTERESTING FAILURE, AND IT REFUTES THE ROUTE'S PREMISE AS INHERITED.** QUEUE item 4c
carried *"`user` is 2× `real`, so Lean elaborates this file in PARALLEL"*. Per reading the default
arm's u/r was **1.01, 1.17, 1.66, 1.50, 1.17** — it reaches 1.66 only when the box has cores free
and falls to 1.01 when it does not. ⇒ 🔑 *"user is 2× real" is not a property of Lean; it is a
property of Lean plus idle cores, and it was quoted as a property of the code.* A premise measured
once on a quiet box became a standing sentence about the compiler.
[[feedback-a-single-reading-is-about-its-run]]

⛔ **P4 IS SCORED ON THE STATISTIC IT NAMED, NOT ON THE ONE THAT WOULD PASS.** The seal said CV, and
CV gives 17.24 / 23.66 = **0.73**, short of the 0.5 it claimed. The drift-robust estimator this run
also prints — each arm's median |consecutive-round difference| as a share of its own median — gives
**6.90 / 23.89 = 0.29**, which would clear the threshold, and on a box whose load moved 16.6 → 62.3
that estimator is the more trustworthy of the two. **Both numbers are reported and the seal is
scored on the one it wrote down.** Choosing the estimator after seeing the data is how a prediction
becomes right by construction, which is the defect D144 caught in this seat two entries ago.

### 3. ⭐⭐⭐ WHAT REPLACES THE ROUTE: THE QUANTITY THAT WAS ALREADY IN THE PASS

`kernel_cost.py` runs **one `lean` process per module**, so `getrusage(RUSAGE_CHILDREN)` already
yields a **per-unit** CPU time at zero extra cost. Against the profiler's `type checking`:

```
  CV% over 5 readings          type checking      user CPU     ratio
  Tests.Coverage   default          23.66            1.33       0.06
  Tests.Coverage   threads=1        17.24            3.12       0.18
  X86.Basic        default          18.44            6.38       0.35
  X86.Basic        threads=1        65.07            7.92       0.12
  X86.Semantics    default          79.10            6.58       0.08
  X86.Value        threads=1        46.11            5.64       0.12
```

Twelve of twelve subject×arm pairs, and the plant control passes for `user` in both arms (a 4× plant
reads 3.59× and 3.49× bigger), so this is not the quiet of an instrument that stopped listening.

⚠️ **AND THE THREE THINGS THIS DOES NOT SETTLE, BEFORE ANYONE GATES ON IT.**
1. **It changes WHAT is gated, not how it is measured** — the opposite of `--threads 1`'s one virtue.
   `user` is the whole module's CPU (elaboration *and* kernel); the gate today is the kernel phase
   alone. Every budget in `kernel_ceilings.txt` and `kernel_delta_budget.txt` would need
   re-derivation **from a second source**, never from these readings.
   [[feedback-widening-a-gate-needs-a-second-source]]
2. **It is quieter, not deterministic.** 3.6% is not 0%. The kernel-unfolding counter (D146, D148)
   remains the only candidate that reads *exactly* zero on a no-op; its problem is the opposite one
   — no budget and no second machine.
3. **Machine independence is unmeasured**, exactly as for every other candidate.

### 4. WHAT `--threads 1` ACTUALLY BOUGHT, SO THE ROUTE IS CLOSED WITH A NUMBER

The gated level falls to **0.76×** and the spread from CV 23.7% to 17.2%, for **1.62× the wall
time**. That is a real effect in the predicted direction and it does not solve the problem: a gate
whose instrument still swings 17% cannot police a 7% budget. ⇒ **Route 4c is measured and closed.**
Its residue is the finding in §1 and the candidate in §3, both of which came out of the same run.

### 5. TWO SMALLER THINGS THE RUN TAUGHT, BOTH ABOUT INSTRUMENTS

- ⛔ **A FAILED ELABORATION STILL PRINTS A CUMULATIVE BLOCK.** The plant's first version omitted
  `set_option maxRecDepth`; Lean aborted with *"maximum recursion depth has been reached"* and the
  profiler **still printed `type checking 0.227ms`**. A parse that looked only for that line would
  have filed a failed run as a very fast one. `profile()` refuses on a non-zero exit, which is the
  only reason this surfaced as an error instead of as a very quiet control.
  ⇒ *the presence of a profiler block is not evidence that the module was checked.*
- ⚠️ **A CONDITIONS SAMPLE TAKEN BEFORE A 56-SECOND MEASUREMENT DESCRIBES A DIFFERENT MINUTE.**
  Round 0 began at 40.1% idle and ended with the box at 0.0%; its reading is the highest of the
  five. `load_before`/`load_after` bracket the run, `idle` does not yet. For a unit this long the
  conditions must be sampled during, or at both ends.
  ⚠️ Correlations from this run are readings, not the argument: over n=5, `corr(type checking,
  mean load) = 0.70` and `corr(user CPU, mean load) = 0.32`. n=5 supports neither on its own; they
  are recorded because they point the same way as the mechanism and the CV table, which do.

## D151 — QUEUE items 7 and 8 discharged, item 4d's instrument built, and its deciding statistic refuted by the control that was built beside it

The sitting's commissioned item was 4d: price the child's `user` CPU as the gated quantity in place
of the profiler's cumulative `type checking`, which D150 measured swinging 22,500 ms on ONE
unchanged tree against a 1,764 ms budget. What 4d owed before it could gate: a SECOND SOURCE for its
budgets — never `docs/threads-ab-2026-09-05.jsonl`, the corpus that nominated it — and a second
machine for the portability claim every candidate here still owes.

**CONDITIONS, because this entry is largely about conditions.** Every reading tonight was taken on a
box shared with the math seat's salt builds: 1-minute load 10 → 98, CPU idle 0.0 → 66%. That is
recorded per reading now rather than remembered, and the corpus is named `…-CONTENDED-…` rather than
labelled by hand.

### 1. WHAT LANDED, AND WHAT DELIBERATELY DID NOT

`kernel_cost.py`'s `profile_module()` records the child's `user`/`sys`/`real` from
`getrusage(RUSAGE_CHILDREN)` around the ONE `lean` invocation per module, so the CPU figure belongs
to exactly the pass whose milliseconds sit beside it. It costs nothing: D150's point was that the
quantity was in every pass already.

⛔ **RECORDING IS NOT GATING, and that restraint is the item.** `scripts/user_cost_budget.py` scores
the candidate and gates nothing. Item 4d is not discharged by this entry.

Items **7** (idle % in the conditions, sampled BEFORE and AFTER the pass — D150 measured one sample
describing a different minute) and **8** (the orphan pre-flight, attributing by cwd and never by
command name) are DISCHARGED.

### 2. ⛔⛔ THE DECIDING STATISTIC HAD A PREMISE, AND THE CONTROL BESIDE IT REFUTED THE PREMISE

"14.6× tighter" cannot decide a gate. `user` charges Lean's startup, import loading and elaboration
as well as the kernel, so on `Tests.Coverage` it is a ~57,000 ms number where the gated one is
~25,000 ms, and on a small module it is nearly all constant. **A constant addend shrinks the
relative noise and shrinks the relative SIGNAL by the very same factor**, so a candidate can read
twice as quiet and catch nothing extra. The comparison was therefore re-cast as MINIMUM DETECTABLE
REGRESSION — `budget% × level`, in milliseconds, lower is better.

MDR carried its own assumption, and it was written into the code as "doing work": that X ms of extra
kernel work adds about X ms to the child's CPU time, so the two arms' milliseconds are the same
scale. **The first run that printed both columns measured `Δuser/Δms` at 8.3, not 1.0.** A real
change moves the child's CPU several times the milliseconds it moves `type checking`, because it
moves elaboration too.

⇒ a candidate whose budget is 3× larger but which hears the signal 8× louder is MORE sensitive, and
the uncorrected table said the opposite in **16 of 23 rows**. The deciding column is now
`MDR / transfer`, and the raw column is kept beside it because the correction is an estimate with
real spread (interquartile 2.0–13.7).

```
  contended corpus, 14 readings      raw:        better  1 · WORSE 16
                                     corrected:  better  1 · WORSE  2 · UNDECIDED 14 · inexpressible 6
```
⇒ **the contended corpus cannot decide item 4d**: 106 of 114 pairs sit below the ms noise floor, so
most units have no measurable transfer ratio at all. That is the honest verdict, and saying it is
the point. [[feedback-audit-the-premise-of-a-right-decision]] [[feedback-the-burden-is-on-the-departure]]

### 3. ⛔ FOUR OF THE TWENTY-THREE GATED UNITS CANNOT BE EXPRESSED BY THE CANDIDATE, EVER

`getrusage` accounts per PROCESS; `kernel_cost.py` profiles one process per MODULE; so there is no
per-DECLARATION CPU time to be had. `Tests.Coverage @decl memDestSweep`,
`@decl pre_states_have_a_returnable_frame`, `@decl vectorCoverage` and `@residue` are outside the
candidate's reach and no re-run of any walk will supply them. A hybrid gate leaves the three tightest
per-declaration budgets on the noisy instrument. This is structural, not a gap in the corpus, and the
report NAMES the rows rather than omitting them — a table that dropped them would report agreement
about units nobody measured. [[feedback-unobserved-regions-report-agreement]]

### 4. ⭐⭐ A FINDING ABOUT THE GATE THAT NEEDS NO CANDIDATE AT ALL

The same tool, over the same twelve commits, on the same box:

```
  docs/kernel-delta-history-2026-09-04.jsonl   median within-commit spread   3.51%   (n=252)
  the 09/05 re-walk                                                        25.63%   (n= 42)
                                                                            7.30×
```
The 09/04 corpus is the one `scripts/kernel_delta_budget.txt` is DERIVED from. ⇒ **the budgets this
repository merges on rest on a quieter afternoon than an ordinary one.** ⛔ And that is not a licence
to widen them: re-deriving from the noisier corpus would be deriving the allowance from a measurement
of contention. Two days are not a distribution over days. Filed as QUEUE item 9.
[[feedback-a-single-reading-is-about-its-run]]

### 5. ⚠️ THE SEALED PREDICTIONS, AND WHY A GOOD SCORE HERE WOULD NOT BE A CONFIRMATION

Five predictions were sealed on the bus at 20:2x, each naming the printed statistic it would be
scored on, before the corpus landed. On the contended corpus and the RAW statistic they score 5/5.
**That score is not evidence, and recording why is more useful than the score.** Three of the five
(P1, P2, P3) are scored on MDR or on the relative/absolute split — and MDR's premise was refuted, by
a control in the same run, after the seal was written. A prediction confirmed by a statistic whose
premise the same run overturns is [[feedback-a-confirmed-prediction-is-not-a-checked-statistic]] in
its purest form: D148 sealed 8/11 and got 8/11 off a rule that scored SILENCE as agreement. The seal
is scored properly against the quiet corpus, on the CORRECTED statistic, and the score is reported
with that caveat attached.

### 6. THE HARNESS LESSONS, WHICH COST MORE OF THE EVENING THAN THE MEASUREMENT

- ⛔⛔ **TWO PLANT PROBES REPORTED EVERY DEFECT CAUGHT WHILE THEIR HARNESS WAS BROKEN.** A mutated
  copy in a temp directory could not import its siblings; the rebuilt one was not a git repo, so
  `git rev-parse` returned empty and the same arm died first on every run. The unplanted CONTROL
  failed in both, and it is the only thing that distinguished a caught defect from an ImportError
  wearing a finding's clothes. The tell on the second was sharper than the first: **every plant
  reported caught by the SAME arm.** Fixed by running the control FIRST and after every restore, and
  by printing which arm caught each plant and counting the DISTINCT arms.
  Final: 10 planted, 10 caught, 7 distinct arms. [[feedback-a-plant-probes-control-comes-first]]
- ⛔ **A NEGATIVE ARM PASSES VACUOUSLY WHEN ITS SUBJECT NEVER EXISTED.** Testing the contention
  stamp, the fake build was `/bin/sleep` copied to a file named `lean` — and macOS KILLS a copied
  platform binary on exec, because the copy has lost its code signature. The positive arm went red
  and I looked; the held-out arm ("the same binary inside the repo is NOT counted") went GREEN and
  would have forever, because "not counted" is also what you get when there is nothing to count.
- ⛔ **THREE STATISTICS WERE SILENT WHEN FIRST PLANTED** and each has an arm now: the exact-zero
  tie count (which guards a bias that flatters the shipped arm, i.e. my own sealed answer), the
  live/no-op split, and the transfer correction itself. ⚠️ The live/no-op arm was silent even after
  it was written, because it planted its outlier on a LIVE pair; collapsing the split only shows
  when the NO-OP pair carries the biggest move — which is the real corpus's own situation.
- ⛔ **A FIXTURE BUILT ON REAL COMMITS INHERITS THEIR REAL DIFF STRUCTURE.** The MDR fixtures plant a
  spike at pair 3→4 rather than 2→3 because `76cb51b..3769ea0` changes no `.lean` file, so the whole
  planted signal was scored as CONTROL noise and discarded as a no-op — the fixture then read
  UNDECIDED for a reason that had nothing to do with the code under test.
- ⛔ **AND THE FIRST DRAFT OF THIS WORK'S COMMIT MESSAGE CLAIMED A FIX THAT WAS NEVER MADE.** The
  repeatability header said "the median over the twelve trees" on a corpus with two; I described the
  defect in prose and never edited the line. Caught only by re-grepping my own message's claims
  against the tree. ⇒ **verify a commit message's factual claims the way a gate would, not the way
  an author remembers.** [[feedback-a-citation-is-an-ungated-claim]]

### 7. ⛔ A GUARD FIVE SCRIPTS WERE MISSING, AND WHY IT IS A SIBLING FAILURE

`import kernel_cost` RAN THE WHOLE GATE — a two-minute profiling pass, then `sys.exit` — which is how
this was found, from a probe that appeared to hang. D148 had given `kernel_delta.py` that exact guard
for that exact reason and swept nothing; five more scripts were unguarded (`ci_local`,
`deterministic_cost`, `kernel_delta_history`, `census_redprobe`, `check_readme_lean`). All eight are
now verified importable. ⇒ when a defect's repair is a one-line idiom, the sweep is a grep for that
idiom's ABSENCE across the repo, and it costs a minute.
[[feedback-naming-a-defect-is-not-finding-its-siblings]]

### 8. ONE RULE, TWO QUANTITIES

`kernel_delta_history.budget_info()` is extracted from `register_budget` so the candidate cannot be
scored by a rule invented beside the shipped one — D148 §2 recorded what that costs: a referee looser
than the gate it refereed, disagreeing in the flattering direction. Proof the extraction did not move
the rule: `kernel_delta_budget.txt` regenerates BYTE-IDENTICAL from the committed 09/04 corpus, and
that check is now a CI step, because the file's own header said "DO NOT EDIT BY HAND: every number
below is derived" and nothing checked it. ⚠️ The step proves the FILE IS THE SCRIPT'S OUTPUT. It
proves nothing about the rule being right, and it says so.
[[feedback-a-derivation-gate-wraps-a-false-sentence]]

### 9. THE FLEET INCIDENT, AND THE ONE THING IN IT THAT IS MINE TO CARRY

The walk collided with the crown's campaign on a shared box. The helm ruled by precedence, then
AMENDED its own ruling ninety minutes later on math's better discriminator — *the party whose numbers
contention merely SLOWS yields to the party whose numbers contention INVALIDATES, regardless of
precedence*. Mine to carry: I stopped the walk at 14 of 24 and **the stop produced an orphaned `lean`
holding a deleted worktree** — the exact class QUEUE item 8 names, forty minutes after I shipped the
check that detects it. Caught by running my own pre-flight on myself, attributed by cwd, killed by
pid. ⇒ **the pre-flight runs before a run, and stopping a job is where orphans are MADE.** A
post-flight is QUEUE item 10.

The helm's general rule is now enforced by the tool rather than by whoever writes the receipt:
`conditions()` counts `lean`/`lake` processes whose cwd is OUTSIDE this repository and sets
`contended`. ⚠️ The command name says WHAT the work is; the CWD says WHOSE. That is the reverse of
`repo_orphans`, which must never match on command name because it feeds a decision about KILLING —
the orphan found at this seat's last exit had a command line identical to its own armed bus watch.

### 10. WHAT REMAINS

- The quiet re-walk, which is what actually decides 4d, and the seal scored against it on the
  corrected statistic.
- **Portability, for every candidate this queue item has considered.** One box, arm64. `ci.yml`
  already records the same tree reading 1.7×–3.1× slower on a runner DEPENDING ON THE MODULE, which
  is precisely the shape that breaks a percentage. The report prints this as an unmeasured debt
  rather than a caveat in prose.

## D152 — QUEUE item 4d answered: do not adopt `user` CPU, its motivating number does not reproduce, and the corpus cannot decide the question the item was really asking

D151 built the instrument and refuted the deciding statistic's premise. This entry is the
measurement it was built for: the twelve-commit walk re-run with the CPU fields recorded, 24
readings, 12 trees with repeats, the same commits `scripts/kernel_delta_budget.txt` is derived from.

**CONDITIONS**: loads 9–15, CPU idle 30–65%, the math seat's two salt builds present throughout and
STAMPED `contended` by the tool rather than remembered — the helm's rule of 09/05, as code.

### 1. ⛔⛔ THE VERDICT: DO NOT ADOPT `user` CPU

```
                       ms rel%   user rel%   rel×      ms abs   user abs   abs×
  Tests.Coverage          2.69        2.05   1.31       600ms     1159ms   0.52
  X86.Theorems            3.44        3.02   1.14        32ms      152ms   0.21
  X86.Syntax              5.52        5.01   1.10        13ms      149ms   0.09
  Tests.Anchors           3.87        5.00   0.77        20ms      120ms   0.17
  Tests.Nonvacuity        2.59        4.53   0.57         4ms       34ms   0.10
  median, all units       4.82        3.41   1.41         2ms       16ms   0.14
```

**D150's 14.6× does not reproduce — not even on `Tests.Coverage`, the one unit it was measured on**,
where the twelve-tree corpus reads **1.31×**. The candidate is worse in ABSOLUTE terms on every unit
and worse in RELATIVE terms on two. D150's five profiles were taken on an evening when the shipped
arm swung 52.7% on one tree; tonight it swings 2.69% on that same tree.
⇒ 🔑 **a ratio between two instruments is a reading of the WORSE one's night.** My own card said the
spread is a single reading too; it applies to the headline number of the entry that proposed this
work. [[feedback-a-single-reading-is-about-its-run]]

⛔ **AND THE CONTROL KILLS THE MECHANISM.** `real_s` — the same child's wall clock — is as tight as
`user_s` (2.57% vs 2.05% on `Tests.Coverage`; 16 ms vs 16 ms median absolute). Whatever small
advantage exists comes from measuring the WHOLE PROCESS rather than trusting the profiler's internal
attribution, NOT from CPU accounting being robust to contention. Sealed as P5 in the opposite
direction, and refuted.

Add the structural limit — **4 of 23 gated units can never be expressed** by a per-process
measurement, including the three tightest per-declaration budgets — and the case closes. A 1.3×
relative gain, negative in absolute terms, on 19 of 23 units, is not worth re-deriving every budget
in the repository from a second source.

### 2. ⭐⭐⭐ THE FINDING THAT OUTLIVES THE CANDIDATE: THE SIGNAL AND THE NOISE ARE THE SAME SIZE

```
  pairs clearing the noise floor:   floor = MAX same-tree spread (used)    0 of 102
                                    floor = MEDIAN                        49 of 102
                                    floor = MIN                           99 of 102
```
`Tests.Coverage`'s largest real batch delta in this history is **1,700 ms** against a same-tree
spread of **600 ms (median) to 2,600 ms (worst)**. ⇒ whether a batch is "resolvable" is decided by
which noise statistic one picks, not by the readings.

That is the honest answer to what item 4 was really asking, and it is about the SHIPPED instrument,
not the candidate: **the gate is trying to resolve changes the same size as its own noise.** No
choice of quantity among those measured fixes that — heartbeats are blind (D146), `--threads 1`
leaves 17% (D150), `user` is 1.3× (here). The kernel-unfolding counter (4b) remains the only
candidate that reads exactly zero on a no-op, and it is the only one not yet refuted.

⛔ The floor was NOT loosened to produce an answer. UNDECIDED is the output; the sensitivity is
printed beside it, because a verdict without it is a choice wearing a measurement's clothes.

### 3. THE SEAL, SCORED ON WHAT IT NAMED

| | prediction (sealed 20:2x, before any reading) | measured | verdict |
|---|---|---|---|
|P1| relative tightening ≥ 2.00× | **1.41×** | ⛔ **REFUTED** |
|P2| absolute tightening < relative | 0.14× vs 1.41× | ✅ confirmed |
|P3| MDR: candidate WORSE on ≥ 8 of 19 | raw: 17 of 17; corrected: all UNDECIDED | ⚠️ confirmed on the statistic as SEALED, void on the corrected one |
|P4| MDR: candidate BETTER on `Tests.Coverage` | worse, raw and corrected | ⛔ **REFUTED** |
|P5| `real_s` noisier than `user_s` | 16 ms vs 16 ms — equal | ⛔ **REFUTED** |

⛔⛔ **AND THE SCORE ON THE PARTIAL CORPUS WOULD HAVE BEEN 5/5.** Every one of these was checked
against the 14-reading contended corpus first, and every one appeared confirmed. Three of five
reverse on the completed walk. ⇒ 🔑 **a prediction scored against a partial corpus is scored against
the conditions that truncated it**, and a seal is only worth what its denominator is.
[[feedback-a-confirmed-prediction-is-not-a-checked-statistic]] [[feedback-a-batch-cannot-be-sampled]]

### 4. ⛔ A CLAIM I POSTED TWICE AS "FIRM", WITHDRAWN

QUEUE item 9 was filed and posted on the bus twice: *"the shipped budgets rest on a day 7.30×
quieter than an ordinary one."* Measured on the completed corpus: **1.37×**. The 7.30× came from the
14-reading contended partial — n=42, one reading taken at load 98. There is nothing to act on and
the row is kept only so the withdrawal is as findable as the claim.
🔑 The comment in my own tool, three lines from the number, read *"It is one extra pair of days, not
a distribution over days."* **The discipline was written down and not applied to the sentence being
written beside it.** [[feedback-ungated-prose-overclaims]]

### 5. THE TIE-COUNT EARNED ITS PLACE

The shipped arm has **9 exact-zero spreads of 252** — Lean's profiler prints three significant
figures, so two sweeps of one tree can print the identical string — against the candidate's **0 of
228**. That biases the shipped arm to look steadier, which is the direction of §1's conclusion. It
is printed so the conclusion can be discounted for it rather than trusted through it.
[[feedback-a-noise-estimate-that-can-reach-zero]]

### 6. WHAT REMAINS

- **Item 4 is not closed by this.** 4a (heartbeats) and 4c (`--threads 1`) are refuted, 4d is
  refuted here; **4b — the kernel's own unfolded-declaration counter — is the survivor** and still
  owes a budget from a second source and a second machine.
- **Portability remains unmeasured for every candidate.** One box, arm64.
- §2 suggests the question may not be "which quantity" at all: if the signal and the noise are the
  same size, the repair is to make the DELTA bigger relative to the noise — more repeats, or a gate
  on an accumulated multi-batch drift rather than on one batch. Neither is priced.


## D153 — QUEUE item 4f priced: the repair is the WINDOW and it is free; repeats saturate at n≈3-4, and the projection that says otherwise cannot express a floor

D152 refuted 4a, 4c and 4d and left one finding standing — **the gate is trying to resolve changes
the same size as its own noise** — plus two untried repairs, neither priced. This entry prices both
on the one axis they both move, against **two independent walks over the same twelve commits**
(09/04 22:02-22:29 at load ~4.5; 09/05 21:08-21:42 at load ~12.3) and a **sixteen-reading run on one
frozen tree** taken tonight for the half no walk can answer.

Tool: `scripts/delta_repair_price.py` — selftest 10 arms, the unplanted CONTROL first, **8 distinct
arms** catching plants. ⛔ It **imports** `resolution`, `effective`, `repeats_to_decide`, `K_SIGMA`
and `MEDIAN_SE_FACTOR` from `kernel_delta.py` rather than restating them; the only thing it adds is
which readings are handed to those rules as `base` and `head`.
[[feedback-a-duplicate-born-in-agreement]]
Readings committed beside it: `docs/repeat-scaling-2026-09-05.jsonl` (a timing run cannot be
re-derived on another day, so the readings ARE the evidence).

### 1. ⭐⭐⭐ ONE AXIS: R = band / allowance

`R < 1` means the instrument can see a change the size of the change the gate is willing to *permit*.
`R > 1` is D152's finding as a number.

```
  unit                                                     09/04   09/05
  Tests.Coverage                                            0.35    0.88
  Tests.Coverage @residue                                   0.36    0.75
  Tests.Coverage @decl memDestSweep                         0.36    1.78
  Tests.Coverage @decl pre_states_have_a_returnable_frame   0.54    0.35
  Tests.Coverage @decl vectorCoverage                       0.52    0.32
  Tests.Anchors                                             0.32    0.34
  X86.Theorems                                              0.29    0.94
  X86.Syntax                                                0.33    1.02
  — median over all 23 gated units —                        0.21    0.29
  — units that cannot resolve their own allowance (R>1) —      0%     18%
```

⚠️ **The two nights disagree about whether the gate works.** Same twelve trees, same instrument,
twenty-three hours apart: on the quiet night no unit fails to resolve its allowance; on the loaded
night 18% do. [[feedback-a-single-reading-is-about-its-run]]

### 2. ⛔⛔ THE OBVIOUS PRICE FOR REPAIR A IS THE WRONG NUMBER

The gate's `~N repeats a side would decide it` divides by `|delta − budget|`. Read straight off the
09/05 walk it says the worst case needs **587,413 repeats a side — 32,210 hours for one merge**.

That number is not about noise. Its margin is **+4.4 ms against a budget of 1,695.6** — a commit
landing on its line, which the gate's own comment already calls a fact about the commit. Quoting it
as repair A's price prices the instrument with the commit's number.
[[feedback-a-wrong-models-score-is-a-joint-fact]]

Margin-free — *how many repeats bring the band under the allowance*:
```
  09/04   NO case has R >= 1: every unit already resolves its allowance at n=2
  09/05   45 of 253 cases do; p90 = 19 repeats a side  =>  63 min a merge
```
⇒ **repair A's price is set by the night, not by the code.**

⛔ And a correction inside my own reading of it: `repeats_to_decide` returns `max(n + 1, ceil(need))`,
so it can never say "fewer than three" or "none". Read over an already-resolved corpus it reports a
median of **3** — the function's floor wearing a price's clothes.
[[feedback-a-declared-list-inherits-its-default]]

### 3. ⛔⛔⛔ AND THE PROJECTION IS REFUTED WHERE IT MATTERS: THE SPREAD SATURATES

`repeats_to_decide` models the band as falling like `1/sqrt(n)` without limit, so it will always
name a finite N however large. Sixteen readings of ONE frozen tree (`master bd8881e`, 21:58-22:17,
loads 4.9-16.0, conditions recorded per reading) say the delta's actual spread does not behave that
way. `rms |d|` over all splits, against what `1/sqrt(n)` predicts from n=1:

```
                                    n=1     n=2     n=3     n=4     n=6
  Tests.Coverage        observed  585.9   326.7   104.4   104.1   109.5
                        1/sqrt(n) 585.9   414.3   338.3   293.0   239.2
  @decl vectorCoverage  observed  131.3   105.0    25.4    16.2    17.0
  X86.Theorems          observed  213.7   124.0    51.9    39.2     7.7
  @decl pre_states...   observed   45.8    33.9    28.1    14.5    13.6
```

Two things, and they cut in opposite directions:
- **n=2 → n=3 falls far FASTER than 1/sqrt(n)** (Tests.Coverage 327 → 104 where the model says 338).
  The median starts rejecting outlier readings — this run has a 25,800 ms reading against a level of
  23,800 — and a median of three throws away what a median of two averages in.
- **Past n≈3-4 it FLATTENS** on the units with the most at stake: Tests.Coverage 104 → 104 → 110,
  vectorCoverage 25 → 16 → 17. ⇒ **there is a floor, and the projection cannot express one**, so it
  will keep naming N for a question no N answers.

⚠️ Not uniform: `X86.Theorems` keeps falling to n=6, and `memDestSweep` is non-monotone (36 → 59 → 34)
on 13/11/9 splits. The n=6 column rests on 5 splits. What is defensible is the shape, not a floor
value per unit. [[feedback-a-single-reading-is-about-its-run]]

⇒ **repair A's useful range is n=2→4 and it saturates there** — which is where `kernel_delta.py`'s
own default already sits (3; CI runs 6). Buying the 19, 377 or 587,413 repeats the projection names
would not deliver what the arithmetic promises.

### 4. ⭐⭐ WHAT REPEATS DO BUY: BAND HONESTY AT SMALL n

On a frozen tree the true delta is zero, so every `|d|` is the gate's own error and the band is its
own claim about that error. A nominal 2σ band should be exceeded about 4.6% of the time:

```
    order        n   units   obs    |d| > band    worst |d|/band
    block        2      21   273    35 (12.8%)              9.03
    block        3      21   231    16 ( 6.9%)              1.89
    block        4      21   189     8 ( 4.2%)              1.26
    alternate    2      21   273    35 (12.8%)              7.58
    alternate    3      21   231    15 ( 6.5%)              2.50
    alternate    4      21   189     7 ( 3.7%)              1.47
```

**At n=2 the band is exceeded 12.8% of the time against a nominal 4.6%, by up to 9×.** `K_SIGMA = 2`
is a normal quantile and `MEDIAN_SE_FACTOR` is asymptotic, but at n=2 the variance estimate carries
one degree of freedom a side. By n=4 the rate is nominal. The mechanism is serial DRIFT, not
quantization — I checked quantization first and it is refuted: the only exactly-zero bands belong to
`X86` and `Tests`, the two content-free aggregator modules, which are excluded anyway. The signature
is `X86.Memory` reading base [13.0, 13.1] and head [11.4, 11.5] — each side tight, the sides 1.6
apart, tracking the load falling 16 → 9 across the run.

⛔ **AND THE TWO SPLIT ORDERS ARE INDISTINGUISHABLE** (12.8/12.8, 6.9/6.5, 4.2/3.7). I first measured
this at m=8, read "alternation is WORSE at n=3 and n=4", and held it: those cells were 6 and 1
events. At m=16 the difference is gone. `kernel_delta.py`'s docstring says the alternation-inflated
`se` errs in the conservative direction; on these readings the effect is not measurable either way,
which is neither the confirmation nor the refutation it might be read as.

⚠️ Where n=2 actually runs: **both committed walks**, and `--selftest-measure` (CI passes
`--repeats 2`). The MERGE gate defaults to 3 (`kernel_delta.py:1185`) and CI runs 6, so the gate
itself is inside `delta_band_calibration.py`'s swept range — which starts at n=3 and draws i.i.d.
Gaussian, and therefore cannot see any of the above.

### 5. ⭐⭐⭐ REPAIR B: THE LEVER IS REAL, ITS PREMISE NEEDED CORRECTING, AND IT IS FREE

Over k=1→11, with the allowance summed per step (never k × one budget):
```
                 band     allowance      R
  09/04         1.01x        11.37x    falls to 0.11x
  09/05         1.43x        11.22x    falls to 0.23x
```
The band is **not** k-independent — on the loaded night it moves 1.43×, because the trees at the ends
of a longer window sit further apart in level and the spread travels with the level. **The honest
claim is that the allowance grows an order of magnitude faster than the band.** The lever survives
its premise being wrong. [[feedback-audit-the-premise-of-a-right-decision]]

On the loaded night the refusal rate falls **17% → 6% → 3% → 1% → 0%** at k=1..5.

⛔⛔ **WHAT THAT COLUMN IS NOT.** Both walks return **zero OVER at every k** — the twelve commits
landed, so they are all within budget. ⇒ this corpus measures REFUSAL and never DETECTION, and the
k-column is a table about how often the gate stops shrugging.
[[feedback-an-implied-assertion-is-not-a-second-gate]] The lever is demonstrated where it can be, on
a plant sized to the band in closed form: a corpus over budget **every** batch (180 against 100, a
margin of 80 under a band of 177.2) is UNMEASURABLE at k=1 and k=2 and **CONVICTED 9 of 9 at exactly
the predicted k=3**.

⚠️ And the design's arithmetic limit, stated because the R numbers hide it: with the allowance summed
per step, `sum d_i > sum bud_i` is impossible when every batch was measurably under its own budget.
**The drift gate cannot convict where the per-batch gate passes.** Its power is entirely over the
cases the per-batch gate REFUSED — 17% of them on the loaded night. That is the case D152 named, and
it is why this is a second gate beside the first, not a replacement.

### 6. ⭐⭐ HEAD TO HEAD, IN EACH CURRENCY

```
  k   R falls        repeats a side to match      cost of the repeats
  2     2.0x                              9        24 - 30 min a merge
  4   3.6-3.9x                        27-31        71 - 102 min a merge
  8   6.1-7.5x                       75-114       247 - 301 min a merge
```
Repair B pays **zero extra profiling** — the gate already reads two trees, they are just further
apart — and pays in LATENCY (caught k batches late) and ATTRIBUTION (a window, not a commit). And
per §3 the repeats column is an upper bound on what repeats could deliver even if bought, because
the spread saturates around n=4.

### 7. ⛔⛔ THE CHEAP SPELLING OF REPAIR B IS REFUTED

```
  spelling                              OVER     ok   UNMEAS   median |d|
  re-profiled (both sides one night)       0    210       43          2.0
  cached anchor (base last night)          9    173       71          3.9
```
Caching the anchor halves the profiling and **manufactures 9 convictions the same-session comparison
calls `ok`** — regressions made out of the difference between two nights, judged by a band that does
not know the nights differ. The refusal count rising 43 → 71 is honest; the conviction count rising
0 → 9 is not. ⇒ **re-profile the anchor**, which costs exactly what the gate costs today.

The cross-night table says the same from the other side: 92% of 231 deltas sit inside their combined
bands (median gap/band 0.35), and the worst — `X86Native`, `d_A −0.6` against `d_B +8.4` — misses by
**29×**, both nights having estimated a 0.2-0.3 ms band from two nearly equal readings.

### 8. THE RECOMMENDATION, AND IT IS NOT A CHOICE BETWEEN THEM

- **Repair B for resolution** — a SECOND gate beside the per-batch gate. Free in profiling; the
  anchor is re-profiled, never cached; the allowance is the sum of the per-step budgets.
- **Repair A is NOT a resolution repair** and should not be bought as one: the spread saturates at
  n≈3-4 and the gate is already there. What the n=2 → 4 range buys is BAND HONESTY (12.8% → 4.2%),
  and that matters for the two places n=2 still runs — the history walks and `--selftest-measure`.

⛔ NOT DONE and not implied: neither repair is BUILT. This entry prices them. A drift gate needs its
own anchor policy, accumulated-allowance rule and red probes — a batch, not a tack-on.
⛔ Portability unmeasured, as for every candidate in item 4. One box, arm64.
⛔ The frozen-tree run is ONE session on ONE night, and its n=6 column rests on five splits.

## D154 — QUEUE item 4f BUILT: the drift gate ships as a second gate, and the "flat" allowance it forbids is wrong in BOTH directions, not just the conservative one

D153 priced item 4f and chose **repair B** — gate the accumulated drift of a WINDOW of k landed
batches, beside the per-batch gate rather than instead of it. This entry builds it:
`scripts/kernel_drift.py`, the allowance ledger it reads, and the two CI gates that keep the ledger
honest. Nothing in `kernel_delta.py`'s verdict path changed; the merge gate is untouched.

### 1. THE ALLOWANCE IS THE SUM OF THE PER-STEP BUDGETS, AND THE LEDGER IS WHERE THEY COME FROM

Every budget in `kernel_delta_budget.txt` is a PERCENTAGE (22 of 22 units; the only absolute line is
`@floor`), so a step's allowance depends on the tree that step started from. The gate profiles two
trees and cannot measure the k−1 trees between them — and does not need to: **the per-batch gate
already computed each step's allowance when that step merged**, against exactly that step's own base.
`docs/delta-allowance-ledger.jsonl` is that number written down, one row per landed step, carrying
the allowance (the verdict input), the base reading (AUDIT ONLY), and a digest of the registry that
priced it. Backfilled for the 09/04 walk's eleven steps: **11 steps x 23 units = 253 allowances**,
registry `18bdabbfe9cf597e`.

⛔ Summing allowances priced against two different registries prices a window with a rule it was
never judged by, so a digest mismatch is a refusal. So is a missing step: **a gap in the window is
not a cheaper window.** [[feedback-a-join-on-a-lossy-key]]

### 2. ⛔⛔ THE FORBIDDEN SPELLING IS WRONG IN BOTH DIRECTIONS — AND I HAD WRITTEN DOWN THE WRONG REASON

D153 and my own first docstring justified `sum of per-step budgets` over `k x one budget` like this:
*"the tree grows across the window, so every later step is entitled to more than the anchor was"* —
i.e. the flat spelling is merely CONSERVATIVE, too tight, able only to over-convict.

**The cross-check refuted that in the same sitting.** Over the 1,518 (window, unit) cases of the
09/04 walk:

```
  sum > flat   468 of 1518   30.8%    the flat gate is too TIGHT — manufactures convictions
  sum = flat   863 of 1518   56.9%    floor-bound, and identical by construction
  sum < flat   187 of 1518   12.3%    the flat gate is too GENEROUS — lets drift through
  ratio sum/flat: median 1.0000 · p90 1.0334 · max 1.1853   (per-k: p90 1.09-1.10 by k=10)
```

The trees do not only grow. In an eighth of cases the flat window would ACQUIT accumulated drift
that the summed allowance convicts, so the error is not one an "it can only be too strict" argument
covers. 🔑 **An "it can only err in the safe direction" premise is exactly the one to measure**, and
a correct decision is the least-inspected place to leave a wrong reason.
[[feedback-conservative-is-a-direction-not-a-margin]] [[feedback-audit-the-premise-of-a-right-decision]]

⚠️ And the median ratio is **1.0000 at every k**, which is not evidence the difference is small:
**~48% of gated cases are FLOOR-BOUND** — their percentage falls under `@floor 6`, so `effective`
returns the constant 6 and the sum IS exactly k x 6. Half the corpus agrees by construction and can
say nothing about the other half. A summary statistic over a corpus half of which cannot vary reports
the frozen half. [[feedback-defects-hide-where-nothing-varies]]

### 3. THE LEDGER AGREES WITH AN INDEPENDENT ROUTE ON 1,518 OF 1,518 CASES

The ledger's accumulated allowance was checked against `delta_repair_price.repair_b`'s own arithmetic
computed straight from the raw readings — a different code path, written for a different purpose:

```
  cases compared             1518
  mismatches (> 1e-9 ms)        0
  worst absolute difference  0.000e+00 ms
```

⚠️ Two routes, not two witnesses: both read the same walk file and both call `kd.effective`. What
this rules out is a transcription or summation defect in the ledger, not a wrong rule shared by both.
[[feedback-two-readings-are-not-two-witnesses]]

### 4. THE ANCHOR IS RE-PROFILED EVERY RUN, AND THE ARM THAT PROVES IT CARRIES ITS OWN CONTROL

D153 measured the cheap spelling and refuted it: caching the anchor's TIMING instead of profiling it
**manufactures 9 convictions the same-session comparison calls `ok`** (OVER 0 → 9, UNMEASURABLE
43 → 71). So the ledger holds ALLOWANCES — policy numbers — and never the readings a delta is
computed from. `base_ms` rides along for audit and is dead to every verdict path.

⛔ An arm asserting "perturbing `base_ms` changes nothing" is satisfied by a gate that reads no
ledger at all. It is therefore paired with a positive control on the SAME readings: perturbing
`allowance` alone moves the verdict `ok` → `OVER`. Silence is only evidence once something has been
shown to speak. [[feedback-a-probe-must-create-its-condition]]

### 5. THE SELFTEST — 18 ARMS, THE CONTROL FIRST, 10 DISTINCT ARMS CATCHING A PLANT

`python3 scripts/kernel_drift.py --selftest`, ~0.1 s, no measurement in any arm — and it says so,
because a green here says nothing about whether the profiler can see a code change.

```
  CONTROL (first)  an unplanted window is `ok`, sums to k x its steps, nothing unpriced
  A  flat-allowance CONVICTION   growing window: delta 90 is `ok` on the sum (150), `OVER` on flat (40)
  A  flat-allowance ACQUITTAL    shrinking window: delta 200 is `OVER` on the sum (150), `ok` on flat (320)
  A  floor-bound agreement       the two spellings are EXACTLY equal where the floor binds
  B  missing step / foreign registry / partial pricing   each REFUSES, rc 2, naming what it saw
  B  a conflicting record REFUSES *before* writing, leaving the ledger byte-unchanged
  C  dead `base_ms` (10x) + its positive control on `allowance`
  D  detection on a plant: band 16.37, surplus 5.0/batch ⇒ PREDICTED flip at k=4, stated first;
     UNMEASURABLE at k=1,2,3 and OVER at exactly k=4; a NULL window of the same length stays `ok`
  E  one reading a side is UNMEASURABLE (infinite band), 500 ms delta against a 400 ms allowance included
```

⛔ **The detection arm cannot come from the corpus.** Both recorded walks return **zero OVER at every
k** — the twelve commits landed, so they are in budget everywhere, and the k-curve measures REFUSAL,
never DETECTION. The flip point is computed in closed form from the gate's own band and asserted
BEFORE the sweep, so a "best k" search cannot pass it.
[[feedback-a-landed-corpus-cannot-measure-detection]]

⛔ **Two of my own arms were wrong and the harness caught them, not me.** (i) The positive control in
C was written against readings whose drift (10) sat under their own band (10.2), so `d − band` was
NEGATIVE and NO allowance could ever have convicted them — the arm could not have gone green for any
correct gate, and it went red on the first run. (ii) The detection plant was first sized so the flip
landed at **k=2**, leaving exactly ONE sub-flip observation; "not convicted below k" then rests on a
single cell. Re-sized to flip at k=4, three windows sit below it and each is checked.
[[feedback-a-plant-probes-control-comes-first]] [[feedback-size-the-plant-to-the-gate-not-the-phenomenon]]

⛔ **A THIRD DEFECT WAS FOUND BY PROBING THE `--record` PATH RATHER THAN READING IT**, and it was
the worst of the four: the first spelling APPENDED the new rows and THEN re-read the file to check
them. A conflicting record therefore refused *correctly* — after leaving the bad row on disk, so
every later run refused too, until a human hand-edited the ledger. A gate that corrupts its own data
store and then declines to work is worse than one that simply declines. The check now runs before
the write, and the arm asserts the file is BYTE-UNCHANGED after a refusal, with a positive control
that a non-conflicting step still appends. [[feedback-probe-gates-both-ways]]

⛔ A fourth defect was cosmetic and would have hidden a real one: the synthetic step shas were
sequential integers in 40 hex digits, so **every one of them renders as `000000000`** in the `sha[:9]`
that every refusal prints. An arm asserting "the refusal NAMES the missing step" passed while the
refusal named an indistinguishable string. Now `sha1(i)`.

### 6. WHAT THIS GATE CANNOT DO, STATED SO IT IS NOT ASSUMED

* **It cannot convict where the per-batch gate passed.** With the allowance summed per step, a window
  under budget every batch is under the summed budget by construction. Its whole power is over what
  the per-batch gate REFUSED — 17% of cases on the loaded night, 0% on the quiet one. A SECOND gate,
  never a replacement: as a replacement it is strictly weaker.
* **It buys latency and attribution, not sensitivity.** A regression is caught k batches late and
  attributed to a window rather than a commit.
* **It does not buy repeats.** The spread SATURATES at n≈3-4 (D153); the projection that names a
  finite N cannot express a floor.
* **Its backfilled allowances are RETROSPECTIVE** — computed from a committed walk, not by the gate
  that let those batches merge, because this gate did not exist then. Every row carries `source`, and
  the report prints how many of its steps are backfilled.
* **Portability is unmeasured.** One box, arm64. And ~48% of units are gated by an absolute 6 ms
  floor, so for those the budget file's own argument — *"the units are percentages BECAUSE a
  percentage travels"* — does not apply. That is a finding about the EXISTING registry, not this gate.

### 7. GATES REGISTERED

```
  Drift-gate arithmetic and ledger, driven red          kernel_drift.py --selftest
  Drift allowance ledger is DERIVED                     kernel_drift.py --verify-ledger <walk>
  Delta repair pricing agrees with the gate it prices   delta_repair_price.py --selftest
```

⛔ The third was found **off the gate list entirely**: `delta_repair_price.py`'s ten arms had never
run in CI. It now delegates its verdict rule to `kd.judge_delta`, so a divergence between what the
repository merges on and what it prices would be exactly the kind of drift nothing was watching for.
"Not on the gate list" is where a red hides. [[feedback-a-gate-behind-a-failing-step-is-silent]]

The verify-ledger gate was probed in BOTH directions before being registered: green on the committed
ledger (253 allowances), red on one allowance edited by +0.5 ms, red on a deleted step.
[[feedback-probe-gates-both-ways]]

⛔ The three-way verdict rule now lives in ONE place, `kd.judge_delta`, called by the gate, the
pricing tool and the drift gate. It was about to become a third copy born in agreement.
[[feedback-a-duplicate-born-in-agreement]]

⚠️ **None of these have run on a runner.** GitHub Actions still refuses every job on this account for
billing (desk FH), so every receipt here is local and arm64.

### 8. THE GATE RUN ON REAL TREES — a k=2 window, two trees profiled in one session

`kernel_drift.py --anchor 144e9a3cf --head 76cb51bd0 --repeats 2`, four passes, ~5.5 min.

```
  pass base load1=10.17    97s  Tests.Coverage=21800  X86.Syntax=237.0
  pass head load1=13.49   108s  Tests.Coverage=23700  X86.Syntax=239.0
  pass base load1=11.95    67s  Tests.Coverage=23400  X86.Syntax=212.0
  pass head load1=13.94    65s  Tests.Coverage=22300  X86.Syntax=216.0

  23 judged · 0 OVER · 1 UNMEASURABLE · 0 unpriced
  BOX yukon.lan · macOS-26.6.2-arm64 · 14 cpus · load(1/5/15) 12.10/11.97/10.60 · 22:45:50 PDT
```

⭐ **D152's finding is visible in the one refusal.** `Tests.Coverage` reads delta **400.0** against a
band of **2,664.6** and an accumulated allowance of **2,808.0** — R = 0.95, just under one, so at k=2
the band still very nearly spans the whole allowance and the gate cannot say which side the window is
on. Everything else resolved. That is the gate behaving exactly as D153 priced it: at k=1 this unit
is unresolvable on a loaded night, at k=2 it is marginal, and the refusal rate falls with k.

⚠️ **The box was loaded and the two base passes disagree by 7%** — 21,800 and 23,400 on the SAME
tree — which is where that 2,664.6 band comes from. This is one run on one loaded night; it is not a
statement about the instrument in general. [[feedback-a-single-reading-is-about-its-run]]

⛔⛔ **AND HERE IS A TRAP THIS REPORT SETS FOR ITS OWN READER, WHICH I NEARLY WALKED INTO.** Every
`sum/flat` ratio on this window is ≤ 1.000 — 1.000 on the twelve floor-bound units, and 0.772 to
0.922 on the eleven percentage-bound ones. Read naively that is a beautiful real-data confirmation of
§2's finding that the flat spelling can be too GENEROUS, and in exactly the direction my first
reasoning denied. **It is not clean evidence of that, and I will not bank it as such.** `flat` is
k x the budget computed from TONIGHT's anchor profile, while `allow` sums allowances priced from the
09/04 walk. The ratio therefore carries the difference between two nights — and tonight's box is the
loaded one, so tonight's anchor reads high and inflates `flat` — as well as any growth in the trees.
The clean measurement of the two spellings is §2's, computed entirely INSIDE one walk.
🔑 A ratio whose numerator and denominator come from different sessions measures the sessions too,
and it will happily agree with whatever you were hoping to confirm.
[[feedback-two-readings-are-not-two-witnesses]] [[feedback-a-join-on-a-lossy-key]]
⇒ The report now prints that caveat itself, on every run, rather than leaving it to a reader who has
the decision note in front of them.

⚠️ **Twelve of the twenty-three units are FLOOR-BOUND on this window** (`allow` exactly 12.0 = 2 x 6),
so more than half the table cannot distinguish the two spellings at all — the same blind half §2
measured at ~48% across the whole walk.

## D155 — QUEUE item 4b: the window turns one resolved pair into dozens, and D148's calibration constant turns out to be a SELECTION, roughly twice the unselected value

D148 left item 4b blocked by a sentence of its own: *"no budget has been derived: a calibration
resting on ONE resolved pair is not a second source. Do not gate on it before that."* On the gate's
own band the kernel reference resolved **1 of 11 adjacent pairs**, and `ms per 1k unfoldings` was
therefore the single value **7.65**.

D154's drift gate supplies what was missing at no cost: a k-batch window's delta grows with k against
a band that does not, so windows resolve where adjacent pairs refuse. `scripts/unfolding_calibration.py`
reads the SAME committed walks over windows instead of pairs. Selftest **7 arms, control first, 5
distinct arms catching a plant**. The join is exact — the deterministic-cost walk and both
kernel-delta walks cover the same twelve commits in the same order, checked before anything was
computed — and counters are flattened by `kd.units_of`'s own partition so a ratio's numerator and
denominator describe the same quantity.

### 1. ⭐⭐⭐ THE RATIO FALLS BY HALF AS THE WINDOW STOPS FILTERING ITS OWN EVIDENCE

Quiet night (09/04), module `Tests.Coverage`, the denominator D148 used:

```
   k   cases  resolved  frac   ratios (ms per 1k unfoldings)
   1      11         1  0.09   [7.65]                            <- D148's single value
   2      10         3  0.30   [7.65 8.50]
   3       9         4  0.44   [2.55 3.32 5.43 8.50]             <- low values start entering
   4       8         6  0.75   [2.55 3.23 3.30 3.34 5.93 5.93]
   8       4         4  1.00   [3.19 3.26 3.51 3.99]   ← UNSELECTED
   9       3         3  1.00   [2.39 3.79 4.12]        ← UNSELECTED
  10       2         2  1.00   [3.22 3.89]             ← UNSELECTED
  11       1         1  1.00   [3.18]                  ← UNSELECTED
```

⛔⛔ **A RATIO COMPUTED ONLY OVER THE WINDOWS THAT RESOLVED IS COMPUTED OVER THE WINDOWS WITH THE
BIGGEST DELTAS.** At k=1 exactly one window clears its band — necessarily the one with the largest
|delta| relative to it — and it reads 7.65. As k rises and the band stops dominating, the newly
admitted windows carry LOW ratios and the median falls by half. **At k>=8 every window resolves, so
nothing is filtered at all**, and the calibration sits at **2.39 - 4.12, median 3.38**.

⇒ **D148's 7.65 is the k=1 number and is roughly 2x the unselected value. A budget set from it would
have been about twice too generous.** The reading was not wrong; it was a reading of the one case
that survived a filter correlated with the quantity being measured — and nothing in its output said
so, because a single value carries no denominator.
🔑 **The resolved FRACTION is the only thing that distinguishes a calibration from a selection**, so
the tool prints it beside every ratio and marks the rows where it is 1.0.
[[feedback-a-landed-corpus-cannot-measure-detection]] [[feedback-read-what-the-instrument-measured]]

⚠️ **The ten unselected windows are not ten independent measurements.** Over twelve commits the
k=8..11 windows overlap heavily and share most of their span, so they are closer to one or two
independent observations wearing ten names. The tightness of [2.39 … 4.12] is weaker evidence than
its spread suggests. [[feedback-two-readings-are-not-two-witnesses]]

### 2. ⛔ THE SECOND SOURCE STILL DOES NOT CONFIRM IT — SO THE ITEM STAYS SHUT

The loaded night (09/05, load ~12) **never reaches full resolution** — 0 of 1 at k=11 — and its
ratios span **-5.90 to +37.05**, with **6 sign inversions of 106** resolved cases where kernel time
falls while unfoldings rise. The quiet night has **0 of 96**.

```
  quiet  night, UNSELECTED (k>=8)    2.39 - 4.12, 10 windows, median 3.38
  loaded night, best case (k=8)      3.96 - 13.23, 3 of 4 windows, NEVER unselected
```

⇒ The blocker's first half is LIFTED — dozens of resolved windows instead of one. Its second half is
NOT: two nights on ONE box disagree by more than a budget's margin would tolerate, and machine
independence remains unmeasured because there is no second machine (Actions refuses every job on this
account for billing). **Do not gate on it.** The item's status is unchanged; what changed is that its
reason is now measured instead of assumed, and its headline constant is known to be inflated.

### 3. THE COUNTER BEATS THE NULL, AND THE NULL IS THE ONE THE GATE CURRENTLY USES

D148's head-to-head was scored on a borrowed denominator. All three predictors are now scored over
exactly the same resolved windows. A predictor is good if its per-window ratio is CONSTANT, so the
figure of merit is p90/p10, lower better:

```
                                  09/04 (quiet)   09/05 (loaded)
  ms per 1k unfoldings (ku)            2.66            5.42
  ms per 1k heartbeats  (hb)        INCOHERENT      INCOHERENT     (p10 negative)
  ms per BATCH  (the null)            11.02           26.94
```

⭐ **The null is not a straw man: `ms per batch` is exactly what the merge gate's per-batch budget
assumes.** Beating it by 4.1x / 5.0x is the claim that a ku-based allowance would predict kernel cost
better than the allowance this repository currently gates on. Heartbeats stay incoherent — D146's
refutation reproduced, this time on a shared denominator.

⛔ **And one selftest arm exists so that the scoring can LOSE.** On a synthetic corpus where cost
really is per-batch and the counter is noise, the NULL must win; it does. Without that arm, "ku beats
the null" would be a fact about the comparison rather than about the counter.
[[feedback-score-the-null-model]] [[feedback-refute-a-proxy-with-a-plant]]

### 4. ⛔ TWO OF MY OWN ARMS WERE WRONG, AND BOTH FAILED CLOSED

1. The control asserted the recovered constant was **5.0** on a corpus whose true constant was
   **5000** — my construction multiplied by 1000 twice. The arm was wrong, the tool was right, and it
   went red on the first run.
2. The null arm CRASHED rather than failing: an incoherent spread returns `None`, and `None < float`
   raises. A comparison that throws is not a failed assertion — it stops the remaining arms from
   running at all. `None` now compares as infinitely bad.
🔑 Both defects were in the ARMS, not the subject, for the second batch running. A harness that only
ever confirms is the one to distrust; these two ran red before anything green was believed.

## D156 — QUEUE item 10 discharged: the orphan probe was looking in the one place a killed timing job never leaves an orphan, and the post-flight report then called my own live job an orphan

Item 10's pre-flight half has run since D151: a timing run looks for its own orphans before believing
its numbers. What remained was the POST-flight — *"re-run the orphan probe after a job is killed,
since that is when orphans are made."* Building it broke two of my assumptions and one pre-existing
arm, all of them in the direction of a report that reads as authoritative and is not.

### 1. ⛔⛔ THE DEFECT: ONE PRODUCER NAMED, THIRTEEN EXISTING

`foreign_builds` decided whether a Lean process belonged to another campaign like this:

```python
if rp == want or rp.startswith(want + os.sep) or "x86lean-history" in rp:
    continue        # ours
```

`"x86lean-history"` is the temp prefix of ONE of the **thirteen** `mkdtemp` producers that were
in `scripts/` when this was found. (There are fourteen after this batch; the fourteenth is the
declared foreign fixture in §3, and the arm prints its own count rather than carrying one here.)
The merge gate and the drift gate profile their worktrees under **`x86lean-delta-`**. Measured, one
real process per prefix, with both controls in the same run:

```
  temp tree prefix           counted FOREIGN?   produced by
  x86lean-history-             no (excluded)    kernel_delta_history.py:560   (negative control)
  x86lean-delta-                      YES ⛔    kernel_delta.py:432  (the MERGE and DRIFT gates)
  x86lean-budgetprobe-                YES ⛔    kernel_delta.py:939
  some-other-seat-                    YES ✅    a genuinely foreign tree      (positive control)
```

🔑 **A declared list's gaps all fall the way its default points**, and here the default was "another
campaign's build". [[feedback-a-declared-list-inherits-its-default]]

### 2. AND IT WAS WRONG IN BOTH DIRECTIONS AT ONCE — WHICH IS ITEM 10'S SUBJECT EXACTLY

`repo_orphans` asked whether a process's cwd was `== the repo root, exactly`. A killed timing job
does not leave orphans in the repo root: `kernel_cost.py` does `os.chdir(root)` and the delta gate
passes `--root <worktree>`, so the children run in a **worktree under TMPDIR**. An orphaned profiler
was therefore **invisible** to the probe that hunts my own orphans and **counted** by the probe that
hunts other campaigns' builds, simultaneously. The one process class item 10 exists to catch was the
class both probes misfiled, in opposite directions.

### 3. THE FIX: STRUCTURAL FIRST, SYMMETRIC, AND NAME-BASED ONLY WHERE NOTHING ELSE SURVIVES

`_own_tree(rp, want)`, one place, used by both probes:

1. the repo itself or anything under it;
2. **the main tree seen FROM a worktree** — `want` is the tree being profiled, which during a delta
   run IS a worktree, so without this the main repository counts as another campaign's tree while
   its own gate profiles a worktree of it;
3. **STRUCTURAL, name-free** — a detached worktree of this repo carries a `.git` FILE whose `gitdir:`
   points inside this repo's `--git-common-dir`;
4. **name-based, last, and only when the directory is GONE** — the post-kill case where nothing
   structural is left to read.

⛔ **The first spelling of (4) had no "gone" condition and claimed every `x86lean-*` temp directory.
It promptly reclassified this selftest's own foreign fixture (`x86lean-fake-lean-`, a scratch dir
that deliberately impersonates another campaign) as this seat's, turning a passing arm RED.** The arm
was right and my rule was too broad. A refusal is a design hint before it is an exemption, and the
narrower rule is also the more accurate description of what the fallback is for.
[[feedback-a-gate-that-refuses-names-a-cheaper-build]]

⭐ The convention the fallback rests on is **gated against the source**: an arm reads every
`mkdtemp(prefix=…)` in `scripts/` and requires it to start with `TMP_PREFIX` **or** to appear in
`FOREIGN_FIXTURES`, a declared list with a reason per entry — and it also refuses a STALE entry that
no longer appears in the source, so the exemption list cannot quietly grow.

### 4. ⭐⭐⭐ THE FINDING THAT MATTERS MOST: "ppid 1" IS NOT "ORPHANED", AND I NEARLY ACTED ON IT

The probe's rule is *ppid == 1 and cwd in my trees*. In production tonight, within ten minutes:

```
  pid 37925  Python  up 00:51  cwd = repo   REAL orphan — child of a selftest I had killed
  pid 91860  Python  up 00:17  cwd = repo   ⛔ MY OWN LIVE SELFTEST, running, wanted
  pid 91898  Python  up 01:30  cwd = repo   REAL orphan — child of the next kill
  pid 61710  lake    up 00:25  cwd = repo   REAL orphan — a build left by that kill
```

The report labelled all four **"MINE, ORPHANED"** and said *"these survived a job of mine."* Three
of those readings were correct. The second was my own selftest, launched with `nohup … &` — **every
deliberately backgrounded job in this harness is reparented to init exactly like a stranded one**,
because the launching shell always exits. I had killed a real orphan by pid one minute earlier, so
the reading arrived pre-endorsed by its own track record; I was one command from killing a live job
on the strength of it.

⇒ 🔑 **A signal that is right three times out of four is the dangerous kind, and the fourth case is
indistinguishable from the inside.** This is math's 22:45 near-miss (a `pkill -f bus_watch.sh` would
have blinded six seats) arriving in the tool built to prevent it, one layer down: there the
discriminator was cwd, here cwd is not enough and there is no discriminator at all.

Two changes, and neither pretends to resolve what cannot be resolved:
* `repo_orphans` **never names the calling process**. A probe run as a background job is ppid 1 like
  everything else, and the caller reading a report it asked for is the reader least likely to doubt
  it. (The pre-existing held-out arm already excluded `os.getpid()` for a *parented* process; that
  exclusion was one case short.)
* the report says **"MINE, ppid 1"**, states in the output that ppid 1 is true of every backgrounded
  job as well as every orphan, and requires confirming a process is unwanted **before** killing it
  by pid. It never kills. [[feedback-enumerate-is-not-attribute]]

### 5. WHY IT REPORTS AND NEVER REAPS

Every seat on this box runs identical command lines from identical paths — `sh
~/Documents/seat/watch/bus_watch.sh` is byte-for-byte the same at six seats — so a name-matched sweep
at one seat's exit selects the WHOLE FLEET's watches, silently, discoverable only at the next boot;
and the boot brief's own warning that a relit seat "boots blind until this runs" would have made the
injury look like the ordinary relight condition. math came one command from that tonight and stopped
because it attributed by cwd first; its six hits included this seat's own watch, pid 91614.
[[feedback-a-process-filter-matches-its-own-waiter]]

### 6. ARMS ADDED, each creating its own condition with a real process

```
  3d(a) a Lean build in a REAL detached worktree (x86lean-delta-) is NOT counted foreign
        — a plain temp dir would exercise the NAME rule while claiming to test the structural one
  3d(b) a genuinely foreign tree IS counted          (the control that keeps 3d(a) honest)
  3d(c) a process whose worktree DIRECTORY WAS REMOVED is still recognised as mine
        — reported INAPPLICABLE, not green, if lsof cannot report a deleted cwd on this
          platform; on this box it HAD input and passed, so the fallback is exercised
  3e    every mkdtemp prefix in scripts/ obeys the convention or is a DECLARED fixture,
        read from the source, with stale declarations refused too
  3f    a real ppid-1 process in a delta-gate WORKTREE is reported as MINE …
        … and is NOT also counted as another campaign's build
  3g    the post-flight probe returns 0 when nothing of mine is left detached — the caller's
        own pid included, since a backgrounded probe is itself ppid 1
```

### 7. ⭐⭐ AND THE NEW PROBE IMMEDIATELY CAUGHT THE SELFTEST ITSELF MAKING ORPHANS

Arm 3g went red on the first full run, and it was right. The fake-`lean` fixture every process arm
uses is a two-line shell script:

```sh
#!/bin/sh
sleep 40
```

`Popen` starts the **shell**; the shell starts `sleep` as its child. `pr.kill()` kills the shell, and
the `sleep` is reparented to init — a ppid-1 process with its cwd in one of my trees, for forty
seconds, on every arm that used the fixture. Measured directly rather than inferred: `sh 54864` had
child `55138`; after killing 54864, `55138` survives with **ppid 1**.

⇒ **Two of the leaking arms PREDATE this batch.** The probe built to find orphans left by killed jobs
found them being manufactured by the selftest that tests it, and the leak was invisible until
something asked the question at the right moment — the fixtures' processes expire after 40 s, so any
later check reads clean. Fixed with `exec sleep 40`, which replaces the shell rather than parenting a
child, so killing the pid kills the process there actually is.
🔑 A cleanup that kills a *wrapper* has not killed the work. [[feedback-a-running-script-is-an-open-file-handle]]

### 8. WHAT MY OWN ARMS GOT WRONG

⛔ **Two of my own arms were wrong before the subject was.** Arm 3f first created its process in a
bare temp directory, which under the corrected (narrowed) rule is correctly NOT this seat's — the arm
was asserting the over-broad rule I had just removed. And arm 3g read `post_flight()` immediately
after 3f sent SIGKILL, before init had reaped the process, so a correct tool failed a racing control;
it now waits for the pid to actually vanish.
🔑 For the third batch running, the defects were in the ARMS rather than in the subject. That is what
a harness that can go red is for.

### 9. RECEIPTS

`python3 scripts/kernel_cost.py --selftest` → **PASS (21 arms)**, ~11 min, none INAPPLICABLE.
`--post-flight` immediately after that run: **0 ppid-1 processes in my trees, 0 builds in other
trees** — which it was NOT before the `exec` fix, so the fixture leak is closed and the probe says so.
⚠️ The ceiling control printed *"UNMEASURABLE at this load — the control PASSED WITHOUT CHECKING THE
CEILINGS"*: the box was loaded (load 12-15 all evening) and that arm refused rather than guessed,
which is the behaviour D111 registered. It is a refusal, not a pass, and is recorded as one.
⚠️ Local and arm64. Actions still refuses every job on this account for billing.
## D157 — P2 BATCH 34: the buildable group nobody had named, and a sentence written to explain a measurement that had not been taken

**QUEUE item 2** says *"land the buildable groups the census has surfaced"* and never
named one. It was the queue's only unblocked substantial item for three sittings, and the
reason it stayed unnamed is worth more than the batch.

### 1. THE GROUP IS THE COMPLEMENT OF A CORRECT PARTITION

The P2 roster's ranked table prints its top FORTY rows. Every unclaimed row there that the
oracle executes is either VEX (`vmovdqa`, `vpaddw`, … — a new capability) or scalar FP
(`mulss`, `addsd`, … — the soft-float commission). Read there, and the residue looks
blocked on one of two large additions. It is not:

```
  64 unclaimed SSE-legacy (xmm) pairs EXECUTE on the oracle    47,965 instructions
− 40 that are the soft-float commission's                      36,925
= 24 pairs needing NO rounding rule at all                     11,040
```

⇒ 🔑 **A CATEGORY NAMED FOR WHAT IT CONTAINS SAYS NOTHING ABOUT ITS COMPLEMENT.** The
commission partitioned the FLOATING-POINT mnemonics correctly and completely — its three
sub-group totals reproduce from the live census to the instruction. What nothing named was
the set it left behind, and those members read as "FP" in any ranked table because their
mnemonics end in `ps`/`pd`. **Being FP-TYPED is not being FP-VALUED**: `xorps` reads no
exponent, consults no MXCSR and rounds nothing.
[[feedback-a-declared-list-inherits-its-default]]
[[feedback-a-category-is-a-hypothesis-about-its-members]]

⭐ The partition is now DERIVED and GATED, not asserted: `scripts/p2_residue.py`, three
gates, selftest 4 of 4 arms with the control first. Gate 3 re-derives the commission's own
published `12/6,619`, `2/898`, `26/29,408` from the census and refuses if they move — which
is precisely the defect the commission's §2 records about itself (its price grew 44% while
it sat docketed, because that price was a sentence and not a derived number).
⛔ What gate 3 proves is that the DOC AND THE CENSUS AGREE. It does not prove either right.

### 2. WHAT LANDED — nine mnemonics, one new function

`pandn`/`andnps`/`andnpd` (one operation at three opcodes) and the `ps`/`pd` spellings of
AND/OR/XOR. Nine roster rows, 21 vectors, NO new state, NO new constructor: they are
`VBinKind` members, so both operand shapes came free.

⛔⛔ **`ANDN` IS ASYMMETRIC AND THAT IS THE WHOLE BATCH.** `DEST ← (NOT DEST) AND SRC` —
the destination is complemented, not the source. Confirmed on a SECOND source before a line
was written: K's `pandn_xmm_xmm.k` is `andMInt(negMInt(DEST), SRC)`, and `negMInt` is
one's complement rather than arithmetic negation — read off `sbbb_rh_imm8.k`, where
`a + negMInt(b)` is the CF=1 arm of `a − b − CF` and so can only be bitwise NOT.
[[feedback-two-readings-are-not-two-witnesses]]

⚠️ Six of the nine are new ENCODINGS of an operation already present, and they are separate
KINDS because the BYTES differ (`pand` `66 0f db`, `andps` `0f 54`, `andpd` `66 0f 54` —
measured on the assembler). That is the `movdqa`/`movaps` rule, NOT the `pmovmskb` r32/r64
one, where batch 18 refused a width field because the two spellings emitted identical bytes.
⭐ Their semantics is shared by NOT branching: nine kinds, three arms in `vbinApply`, one
new function. And the identity claim is a THEOREM, because no differential vector tests a
spelling against its sibling — each is tested only against the oracle. Planted red: routing
`.andps` to `|||` breaks it.

### 3. ⛔⛔ WHAT I GOT WRONG, AND IT WAS PROSE ABOUT A NUMBER I HAD NOT MEASURED

I wrote — in a vector comment, an arm docstring and a theorem docstring — that the swap arm
is INVISIBLE on the diagonal pre-states, "where `diag` sets xmm0 = xmm1, so `(NOT a) AND a`
and `a AND (NOT a)` are both zero", and that a score below 88 should be read as that rather
than as a weak rule.

**Every clause was false.** `diag` is `mkPre a a 0`: it equalises the two GENERAL-PURPOSE
operand values. The XMM file is filled by `xmmPattern`, which gives register `r` the value
`(a + r.index) : (c XOR r.index * 0x1111…)` — distinct per register BY CONSTRUCTION, exactly
so that a model ignoring its operand fields is catchable. Computed over all twenty diagonal
states: **xmm0 = xmm1 in ZERO of them, and the swapped model disagrees in all twenty.**

🔑 **A sentence written to explain a measurement you have not yet taken will fit whatever
arrives.** It was ready to absorb any score below 88 as expected — and it was three
paragraphs of confident mechanism resting on a function I had not opened.
[[feedback-a-confirmed-prediction-is-not-a-checked-statistic]]
[[feedback-the-burden-is-on-the-departure]]

### 4. AND A JUSTIFICATION THAT HAD OUTLIVED ITS CONDITION

`vbinm_unaligned_faults` carried: *"at the other sixteen kinds it is theorem-only, and the
split is a fact about x86isa's source tree rather than a judgement."* True when written, and
a reason not to look again. The fact about the source tree is larger than the three
mnemonics the sentence names: `logical.lisp`'s function is
`x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM` — ONE body serving TWELVE
mnemonics, with the `:memory-address-is-not-16-byte-aligned` branch inside it, read in the
body rather than off its doc comment. The run-backed set is twelve of twenty-eight kinds now.
⚠️ Two unaligned vectors were added, not nine: both sides share their rule, so the other
seven would be one test wearing seven names. What varies is the DISPATCH, whose live
dimension is the mandatory prefix — hence one prefixed and one bare.
[[feedback-a-justification-outlives-its-condition]]

### 5. AND THE CENSUS REBUILD USED A DIFFERENT CORPUS ON THE FIRST TRY

A roster change makes `docs/DEMAND-CENSUS.md` stale by construction, so the batch had to
rebuild it from the public Debian corpus the document's own recipe names. The recipe says to
unpack each package into its column directory and let the script's ELF walk choose; I
hand-picked files instead. **Every gate would have passed** — the staleness check compares
the model sha and the mapping rules, not the corpus.

⭐ What caught it was a quantity that must NOT move: the RAW per-column instruction totals,
a property of the corpus alone. Three columns shifted — `cc1` −107,103, `glibc` −77,811,
`coreutils` −6,452 — and they are exactly the three I hand-picked, while the six unpacked
whole matched to the instruction. Rebuilt properly, all eleven reproduce exactly.

⭐⭐ And the recomputed census then agreed with the roster **to the instruction**: the pooled
assembly class gained `+3,556` covered instructions, the same figure
`p2_roster.bucket_demand` prices this batch's nine mnemonics at, by a different route from a
different input.
🔑 **A REGENERATED ARTIFACT NEEDS A QUANTITY THAT MUST NOT CHANGE**, or "it regenerated
cleanly" only means the generator ran. [[feedback-a-staleness-stamp-hashes-only-one-half]]

### 6. THE UNLANDED BATCH NOBODY'S QUEUE MENTIONED

`p2-batch32-fp-compares` (`3a811fb`, 2026-09-05) builds `comiss`/`comisd`/`ucomiss`/`ucomisd`
— FOUR of sub-group A's twelve pairs, 2,256 instructions — with a green differential, and is
held off `master` only by a kernel-cost verdict of UNMEASURABLE whose honest reading was that
it MAY FAIL (`+2,900` on `24,700`, `+11.7%` against a `7.2%` budget). Neither the P3
commission nor QUEUE item 2 mentions it, so "take sub-group A as an ordinary P2-shaped batch"
was advice to build a third of something already built. It waits on a QUIET-BOX measurement
and on nothing else. ⚠️ Its 8 vectors cost ~375 ms each and batch 23's 2 cost ~290, so a
batch's kernel price is set by its VECTOR COUNT — the thing to size a batch against first.

### 7. AND THE BATCH EXPOSED A QUALIFIER ON D144's HEADLINE, WITHOUT CREATING IT

D144 closed the availability census with *"every pair x86isa IMPLEMENTS has now been asked"* and
called it finished "without a qualifier". After this batch the same tool reports **1 implemented
pair unasked — `pandn` @ `MMX (mm)`, 88 instructions** — and the mechanism is not a regression.

`p2_oracle_support`'s remainder loop takes each mnemonic's **DOMINANT** bucket
(`p2_roster.dominant_bucket` is `Counter.most_common(1)`) and `continue`s if that one pair is
measured. It therefore shows **at most one bucket per mnemonic**, and every non-dominant bucket has
never been in its denominator. Measured, HEAD vs this batch, from the two census JSONs:

```
  pandn uncovered demand   HEAD: {SSE-legacy (xmm): 2,980, MMX (mm): 88}
                          BATCH: {                          MMX (mm): 88}
```

SSE-legacy was dominant and measured, so `pandn` contributed nothing. Covering it took that demand
to zero, which promoted MMX to dominant, which made a pair that was **always** unasked appear as
new work.

⇒ 🔑 **A CENSUS KEYED BY "THE BIGGEST BUCKET PER NAME" REPORTS ABOUT NAMES, NOT KEYS.** Covering a
mnemonic can only reveal its next bucket, never add one, so the count can rise for a reason that is
pure bookkeeping. The defensible sentence is *"every DOMINANT pair x86isa implements has been
asked"*, and the unobserved region is every mnemonic whose demand straddles buckets — the tool
already prints 3,991 instructions living at mnemonics' other buckets and nothing read it as a gap.
⚠️ Not repaired here, and the two candidates are recorded in the queue: enumerate every
(mnemonic, bucket) pair with demand, or keep this view and PRINT the non-dominant count beside it
so the blind spot carries a number. [[feedback-a-census-is-per-key-not-per-name]]
[[feedback-unobserved-regions-report-agreement]]

### 8. THE TWO ARMS AGREED TO THE CASE

Both planted arms were caught and the filtered selftest PASSED — and both reported **exactly 504
disagreements in `xmm0`, 588 total**. Identical counts in identical fields are the signature this
repository already has a name for, so it was checked rather than recorded as two receipts. Over all
60 register-shape pre-states: arm 1 fires on 60, arm 2 on 60, **intersection 60**.

The models are not the same — `andn_is_not_its_operand_swap` and `andn_is_not_nand` are separate
witnesses and neither equals the other. What is duplicated is the COVERAGE: `504` measures how many
ANDN cases the vector table executes and compares, not how discriminating either arm is. Arm 2 rules
out a second misreading and adds no case arm 1 did not already cover, for ≈13 minutes of wall-clock.
⇒ 🔑 **Say which of the two things is duplicated — the model or the coverage — before reading two
arms as two tests.** [[feedback-two-arms-that-agree-to-the-case]]

⛔ And arm 2's docstring had claimed the pair "complementary by construction", because arm 1 was
believed blind on the diagonal. Both halves were false, and this is the SECOND time in one batch
that a sentence about the pre-states was written without opening `xmmPattern`. The first correction
did not sweep for its own siblings. [[feedback-naming-a-defect-is-not-finding-its-siblings]]

### 9. THE MERGE GATE REFUSED ON TWO UNITS, AND THE FORK IT LEAVES

`kernel_delta 8a74e36 → 5c1f09e`, repeats 3: **21 of 23 units `ok`**, including the parent
`Tests.Coverage` (+1,100 vs 1,728) and `@residue` (+820 vs 2,062.8). Two UNMEASURABLE:
`Tests.Coverage @decl vectorCoverage` (+230.0 vs 260.6, band ±39.2) and `X86.Coverage`
(+0.5 vs 6.0, band ±8.5).

**THE ARMS, POSTED RATHER THAN DECIDED SILENTLY.**
* **(a) Hold the batch off `master`,** as `p2-batch32-fp-compares` was held. Consistent with
  "UNMEASURABLE IS NOT A GREEN" read as a rule about the WORD.
* **(b) Keep it on `master` and record the refusal in full.** ⭐ TAKEN, and the reasons are
  readings rather than preferences: both refusing units' point estimates are INSIDE their budgets;
  the whole module and the residue both pass; and `X86.Coverage`'s refusal is **structurally
  unresolvable** — a 0.5 ms delta against a `@floor 6` budget with an 8.5 ms band, which no repeat
  count fixes and which would refuse for every future batch equally, including ones that change
  nothing. Batch 32's verdict shared this word and NOT its content: there the honest reading was
  *"this batch MAY FAIL"* at +11.7% against a 7.2% budget. Treating two different readings
  identically because a gate printed one word for both is the error, not the consistency.
  [[feedback-a-category-is-a-hypothesis-about-its-members]]

⚠️ **WHAT THIS DOES NOT CLAIM.** It is not a pass. The worst case inside `vectorCoverage`'s band is
3% over budget. A quiet-box re-measurement is the receipt, and it is the same measurement batch 32
is waiting for — so the two should be re-run together.

⭐⭐ **AND THE ARITHMETIC THE NEXT BATCH NEEDS.** At ~11 ms per vector against a 260.6 ms allowance,
`vectorCoverage` affords about **24 vectors per batch**; this batch spent **21**. The next vector
batch on this declaration has no room, whatever it contains. "Size it by vector count" stops being
advice at that point. [[feedback-a-pass-at-97-percent-is-not-headroom]]

---

## D158 — QUEUE item 2a: the sizing rule was keyed to the wrong quantity, the allowance was never a constant, and both errors read as arithmetic

My gate handed me an order and a rule to size it by, in the same words my bank and
`docs/QUEUE.md` both carried: *"`vectorCoverage` affords ~24 vectors a batch (~11 ms each
against 260.6) and batch 34 spent 21, so 15 mnemonics at both operand shapes will NOT fit —
split the group."* Every number in that sentence is a real reading. Its conclusion is
right. I split the group. **And the rule is wrong in two independent ways, either of which
would have cost a night's build.**

### 1. THE DECLARATION DOES NOT COST BY THE VECTOR

`X86.Tests.vectorCoverage` is not a sweep over vectors — it stopped being one at D105, when
a kernel SEARCH became a kernel CHECK of a generated certificate. Its four conjuncts:

```
  mnemonicRuns == vectorRunIdx.map (fun i => tableMnemonics.getD i "")   O(runs x rows)
  (List.range rosterSize).all (fun i => vectorRunIdx.contains i)         O(rows x runs)
  vectorRunIdx.all (fun i => i < rosterSize)                             O(runs)
  vectorRunIdx.eraseDups.length == rosterSize                            O(runs^2)
```

The VECTORS enter once, linearly, through `collapseAdjacent`, and that is the term the
kernel barely charges for. ⇒ the growth law is **quadratic in (rows x runs) and flat in
vectors.**

Measured on a plant (`scripts/p2_batch_size.py`) whose two candidate models predict
**opposite signs**, so the run was free to refute me:

```
  arm                          measured Δ    per-VECTOR model    per-ROW model
  +30 vectors, +0 mnemonics        −10 ms    predicts +330       predicts +160
  +15 mnemonics, +15 vectors      +370 ms    predicts +165       predicts +340
```

A vector costs **0.0 ms**. A mnemonic costs **~25 ms** — and that is what batch 34 itself
paid (230/9 = 25.6) and what the twelve-commit history in
`docs/kernel-delta-history-2026-09-04.jsonl` pays (22.5 by least squares over 12 commits,
27.3 by endpoints). **The per-ROW price reproduces on three independent routes; the
per-VECTOR price does not survive a change of mix**, and that is exactly what happened:
batch 34's mix was 21 vectors over 9 mnemonics where the history's is 61 over 13, so
dividing by vectors gave 11 ms where the corpus gives 5.4.

⭐ The positive control is the second witness to the law rather than a formality: doubling
every dimension reads **4.13x**, not 2x. A quadratic instrument announcing itself.

⇒ 🔑 **A PRICE DIVIDED OUT OF ONE BATCH IS KEYED TO WHATEVER THAT BATCH'S RATIO HAPPENED TO
BE.** It reads as arithmetic because the division is real. The defect is not in the
division; it is that nothing recorded which of the several quantities a batch grows was the
one being charged for. [[feedback-match-the-gate-units-to-the-growth-law]]
[[feedback-a-total-cannot-see-its-parts]]

⚠️ **And the practical consequence points the opposite way from the advice.** The handed-on
rule says *reduce the VECTOR count* — i.e. take all 15 mnemonics at one operand shape
instead of two. Under it that batch is 15 vectors, ~165 ms, comfortably inside. Under the
measured law it is 15 mnemonics, ~375 ms, and blows the gate. **The one repair the rule
recommends is the one that does not work.**

### 2. `260.6` WAS NEVER AN ALLOWANCE

`scripts/kernel_delta_budget.txt` sets `Tests.Coverage @decl vectorCoverage 15.7%` — a
**percentage of the base**. 260.6 was that percentage times one particular base, quoted
onward as a constant, by me among others.

The direction of that error is not the one intuition offers. Marginal cost grows like `R`
while a percentage budget grows like `R^2`, so

```
  k_max ≈ 0.157 · R·U / (U + 2R)  ≈  0.074 · R      (at U ≈ 1.8R)
        ≈ 10 mnemonics at R=144 · 15 at R=200 · 22 at R=300
```

**The affordable batch GROWS with the roster.** Read with the frozen 260.6, the same
quadratic law says batch sizes shrink toward zero and the merge gate must be redesigned
before the campaign can continue — an alarm I had begun to write down before I opened the
budget file. It is an artefact of freezing a percentage into a number.
[[feedback-a-citation-is-an-ungated-claim]]

### 3. WHAT LICENSES SIZING A BATCH ON A SYNTHETIC PLANT

Nothing, until it reproduces a real one. `--calibrate` replays P2 batch 34's own transition
(134/239/954 → 144/260/977) and requires the plant to reproduce the `+230.0 ms` that
`kernel_delta.py` actually measured. Three runs: **+210, +240, +240** — 0.91x, 1.04x, 1.04x.
The plant's absolute LEVEL is synthetic (its strings are `m0..mN`; it carries no other
declaration); only its RATIOS transfer, and the calibration is what says they do.
[[feedback-a-ratio-travels-where-a-ceiling-cannot]]

**THE ANSWER: 8 mnemonics at both operand shapes.**

```
   6 mnemonics  +120 ms   6.2% of base   ✅ clean
   8 mnemonics  +210 ms  10.9% of base   ✅ clean, band included
  10 mnemonics  +310 ms  16.1% of base   ⛔ over the 15.7% budget
```

A CLEAN `ok` needs `delta + K·se < budget` with K=2, not merely `delta < budget` — the
difference between a pass and the UNMEASURABLE that has held `p2-batch32-fp-compares` off
master since 09/05 and left batch 34's own verdict unresolved. 10 is inside the budget and
outside the band; 8 is inside both.

### 4. WHAT I GOT WRONG

1. **I published `+945 ms` for the 15-mnemonic arm from an n=2 median.** It contradicted my
   own quadratic model by 2x and I wrote it into a table anyway. Re-run at n=4: **+395**,
   which the model predicts at +447. The arm that disagrees with the model is the one that
   needed the repeats, and I had D153's "the spread saturates at n≈3-4" in my own memory
   bank while reading a two-point median.
   ⇒ and the two n=2 sweeps disagreed with each other elsewhere too (k=12: +300 then +430).
   [[feedback-a-single-reading-is-about-its-run]]
2. **My first harness reported CONTROL FAILED on a working plant.** The parser looked for
   `type checking took` where the cumulative block prints `type checking 1.99s`. The control
   caught it before a single arm was read — which is the whole reason the control runs
   first — but I had written the regex off a per-declaration line I had seen and the
   cumulative line I had not. [[feedback-a-plant-probes-control-comes-first]]
3. **The plant would not compile and the reason was in the file I was copying from.**
   `maximum recursion depth has been reached`: `Tests/Coverage.lean` sets `maxRecDepth 40000`
   at line 38 and I had copied the theorem without the options that make it checkable.
4. **I began writing the "batch sizes shrink toward zero" alarm before opening the budget
   file.** The prose was two sentences in when the percentage refuted it. That is the
   [[feedback-prose-written-before-the-measurement]] card recommitted, four batches after I
   wrote it, in the same shape: an explanation authored ahead of the number.

### 5. THE GATE, AND WHY IT IS PROSE THAT IS GATED

The defect was never a wrong measurement. It was a **sentence** — keyed to the wrong
quantity, sitting in the most-read planning doc, reproduced verbatim into two banks because
it read like arithmetic. No timing gate could see it. So `--check` (in `ci.yml`, three arms,
no Lean toolchain needed) gates the queue's own law — *a row's PRICE is a derived number or
it is absent, and prices name the tool that prints them* — for this one price, plus the two
inputs whose renaming would leave the tool reading a default. **Probed both ways**: red
first (rc 1, "QUEUE.md states a batch size without naming the tool that derives it"), then
green after the row was rewritten. `--selftest` is 6/6 with a control first and a **LYING
plant** among the arms — a shape whose theorem is FALSE, which `lean` must REFUSE, because a
run in which the kernel checked nothing would otherwise time out at a plausible number.
[[feedback-ungated-prose-overclaims]] [[feedback-a-certificate-the-kernel-checks]]

## D159 — P2 BATCH 35 lands, and the second gate built to answer item 4's refusals turns out to have been unusable since the day it shipped

Batch 35's tail was mechanical and it is done: the census regenerated, three derived
artifacts repaired, `ci_local` CLEAN 33 of 33 on master at `0c392cf`. Two things came out
of the tail that are worth more than the batch.

### 1. THE CENSUS RECIPE REPRODUCES, AND THAT SENTENCE HAD NEVER BEEN TESTED

`docs/DEMAND-CENSUS.md` says its recipe exists *"so the number can be re-derived rather
than believed"*. Until 09/06 that was itself a belief: no head had re-downloaded the
corpus, so the document's central self-claim had exactly the status of the claims it warns
about. Rebuilt whole — all 19 documented packages, ~250 MB, the fetch refusing and naming
any package it could not get rather than proceeding on a subset. **It reproduces**, on two
checks whose sources are independent of each other:

* per-column ELF counts match the committed census in **all 10 columns exactly**
  (2 / 106 / 28 / 1 / 2 / 52 / 19 / 1 / 1 / 1);
* the assembly-class demand this batch had already published — `movapd` **2,420** ·
  `movupd` **113**, sum **2,533** — recomputes EXACTLY off the new corpus through
  `_classify`, which keys by the **objdump mnemonic** and is therefore independent of the
  model whose growth made the census stale in the first place.

The second is the stronger: a number the batch committed to before the corpus existed on
this box, re-derived from bytes fetched afterwards. With the corpus held identical, the
census's movement is attributable to the model alone — "not mapped at all" fell in every
column and rose in none.

⛔ **AND MY FIRST READING OF THE REBUILD WAS WRONG, BY THE RULE THIS REPOSITORY ALREADY
OWNS.** An ad-hoc ELF counter read glibc 29 / dav1d 2 / ffmpeg 4 / vpx 3 against the
committed 28 / 1 / 2 / 1, and I was six objects from filing a corpus-drift finding. All six
were **symlinks** (`libdav1d.so.7` beside `libdav1d.so.7.0.0`). `elf_targets` already
refuses them — it skips links and dedupes by inode, under a docstring about this precise
defect. I had written a SECOND filter that shared the tool's purpose and not its rule,
which is the shape D143 repaired in `probe_bucket`. 🔑 **When a count disagrees with a
committed count, recount with the tool's own function before believing your own.**

### 2. ⛔⛔ THE DRIFT GATE HAS NEVER BEEN ABLE TO ADJUDICATE ANYTHING

D154 (09/05) built `kernel_drift.py` as the answer to item 4's refusals, and the reasoning
is sound and measured: over k=1→11 the accumulated allowance grows **11.4× / 11.2×** while
the band moves only **1.01× / 1.43×**, so the resolution ratio falls to 0.11× / 0.23×, at
**zero extra profiling**. Its whole power is over what the per-batch gate REFUSED.

It cannot be run. Demonstrated, rc 2, no profiling:

```
  $ python3 scripts/kernel_drift.py --anchor 51e760b --head 26eb0b6
  ⛔ the ledger is missing 1 of 1 steps in this window ...
```

`docs/delta-allowance-ledger.jsonl` holds **11 rows, every one `backfill:`**, ending at
`5c0159983` — and master was **40 commits past that** before batch 35 landed.
`window_steps` is `rev-list --first-parent`, so all 40 are steps, and the gate's own law is
that **a gap is a REFUSAL, not a zero**. So every window reaching back across them refuses,
and did on the day the gate shipped.

⇒ 🔑 **AN UNRECORDED LANDING DOES NOT MERELY FAIL TO HELP — IT EXTENDS A DEAD ZONE**, and
nothing complained for 40 commits because the only instrument that would complain is the
one the gap disables. A gate whose precondition is maintained by a separate discipline is
disabled by the first person who forgets, and reports nothing while it is.

⛔ **AND `--record` IS NOT THE "ONE CALL" THE QUEUE PRICED — IT HAS A FIXED POINT.** The
ledger is a TRACKED file, so writing step N's row is a commit, and that commit is itself a
first-parent step needing a row. This is not hypothetical: **D154's own commit `491dcff`,
the one that wrote the 11 rows, has no row of its own**, and there is no exemption in
`window_steps` or `accumulated_allowance` for a commit that changes no `.lean`. Candidates
for breaking the recursion are recorded in QUEUE 4g(a); none is taken here, because
choosing one is a design decision and I found the problem at the end of a batch rather than
at the start of a sitting.

⚠️ **An operational constraint fell out of the same reading, and it had been silently
satisfied until now.** A ledger row's key is an **adjacent (parent, child) pair** — all 11
are adjacent, and master carries 0 merge commits — while `--record` keys the row off the
readings blob's `base_rev`/`head_rev`. So **the commit that lands must be the commit that
was measured**: a three-commit branch measured base→tip yields a row matching no step.
Batch 35 was therefore squashed to one commit and its tree verified byte-identical to the
measured commit (`git diff 73bc95c HEAD` empty) before landing.

### 3. THE BATCH'S OWN VERDICT, AND THE BAND THAT MOVED 20× IN A DAY

```
  Tests.Coverage @decl vectorCoverage   base 1850  head 1915  delta +65.0  ±32.0  budget 290.4  ok
```

The unit D158 is about, and the one that read `+30.0 ± 657.3 UNMEASURABLE` the night
before **off the same base median of 1850**, resolved cleanly at ±32 — a band that fell
from 2.3× the budget to 0.11× of it, same repeats, same box, one day apart. The gate's
overall verdict is still **UNMEASURABLE (rc 3)**: `Tests.Coverage`, `@residue` and
`pre_states_have_a_returnable_frame` have bands that straddle their budgets. ⚠️ **Every
unit's point estimate is UNDER its budget; not one delta exceeds its allowance.** The
refusals are all "the band straddles", never "the delta exceeds", and rc 3 is deliberately
not rc 1 — *reported as `ok` it is a pass nobody measured, and reported as OVER it is a
conviction built out of noise*. It is recorded here as neither.

⚠️ The largest single cost is **`@residue` +1435 ms (band ±815, budget 2184)**, which is
plausibly the §4 gate repair — `vmov_alignment_is_by_kind` now quantifies over
`VMovKind.all` by `cases` rather than four literals — and not the `movapd`/`movupd`
semantics at all. That attribution is UNMADE and is the first thing to measure next.
[[feedback-a-single-reading-is-about-its-run]] [[feedback-a-total-cannot-see-its-parts]]

## D160 — QUEUE 2b, step 1: the field change that was priced before the semantics, and an inherited hazard that was about a different kind of thing

QUEUE 2b's first order was not to write semantics. It was: *"⛔ THIS MODIFIES `vloadh`/
`vstoreh`, WHICH IS THE EXPENSIVE PART AND MUST BE PRICED FIRST. Two fields on an existing
constructor blew three unrelated record proofs before."* This note records what the price
turned out to be, and — more usefully — that the citation behind the fear was about a
different kind of object than the one it was pointed at.

### 1. THE INHERITED HAZARD WAS ABOUT A RECORD; THE SUBJECT IS AN INDUCTIVE

`[[feedback-a-state-field-costs-every-record-proof]]` records a real and expensive event:
two `BitVec 64` fields on **`Cpu`** took three inherited `bsf`/`bsr` frame lemmas over the
heartbeat limit at once, because those proofs closed by `rfl` over the whole record and a
whole-record `rfl` costs O(fields).

`vloadh` is not a record. It is a **constructor of the `Op` inductive**, where a `match` is
compiled and a field is not walked by a defeq check over every sibling. The two cost shapes
are not the same, and the tree already carried the evidence: **`vload`/`vstore` have carried
a `VMovKind` field since batch 3 and cost nothing for it.** The queue's warning was worth
obeying — the price was unmeasured and the fallback was real — but the *mechanism* it named
could not have applied, and reading it as though it did would have bought the duplicated-rule
fallback for a hazard that was never in this position.
⇒ 🔑 **A CITED HAZARD IS A CLAIM ABOUT A MECHANISM, AND A MECHANISM HAS A SUBJECT.** Check
that the new subject is the same KIND of thing before paying the remedy.
[[feedback-inherited-diagnosis-is-a-hypothesis]]

### 2. WHAT WAS MEASURED, AND WHY IT IS A COMMIT OF ITS OWN

`abe83b8` changes the fields and NOTHING else: `vloadh`/`vstoreh` become `vloadq`/`vstoreq`
carrying `VHalf` (which quadword is written, hence which is PRESERVED) and `VQuadKind` (the
mandatory prefix, i.e. the spelling); the same six vectors are respelled `.hi .ps`; the
mnemonic they produce is still `movhps`; the roster, the coverage table and the differential
do not move. Splitting it from the semantics is what makes the reading a fact about the
FIELDS rather than about the fields and six mnemonics together.

`kernel_delta.py --base e6dd9c6 --head abe83b8 --repeats 3`, passes alternated, one session:

```
  X86.Syntax                       244.0 → 239.0    -5.0  ±7.6     budget  45.6   ok
  X86.Semantics                     14.6 →  14.2    -0.4  ±1.8     budget   6.0   ok
  X86.Theorems                    1020.0 → 990.0   -30.0  ±263.8   budget 186.7   UNMEASURABLE
  X86.Value                         28.8 →  25.9    -2.9  ±15.3    budget   6.1   UNMEASURABLE
  Tests.Coverage @decl vectorCoverage 1950 → 1890  -60.0  ±1689.2  budget 306.1   UNMEASURABLE
  Tests.Coverage @residue          15780 → 15870   +90.0  ±2900.7  budget 2193.4  UNMEASURABLE
  (every other unit ok)                                                     overall rc 3
```

### 3. THE VERDICT IS `UNMEASURABLE`, AND THAT IS NOT THE SAME AS "EXPENSIVE"

Four units refused. Every one of them refused because its BAND straddles, never because its
delta exceeds: the largest positive delta in the whole table is `@residue` at **+90 ms
against a budget of 2,193**, and three of the four refusing units have **negative** point
estimates. The two modules the commit actually EDITS — `X86.Syntax`, where the constructors
live, and `X86.Semantics`, where the rule does — are both **decided `ok`**, and both read
NEGATIVE.

⭐ And the unit where the inherited hazard would have appeared if it applied is
`X86.Theorems`, the module holding the frame lemmas. It read **-30.0 ms**. The hazard did
not materialise, in the one place it would have shown.

⛔ WHAT THIS RUN DOES NOT SAY. It does not say the commit is under budget on those four
units; a band that straddles is a statement about the run. It is not quoted as a pass, the
allowance was not widened to make it one, and the design decision below rests on the two
DECIDED units plus the sign of the third, not on the refusals.

⚠️ AND THE BOX CANNOT BE QUIETED INTO AGREEING. Loads during the passes ran 9.28–18.66 on
14 cpus, and most of that is the profiling build itself saturating the machine. "Wait for a
quiet box" is not available to an instrument whose own measurement is the load — which is
why the tool's first suggestion is repeats, and why the standing order is to RE-RUN a
refusal rather than wait on one. A second run at 5 repeats a side was taken for exactly that
reason.

⇒ **THE DESIGN DECISION: arm A, the two-field constructors. The duplicated-rule fallback is
NOT taken.** Nothing in the measurement priced it dear, and the fallback's cost — two more
constructors and a second copy of a rule that must agree with the first — is the shape this
repository has repeatedly recorded as a drift waiting to happen.

### 3b. ⭐⭐⭐ THE RE-RUN, AND WHAT IT SAYS ABOUT THE INSTRUMENT RATHER THAN THE COMMIT

The standing order is to RE-RUN a refusing `kernel_delta` before waiting for a quiet box.
Obeyed here at 5 repeats a side, same two revs, same box, forty minutes later:

```
  UNIT                                  run 1 (3 reps)          run 2 (5 reps)
  Tests.Coverage @decl vectorCoverage   ±1689.2  UNMEASURABLE   ±51.6    ok
  Tests.Coverage @residue               ±2900.7  UNMEASURABLE   ±2239.3  ok
  X86.Theorems                          ±263.8   UNMEASURABLE   ±48.8    ok
  X86.Value                             ±15.3    UNMEASURABLE   ±2.1     ok
  Tests.Coverage @decl memDestSweep     ±105.0   ok             ±1244.4  UNMEASURABLE
```

**Every unit that refused in run 1 passes in run 2, and the ONE unit run 1 decided is the
only one run 2 refuses.** The two refusing sets are disjoint. Nothing about the commit
changed between them — the revs were pinned — and nothing about the box changed that was
under anyone's control.

⇒ 🔑 **A REFUSAL IS NOT A PROPERTY OF THE UNIT ANY MORE THAN OF THE BOX.** The bank already
recorded that the BAND is not a property of the box (one unit moved 20× in a day off an
identical base). This is the next term in the same law: which units refuse is re-rolled every
run, so "unit X is the noisy one" is a sentence about a run, and a plan built on it —
tightening X, excluding X, buying repeats *for X* — is aimed at last night's dice.

⛔⛔ AND THE TOOL'S OWN REPEAT PROJECTION IS PART OF THE SAME PROBLEM. Run 1 told me
`vectorCoverage` needed **~64 repeats a side** to decide. **Five decided it**, with a band 33×
smaller. In the other direction `memDestSweep`, decided at three repeats, now claims to need
29. The projection is a `1/sqrt(n)` extrapolation from the single run's own band — so it
inherits exactly the instability it is being used to plan around, and it always names a
price. ⇒ **A PROJECTION COMPUTED FROM AN UNSTABLE ESTIMATE IS NOT A PLAN, IT IS THAT ESTIMATE
WEARING A UNIT OF WORK.** Quoting "~64 repeats" as a reason to give up on a unit would have
been the cheapest possible way to abandon a measurement that in fact cost one more run.
[[feedback-a-projection-with-no-floor-always-names-a-price]]
[[feedback-a-single-reading-is-about-its-run]]

⭐ WHAT THE TWO RUNS SAY TOGETHER ABOUT THE COMMIT, WHICH IS THE QUESTION THEY WERE ASKED:
across both, **every one of the 22 units has been read `ok` in at least one run**, no unit
produced a delta near its budget in either, and the largest positive delta anywhere in either
table is +90 ms against a 2,193 ms budget. That is as strong as this instrument gets, and it
is stated as two runs rather than as one pass.

### 4. K DECIDED THE SEMANTICS, AND IT CONFIRMED THE DESIGN'S LOAD-BEARING CLAIM

`vendor/k-x86-64` carries all eight forms of the group. Decoding its 256-bit parent
(MSB-indexed `extractMInt`, so `[128,192)` is the xmm HIGH quadword and `[192,256)` the low):

```
  movlps/movlpd xmm,m64   parent[0,192) ++ Mem64                    LOW  written, high preserved
  movhps/movhpd xmm,m64   parent[0,128) ++ Mem64 ++ parent[192,256) HIGH written, low  preserved
  movlps/movlpd m64,xmm   stores parent[192,256)                    the LOW  quadword
  movhps/movhpd m64,xmm   stores parent[128,192)                    the HIGH quadword
  movhlps R1,R2   R2[0,192) ++ R1[128,192)      dst LOW  <- src HIGH, dst high preserved
  movlhps R1,R2   R2[0,128) ++ R1[192,256) ++ R2[192,256)  dst HIGH <- src LOW, dst low preserved
  movddup R1,R2   R2[0,128) ++ R1[192,256) ++ R1[192,256)  BOTH halves <- src's LOW
```

⭐⭐ The `ps` and `pd` members are **bit-identical in all four positions**. That is the
entire justification for `VQuadKind` being a KIND rather than a pair of constructors, and it
is now MEASURED on a third source rather than asserted from the prefix rule. It also
re-confirms the inherited batch-20 `movhps` rule against a source **batch 20 did not use** —
batch 20 cited the SDM and the oracle.
⚠️ NO DIFFERENTIAL VECTOR CAN SEE THIS CLAIM, because no vector tests a spelling against its
sibling. It is batch 19's `.andps`-routed-to-OR shape and it belongs in a THEOREM, which is
step 2's work and is named in the queue there.

⚠️ AND THE `.lo`/`.pd` BRANCHES ARE WRITTEN BUT NOT WITNESSED. No vector in `abe83b8`
reaches them. They are confirmed by K, which is a reading; they become tested when step 2
adds the vectors. An unreached branch is not a gated branch.
[[feedback-an-implied-assertion-is-not-a-second-gate]]

### 5. THREE DEFECTS OF MINE, AND THE FIRST IS A FAMILY RATHER THAN AN INCIDENT

1. **`kernel_delta.py --help` is not a help flag — it started a real measurement.** This is
   the previous head's `ci_local.py --help` defect (its §5.4) in a sibling script, one seat
   later. Two scripts now share the shape, so it is a FAMILY: this repository's tools parse
   `sys.argv` for their own flags and treat everything else as "run". I killed it, verified
   the tree clean and nothing detached, and read the CLI out of `main()` instead.
   ⇒ 🔑 **NAMING A DEFECT IS NOT SWEEPING FOR ITS SIBLINGS**, and the sweep that was owed
   here was owed to a note that had already been written.
   [[feedback-naming-a-defect-is-not-finding-its-siblings]]
2. **I recomputed the batch's demand with a second rule and got six wrong numbers.** Summing
   `miss_all` over all ten census columns read `movhlps` 1,661 where the queue says 1,341,
   and five more the same way. The queue is RIGHT: `p2_roster.demand()` pools only columns
   whose declared class is `asm`, *"never with the compiler columns, and never with the
   kernel"*. Excluding the three compiler columns reproduces all six figures exactly. This
   is the D143 `probe_bucket` shape — a second filter sharing a tool's PURPOSE and not its
   RULE — and I wrote it one step after reading the previous head's §4 warning about writing
   exactly that. ⛔ The tell was there and I nearly walked past it: `movhps` read **0**, and
   a mnemonic with 3,672 instructions of demand reading zero is either a broken probe or a
   fact — here it was a fact (`miss_all` is UNCOVERED demand, and `movhps` is built), but it
   was the thing that made me check the rule. [[feedback-two-readings-are-not-two-witnesses]]
3. **A wrapper's exit code masked the tool's.** The background job reported *"completed
   (exit code 0)"* while `kernel_delta` had returned **3**: my command ended in a `tail`, and
   a compound command exits with its LAST member. The rc was only visible because the same
   line had appended `echo "rc=$?"` to the log. ⇒ a run whose verdict lives in a return code
   must capture that code AT the call, or the notification reports the formatting step.

### 5b. ⛔⛔ THE EXIT-CODE DEFECT RECURRED A THIRD TIME AND IS NOW A FLEET ITEM

§5.3 above recorded a wrapper's exit code masking the tool's. **It happened again two hours
later**, reading `rc=0` from `check_readme_snapshot.py | tail -4` while the script was printing a
red — and it had ALREADY happened at this seat's boot, where `timeout 300 python3
scripts/kernel_cost.py --post-flight` died with `timeout: command not found` (macOS has no
`timeout`; it is `gtimeout`). Three in one session, at one seat.

The helm hit the identical `timeout` defect independently the same night and called it the fourth
instance fleet-wide; on this seat's correction the count went to **seven**, and jas added an eighth
from a third tool within the hour. It is promoted out of the starved-instrument class into its own
07:41 pack item, split into two carriers: **(a) the SUBJECT is wrong** and **(b) THE EXIT CODE IS
NOT THE ONE YOU WANT.**

⇒ 🔑 **THE REASON IT KEEPS HAPPENING IS THAT THE WRAPPER IS WRITTEN FOR READABILITY.** `timeout`,
`| tail`, `| head` are all added to make output legible, and every one of them becomes a NEW LAST
COMMAND — so the formatting step silently becomes the thing whose status is reported. Vigilance is
not the fix; the fix is mechanical: `cmd > log 2>&1; rc=$?` **before** anything is piped anywhere,
or `set -o pipefail`, and never an `echo` between a command and the `$?` that is supposed to be its.
⛔ `| head` is the worst of the three, because this repository has already recorded it TRUNCATING a
probe's input and producing a refutation of a design that was fine.

### 5c. ⭐⭐ A STALENESS GATE THAT PASSED BECAUSE BOTH ITS INPUTS WERE STALE

`ci_local` step **12** (the census staleness check) went **✔** on the run where step **32** (*"the
coverage table is GENERATED, not written"*) went **⛔**. On the next run, with nothing about the
census changed, step 12 **failed**: *"generated against a model of 146 mnemonics … it is now 152."*

The cause is not a bug in either gate. `demand_census.py` reads the model set **from
`docs/COVERAGE.md`** — its own comment says so, *"read from the GENERATED coverage table"* — and
`docs/COVERAGE.md` is itself a generated artifact whose freshness is what step 32 checks. On the
first run both were stale in the same direction, **so they agreed, and agreement is what this gate
reports as fresh.** Regenerating the coverage table is what made the census's staleness visible.

⇒ 🔑 **A STALENESS GATE IS ONLY AS FRESH AS THE ARTIFACT IT READS THE TRUTH FROM, AND HERE THAT
ARTIFACT'S OWN FRESHNESS IS CHECKED TWENTY STEPS LATER IN THE SAME SUITE.** Step 12 issues a verdict
whose precondition step 32 has not yet established. Across runs the suite self-corrects — the next
run catches it, which is exactly what happened — but **within a run the ✔ is about a stale input**,
and a reader who saw `12 ✔ / 32 ⛔` would reasonably conclude the census was fine and only the table
needed regenerating. Both needed it.

⚠️ THE CHEAP REPAIR IS ORDERING, NOT LOGIC: any gate that derives truth from a generated artifact
must run AFTER the gate that proves that artifact current. The alternative — having `demand_census`
read `rosterP0` from the Lean source rather than from the rendered table — trades one derived input
for a second route to the same list, which is the duplicate-born-in-agreement shape this repository
declines elsewhere. Ordering is the honest fix.
[[feedback-a-staleness-stamp-hashes-only-one-half]] [[feedback-two-defects-that-cancel]]
[[feedback-a-gate-behind-a-failing-step-is-silent]]

### 5d. ⛔ `TaskStop` SKIPS A TOOL'S CLEANUP, AND kernel_delta LEAKS TWO WORKTREES PER KILL

`kernel_delta.measure()` creates two detached worktrees and removes them in a `finally`. Killing
the process — which is what a harness `TaskStop` does — never runs that block, so **each killed run
leaves two worktrees registered in `git worktree list` and two trees on disk.**

Found by counting rather than by noticing: `git worktree list` showed three `x86lean-delta-*`
PAIRS while only one run was live. The live one was `base e6dd9c6 → head 5c18c59` (this batch's
merge gate). Of the other two, `base 9aaf7e7 → head e6dd9c6` is **exactly the pair the accidental
`--help` run would have built** before I stopped it (§5.1), so that leak is mine; the third pair
names commits from an earlier session and predates this seat.

⇒ 🔑 **A `finally` IS NOT A CLEANUP GUARANTEE WHEN THE PROCESS CAN BE KILLED FROM OUTSIDE.** The
cost here is small and bounded — stale worktree registrations and disk — but the shape is not: a
tool whose only cleanup path is in-process leaves its garbage precisely on the runs that went
wrong, which are the runs a successor is most likely to be re-doing. **A killed run is the normal
case for a long measurement, not the exception**, so the sweep belongs at the START of the next
run — `git worktree prune` plus a removal of any `x86lean-delta-*` this repo still lists — not only
at the end of a run that may not reach its end.
⚠️ AND THE SWEEP MUST NOT TOUCH A LIVE PAIR: the discriminator is the (base, head) revs, which name
what a run is measuring, so a cleanup keyed on directory age alone would kill a slow live run.

### 5e. ⭐⭐⭐ THE MERGE GATE, IN THREE DRAWS — AND THE THIRD INSTANCE OF THE RE-ROLL LAW

`kernel_delta --base master --head 5c18c59 --repeats 5`, three times over the same PINNED revs:

```
  unit                                  draw 1            draw 2            draw 3
  Tests.Anchors                         +98  ±80.9  UNM   +29  ±190.7 UNM   +3.0 ±39.4  ok
  Tests.Coverage @decl vectorCoverage   +130 ±859.8 UNM   +100 ±56.9  ok    +70  ±680.9 UNM
  X86.Syntax                            +12  ±24.5  ok    +18  ±93.6  UNM   +19  ±21.1  ok
  X86.Theorems                          +40  ±94.4  ok    +60  ±203.1 UNM   +29  ±68.5  ok
  X86.Basic / X86.State / X86.Value     ok                UNM               ok
  loads during the passes               9-16              17-22             9-14
  units refusing                        2 of 23           6 of 23           1 of 23
```

**EVERY UNIT HAS READ `ok` IN AT LEAST ONE DRAW, AND NO UNIT EXCEEDED ITS BUDGET IN ANY DRAW.** The
gate never returned rc 1. That is the merge case, and it is stated as three draws rather than
laundered into one pass — three `UNMEASURABLE` results do not add up to a verdict, but a unit that
reads `ok` on a quiet box and refuses on a loud one has been measured.

⭐ **`Tests.Anchors` IS THE WHOLE ARGUMENT FOR HAVING RE-RUN.** Draw 1 put it at **+98 against a
125.6 budget — 75% of its allowance, the tightest margin in the table**, and it is a module this
batch does not edit. Had I landed on one draw I would have recorded a near-miss that wanted
watching. Three draws read **+98 → +29 → +3.0**: it converges to zero and the first reading was
noise. ⇒ **A MARGIN IS A READING TOO**, and the number that most deserves a second draw is not the
one that refuses loudest but the one that passes — or nearly fails — narrowest.
[[feedback-a-pass-at-97-percent-is-not-headroom]]

⛔ **AND THE RE-ROLL LAW NOW HAS THREE INDEPENDENT INSTANCES IN ONE SESSION** (§3b's two, plus these
three draws). Draw 2 ran on a box at load 17-22 and refused **six** units; draw 3 at load 9-14
refused **one**, and it was not one of draw 1's two. The refusing SET tracks the box at the minute
of the run, not the commit and not the unit. ⇒ the operational rule stands and is now cheap to
state: **re-run before doing anything else, and never plan around `repeats_to_decide`** — across
five draws tonight it was wrong in both directions every time it was checkable.

⭐ WHAT THE THREE DRAWS SAY ABOUT THE BATCH ITSELF, WHICH IS WHAT THEY WERE ASKED: `X86.Syntax`
**+12 / +18 / +19** against a 47.1 budget. Step 1 isolated the two FIELDS at **−5.0** on that same
unit, so the ~+15 ms is the three new CONSTRUCTORS and not the fields — a decomposition that exists
only because the field change was committed separately, which is what QUEUE 2b's "price it first"
order actually bought.

### 6. A THIRD MEASUREMENT OF THE ENCODING TABLE, UNASKED FOR AND FREE

QUEUE 2b's table was measured twice. Assembling the fifteen forms step 2 needs with
`clang -target x86_64-unknown-linux-gnu` and disassembling makes a third, and it agrees
exactly. LLVM's own operand comments carry the semantics as well — `movhlps: xmm0 =
xmm1[1],xmm0[1]`, `movlhps: xmm0 = xmm0[0],xmm1[0]`, `movddup: xmm0 = xmm1[0,0]` — which is
a fourth witness to the half-selection rules, from the assembler rather than from K or the
SDM.

## D161 — QUEUE 4g(a): the drift ledger's fixed point removed by re-keying, my own safeguard refuted, and the NEXT blocker named at the object

D159 recorded that `--record` has a fixed point: the ledger is TRACKED, so writing step N's row is
itself a commit, and that commit is a first-parent step needing a row. Three candidate escapes were
listed and none taken. The helm's 05:33 audit added an observation — that a row keyed to the DIFF
rather than to the produced commit would not have the fixed point — and left the call here.

### 1. THE READ, AND IT SAYS MORE THAN THE OBSERVATION ASSUMED

Every budget in `kernel_delta_budget.txt` is a PERCENTAGE (22 of 22; `@floor` is the only absolute),
and the file's own prose says *"a step's allowance depends on the tree that step STARTED FROM"* and
*"the per-batch gate already computed each step's allowance when that step merged, against exactly
THAT STEP'S OWN BASE."* `--record`'s implementation agrees: it derives the row's `allowance` from
`data["readings"]["base"]` alone, and uses `head_rev` only to fill a field.

⇒ **`allowance(step N) = f(parent tree, budget registry)`, and BOTH inputs exist before the child
is made.** The fixed point was never in the data. It was in the KEY — `(base, head)` names the sha
the step produces. `--first-parent` makes `base → head` a function on the walked chain, so `base`
identifies the step by itself.

**The repair, in full:** `key = (r["base"], r["head"])` → `key = r["base"]` in `load_ledger` and
`append_rows`; index by `s[0]` in `accumulated_allowance`; `head` stays in the row as audit-only,
beside `base_ms`, which is where it belonged. All 11 committed rows load unchanged under the new
key.

### 2. ⛔ AND MY OWN SAFEGUARD WAS REFUTED BY THE FACT THAT MOTIVATED IT

I posted a refusal clause with it: *"a re-cut branch can give one base two children, and a gate
that silently picked either would be pricing one step with another's allowance."* **That is false.**
Two children of one base are priced from the SAME tree, so their allowances are **identical** and
either row sums the window correctly. I reasoned about the key's uniqueness while holding the very
fact — allowance is a function of the base — that made the collision harmless, and failed to carry
it three sentences.

⇒ 🔑 **A SAFEGUARD ADDED FOR A COLLISION IS A CLAIM ABOUT WHAT THE COLLISION WOULD COST, AND THAT
CLAIM IS SEPARATELY CHECKABLE.** Mine cost nothing. Worse, a blanket refusal on a duplicate `base`
would have been actively wrong: it would reject the benign same-night case. What genuinely differs
between two rows for one base is the NIGHT `base_ms` was measured, and `load_ledger`'s existing fork
check has always caught exactly that — its own message reads *"Two readings of the same step are two
nights, not two witnesses."* **The rule needed no change at all.**
[[feedback-a-remedy-is-an-ungated-claim]] [[feedback-a-state-added-for-a-defect]]

### 3. DRIVEN RED, NOT ASSERTED

`--selftest`: **18 arms, 18 green, 10 DISTINCT arms caught a plant** — including `missing step`,
`foreign registry`, `partial pricing` and `write-before-check`, so the refusal paths survive the
re-key. ⚠️ Every fixture was updated to the new contract (keyed by the step's base) rather than the
lookup being relaxed to accept either shape: an "accepts both" reader cannot see the next silent
change, which is the rule `lib-liveness`'s arity arm was repaired to elsewhere in the fleet.
And the fork check was driven red on the REAL ledger — a planted twelfth row, same base, doubled
allowance — which refuses rc 2 naming both rows and their nights.

### 4. ⛔⛔ THE NEXT BLOCKER, WHICH IS NOT THE KEY AND IS BIGGER THAN IT

The fixed point is gone; the ledger is still unwritable in practice, for a reason the key change
does not touch. **The ledger wants one row per first-parent COMMIT. The gate that produces
allowances measures one delta per BATCH**, and a batch is not one commit — batch 36 landed as
FIVE, deliberately unsquashed so that D160's price decomposition survives in history. So a merge
gate run over `master → head` yields ONE row spanning five steps, and the window walk then reports
four of them missing.

⇒ **THE UNIT OF THE LEDGER AND THE UNIT OF THE MEASUREMENT DISAGREE**, and squashing to reconcile
them (batch 35's route) pays for it by destroying exactly the per-commit history that made batch
36's price auditable. ⭐ **The clean answer is neither: land batches with `--no-ff`.** A merge
commit is exactly ONE first-parent step per batch while preserving every individual commit on the
branch — the ledger gets one row per batch, and the decomposition survives. Batch 36 was merged
fast-forward, so it is five steps; that was the wrong call for this gate and is the first thing to
change about the landing ritual.

### 5. THE COMPOUNDING, MEASURED A THIRD TIME BY THE THING CAUSING IT

D159 recorded the gap at **40** commits (03:27). The helm measured **43** (05:3x) and named the
class: an instrument that degrades monotonically with the work it watches. After batch 36 it is
**48** — and five of those five are mine, landed in the same session that read the warning.
⇒ the backfill that pays for this grows with every landing, so the cheapest moment to record a row
is always the merge it belongs to, and always was.

## D162 — the derivation gate D161 broke, why nothing said so, and the arm that now would

D161 re-keyed the drift ledger from `(base, head)` to `base` and its record reads *"All 11 committed
rows load unchanged"*, *"selftest 18/18, 10 distinct plants"*, *"`ci_local` CLEAN 33/33 after the
change"*. **Every one of those sentences is true.** Master still shipped a red gate for four hours.

### 1. THE OBJECT

`kernel_drift.py --verify-ledger docs/kernel-delta-history-2026-09-04.jsonl` is a CI step
(`.github/workflows/ci.yml:527`). At master `eb14280` it returned **rc 2, 22 discrepancies**:

```
   144e9a3cf→4f6766b9b  ABSENT from the ledger        ← x11, every step of the walk
   3→2   in the ledger under backfill:… but not a step of that walk    ← x11
```

`want` was built keyed on `(order[i], order[i+1])` — a TUPLE — and joined against
`load_ledger`'s output, which D161 re-keyed to a bare `base` STRING. No key ever matched, so all 11
derived steps read ABSENT and all 11 stored rows read surplus. The `3→2` renders `key[0][:9]` and
`key[1][:9]` of a *string*: characters 0 and 1 of a sha. **The gate could not have passed on any
input.**

⭐ **CAUSE PINNED AT THE OBJECT, NOT INFERRED.** Same command, same ledger, two worktrees:

```
  f46de06  (D161's parent)   rc 0   ✅ 11 steps x 23 units = 253 allowances re-derived
  e39abc2  (D161 itself)     rc 2   ⛔ 22 discrepancies
```

### 2. ⛔⛔ WHY THREE GREEN RECEIPTS ALL MISSED IT, AND THE TWO REASONS ARE DIFFERENT

**(a) `ci_local` RUNS ONE JOB OF FOUR.** `ci_local.py` defaults to `--job build` — 33 steps, hence
"33/33". The drift gate and its ledger derivation live in the **`kernel-delta`** job. `ci_local`
parses `ci.yml` precisely so its STEP list cannot go stale, and its own docstring warns that the
per-batch discipline runs *"a SUBSET of this workflow"*. That warning is about steps. The same
defect sits one level up in JOBS, unstated, and "33/33" reads as a whole-workflow receipt because
the denominator is the only number in it.
⇒ 🔑 **A COMPLETE COUNT OF A SUBSET IS INDISTINGUISHABLE FROM A COMPLETE COUNT.** `n/n` says the
list was finished; it never says what the list was.
*(Measured, so the shape is on the record: `build` 33 · `selftest` 2 · `kernel-delta` 7 ·
`kernel-delta-redfirst` 1. Six of the seven `kernel-delta` steps are pure-python and take seconds.)*

**(b) THE GATE HAD NO CALLABLE SURFACE.** `--verify-ledger` was an inline block inside `main()`.
A selftest calls functions; there was no function. So the 18 arms sat beside it, green about the
ARITHMETIC, reading as though they were green about the FILE.
⇒ 🔑 **A GATE WITH NO CALLABLE SURFACE CANNOT BE ARMED**, and an unarmed gate's neighbours lend it
their green.

### 3. THE REPAIR IS THE EXTRACTION, AND ITS PROOF IS A PLANT

`verify_ledger(want, ledger, tag, digest)` is now a function; `main()` builds `want` as
`{base: (head, allowances)}` — the shape `load_ledger` actually produces — and delegates. Section
**B2** of the selftest, 8 arms, control first:

* ⭐ **every ledger in it is written with `append_rows` and read back with `load_ledger`** — the
  shipped producer and consumer — so the key shape under test comes from the ARTIFACT, never from
  the test's own hand. A section that built its dict directly would have adopted whatever key D161
  chose and agreed with the bug. [[feedback-a-duplicate-born-in-agreement]]
* the plants: an edited allowance · a missing step · a surplus row under the same tag · a foreign
  budget registry · **a rotted `head`** — the field D161 demoted to audit-only, hence the field
  nothing else would report rotting.
* ⛔ **and the load-bearing negative control**: a `source="gate"` row beside the backfill is
  INVISIBLE to this gate, with its positive control (the same row re-tagged IS caught). Without
  that arm the ledger could hold backfilled rows or live rows but never both — which would make the
  landing ritual and the 48-commit backfill mutually exclusive.

**DRIVEN RED ON THE REAL DEFECT.** `load_ledger`/`append_rows` re-keyed back to the pre-D161 tuple:
selftest **rc 1, five B2 arms fire, control first**. Restored: **26 arms, 26 green, 16 distinct
plants** (was 18 / 10). ⭐ **Under that plant the eighteen pre-existing arms stayed GREEN** — the
measurement of how blind the old selftest was to this class, rather than a claim about it.

### 4. WHAT THIS COSTS THE ORDER IT INTERRUPTED

The relight order was to land the next batch `--no-ff` and write the ledger's first LIVE row. That
row would have gone into a ledger whose derivation gate was red, under a receipt that would not have
looked at it. The order is unchanged; it is one gate less blind.
[[feedback-a-gate-behind-a-failing-step-is-silent]] [[feedback-verify-what-the-build-command-builds]]
[[feedback-a-gate-is-not-exempt-from-its-own-defect]]

### 5. THE SCOPE REPAIR IN `ci_local`, AND A SIBLING FOUND ONE LINE AWAY

`ci_local.py` now parses the workflow's JOB list the same way it already parsed its STEP list, and
every receipt carries what it left out:

```
ci_local: CLEAN (6 of 7 steps of CI job 'kernel-delta' RAN, steps 1-6 of 7 selected by --from/--to)
⚠️  SCOPE: this ran CI job 'kernel-delta' ONLY. The workflow has 4 jobs; NOT RUN here:
    build (33 steps), selftest (2 steps), kernel-delta-redfirst (1 steps).
```
An unknown `--job` now refuses and names the four. `--jobs` lists them with their step counts.

⛔ **AND THE SAME CLASS WAS SITTING ONE LINE BELOW.** `--from 99` ran ZERO steps and printed
`CLEAN (7 steps of CI job 'kernel-delta')` — the number was the length of the LIST, not of what
executed, which is the identical substitution as `33/33` for the workflow. It now refuses when the
selection is empty, and a partial run says which steps it selected. **Found by grepping the file I
was already editing for the shape I had just named**, not by a second sitting.
[[feedback-naming-a-defect-is-not-finding-its-siblings]] [[feedback-read-what-the-instrument-measured]]

⭐ **`--to N` ADDED, AND IT IS WHAT MAKES THE NEW DISCIPLINE TYPEABLE.** `kernel-delta` is six
pure-python gates (seconds, all six green here) and one full two-tree profiling run — the merge
gate. Without a way to name the cheap prefix, *"run the drift gates before merging"* is advice
nobody can execute, and `python3 scripts/ci_local.py --job kernel-delta --to 6` now is that command.
[[feedback-make-the-probe-cheap]]

⚠️ **WHAT IS STILL NOT GATED**: nothing makes a head RUN the other three jobs. This turns a silent
subset into a stated one; it does not turn one command into four. The `selftest` job (~2h15m sharded
six ways) and `kernel-delta-redfirst` (four builds) are priced out of a per-batch ritual, and saying
so beside the receipt is the whole of what changed. [[feedback-a-gate-whose-precondition-is-a-discipline]]

## D163 — the post-flight probe answered an adjacent question, and 293 MB were sitting in the gap

`kernel_cost.py --post-flight` is what a head runs at boot and at exit to ask *"did I leave anything
behind?"*. It printed, all session:

```
   0 ppid-1 process(es) in my trees · 0 build(s) in other trees · NOTHING WAS KILLED
✅ nothing of mine is running detached.
```

**True, and answering a narrower question than the one being asked.** `git worktree list` at the same
moment showed FIVE checkouts registered to this repository beyond the main one:

```
  /private/tmp/x86ci                                    f45aa6c   149 MB   (the batch-12 era)
  …/T/x86lean-delta-6inj80fs/{base,head}   e39abc2/eb14280    51 MB
  …/T/x86lean-delta-p3yvdbuv/{base,head}   e39abc2/eb14280    93 MB
                                                              ─────
                                                              293 MB
```

`kernel_delta.measure()` adds two detached worktrees per run and removes them on the way out; a run
that is **killed** never gets there, and a timing run is the longest thing a seat starts, so it is
the likeliest thing to be killed. Four of the five above are mine, from two `kernel-delta` jobs I
stopped this session. The fifth is not new.

⛔⛔ **AND IT WAS FILED AS HOUSEKEEPING ONCE ALREADY.** `docs/DIFFERENTIAL-P2-BATCH19.md:221` records
the identical finding — *"two full checkouts left behind by an EARLIER delta run … plus
`/private/tmp/x86ci`"* — under the heading *"Housekeeping, not a complaint"*. That was 17 batches
ago. `/private/tmp/x86ci` is still there in the list above.
⇒ 🔑 **A LEAK FILED AS HOUSEKEEPING IS A LEAK NOBODY OWNS.** Naming it in a batch record puts it
where nothing re-reads; the only durable place for it is the probe a head runs anyway.

### THE REPAIR, AND WHAT IT DELIBERATELY DOES NOT DO
`stale_worktrees()` beside `repo_orphans()` and `foreign_builds()`; `post_flight` returns **1** when
either half is non-empty, and the ✅ line now says *"and no worktree of mine is registered beyond the
main checkout"*. It **reports and never removes**, for the same measured reason the process half
never kills: **a live `kernel_delta` legitimately holds two of these**, and this probe cannot tell a
live measurement from a killed one's leavings any more than `ppid 1` can tell a wanted background
job from a stranded one. It names the ambiguity and prints the per-path command.
⚠️ It also prints `(DIRECTORY GONE)`, because that is the only case `git worktree prune` alone would
clear — and the usual case is the other one, where the disk is still occupied.

### THE ARMS (3h), CONTROL FIRST
```
  CONTROL   stale_worktrees() = []              post_flight rc=0
  PLANT     a registered extra worktree         FOUND by path, rc=1, line names it
  PLANT     a registration whose DIRECTORY IS GONE   flagged `exists=False`
  RESTORE   removed and pruned                  rc=0, stale_worktrees() = []
```
⭐ The second plant exists because the first shares the real leak's dimension — both sit under
`$TMPDIR` — and the report has a branch (`DIRECTORY GONE`) that no input would otherwise reach.
[[feedback-a-control-can-share-the-blind-spot]] [[feedback-an-implied-assertion-is-not-a-second-gate]]
⭐ The RESTORE is itself an arm: a selftest that left its plant registered would make every later run
report the plant as a finding — the gate manufacturing the leak it was written to catch.

## D164 — QUEUE 4g(b): the `--no-ff` ritual proven with its control, and the gate that makes it survive being forgotten

4g(b) was handed on as *"ONE FLAG"*: merge batches with `--no-ff` so the ledger's unit (a
first-parent commit) matches the gate's unit (a batch). The flag is right. It is not the whole
repair, and two things had to be measured before a batch rode on it.

### 1. ⭐ THE DEFECT, MEASURED RATHER THAN RESTATED
Batch 36's merge gate measured the span `e6dd9c6 → 5c18c59` and paid for **three draws** of it. That
span, fast-forwarded, became **four** first-parent steps:
```
   abe83b8  BATCH 36 step 1 of 2: the half-move FIELD CHANGE
   579dbd3  BATCH 36 step 2 of 2: the six half-moves
   c10382b  tail: the census regenerated
   5c18c59  tail: the P2 roster re-derived
```
⇒ **three paid measurements can price ONE of the four steps they cover** — the row is keyed at the
base, and the base of steps 2-4 was never measured. That is the unit mismatch, in units.

### 2. ⭐⭐ THE RITUAL, REHEARSED END TO END ON A THROWAWAY BRANCH, WITH ITS NEGATIVE CONTROL
⛔ Rehearsed rather than reasoned about, because D161 removed the fixed point *in the key* and the
question that decides the ritual is a different one: **the ledger is a tracked file, so does writing
the row need a commit of its own?** It does not — and that is what `--no-ff --no-commit` buys:

```
  git merge --no-ff --no-commit <branch>
  python3 scripts/kernel_drift.py --record --readings <merge-gate json>
  git add docs/delta-allowance-ledger.jsonl && git commit
```
The row rides **inside** the merge commit. Measured on a 2-commit branch off master, with real
batch-36 draw-3 readings relabelled to the rehearsal:
```
  WINDOW  79bb658 → 28746fd   ⇒ 1 first-parent step        (was: 2 commits)
  LEDGER  12 rows; the live one keyed 79bb658, source=gate
  ✅ ACCUMULATED over 1 step: 23 units priced, 0 unpriced, NO missing step
  ✅ CONTROL — with that one row deleted the SAME walk refuses rc 2
```
⛔ The control is the half that matters: without it, "the walk found no missing step" is equally
consistent with a walk that never checks. And the 12 rows confirm on the real ledger what the new
B2 arm predicts — **a `source=gate` row and the eleven `backfill:` rows coexist**, so the ritual and
the backfill are not mutually exclusive.

### 3. ⛔⛔ AND THE FLAG IS A DISCIPLINE, WHICH IS THE FAILURE MODE THIS REPOSITORY KEEPS RE-LEARNING
Fast-forwarding costs nothing visible: tests pass, the merge gate passes, the bank reads clean. The
only instrument that would report the new hole is the drift gate — **which the hole disables**. The
head who wrote *"the fix is `--no-ff`"* had fast-forwarded batch 36 four commits earlier in the same
session. A paragraph in the queue will not survive that.
[[feedback-a-gate-whose-precondition-is-a-discipline]]

**`kernel_drift.py --gap` + `docs/drift-gap-ratchet.txt`.** It judges no kernel time; it judges
whether the ledger is still being kept.

### 4. ⭐⭐⭐ AND MEASURING IT RE-PRICED THE BACKFILL BY 10×
The inherited number was *"the gap is 48 commits and grows with every landing"*, which prices the
backfill at ~50 profiling runs — hours, and the reason item 3 kept being deferred. It is **51 steps
at `79bb658`, and they are three populations**:
```
    5  change a `.lean` file       ⇐ batches 23, 34, 35, 36a, 36b. A REAL measurement each.
    5  change no `.lean` but DO change scripts/kernel_cost.py or the budget registry
                                   ⇐ these move the READING or the ALLOWANCE without moving
                                     the code, so "nothing to price" is FALSE for them.
   41  change none of the above    ⇐ an exemption CANDIDATE, and nothing in the tool treats
                                     it as zero.
```
⇒ 🔑 **A TOTAL CANNOT SEE ITS PARTS.** The backfill is **five** profiling runs plus a written
argument, not fifty. ⛔ And the second bucket is the one that would have been assumed away: the
obvious exemption is *"no `.lean` change ⇒ no kernel delta"*, and it is wrong for exactly those five
— which is why the tool prints three numbers and exempts none of them.
[[feedback-a-total-cannot-see-its-parts]] [[feedback-the-burden-is-on-the-departure]]
[[feedback-a-category-is-a-hypothesis-about-its-members]]

### 5. WHY THE GATE IS ON ONE BUCKET, AND WHY BOTH DIRECTIONS REFUSE
Gated: the `.lean` count. **That is the quantity ordinary work does not move** — a docs commit grows
the chain and leaves it alone, so the gate is not a chore; a batch landed without its row raises it
by one and goes red, naming the ritual rather than a wider ceiling.
[[feedback-match-the-gate-units-to-the-growth-law]]

Both directions refuse. A ceiling that only complains upward rots upward: a backfill that removes
four holes would leave a ratchet claiming four holes that are gone, and **the next unrecorded
landing hides inside that slack**. Lowering it is one line in the commit that earned it.
[[feedback-under-claims-are-unpoliced]]

### 6. THE ARMS (B3), AND ONE OF THEM IS D162 APPLIED TO ITSELF
⛔ `read_ratchet` and `judge_ratchet` are FUNCTIONS, not an inline block in `main()` — writing this
gate the way `--verify-ledger` was written would be the defect surviving the sitting that named it.
```
  CONTROL  the anchor is a step boundary on the walked chain, not a written-down name
  the three buckets PARTITION the steps: 11 recorded + 51 missing = 62   ⇐ an INVARIANT,
     never the literal 51, which the next commit would falsify and someone would EDIT
  a ledger with NO base on the chain REFUSES — a wrong ledger, not an empty gap
  a ledger recording EVERY step empties all three buckets   ⇐ or "5" might be a constant
  deleting ONE row for a `.lean` step puts exactly that step, in that bucket, back
  gap == ceiling silent · gap > ceiling refuses naming the ritual · gap < ceiling ALSO refuses
  an ABSENT ratchet reads None · a written one reads back 7 · a line with NO number is
     UNPARSEABLE, which the caller refuses on rather than treating as absent
```
Selftest: **37 arms, 37 green, 23 distinct plants** (18 / 10 at this session's boot).

## D165 — batch 35's `@residue` +1435: the attribution made from readings already on disk, and the named suspect refuted

Item 4 of the standing order — *"batch 35's `@residue` +1435 ms attribution is STILL UNMADE"* — has
been inherited three times and deferred three times, priced each time as a measurement. **It needed
no measurement.** `kernel_delta`'s saved readings blob already carries `decls[module][name]` for
every declaration the profiler emits, not only the gated ones, and batch 35's blob was on disk.
[[feedback-the-quiet-quantity-was-already-in-the-pass]]

### 1. THE NAMED SUSPECT IS REFUTED AT THE OBJECT
D159 wrote that the +1435 is *"plausibly the §4 gate repair — `vmov_alignment_is_by_kind` now
quantifies over `VMovKind.all` by `cases` rather than four literals"*.

**`vmov_alignment_is_by_kind` does not appear in the `decls` map of ANY of the twelve readings**,
six a side. The profiler emits a declaration only above a **100 ms** threshold (base's smallest
emitted reading is 144 ms, head's is 100 ms), so that theorem costs **under 100 ms on both sides**
and cannot be a 1,435 ms item. The suspect was named from what CHANGED in the batch, which is
where a plausible cause comes from; the readings were never asked.

### 2. THE DECOMPOSITION, WITH ITS IDENTITY CHECKED PER READING
⛔ Buckets computed over ONE shared name set (a declaration absent on a side counts 0), and the
identity `residue == ungated + unemitted` **verified in all twelve readings** before any median was
taken — a split whose parts do not reconstruct the whole is arithmetic the author invented.
```
  bucket                          base       head      delta
  Tests.Coverage TOTAL         25100.0    26700.0    +1600.0
    gated declarations          9305.0     9570.0     +265.0
    @residue                   15715.0    17150.0    +1435.0   ⇐ the number in question
      ungated decls ≥ 100 ms   14286.0    14509.0     +223.0
      in NO declaration block    1360.0     2088.0     +728.0   ⇐ the largest identified part
```
⇒ ⭐⭐ **THE BIGGEST IDENTIFIED COMPONENT IS NOT A DECLARATION AT ALL.** `@residue` is
`module total − gated declarations`, so it contains everything the profiler does not attribute to a
`type checking` block — elaboration, imports, the file's top level. **No per-declaration repair can
reach +728 ms of it**, which is why every attempt to name a theorem was going to fail.

### 3. ⛔ AND THE DECOMPOSITION IS SMALLER THAN THE AGGREGATION CHOICE
```
  median(ungated)Δ + median(unemitted)Δ = +951    vs   median(residue)Δ = +1435
  MEANS, which do sum:  residue +1130 = ungated +414 + unemitted +716
```
Medians do not sum — that is a property of medians, not an error — but **the gap is 484 ms and the
median and mean of the same residue delta differ by 305 ms**. The quantity being attributed is
smaller than the spread between two defensible ways of aggregating it.
⇒ 🔑 **AN ATTRIBUTION IS ONLY AS SHARP AS THE AGGREGATION IT SURVIVES.** Reporting "+1435, of which
+728 is X" would imply a precision the six passes do not carry; the honest statement is that the
residue's growth is **dominated by cost outside every declaration block**, at roughly +700 ms by
both aggregations, and that the rest is not resolvable at this repeat count.
[[feedback-a-single-reading-is-about-its-run]] [[feedback-conservative-is-a-direction-not-a-margin]]

### 4. ⭐ AND AN INSTRUMENT FINDING THAT WILL BITE ANY FUTURE ATTRIBUTION
Three declarations appear at head and not at base, worth 100/131/135 ms — which reads as new work
and is not. They are `cmpxchg_vectors_never_target_the_accumulator`,
`dshift_memory_vectors_at_w_are_immediate_only` and `loop_covers_all_three_predicates`: pre-existing
theorems about `cmpxchg`, `dshift` and `loop`, untouched by a batch about `movapd`/`movupd`. They
**crossed the 100 ms emit threshold**, and they did so in only 1 or 2 of the six head passes:
```
  dshift_memory_vectors_at_w_are_immediate_only   base [-,-,-,-,-,-]   head [160, -, -, -, 102, -]
```
⇒ 🔑 **A THRESHOLDED PROFILER MAKES A DECLARATION'S FIRST CROSSING LOOK LIKE ITS ENTIRE COST
APPEARING FROM NOWHERE**, and near the threshold the crossing is *noise*, not a level. It does not
corrupt the module total, but it moves cost between the decomposition's buckets — so per-declaration
attribution is structurally unreliable for anything within a factor of ~2 of the threshold.

### 5. ⛔⛔ AND THEN THE FREE COMPARISON REFUTED §4's SUCCESSOR HYPOTHESIS — MINE — IN ONE PASS

The paragraph that stood here asked *"is ~+700 ms per batch of non-declaration cost a LEVEL?"* and
priced the answer at zero new measurement, because every saved readings blob is on disk. It was
answered before it was published. **Seven real base→head pairs, the same decomposition:**
```
   base→head                 n     @residueΔ   ungatedΔ   unemittedΔ    unemitted base→head
   5c01599→e090bc2  (b23)   3/3       -60.0       +3.0        -63.0     1220 →  1157
   e6dd9c6→abe83b8  (36a)   3/3       +90.0     -796.0        +12.0     1382 →  1394
   c372d80→3a811fb  (b32)   6/6      +735.0     +631.0        +39.0     1578 →  1617
   e6dd9c6→5c18c59  (b36)   5/5      +600.0     +552.0       -262.0     1792 →  1530
   26eb0b6→73bc95c  (b35)   6/6     +1435.0     +223.0       +728.0     1360 →  2088
   c372d80→9cf72aa          3/3     +3000.0     +484.0      +2668.0     1045 →  3713
```
⇒ **`+728` IS NOT A LEVEL AND IT IS NOT AN ATTRIBUTION — IT IS NOISE.** The bucket's *base* value
is stable across every pair (1,045–1,792 ms). Its *delta* spans **−262 to +2,668**. A bucket whose
pass-to-pass movement is larger than the bucket cannot carry a 728 ms explanation.
⛔ `ungatedΔ` is no better: **−796** on batch 36's step 1, a commit that added two fields.

⇒ 🔑 **THE HONEST VERDICT ON THE WHOLE ITEM: batch 35's `@residue` +1435 CANNOT BE ATTRIBUTED,
AND THE REASON IS NOT A MISSING MEASUREMENT BUT THAT EVERY COMPONENT OF THE RESIDUE MOVES MORE
THAN THE NUMBER BEING EXPLAINED.** Three sittings deferred this as work to be done. It was work
that could not succeed, and one hour of already-paid readings says so.
⚠️ Stated with its conditions: the seven pairs are different nights, loads and repeat counts
(3–6 a side), so the spread above is an upper bound on how well any of them is resolved — which is
the finding, not a caveat against it. [[feedback-a-measurement-without-its-conditions]]

### 6. WHAT ACTUALLY REMAINS
**Not an attribution — a resolution question.** `@residue` is gated at 2,184 ms and its
constituents move ±700–2,700 between runs, so the gate is watching a quantity it cannot resolve.
That is item 4's territory (*"the gated unit is noisier than the budget it is gated against"*),
and this is the first per-COMPONENT evidence for it rather than per-module. ⛔ Do NOT buy repeats:
D153 measured the spread saturating at n≈3–4. The route with a floor is to gate the DECLARATIONS,
where the base values are stable, and stop gating the difference of two large numbers.
[[feedback-a-total-cannot-see-its-parts]] [[feedback-match-the-gate-units-to-the-growth-law]]

## D166 — the null run the landing ritual paid for, and a band set by one pass in ten

QUEUE 4g(b)'s first live ledger row needed a merge-gate measurement, and the branch it measured
changed **no `.lean` file** (`git diff --name-only master c121563 -- '*.lean'` is empty). So the
run is a **null**: the true delta is exactly zero for every unit, known before the readings arrived.
That makes it the most informative run this gate has produced, because it is the only kind where
the answer is known independently of the instrument.

### 1. WHAT THE INSTRUMENT SAID ABOUT A KNOWN ZERO (repeats 5, loads 7.8–15.9)
```
  Tests.Coverage             -400.0  ±4651.2   budget 1922.4   UNMEASURABLE
  Tests.Coverage @residue     +40.0  ±4205.9   budget 2293.5   UNMEASURABLE
  X86.Syntax                   +5.0    ±53.4   budget   47.7   UNMEASURABLE
  Tests.Vectors                +2.4     ±6.0   budget    7.6   UNMEASURABLE
  ...19 other units ok
```
⭐ **Every point estimate is at or near zero — the instrument's ACCURACY is fine.** What fails is
its RESOLUTION: the bands are 2.4× and 1.8× the budgets they are compared against.
⭐ And the gate **refused rather than passing**, which is the right behaviour and worth recording
against D146's control, where an identical-trees run *returned `ok`* while inventing a −2,150 ms
difference against a 1,980 ms budget. A null that refuses is a better instrument than a null that
passes. ⚠️ D146's run was not re-executed here, so this compares two records, not two runs.

### 2. ⭐⭐ THE BAND IS SET BY ONE PASS IN TEN, AND THAT IS MEASURED, NOT EYEBALLED
Leave-one-out over **all ten** passes (both sides, so the drop is not chosen to flatter one):
```
  Tests.Coverage        band with all 10 passes                ±4651
     dropping any of the other nine                     ±4650 – ±5932
     dropping head pass 5 (load 15.89, read 35600)             ± 817     ⇐ 5.7x collapse
  Tests.Coverage @residue                     ±4206  →  ± 763  on the same drop
```
The other nine head/base readings span 25,900–27,200; that one reads **35,600**. With it removed
the band (±817) sits **below** the budget (1,922) and the gate would have returned `ok` — correctly,
on a run whose true answer is zero.

### 3. ⛔⛔ AND THE OBVIOUS RULE IS REFUTED BY THE CORPUS ALREADY ON DISK
The contaminated pass has the highest `load1` of the ten (15.89 vs 7.8–12.8), which suggests
excluding passes by load. **`kernel_cost` has recorded `load1` per pass all along**, so the
hypothesis is testable for free:

* **The committed walk** (`docs/kernel-delta-history-2026-09-04.jsonl`, 12 commits × 2 passes):
  within a tree, the higher-load pass reads higher in **6 of 11** pairs. **That is chance.**
* **Tonight's own two sides disagree**: base (loads 8.99–12.61) is 3 concordant / 7 discordant —
  no signal at all; head is 9/9, and monotone even with the outlier removed.

⇒ **load1 does not predict a reading, and a load-based exclusion is not licensed by anything here.**
⛔ AND THE CORPUS CANNOT SETTLE IT EITHER WAY: **every load in the committed walk is between 3.75
and 5.57.** It has no observations anywhere near 15.9, so its "no effect" is a statement about a
region the tail does not live in — an unobserved region reporting agreement.
[[feedback-unobserved-regions-report-agreement]]

⛔ **And "drop the worst pass" is not available as a rule at all**: it derives the verdict from the
readings it is judging. A load threshold decided BEFORE a pass is read is a different object and is
checkable — but on n=1 it would be a rule fitted to one point.
[[feedback-widening-a-gate-needs-a-second-source]] [[feedback-a-single-reading-is-about-its-run]]

### 4. WHAT WOULD ACTUALLY DECIDE IT, AND IT ACCRUES FOR FREE
The blob every merge gate writes already carries `(load1, per-unit ms)` for every pass, and it is
thrown away with the session scratchpad. **Persist a per-pass `(load1, secs, module ms)` summary
beside each ledger row** — a few hundred bytes per landing — and the corpus that can test a
load-exclusion rule builds itself out of work already being done, at loads that actually occur.
Until then this is one observation, and it is recorded as one. [[feedback-a-landed-corpus-cannot-measure-detection]]

⇒ This is also the first per-RUN evidence for QUEUE item 4 with a known ground truth, and it agrees
with D165's per-COMPONENT evidence from a different direction: `@residue`'s +728 there and its
±4,206 here are the same phenomenon seen twice.

## D167 — P2 batch 37 specified at the object: four of its seven mnemonics are inert spellings, and a text diff would have said otherwise

`p2_residue.py` on today's tree: **7 pairs / 1,833 instructions need no rounding rule at all** —
`shufps` 1545 · `shufpd` 70 · `unpcklps` 64 · `movmskps` 53 · `unpcklpd` 45 · `unpckhps` 40 ·
`unpckhpd` 16. That is D158's planned split, unchanged by the two batches since. The batch was
handed on as *"ALL the new semantics"*. Measured against the model and against K, it is three
different kinds of work in very unequal proportions.

### 1. ⭐⭐ FOUR OF THE SEVEN ARE BIT-IDENTICAL TO `VBinKind` MEMBERS ALREADY IN THE MODEL
```
   unpcklps ≡ punpckldq      unpckhps ≡ punpckhdq
   unpcklpd ≡ punpcklqdq     unpckhpd ≡ punpckhqdq
```
⇒ the batch-19/batch-36 shape exactly: separate KINDS because the BYTES differ, semantics shared by
not branching, held apart by `check_encodings.py` and held together by a THEOREM — and **no
differential vector can witness the identity**, which is why it must be a theorem.
Their whole demand is **165 instructions of 1,833**.

### 2. ⛔⛔ AND A TEXT DIFF OF K'S OWN FILES SAYS TWO OF THE FOUR ARE DIFFERENT
Whitespace-normalised, the generated rule bodies compare:
```
   unpcklpd vs punpcklqdq    IDENTICAL   (207 chars)
   unpckhpd vs punpckhqdq    IDENTICAL   (207 chars)
   unpcklps vs punpckldq     DIFFER at char 122   (345 chars each)
   unpckhps vs punpckhdq     DIFFER at char 122   (345 chars each)
```
The difference is **pure re-association**: `concat(concat(concat(a,b),c),d)` against
`concat(concat(a,b),concat(c,d))`. `concatenateMInt` is associative on bit strings, so the normal
form is the left-to-right sequence of LEAVES, and under it all four pairs are identical — with the
controls (`unpcklps` vs `unpckhps`, `unpcklpd` vs `unpcklps`) differing:
```
   unpcklps / punpckldq  →  R2[0,128) · R1[192,224) · R2[192,224) · R1[224,256) · R2[224,256)
   unpcklpd / punpcklqdq →  R2[0,128) · R1[192,256) · R2[192,256)
```
⇒ 🔑 **A GENERATED FILE'S TEXT IS NOT ITS MEANING WHEN THE OPERATOR IS ASSOCIATIVE.** Two
stratification runs emitted the same function with different parse trees.
⛔ **And the failure would have been worse than a false negative**: the two `pd` pairs matched
textually and the two `ps` pairs did not, so a byte comparison over the four reads as *"two are
spellings, two are new semantics"* — a plausible, self-consistent, wrong design with an apparent
`ps`/`pd` explanation attached. **A comparison that fails on HALF a set invites a theory of the
half.** [[feedback-two-readings-are-not-two-witnesses]] [[feedback-a-partition-says-nothing-about-its-complement]]

### 3. ONE IS A FIELD CHANGE, AND THE MODEL ALREADY HAS THE SHAPE
`movmskps` is `vmovmsk (dst : GPR) (src : XmmReg)` — the constructor `pmovmskb` already uses — with
a KIND added (byte-signs vs `ps` lane-signs). K writes `concat(mi(60,0), <4 bits>)`, so the 32-bit
write zero-extends by the rule the model already obeys; the `r32`/`r64` rows are one semantics, and
whether they are also one ENCODING must be measured with `check_encodings.py` as `pmovmskb`'s were,
not inherited from it. **53 instructions.**

### 4. AND THE WHOLE RISK IS IN TWO MNEMONICS THAT ARE ALSO 88% OF THE DEMAND
`shufps` (1,545) and `shufpd` (70) read **both** operands — unlike `pshufd`, which the existing
`vshuf`/`VShufKind` expresses and which selects four lanes from ONE source. So `VShufKind` is the
wrong home: a new constructor is needed, not a new kind. K decides both, and the imm bit order is
K's big-endian, verified against the SDM's `Select4`:
```
   shufps  lane0,lane1 ← DEST selected by imm[1:0], imm[3:2]
           lane2,lane3 ← SRC  selected by imm[5:4], imm[7:6]
   shufpd  qword0 ← DEST[imm[0]]      qword1 ← SRC[imm[1]]
   both PRESERVE the YMM upper 128 (legacy SSE), which K writes explicitly as R2[0,128)
```

### 5. THE ORDER, AND IT FOLLOWS D160'S PROVEN SHAPE
**Step 1 — the field change alone**, isolable and measurable: the `vmovmsk` kind, nothing else.
D160 established this is what buys a price decomposition (`X86.Syntax` +12/+18/+19 for the batch
against −5.0 for the fields alone ⇒ the ~+15 ms is the constructors).
**Step 2 — the four inert spellings + `movmskps`**, with `shuf_spelling_is_inert`-style theorems
driven red by routing one kind to another.
**Step 3 — `shufps`/`shufpd`**, the new constructor, where every wrong-model arm belongs.
⛔ **Land it `--no-ff` with `--record` inside the merge commit** (D164), or `--gap` goes red and
names the ritual.
⚠️ `p2_batch_size.py` must be re-run against the tree of the day before sizing: D158's law is that
the affordable batch GROWS with the roster, so yesterday's number is a floor, not a ceiling.

---

## D168 — P2 batch 37 step 1: the `vmovmsk` field change, and the literal the comment beside it had already called a hazard

D167 ordered the field change as its own commit, on D160's proven shape: splitting it from
the semantics is what makes the reading a fact about the FIELD. `5dc2a13` changes the fields
and nothing else — roster, coverage table, differential and `rosterP0` do not move, and
`movmskps` is not yet a claimed form.

### 1. THE PRICE: FREE, AND THE CONFOUND POINTS THE WRONG WAY

`kernel_delta.py --base c61d7f5 --head 5dc2a13 --repeats 3`, passes alternated, one session:

```
  X86.Syntax        274.0 → 260.0   -14.0  ±16.5   budget 51.2   ok
  X86.Semantics      14.9 →  15.9    +1.0   ±2.7   budget  6.0   ok
  Tests.Coverage  28300.0→26500.0 -1800.0 ±2579.3  budget 2037.6 ok
  Tests.Nonvacuity  143.0 → 136.0    -7.0 ±148.2   budget 49.0   UNMEASURABLE ⛔
  (every other unit ok)                                          overall rc 3
```
The one refusal is a band, not a cost: `Tests.Nonvacuity`'s ±148 is larger than the 143 ms
module it is about. ⇒ a ceiling whose margin is under the machine's own spread reports the
machine. D160's verdict verbatim: UNMEASURABLE is not the same as expensive.

⭐ AND THE LOAD CONFOUND IS CONSERVATIVE, which is worth stating because it usually is not:
the head's three passes ran at mean load **14.58** against the base's **13.06**, and still
read LOWER. The reading that says "the field is free" was taken under conditions biased
against it. [[feedback-conservative-is-a-direction-not-a-margin]]
[[feedback-a-measurement-without-its-conditions]]

### 2. ⭐⭐ THE COMMENT THAT NAMED THE HAZARD AND THEN COMMITTED IT

`Op.vmovmsk`'s semantics was written as a fold "rather than sixteen `|||` terms so the LANE
COUNT is derived from the width — a literal sixteen repeated in the body is a place for a
typo no type can catch." The body then read `List.range 16` and `8 * i + 7`: the sixteen AND
the eight were literals in exactly the position that sentence calls a hazard.

Harmless while there was one kind. The second kind is the change that pays for it — and a
reader auditing whether the count was derived would have read the sentence and stopped.
⇒ 🔑 **A COMMENT THAT NAMES A HAZARD IS NOT A DEFENCE AGAINST IT**, and it is worse than
silence, because it describes the code its author meant to write. Both literals now come
from `VMovMskKind.laneBits`: `result bit i = src bit (w*i + (w-1))`, for `i < 128 / w`.
[[feedback-a-citation-is-an-ungated-claim]]

### 3. ⛔ THE r32/r64 QUESTION WAS RE-ASKED, NOT INHERITED

D167 was explicit that `pmovmskb`'s answer must not carry over, because the answer is a fact
about the ASSEMBLER and not about the family. Measured with the assembler
`check_encodings.py` uses: `movmskps %xmm1,%eax` and `movmskps %xmm1,%rax` both give
`0f50c1`. K agrees on the other side — `movmskps_r32_xmm.k` and `movmskps_r64_xmm.k` are the
identical `concatenateMInt(mi(60,0), …)`. So one row, and the reason is measured twice.
[[feedback-a-batch-cannot-be-sampled]]

### 4. THE PROBE, ITS CONTROL, AND THREE PLANTS

A generalisation has two ways to be wrong — the new kind and the old one — so the old kind is
anchored beside the new one on the SAME source, and the two must disagree:
```
  movmskps on a source with signs 1,0,1,0 per dword lane   = 0xA      ✔ by `decide`
  pmovmskb on the SAME source, the pre-batch-37 answer     = 0x87F0   ✔ (the control)
  the two kinds DISAGREE there                                        ✔
  plant `.ps` laneBits 32→16                     ⇒ RED, 2 arms
  plant `.b`  laneBits  8→16                     ⇒ RED, 2 arms — the control fires ALONE
  plant sign bit `w*i+(w-1)` → `w*i`             ⇒ RED, both arms
```
The middle plant is the one that matters: it proves the control is not riding on its
neighbours. [[feedback-a-plant-probes-control-comes-first]]

---

## D169 — P2 batch 37 step 2: four inert spellings, and a witness that was silent on its own last conjunct

Four `VBinKind` members joining the `vunpack` arms they are identical to (batch 34's shape),
plus the `.ps` member D168 added. Five roster rows, ten vectors, no new function.

### 1. THE IDENTITY IS A THEOREM BECAUSE NO VECTOR CAN WITNESS IT

Each spelling is tested only against the oracle, never against its sibling, so a model
decoding `0f 14` as `punpckldq` scores identically on every case in the table. Bytes held
apart by `check_encodings.py` (CLEAN over 1014 forms); semantics held together by
`unpack_aliases_are_their_integer_siblings`.

⭐ THREE SOURCES AGREE AND THE TEXT OF ONE DISAGREES — re-derived here with an independently
written parser, though K's files are ONE origin however many instruments read them:
```
  K, leaf sequence     all four IDENTICAL; three controls DIFFER
  K, byte comparison   TWO identical, two differ at char 122 of 345 (pure re-association)
  LLVM's disassembler  one operand comment per pair
```
The byte comparison splits 2/2 along `ps`/`pd` — a self-consistent WRONG design with its own
explanation attached. [[feedback-two-readings-are-not-two-witnesses]]

### 2. ⛔⛔ THE WITNESS THAT PASSED THREE CONJUNCTS AND WAS BLIND ON THE FOURTH

`unpack_siblings_are_pairwise_distinct` was first written `⟨0, 1, …⟩`. That satisfies the
first three and makes the fourth FALSE: `1` lies entirely in the LOW half, so `unpckhd` and
`unpckhq` both read zeros and AGREE. `decide` caught it — but had the theorem been written
with only the three conjuncts that passed, a natural thing to do, it would have been GREEN
and blind to exactly the pair a mis-routed `unpckhps`/`unpckhpd` lands on.
⇒ 🔑 **A WITNESS DRAWN FROM THE SAME HALF OF THE SPACE AS EVERYTHING ELSE IS SILENT IN THE
DIMENSION THE CLAIM IS ABOUT.** [[feedback-a-control-can-share-the-blind-spot]]

### 3. ⛔⛔ TWO WRONG-MODEL ARMS WOULD HAVE RUN ON THE NEW VECTORS AND BEEN NO-OPS

`wrongUnpackHalf` ends in `| other => other`; `wrongUnpackOrder` names its eight members and
falls to `| _ => step i s` — the GOOD model. The four new mnemonics contain `unpck`, so both
arms would have been SELECTED for the new vectors, RUN, and been bit-identical to the good
model on every one: scoring 0 and reading exactly like an arm that was exercised and found
nothing. Both extended.
⇒ 🔑 **A CATCH-ALL IS WHERE A NEW MEMBER GOES TO BE SILENTLY EXEMPTED FROM THE GATE THAT
COVERS ITS FAMILY.** The second was found by grepping the file for the SHAPE after fixing the
first. [[feedback-naming-a-defect-is-not-finding-its-siblings]]

⚠️ **AND THE SAME SHAPE IS CORRECT ONE FILE AWAY.** `Tests.Coverage.isVShiftForm` also ends
in `| _ => false`, and the two new constructors were deliberately NOT added to it: all four
consumers of `vshiftVectors` match on `.vshifti`/`.vshiftx`/`.vshiftm` only, so an added
member would be inert and would cost kernel walk. ⇒ the discriminator is whether anything
downstream ASKS a question of the omitted member — in `Main.lean` the omission was still
selected and SCORED, so its silence was reported as evidence; here nothing asks.

### 4. THE COUNTS ARE HAND-DERIVED AND CHECKED, NOT READ BACK

`roster_size_is_159` and `vector_count_is_1014` were written from what the batch INTENDED to
add; `decide` checking them against the tables is what makes two sources agree. Deriving them
from the tables would have made the gate confirm whatever the tables held.
`claimed_forms.py` then arrived at the same pair independently, from the vectors' AT&T text
and the rows' encodings. [[feedback-widening-a-gate-needs-a-second-source]]

---

## D170 — P2 batch 37 step 3: the two-source shuffles land, and `movmskps` does not — the availability gate scored a form the oracle never ran as available

Step 3 is `shufps` and `shufpd`, 88% of the batch's demand and its only new semantics. They
landed. `movmskps`, which D168 built the field for and D169 claimed, did NOT — and finding
out why cost the batch its most useful hour.

### 1. THE TWO-SOURCE SHUFFLES ARE A NEW CONSTRUCTOR, AND THE REASON IS STRUCTURAL

`VShufKind`'s every member selects from ONE source; `vshufApply`'s signature takes a single
`src`. `shufps` reads BOTH operands (lanes 0-1 from the destination, 2-3 from the source), so
it could not be expressed at any kind of that type. `Op.vshufp`/`Op.vshufpm` and
`VShufpKind`. D167 called this and it holds at the object.

⚠️ AND THE DESTINATION IS READ, which no other shuffle here does — `Op.vshuf` overwrites its
destination without consulting it. A frame lemma or wrong model that treats the destination
as write-only is right for that constructor and wrong for this one.

⭐ THREE SOURCES BEFORE A LINE WAS WRITTEN: K's rules decode to lane0←DEST[imm[1:0]],
lane1←DEST[imm[3:2]], lane2←SRC[imm[5:4]], lane3←SRC[imm[7:6]] for `ps` and qword0←DEST[imm[0]],
qword1←SRC[imm[1]] for `pd`; the SDM's `Select4`; and LLVM, which renders
`shufps $0x1b,%xmm1,%xmm0` as `xmm0 = xmm0[3,2],xmm1[1,0]`. The anchors quote LLVM's own
example immediate, so their expected values are read off a source independent of the rule
under test.

⛔ The plants: swapping `vshufpsAux`'s `if i < 2 then a else b` reds 3 arms; making `shufpd`
read imm[1] for qword 0 reds 3 arms.

### 2. ⛔⛔⛔ THE FINDING: `movmskps` STALLS ON THE ORACLE, AND TWO GATES CALLED IT FINE

The differential returned **unexplained=464**, every one of them `movmskps`. Measured at the
object, over 88 pre-states per vector:
```
   movmskps_x1_eax   88/88  RIP NEVER ADVANCES, refused-flag = 0
   movmskps_x5_ecx   88/88  RIP NEVER ADVANCES, refused-flag = 0
   pmovmskb_x1/x5    88/88  executes      ← same constructor, same shape
   unpcklps_xx/_m    88/88  executes      ← also a NO-PREFIX SSE form
   shufps/shufpd     88/88  executes, and MATCHED
```
Two positive controls in the SAME run, chosen to differ in the two dimensions a reader would
blame: the constructor, and the prefix/feature class. So the stall is a fact about this
MNEMONIC. x86isa defines `x86-movmskps-sse` and `inst-listing.lisp` carries the entry, so
this is not a missing implementation but an unreachable one; running it down inside x86isa is
not this batch's work.

⛔ **AND IT IS THE ONLY FORM IN THE TABLE THAT STALLS WITH THE REFUSAL FLAG CLEAR.** Every
other non-advancing form — `div`, `idiv`, `call_ind`, the `_unal` alignment vectors — sets
`refused=1`. (The `rep_*` forms also leave RIP unadvanced with the flag clear, but that is
their SEMANTICS, D46.) Because the flag was clear, the differential classified 464 field
mismatches as `spec` — i.e. as THIS MODEL being wrong about a rule the oracle never evaluated.

### 3. ⛔⛔ AND THE GATE THAT EXISTS TO PREVENT EXACTLY THIS SAID `executes 88/88`

`oracle_availability.py` is the instrument P1 batch 21 built so the unavailable list would be
MEASURED rather than declared — its docstring: *"a declared list inherits the direction of its
default … every gap in it INVENTS work."* Asked about `movmskps`, it answered **executes,
88 executed, 0 refused**, while the differential was producing 464 mismatches for the same
form on the same oracle.

Its classifier was `if refused=1 then refused else EXECUTED`. **`executed` was a residual, not
a measurement.** A case that neither refused nor ran fell into it.
⇒ 🔑 **A TWO-VALUED CLASSIFIER OVER A THREE-VALUED WORLD SCORES THE UNSEEN STATE AS WHICHEVER
VALUE IS THE RESIDUAL** — and here the residual was SUCCESS, in the one gate whose stated
purpose is to stop unavailable work from being invented. The gate was not merely blind; it
was blind in the direction that manufactures work.
[[feedback-a-tool-has-no-concept-of-not-applicable]] [[feedback-a-route-cannot-see-its-subject]]
[[feedback-under-claims-are-unpoliced]]

**REPAIRED, three-valued: refuses · executes · stalls**, where a stall is `rip UNCHANGED`.
`movmskps` is declared `stalls` and the gate now measures it. ⚠️ The test is `rip unchanged`
and NOT `rip == entry + len`, because a jump, a taken branch, or a `rep` signalling another
iteration would fail the stricter one; no such form is in `FORMS` today and the comment says
so for the head who adds one. The ten BMI forms and `movnti` still read `refuses` in the same
run — the positive control that the new branch did not swallow the refusal class — and both
`executes` controls still execute.

### 4. WHAT THE MODEL KEEPS, AND WHAT IT NO LONGER CLAIMS

`VMovMskKind.ps`, its semantics and its five anchors STAY: the model computes `movmskps`
correctly and the kernel checks that against K and LLVM. The **roster row and its two vectors
are withdrawn**, because in this repository a roster row means *differentially tested* and it
is not. 158 mnemonics / 1012 vectors, not 159 / 1014.
⇒ this is `movnti`'s precedent (D59, D61) applied to a form the model can execute: available
work is what the ORACLE can witness, and a row that cannot be witnessed is a claim, not a
measurement. The day x86isa executes it, the availability gate goes RED — declared `stalls`,
measured `executes` — and names the row that can then land.

### 5. ⚠️ AND THE BATCH ASSUMED ORACLE SUPPORT FROM A SIBLING

`movmskps` was never probed before being claimed. `pmovmskb` works, it is the same
constructor at the same shape, and that was allowed to stand for evidence. The declared list
never named `movmskps`, so nothing looked.
⇒ 🔑 **ORACLE SUPPORT IS PER ITEM.** Seven of seven executing does not license the eighth, and
here the eighth was the one the batch had already built a field for.
[[feedback-a-batch-cannot-be-sampled]] [[feedback-a-declared-list-inherits-its-default]]

## D171 — the red-first job that had never been run: a ±2σ test asked 23 times, and an alternation that does not cancel what its comment says it cancels

**The inherited order:** *"attribute the `ci_local --job kernel-delta-redfirst` RED at `c61d7f5`
(its failing arm compares two copies of ONE commit, so it is the box, not batch 37, but it is
unowned and nobody here had ever run that job)."* The conclusion — not batch 37's — is right. The
**cause** handed on with it is wrong, and the difference decides the remedy: "the box" is fixed by
waiting for quiet, and this cannot be.

### 1. ⛔⛔⛔ THE JOB REDS ON A PERFECTLY QUIET BOX, 95.8% OF THE TIME

`selftest_measure`'s arm 1 profiles two worktrees of the SAME commit and asserts, per unit,
`|median(head) − median(base)| > K_SIGMA · se` — with `se` estimated from the same readings, and
the job redding if ANY unit fires. Two things make that not a ±2σ test:

* **`se` has one degree of freedom.** At the CI job's `--repeats 2` there are two readings a side.
  A normal critical value against an SE estimated from two points is wildly anti-conservative —
  the textbook `t(0.975, 1)` is **12.7**, not 2.
* **The question is asked of 23 units and combined with `OR`.**

At `n = 2` the null is exact in closed form. With `d = mean(h) − mean(b) ~ N(0, σ²)`,
`u = b₁−b₂`, `v = h₁−h₂ ~ N(0, 2σ²)`, and `d` independent of `(u, v)` because
`cov(x₁+x₂, x₁−x₂) = 0`, writing `c = K·F/√2` (F = `MEDIAN_SE_FACTOR`):

```
    P(fire) = ∫ 2Φ(−c√x) · ½e^(−x/2) dx  =  1 − c/√(1+c²)          (by parts)
```

| route | per-unit rate at K=2, n=2 |
|---|---|
| closed form above | **12.91 %** |
| quadrature over the χ²₂ density | 12.91 % |
| Monte Carlo through the shipped `resolution()`, 400 k | 12.86 % |
| what the "±2σ" wording implies | 4.55 % |

Over 23 units: **95.8 % family-wise.** The job passed **4.2 %** of the time. The four units that
fired on 09/06 are what the null predicts — 2.97 expected, `P(≥4) = 34.5 %` — in **mixed signs**,
at 1.17× and 2.8× their bands, which is the shape of a marginal false positive and not of a bias.

⇒ 🔑 **A PER-UNIT BAND IS NOT A RUN-WIDE CLAIM.** The sentence the arm prints — *"identical trees
produced no difference THE RUN cannot explain"* — quantifies over every unit, so its threshold has
to as well. A gate that asks one question 23 times and reds on any answer has 23 chances to be
wrong and one to be right. **And it survived because nobody had ever run it**: a 95.8 %-red gate
that is never invoked looks exactly like a gate.

### 2. THE MEASUREMENT, AND THE SAME READINGS JUDGED BOTH WAYS

Arm 1 run for real at `c61d7f5`, `--repeats 4`, 23 units, 8 passes, load 9.0–21.6:

```
  --repeats 4   OLD rule  1 of 23 fire (X86.State +5.6 ms at 2.59x se)   ⇒ RED
                NEW rule  0 of 23 fire                                    ⇒ passes
  --repeats 2   all 36 sub-samples of THOSE SAME readings:
                OLD reds 29/36 = 81%      NEW reds 2/36 = 6%  (target 5%)
```

⚠️ The 81 % is a **resampling of one run** — what this run would have told the CI job at its own
`--repeats 2`, not 36 independent afternoons. It is quoted as the smaller claim it is; the 95.8 %
is the long-run figure and it comes from the null, not from the box.

### 3. THE REPAIR: A CUT DERIVED FROM THE NULL, AND ITS SECOND SOURCE IS THE GATE

`bias_cut(n, units, α)` — Šidák per-unit target `q = 1 − (1−α)^(1/units)`, inverted through the
closed form at `n = 2` (`c = (1−q)/√(q(2−q))`, `K = c√2/F`) and through a seeded Monte Carlo over
`resolution()` itself for `n > 2`. **The two routes agree to 2.1 % at `n = 2` and that agreement is
an arm** — a threshold derived from the thing it thresholds is the defect this file already
records three times. `K_SIGMA` is untouched: the merge gate's per-unit band answers a different
question, and `delta_band_calibration.py --check` still reads `K_SIGMA = 2` and passes.

### 4. ⛔ AND BOTH ERROR RATES ARE CARRIED, BECAUSE A SAFETY BOUND IS FREE TO A SILENT GATE

Swept over the SAME generated draws, family-wise over 23 units:

```
   n   cut    OLD FP    NEW FP    power at a bias of 1σ / 2σ / 4σ / 8σ
   2  16.88   95.8%      5.0%        0.5%   1.2%   4.1%  14.8%
   3   5.51   84.9%      5.0%        1.0%   4.7%  28.7%  88.9%
   4   4.04   71.6%      5.0%        2.0%  12.7%  68.7%  99.9%
   6   3.42   65.3%      5.0%        4.3%  32.3%  96.4% 100.0%
```

⇒ **at `--repeats 2` the arm is bad in BOTH directions**: 95.8 % false red, and blind to any bias
under ~32× one pass's spread. The CI job is raised to `--repeats 4` (measured price: ~22 min → ~45
min, because the job runs `measure` twice). And the arm now prints its unpoliced set — derived
against the BUDGET FILE, not against a number I liked: every unit where `cut · se` exceeds that
unit's own allowance, i.e. where a bias big enough to flip a verdict passes the arm in silence.

⛔⛔ **AND THAT NUMBER REFUTED THE SENTENCE I HAD ALREADY WRITTEN.** The draft of this section and
of the workflow comment said the cut at `--repeats 2` exceeds *every* unit's allowance. Computed
against the budget file on the real `c61d7f5` readings:

```
   --repeats 2  (cut 16.88)   19 of 23 budgeted units UNPOLICED   worst 23x its allowance
   --repeats 4  (cut  4.04)   12 of 23 budgeted units UNPOLICED   worst 68x (X86Native)
```

**Four does not fix it, it halves it.** Some units (`X86Native` at 68×) cannot be policed at any
repeat count this job can afford — which is D152's `R = band / allowance` arriving in a second
place. The deliverable is therefore not "the arm is now sound" but "the arm now NAMES the units it
cannot police", where before it printed one tick over all 23.
[[feedback-prose-written-before-the-measurement]]

### 5. ⛔⛔ A SECOND DEFECT IN THE SAME FUNCTION: `ABAB` DOES NOT CANCEL A DRIFT

`measure()`'s docstring has said since it was written that *"interleaving makes a monotone drift
cancel"*. It is arithmetically false. Under `ABAB` the base sits at passes 1, 3, …, 2n−1 and the
head at 2, 4, …, 2n, so the head's median is exactly **one pass later** at EVERY repeat count: a
drift of `s` ms/pass lands as a bias of exactly `s`, and no number of repeats reduces it. Driven
with the noise switched off, the old order returns **−30.00 ms** against a −30.00 ms/pass drift;
`ABBA` returns **0.00**.

**And the drift is real on this box.** The same 8-pass run, regressed on pass index: **20 of 23
units slope one way**, the largest `Tests.Coverage @residue` at **+295 ms/pass** (+1.75 % of its
median). Under the old order that is a +295 ms standing bias riding inside every delta the gate
reports — in the direction that makes a head look cheaper than its base.

⭐ **The repository already knew.** `kernel_delta_history.py` sweeps forward then REVERSE for
exactly this reason and has since it was written. Two tools, one repo, and the one with the wrong
design carried the sentence asserting the right one. The limit is stated rather than implied:
`ABBA` cancels a LINEAR drift exactly and a curved one only partly.
[[feedback-a-citation-is-an-ungated-claim]]

### 6. THE DRIFT GATE'S EXEMPTION BUCKET WAS AN `else`

`kernel_drift.py --gap` splits the unrecorded steps three ways and the third was
`else:` — "changes no `.lean` and neither profiler path". An `else` is not an argument, it is
whatever is left, and **its gaps all fall to `exempt`, the direction that reports no work.**
`lean-toolchain` and `lake-manifest.json` change every unit's reading and touch no `.lean`: both
were exempt by default. No step in the current window touches either, so this corrects a **latent**
hole and the counts (5 / 5 / 43) are unchanged — which is the point.

The default is inverted: `EXEMPT_RULES` is an allowlist of path prefixes each carrying its reason,
a step is exempt only when EVERY path it touches is argued, and anything else lands in a fourth
bucket `unclassified` that **refuses**, with no ratchet, because the correct number of un-argued
exemptions is zero. The `scripts/` rule is sound for a stated reason: `*.lean` is tested FIRST, so
a generator can only reach a reading by regenerating a `.lean`, and that regeneration is itself a
`.lean` diff already bucketed. [[feedback-a-declared-list-inherits-its-default]]

### 7. ⛔ THE LEDGER WAS JOINED ON `base` ALONE, AND `head` WAS NEVER READ

`gap()` said `if b in ledger: continue`. A row whose `base` sat on the chain closed that step **no
matter what span it had priced**. The path that produces a wrong one is the path this file's own
usage line recommends: `--backfill` rows the CONSECUTIVE pairs of a walk's `order`, and the
five-step backfill is **four disjoint spans** — one walk over all nine commits writes four correct
rows and three bogus ones whose bases are real chain commits. The gap would have read CLOSED.
[[feedback-a-join-on-a-lossy-key]]

**⭐⭐ And my first repair was wrong, which is how the rule got its shape.** Requiring
`rec["head"] == h` refused two rows *already in the committed ledger* — and the object refuted the
check, not the rows. The `--no-ff` ritual measures the BRANCH TIP and writes the row INSIDE the
merge, so the row's head is the merge's second parent while the chain's child is the merge. Their
**trees are not equal either**: they differ by exactly the ledger row the ritual just wrote.

⇒ 🔑 **THE INVARIANT IS NOT THE COMMIT AND NOT THE TREE, IT IS THE READING.** A row prices this
step if what separates its head from the chain's child cannot move a reading — head reachable from
the child, and no `.lean` and no profiler path between them. Measured: 11 rows name the child
exactly, 2 are the ritual's shape, and in both the separating diff is
`docs/delta-allowance-ledger.jsonl` alone. [[feedback-the-burden-is-on-the-departure]]

### 8. WHAT IS NOT DONE

The five `.lean` backfill runs themselves (batches 23, 34, 35, 36a, 36b) are still unmeasured; the
gap ratchet still reads 5 and is exact. §7 is the precondition for doing them safely, and §6 is the
argument for the 43 the walk does not need to visit — **one contiguous span per walk**, which is
now a refusal rather than a convention.

## D172 — queue item 3: a ledger row keeps medians, and medians cannot show that the run drifted

D171 found a real drift on this box — 20 of 23 units sloping one way over an 8-pass run, the
largest at **+295 ms/pass** — and under the old `ABAB` order that landed as a standing bias inside
every delta the gate reported. **The only reason it was visible is that the raw readings happened to
be saved to a scratch file.** A ledger row keeps `base_ms` (the medians) and one `box` stamp taken
when the row was written; neither can distinguish a quiet run from a drifting one, and the row
outlives the readings. That is queue item 3, and D171 is its argument.

### 1. THE PASS INDEX IS STAMPED, NOT RECONSTRUCTED

`measure()` groups readings BY SIDE, so the wall-clock order across the two sides is not recoverable
from the stored blob without knowing the loop's ordering rule — **and that rule just changed from
`ABAB` to `ABBA` in D171.** A consumer that re-derived the order would have been silently wrong for
every run written before the change, in a way nothing would report. Each reading now carries its own
global `pass` and its `side`. [[feedback-an-unrecorded-rule-cannot-be-audited]]

### 2. WHAT A ROW CARRIES, AND WHAT IT DELIBERATELY DOES NOT

`pass_conditions()` returns the per-pass `(pass, side, load1, secs)` plus one drift summary: the
worst unit **by name**, its slope in ms/pass and as a percentage of its own median, and how many of
the profiled units slope the same way. Per-pass PER-UNIT milliseconds are **not** stored — 23 units
× 8 passes × every row is a ledger nobody opens — and the slope is stored with the unit it belongs
to, because a slope with no unit name is a number a reader cannot act on.

⛔ **Absent, never blank, in three places.** Readings with no `pass` stamp (anything written before
this change) report `passes: None` with a stated `why`, rather than an invented order and a drift
figure that would look measured. A row written without conditions **omits the key** rather than
carrying an empty one that reads as *"measured, and quiet"*. And the backfill path — whose walk
visits each commit once per SWEEP, giving too few points per commit for a slope — records its
`(sweep, load1, secs)` and says so in its own `why`, instead of leaving the field absent where
absence would read as *not applicable*. [[feedback-a-tool-has-no-concept-of-not-applicable]]

### 3. ⛔ AND THE ARM THAT CHECKS IT PASSED ON A WRONG PREDICTION FIRST

The drift arm plants a known series and asserts the recovered slope. Its first form asserted
`|slope − 10·4/7| < 2.0`. The true least-squares slope of that plant is `200/42 = 4.762`; my
predicted `10·4/7` is **5.714**. The arm was green — the tolerance was wide enough to cover a
prediction that was wrong by 20%.

Recomputed from the plant itself and asserted to `1e-9`, it then went RED against the stored
`4.76` — catching that the summary rounded to 2 dp. Storage is 3 dp now and **the assertion is
against the stored value**, so the precision is part of the contract rather than something a fat
tolerance hides.

⇒ 🔑 **A TOLERANCE WIDE ENOUGH TO ABSORB NOISE IS WIDE ENOUGH TO ABSORB A WRONG EXPECTED VALUE**,
and the wrong value is the one nothing else will ever check. Compute the expectation FROM THE PLANT,
in the arm, and assert it tightly enough that the storage format is part of what is being asserted.
[[feedback-a-confirmed-prediction-is-not-a-checked-statistic]]

## D173 — the two tools whose answer to an unrecognised request was to start their most expensive path

Typed at 11:0x by a relit head, from this repository's own bank, which names the job by that
spelling: `python3 scripts/ci_local.py --list-jobs`. There is no such flag — the real one is
`--jobs`. `arg()` scans for flags it knows and ignores the rest, so `job` fell to its default
`"build"` and **the tool began running all 33 steps of the build job** in answer to a request for a
listing. The same shape is in `kernel_delta.py`, where the default path is worse: `--help` fell
through to the merge gate and started profiling two worktrees.

⇒ 🔑 **`--help` AND A LISTING FLAG ARE THE FIRST THINGS A RELIT HEAD TYPES, AND THEY ARE THE TWO
PLACES WHERE "IGNORE WHAT YOU DO NOT UNDERSTAND" SPENDS THE MOST.** A tool that answers an
unrecognised request by doing its most expensive thing is worse than one that refuses, because the
refusal is instant and the misfire is not — and the misfire looks like the tool working.

Both now refuse, naming what they saw and what they know, and both suggest the flag that was
probably meant. `--help` prints the docstring. **Positionals are refused too**: neither tool takes
one, so a bare word is a mistyped flag or a glob that expanded.

### ⛔ AND THE GUARD'S OWN RED-FIRST ARM FOUND THE HALF I HAD MISSED

The first form skipped the argument after a value-taking flag and never checked that one was there.
`kernel_delta.py --repeats` — flag present, value absent — **passed the guard**, and `arg()` then
returned the DEFAULT `3`. A flag whose value went missing is the same silent-default defect one
level in, and it would have run a measurement at a setting nobody asked for while printing nothing.
Both tools now refuse a dangling value-taking flag and say what the default would have been.

The arms that matter are the two CONTROLS, not the refusals: `--repeats 6` and `--job build --to 7`
must be ACCEPTED, and a value that itself looks like a flag (`--head --selftest`) must still be
consumed as a value. A guard like this fails by being too strict, and that direction breaks correct
invocations rather than announcing itself.

### THE ARM IS WHERE THE TOOL IS NEVER OTHERWISE RUN

`ci_local.py` is how every gate in the workflow is exercised on a developer box, and **CI never runs
the runner** — it runs the steps directly. So its guard had no driver at all, and an inline block in
`main()` has no callable surface to give one. `check_argv()` is a function, `ci_local.py --selftest`
drives six arms over it, and the workflow now runs that selftest as a step of the `build` job.
[[feedback-a-gate-with-no-callable-surface]]

## D174 — the five-step drift backfill, and the derivation gate that verified eleven rows while printing a sentence about the ledger

The five unrecorded `.lean` steps (P2 batches 23, 34, 35 and 36's two halves) are priced, and
`--gap` reads **0 against a ceiling of 0**. What the backfill turned up on the way is worth more
than the rows.

### 1. FOUR DISJOINT SPANS, FOUR WALKS — AND WHY THAT IS A REFUSAL NOW, NOT A CONVENTION

`--backfill` writes a row for each CONSECUTIVE pair of a walk's `order`. The five steps are **four
disjoint spans** of the chain (23 · 34 · 35 · 36a+36b), so one walk over all nine commits would
have written four correct rows **and three bogus ones across the gaps between spans** — whose bases
are real chain commits, so under the `base`-only join D171 removed they would have read as
recorded, and the gap would have reported itself closed. One walk per span, verified before the
rows were written: 5 rows produced, exactly the 5 wanted steps, zero bogus.

⚠️ `--out` is opened in APPEND mode, so the four walks must not share a file either.

### 2. ⛔⛔ THE DERIVATION GATE VERIFIED A SUBSET AND SAID SO IN A COMPLETE SENTENCE

`--verify-ledger <file>` filters ledger rows by `source == backfill:<that file>`. With the five new
rows written, it re-derived **11 of 18** and printed:

> ✅ ledger DERIVED: 11 steps × 23 units = 253 allowances re-derived … **and equal to the committed
> ledger**

The five rows this session added were derivable by nothing, and **the CI step names that one walk
file by literal**, so it would never have grown to cover them. A gate told a filename stops seeing
work that arrives under a different one.

⇒ 🔑 **THE LEDGER'S OWN ROWS NAME THEIR EVIDENCE.** `--verify-ledger-all` follows each row's
`source` tag instead of being told a path: a walk added tomorrow is covered without editing the
workflow, a row whose walk has been DELETED refuses (the evidence for a committed allowance is
gone), and the two live `source=gate` rows — not derivable from any walk — are **named with their
count** rather than quietly excluded from a green sentence. 16 backfilled + 2 live = 18, the whole
ledger. The single-file mode survives and now prints its own scope.
[[feedback-a-complete-count-of-a-subset]] [[feedback-a-gate-named-by-a-literal-stops-seeing-renamed-work]]

### 3. ⛔⛔⛔ THE BACKFILL SILENTLY DISARMED TWO RED-FIRST ARMS — MY OWN WORK, CAUGHT BY A LIST

Two arms were guarded by `if g_buckets["lean"]:` — the *unrecorded* `.lean` steps. **Emptying that
bucket is exactly what this batch of work did**, so both stopped running. The suite stayed CLEAN and
its arm count went **up**; the only thing that said anything was the DISTINCT-PLANT list falling
from 33 to 32.

⇒ 🔑 **AN ARM WHOSE PRECONDITION IS "THE REPOSITORY IS CURRENTLY IN ARREARS" SWITCHES OFF EXACTLY
WHEN THE WORK IT GUARDS GETS DONE** — and it switches off in the direction that reports success.
Both now draw on every `.lean`-changing step ON THE CHAIN, recorded or not: a property of the
history, which cannot be discharged. A control asserts the chain carries some (12).
[[feedback-a-gate-whose-precondition-is-a-discipline]] [[feedback-probe-silence-has-two-causes]]

### 4. ⚠️ AND THE RE-ARMED FORM WENT RED FOR A REASON THAT IS ITSELF THE FINDING

Re-armed on the first `.lean` step, the arm failed. That step's base **is the anchor**, and
`gap_anchor` takes the earliest ledger base on the chain — so deleting its row does not open a gap,
it **moves the window forward and every bucket reads zero**:

```
   delete the FIRST lean step (= the anchor)   anchor 144e9a3cf → 4f6766b9b   all buckets 0
   delete the LAST                             anchor unchanged               lean = 1  ✔
```

A narrowed observation does not report *unknown*; it reports *nothing unrecorded*. Losing the
earliest ledger row is a **coverage loss that looks like a clean gap**. The arm now picks a
non-anchor step, a second arm records the anchor behaviour so it is known rather than rediscovered,
and `--gap` prints how many commits precede the anchor and are outside the audit.
[[feedback-unobserved-regions-report-agreement]]

⛔ Found in the same place: `recorded` was computed as `len(steps) − nl − npr − nn`, which never
subtracted the `unclassified` bucket D171 added — so an unclassified step would have been counted
as **recorded**. Invisible while that count is zero, which is every day until the one it matters.

### 5. THE CONDITIONS THESE ROWS WERE MEASURED UNDER, PRICED RATHER THAN FELT

```
   b23  load1 median 15.44 (max 16.42)      b34  20.49 (31.16)
   b35  12.60 (20.73)                       b36  14.95 (20.08)
   committed reference: the quiet walk 4.51 · the contended walk 13.72
```

A backfilled allowance is a **percentage of the measured `base_ms`**, so a louder box buys a larger
allowance. Priced from two walks already in `docs/` over the SAME twelve commits: the shift is
**×1.14 median (p90 1.35)** at load 12.3 and **×1.18 (p90 1.55)** at load 13.7, and **every unit's
ratio exceeds 1** — load makes nothing faster. These five rows were taken at load 12.6–20.5, so
their allowances are generous by roughly a fifth, **in the direction that makes the drift window
convict LESS**. That is stated, printed by the tool beside every backfill, and deliberately **not
gated**: a threshold on load average is the heuristic D141 took out of this family of gates.
[[feedback-conservative-is-a-direction-not-a-margin]]

## D175 — the join accepted a row whose head sits before its own base

D171 replaced the ledger's `base`-only join with the READING invariant: a row prices step
`base → child` when its `head` is reachable from the child and nothing between them can move a
reading. Re-reading it while a long job ran, the bound is one-sided — `rh` was required to be at or
before the child and **never required to be at or after the base**. Measured on the real chain:

```
   step 0338526 → 043348c,  row head 939a073 (the commit BEFORE the base)
   records_step(...) = True
```

Such a row claims to price a step off a measurement taken from a point earlier than the step
begins. **Neither shipped writer can produce one** — `--backfill` uses `order[i+1]` and `--record`
uses the run's own `head_rev` — and that is exactly why it would have sat there indefinitely.

⇒ 🔑 **A JOIN IS WHAT DECIDES WHETHER A ROW COUNTS, SO IT MUST REJECT AN INCOHERENT ROW ON ITS OWN
TERMS, NOT LEAN ON TODAY'S WRITERS NEVER PRODUCING ONE.** The correctness of a reader that rests on
a property of the current writers is a correctness that a new writer silently removes — and the
writer's author has no reason to look here. The head must now sit INSIDE the step:
`base ≤ head_of_row ≤ child`. The two real `--no-ff` ritual rows still pass, and their control arm
says so; a red-first arm plants the earlier head and requires the refusal.
[[feedback-a-join-on-a-lossy-key]] [[feedback-the-burden-is-on-the-departure]]

## D176 — a forty-five minute green produced 613 bytes, and the gate's own scope statement was in the part that was thrown away

`kernel-delta-redfirst` at its new `--repeats 4` ran for 45 minutes and **passed** — the first time
that job has ever been green on this box. This is what the runner wrote:

```
   ── [1/1] Delta gate driven on real trees (identical-trees control + planted constructor)
      ✔
```

613 bytes in total. Everything arm 1 printed — its family-wise cut, the bias it can detect at 90 %
power, the box stamp, the drift, and **the list of twelve units it cannot police** — went into a
captured string and was dropped, because the step passed.

⇒ 🔑 **D94 GAVE THIS FILE HALF A LAW.** *A gate that refuses must say what it saw* is written into
`ci_local.py` and was honoured. The mirror was never stated: **a gate that PASSES WITH
QUALIFICATIONS must also say what it saw, and the runner is what decides whether it can.** A scope
statement exists precisely to qualify a green, so printing output only on red makes it unreachable
in exactly the case it was written for. The whole of D171 §4 — the arm naming the units its own
verdict does not cover — is invisible through this runner. The previous head's RED was legible only
because it was red.

⛔ **And the same line carried a second defect**: with `capture_output=True` a 45-minute step prints
nothing while it runs, so a watcher cannot tell *running* from *hung*. I resorted to `ps` and a
worktree listing twice today to answer a question the runner should have answered.

`run_step()` streams the child's output as it arrives, prefixed `│` so it is attributable to its
step, and keeps a 30-line tail for the failure summary D94 requires. It is a **callable surface**
with three arms of its own — a passing step's output is returned, all of it is returned, and a
failing step returns its rc with both streams merged.

⚠️ **The cost is noise and it is accepted rather than hidden**: `--job build` now streams 34 steps.
That is what this seat's standing order to redirect a long run to a FILE and filter the file is
for. **Silence is a defect; noise is a filter problem**, and only one of the two can hide a finding.
[[feedback-a-gate-that-refuses-must-say-what-it-saw]] [[feedback-read-what-the-instrument-measured]]

### THE RECEIPT THIS RECORD EXISTS BESIDE

`ci_local --job kernel-delta-redfirst` — **CLEAN**, both arms, at `--repeats 4`, on `043348c`. The
job that had never been seen to pass, passes: the identical-trees control does not convict two
copies of one commit, and the 512-planted-constructor arm still fails as it must. ⚠️ Stated with its
limit: this run's verdict is all the runner preserved, so the arm's own scope lines for THIS run are
gone. That is the defect above, and it is why the next such run will read differently.

## D177 — QUEUE item 0 (a)+(b)+(c): the census answered "executes" for a form the oracle never runs, and the two-valued classifier it came from had four more homes

QUEUE item 0 asked for three things and each was taken in order. What the item did not know is that
the defect it names — **a two-valued classifier over a three-valued world, scoring the unseen state
as the residual** — was live in **five** places, of which it named one.

### (a) the classifier — and the port that would have re-created the defect it repairs

`measure_cr4`'s emitted ACL2 form printed `flg` and `refused` and no RIP, so `executes` was a
RESIDUAL. The repair is the stall test `measure` has carried since D170.

⛔ **THE OBVIOUS PORT IS WRONG, AND WRONG SILENTLY.** `measure` reads the DRIVER's output, and the
driver prints RIP through `x86l-hex(…, 16)` (`x86isa_driver.lisp:158`); its
`rip=([0-9a-f]+)` + `int(…, 16)` is correct **there**. `measure_cr4` builds a standalone drive that
never loads the driver, so `~x` prints in ACL2's ambient print-base. **Measured, not assumed:** a
probe printing `255` came back `255`, not `ff` — base 10.

```
  ENTRY_RIP           = 0x400000 = 4194304
  ACL2 would print      rip=4194304
  int("4194304", 16)  = 68174084  ≠ ENTRY_RIP
  ⇒ the stall misses the `elif`, falls to the `else`, and is scored `executes`
```

⇒ 🔑 **D170's EXACT DEFECT, RE-CREATED INSIDE THE REPAIR FOR D170, BY COPYING A SIBLING THAT WAS
RIGHT WHERE IT LIVED.** [[feedback-two-readings-are-not-two-witnesses]]

So RIP is printed **twice**: `rip` raw, and `stalled` computed **in ACL2** as a 0/1, which means the
same thing in every print-base. The classifier reads the base-independent one; the two are
cross-checked on every record and a disagreement **refuses**, so a future base change is loud
instead of returning the residual.

**VERIFIED BY EXECUTION, with the controls first.** One run produced all three values —
`refuses` · `executes` · `stalls` — so the classifier was not stuck: `xorpd` executes under CR4_ON
and refuses under CR4_OFF (CR4-dependence is real), `pcmpeqd_mmx` executes under both.

### (b) the refutation — recorded, not retro-fitted

`P2_FORMS`'s `e0`/`e1` are sealed at `sha256 = 6e8474ff…`. The item's own ruling is *record the
refutation, do not retro-fit it*, and that is what `REFUTED_BY_MEASUREMENT` does: **the sealed rows
are byte-unchanged** and are overridden in the open, with evidence and a date. `p2_run` scores a
refuted row against its RECORDED MEASUREMENT — not a wildcard — so a row that starts executing
tomorrow goes red rather than being permanently excused, and prints `⚖`, never `✔`.

⇒ 🔑 **A FUNCTION NAMED `measured_availability` THAT RETURNS A SEALED PREDICTION IS A CITATION
WEARING A MEASUREMENT'S NAME.** That is the defect; `movmskps` was one symptom.

### ⭐ THE SWEEP, AND WHY A SAMPLE WOULD HAVE MISSED TWO OF THREE

D170 knew one stalling row. A four-form probe found a second — **`vmovmskps_v`**, the sibling
nothing had asked about. The full 267-row run found a third: **`emms`**, declared
`(executes, executes)`, measured `(stalls, stalls)` under BOTH CR4 arms.

⇒ 🔑 **THE FOUR-FORM PROBE WAS A SAMPLE OF A BATCH, AND SEVEN OF SEVEN NEVER LICENSED THE EIGHTH**
([[feedback-a-batch-cannot-be-sampled]]). `emms` sits in `NOT_AN_AVAILABILITY_QUESTION`, so it moves
no availability answer — **its declaration was still false and nothing had asked.**

### (c) the cross-table gate, joined on bytes rather than on names

`FORMS` and `P2_FORMS` both answer "what does x86isa do with these bytes" and nothing compared them:
`stalls` at line ~95 and `executes` at line ~917, 850 lines apart in ONE file, for two days.

⚠️ **The join key is (mnemonic, ENCODING), a departure from the item's wording** ("the same
mnemonic"): a mnemonic legitimately holds different verdicts at different buckets — `pandn` at `xmm`
and at `mm` — so joining on the name manufactures contradictions ([[feedback-a-join-on-a-lossy-key]]).

⛔ **MEASURED, AND IT IS THE GATE'S MOST IMPORTANT NUMBER: the two tables share exactly ONE
mnemonic** — 18 against 227, intersection `{movmskps}`. **The gate's entire reach today is its own
founding case.** So it prints the count of shared mnemonics that did not join (0), and an empty
domain reports **VACUOUS** rather than green — a gate that can silently stop checking anything is
the failure it exists to prevent, wearing a tick.

**Its first two red arms were silent, and both were my design errors, kept in the file:** arm 1
planted a P2 value the refutation then overrode back to agreement; arm 2 planted into `xorpd`, which
`FORMS` does not carry. ⇒ **a plant must create its condition, and the arm-checker is what said so.**

### ⛔⛔ THE FOUR OTHER HOMES OF THE SAME RESIDUAL — none named by the item

| site | what it did with `stalls` |
|---|---|
| `measure_cr4`'s classifier | scored it `executes` — item 0(a) |
| `oracle_note` (roster renderer) | rendered it **"⚠️ not measured"** |
| `p2_roster` by-MNEMONIC count | `else:` → published it as **"the oracle REFUSES"** |
| `p2_roster` by-BUCKET count | `else:` → same, and **the conservation law could not see it** |
| `p2_residue`'s `NO_ROUNDING` | declared `movmskps` rounding-free ⇒ **BUILDABLE TODAY** |

The renderer is the one that closes the loop: **"not measured" reads as an invitation to go
measure** — which is precisely the work order the relight gate carried and D170 had already refuted.
⇒ 🔑 **A RENDERER THAT COLLAPSES A KNOWN NEGATIVE INTO "UNKNOWN" RE-COMMISSIONS THE WORK THAT
NEGATIVE WAS RECORDED TO PREVENT.**

⇒ 🔑 And the by-bucket site gives the sharper law: **A CONSERVATION GATE CANNOT SEE A
MISCLASSIFICATION, ONLY A LOSS.** The totals conserved perfectly while 77 instructions were filed
under the wrong verdict, because a residual always conserves — into the wrong bucket.

⇒ 🔑 **A CORRECTION APPLIED AT ONE READER OF A TABLE IS NOT APPLIED TO THE TABLE.** Two independent
accountings read `P2_FORMS`; repairing the one the item named left the one that PUBLISHES still
wrong. [[feedback-naming-a-defect-is-not-finding-its-siblings]]

### ⛔ THE DEFECT I INTRODUCED, AND WHY IT DID NOT CRASH

Adding the CR4=0 arm grew the refutation record from `(verdict, why)` to `(e0, e1, why)`. A consumer
in `p2_roster.py` kept its positional `[0]`, which **silently stopped meaning "the verdict" and
started meaning "the CR4=0 verdict"**. It published `refuses` for two refuted rows and a STALLS
count of **1** where the answer is **3** — a number a reader accepts.
⇒ 🔑 **A POSITIONAL INDEX IS A BET THAT THE RECORD WILL NOT GROW, AND THE PAYOUT IS A PLAUSIBLE
WRONG NUMBER RATHER THAN AN ERROR** ([[feedback-a-positional-index-bets-the-record-wont-grow]]).
Fixed at the cause: the record is a `namedtuple` and every consumer reads `.e1`.

### the result

**THE BUILDABLE RESIDUE IS 0 PAIRS / 0 INSTRUCTIONS**, which is what the previous bank predicted and
could not yet derive. The relight gate's ⭐ order — *"claim `movmskps`, the WHOLE buildable-today
residue"* — was a reading of `e1`, and acting on it would have re-added the roster row D170 removed.

⚠️ **`docs/P2-ROSTER.md` WAS ALREADY STALE BEFORE ANY OF THIS**, and the two deltas are kept apart so
neither is attributed to the other. Measured with the change stashed: committed `EXECUTES 106 /
123,355` against derived `107 / 123,443` **at HEAD** — a pre-existing drift of +1 mnemonic / +88
instructions. D177's own effect is −2 EXECUTES and +2 STALLS in the by-bucket table (77 instructions
moving out of REFUSES, where they had never belonged).

Gates: `--check-encodings` · `--p2` · `p2_roster --check` · `--selftest` · `p2_residue` ·
`--selftest` · `p2_oracle_support` — **all rc=0**. No `.lean` changed ⇒ delta ledger EXEMPT, nothing
profiled.

### D177 addendum (same sitting) — "five homes" was an under-claim; the sweep found seven

Written into D177 as a count, then verified by grepping the SHAPE repo-wide instead of trusting the
sentence — which is what my own note told me to do and is not the same act as writing the note.

* **(6) `check_driver_cr4.py`** carries the identical two-valued classifier (a 2-tuple `(e, r)`, no
  stall state). It is silent only because its six-row `FORMS` list contains none of the three known
  stalling forms. ⇒ 🔑 **A DEFECT ABSENT ONLY BECAUSE THE INPUT SET EXCLUDES IT IS NOT FIXED.**
* **(7) `claimed_forms.py`'s `UNAVAILABLE`** selects `exp == "refuses"` and so drops `movmskps`:
  measured 18 rows, 10 unavailable, and the one form known not to run is outside the set that means
  "cannot run". The gate passes today, so this is a defect in the RULE and not a wrong number yet.

⇒ 🔑 **A COUNT INSIDE A DECISION NOTE IS A CLAIM WITH NO GATE ON IT**, and this one pointed the
unpoliced way: five instead of seven reads as thoroughness. Both are registered as QUEUE item 0b
rather than left in the bus post that announced D177.

### D177 addendum 2 — 0b(7) discharged: a rule repair that moves no number, and an arm that was one-directional

`claimed_forms.py` built `UNAVAILABLE` from `exp == "refuses"`. That was TOTAL when `expect` had two
values and became under-inclusive the moment D170 added `stalls`. The cost is not "an unexplained
row": `work` is `unclaimed − noform − UNAVAILABLE − DECLINED`, and this file **gates that bucket as
empty while calling it AVAILABLE WORK** — so a stalling form would be COMMISSIONED. The same loop
D177 closed in the census and in the roster renderer, reached by a third route.

⚠️ **LATENT, AND SAID SO.** Measured: no `movmskps` row reaches `rows` at all (the P1 roster carries
no xmm form), so the repair moves nothing — the tool's entire 261-line output is byte-identical
before and after. It is a repair to the RULE, whose next stalling form need not be SIMD.

⛔ **THE ARM I WROTE FOR IT WAS ONE-DIRECTIONAL, AND ONLY DRIVING IT SHOWED THAT.** The fixture's
only `executes` row was `CONTROL:mov`, which the `startswith("CONTROL")` filter drops regardless of
the rule — so the over-broad direction was untested while looking tested:

```
   pre-D177 rule (too narrow) ....... CAUGHT
   over-broad (swallows executes) ... NOT CAUGHT      ← before a non-CONTROL `executes` row existed
   after adding `paddd` executes .... all three drives CAUGHT, control green
```

⇒ 🔑 **A CONTROL THAT IS EXCLUDED BY A DIFFERENT FILTER CANNOT WITNESS THE RULE UNDER TEST.** It sits
in the fixture, reads as coverage, and is removed from the rule's reach by an unrelated line.

📌 The arm is build-free and runs FIRST inside `selftest`, before the Lean build that gates the rest
of it — the rule is pure string work, and an arm behind a build is a discipline that gets exercised
less ([[feedback-make-the-probe-cheap]]).
