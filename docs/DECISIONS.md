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
