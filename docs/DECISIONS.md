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
