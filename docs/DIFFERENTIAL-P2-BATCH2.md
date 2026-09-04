# P2 BATCH 2 — the LOCK vocabulary, a batch with no arithmetic, and a roster claim that was three times too generous

**Forms.** P2 addition 2 of the Captain's three. `Ea.lock`, `Op.lockable` (the SDM's list,
transcribed), and one well-formedness test in `step`. It **un-declines `xchg` at a memory
operand** — D25's decline was about atomicity vocabulary, and this is that vocabulary — taking the
roster from **498 to 500 of the 525 rows** and the residue from 27 to 25. Eighteen vectors, four
planted arms, and the first batch in this repository whose subject has **no arithmetic at all**.

```
cases=68886  matched=49000  explained=28774  unexplained=0  oracle-leaks=0  missing=0
  spec: 0   refusal: 0   harness: 0   undefined-region: 28774
801 vectors · 86 pre-states · 84 mnemonics
```

⭐ **AND THE #UD EDGE IS CONFIRMED FROM THE ORACLE'S OWN OUTPUT, not inferred from a green.**
Zero unexplained disagreements would also be what a run in which both models silently executed
everything looked like, so the refusal channel was read directly:

```
lock movq %rax, (%rbx)   refused=1      lock addq %rcx, (%rbx)  refused=0
lock leaq (%rbx), %rax   refused=1      xchgq %rax, (%rbx)      refused=0
lock shlq $3, (%rbx)     refused=1      movq %rax, (%rbx)       refused=0   <- the control
```

x86isa raises #UD on exactly the three forms the SDM's list excludes and executes the ones it
includes — including the `xchg` this batch un-declined. The last column is the pair that makes the
first three evidence rather than silence: same operands, no prefix, executes.

## 1. ⛔ The roster said this would unblock six rows. It unblocks two. (D76)

`docs/P2-ROSTER.md` — a GENERATED document CI re-derives byte-for-byte — said the LOCK vocabulary
would unblock *"`xchg` at memory and the six `bt`-family memory forms"*. Three errors in one
sentence, every one of them flattering the item:

| the sentence | the repository |
|---|---|
| "the six `bt`-family memory forms" | there are **four**; six was the TOTAL of declined rows |
| "D25 declines … the `bt`-family" | **D23** declines them |
| "for want of a LOCK vocabulary" | their reason is signed **BIT-STRING addressing**, which no LOCK vocabulary touches |

The measurement settles it: claimed rows went **498 → 500**, not 498 → 504.

⇒ 🔑 **A DERIVATION GATE IS A WRAPPER A FALSE SENTENCE CAN SIT INSIDE.** `p2_roster.py --check`
proves the file matches what the script emits and says nothing about whether the script tells the
truth — and a hand-written paragraph inside a generated document reads as generated. The paragraph
is derived now, from two tables gated in opposite directions: `DECLINED` (what is still declined,
and by which decision) and `LOCK_UNBLOCKED` (what this addition unblocked — and `--check` requires
every row in it to be CLAIMED, so shrinking the residue fails loud instead of being a deletion
nobody checked).

## 2. What was added, and what it does not claim (D77)

| | |
|---|---|
| `Ea.lock : Bool` | the `f0` prefix, on the effective address |
| `Op.lockable` | the SDM's nineteen mnemonics, TRANSCRIBED |
| one `if` in `step` | a lock on an unlisted form is `#UD` |

**Why the flag is on `Ea`.** The manual permits the prefix *"only to those forms where the
destination operand is a memory operand"*, so on `Ea` a lock without a memory operand is
**unrepresentable** rather than a check somebody has to remember. ⚠️ It also could not go on
`Instr`: 799 vectors build it with `⟨op, len⟩`, and Lean's anonymous constructor requires every
explicit field even when the trailing one has a default — measured in a two-line probe, not
assumed.

**⛔ The list is transcribed, not inferred.** `CMPXCHG16B` is on it and is not in this roster;
**`MOV` is not on it**, is in this roster, and is the form a reader most expects to be lockable —
`lock movq %rax, (%rbx)` looks exactly like the atomic store somebody wants. A list derived from
"the memory-destination forms we have" would have admitted `mov`, the shift group and every
`cmp`/`test`, all #UD on silicon.

**And it does not claim atomicity.** A single-step, single-threaded semantics has no observation
that separates atomic from non-atomic. The flag RECORDS the property; `TRUSTBASE.md` says so in
its own section, with the boundary stated: a reader may rely on what a locked instruction
computes and on which forms accept the prefix, and on nothing about memory ordering.

## 3. ⛔ A batch with no arithmetic, and what that did to the arms

`lock addq %rcx, (%rbx)` and `addq %rcx, (%rbx)` are the **same function** here. No arm can catch a
model that ignores LOCK in the value channel, because there is nothing in that channel to catch.
What is observable is two EDGES: which forms the prefix makes #UD, and the form the vocabulary
un-declined. All four arms live there.

| arm | field | caught | total unexplained |
|---|---|---|---|
| the lock prefix is ignored, so an illegal lock executes | `mem@…1fe0` | 60 | **470** |
| the lockable list is widened to any memory destination | `mem@…1fe0` | 60 | **224** |
| the lockable list drops `xadd` and `cmpxchg8b` | `refused` | 164 | 786 |
| `xchg` at memory still refuses (the model before this batch) | `refused` | 328 | 1110 |

⚠️ **Two of them move the lockable list in OPPOSITE directions, deliberately.** A widened list is
caught by `lock_mov_m_q_ud`; a narrowed one by `lock_xadd_m_q` and its siblings. Neither can stand
in for the other.

⛔⛔ **AND THE FIRST RUN SHOWED THE FIRST TWO ARMS REPORTING THE SAME 60 DISAGREEMENTS IN THE SAME
FIELD, WITH THE SAME TOTAL — 224 AND 224.** They are different CLAIMS and were, on the vector set
as it first stood, the *same observation*: the only unlisted form carrying a lock was `mov`, so
"strip every lock" and "strip `mov`'s lock" could not be told apart.

⇒ 🔑 **TWO ARMS THAT AGREE TO THE CASE ARE ONE ARM.** A claim the vectors cannot distinguish is a
claim nothing tests, and here the evidence was sitting in the selftest's own output — an identical
count in an identical field — which is exactly the shape that reads as confirmation. Two vectors
fix it: `lock leaq (%rbx), %rax` (computes an address, writes no memory) and `lock shlq $3,(%rbx)`
(has a memory destination and is still not on the manual's list). Both #UD, both assemble. The
totals are **470 vs 224** now, and the separation is the measurement.

⚠️ **And the #UD vector's evidence is a PAIR.** Agreement where both models refuse is agreement
about nothing (batch 20), so `lock movq %rax, (%rbx)` is read against `mov_mr` —
`movq %rax, (%rbx)`, same operands, no prefix — which executes in every case of the same run.

## 4. ⭐ The harness could not see a prefix at all (D79)

`objdump -d` disassembles `f0 48 01 0b` as **two lines**: `f0  lock`, then `48 01 0b  addq`. So
`check_encodings.py` read every locked vector as a **one-byte** instruction.

⛔ **The direction is the finding.** The length check would have failed loudly on 4-vs-1 — but a
model that had silently DROPPED the prefix would have AGREED with that 1. **A harness that reads a
prefix as a separate instruction cannot see a model that ignores prefixes.**

A single-byte `f0` line is folded into its successor now, and the fold is gated by the same
three-source shape the segment override uses — the AT&T `lock` token, the `f0` prefix byte, and
the AST's `Ea.lock` must agree per vector, with an arm doctoring each source alone plus a control,
on every invocation. The third arm sets the first byte to something other than `f0`, which is
precisely the unfolded read, so the fold cannot quietly stop happening.

## 5. ⚖️ Three defects of my own, found while building this

1. **A positional index into a record that grew.** `oracle_availability.py` rewrote `c[4]` as the
   `:mem` line. P2 batch 1 inserted a `:fsbase`/`:gsbase` line into the case record, after which
   `c[4]` is `:rflags` and the rewrite placed no bytes at all. ⇒ 🔑 **A positional index into a
   record is a bet that the record will not grow**, and this repository lost that bet twice in six
   hours: batch 1's own oracle run read twelve results off their POSITION because the labels were
   not emitting. Found by content now.
2. **A gate that reused a stale input.** The same script read `if not os.path.exists(CASES)` — so
   it probed whatever `run/cases.lsp` was on disk, possibly from an older emit in an older record
   format. That is why the defect above did not fire in batch 1's run: the file it used predated
   the format change. It always re-emits now.
3. **A stale `DECLINED:` label.** That gate listed `DECLINED:xchg m,r` among the rows it measures,
   with a comment ending *"oracle support is not an argument to un-decline it."* Still true — what
   un-declined it was the vocabulary — but the row is CLAIMED now, and a probe labelling a claimed
   row `DECLINED:` publishes a decision the repository no longer holds. It stays in the run as
   `CLAIMED:xchg m,r`, because a row that just left the residue is exactly the one somebody will
   want to re-check.

## 6. And a fourth, in the sentence that describes the numbers (D78)

`docs/COVERAGE.md`'s roster line says its six numbers "ARE DERIVED, by
`scripts/claimed_forms.py`, and gated in CI". The second half is true; the first is not. The
numbers are **literals in the generator's string**, and the script derives the same six
independently and fails CI if they disagree. A derived number cannot be stale; a gated literal can
be stale until somebody runs the gate — and D56 exists because a literal nobody derived was eleven
low for eighteen batches. The sentence says GATED now, names both sources, and says plainly that
the numbers are written there and checked here.

## 7. The cost, paid once

`step`'s guard sits before the match, so every characterization theorem acquired a side condition:
**61 sites**. Marking the operand walk and the two predicates as `simp` definitions discharges it
structurally wherever the operands are registers — 61 down to **20** — and those 20 gained
`(hl : ea.lock = false)` or `(hl : o.locked = false)`.

⚠️ Those hypotheses are not bookkeeping. For `mov m,r` the theorem was making a claim that is now
FALSE for a locked operand, because a locked `mov` is #UD. Narrowing a claim that had become too
wide is the honest repair; hiding it behind a simp lemma would not have been.

## 8. The kernel cost, measured — and the ceiling raised as the THIRD option (D81)

```
X86.Theorems      733 ms (ceiling 540) ⛔   the guard, at the head of ~200 theorems
                  684 ms                    after the predicate went 3 list passes -> 1
                  678 ms (ceiling 1100) ok  registered at measured x1.6
total             24 100 ms                 (23 500 before this batch)
```

Two cheaper builds were taken before the ceiling moved: the predicate rewritten to one pass, with
its equality to the `opOperands` walk **proved by the compiler** so the duplicate cannot drift;
and the operand walk marked `simp` so 41 theorems keep their statements instead of gaining a
hypothesis. What is left is the feature's price — a guard at the head of `step` is work every
theorem about `step` must do, and the only design without it is one where a locked `mov` executes.

⚠️ **Conditions:** one-minute load 5.03 / five-minute 4.54, above the 2.2–4.1 band the tool
measured as having no effect. All three readings were taken minutes apart under the same
conditions, so the comparison between them is the safe part; the absolutes are loose.
