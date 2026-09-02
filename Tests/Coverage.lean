/-
# Tests.Coverage — the coverage table cannot drift from the model

Plan v1 §3.2: coverage is "a generated table, never prose".  A generated table
can still LIE, in two directions, and both are checked here:

* a row for a form the model no longer has (the table over-claims);
* a form the model has with no row (the table under-reports, which sounds
  harmless and is not — it means the tier and the decode-trust columns are
  silent about a form somebody may be relying on).

The usual coverage-claim failure is the first, and the usual test only catches
the second.  Both directions are `decide`d below.

A THIRD check, which is the one that would actually have caught a real drift:
every mnemonic in the table must appear in the DIFFERENTIAL VECTOR TABLE.  A row
claiming `T-exact` for a form that no vector ever executes is a claim backed by
nothing.

LANE. Personal lane, public sources only.
-/
import X86
import Tests.Vectors

namespace X86.Tests
open X86

/-! ⚠️ `maxRecDepth` bounds the ELABORATOR's own recursion, and the checks in
this file walk the whole vector table — 260 entries at batch 5 and growing every
batch — so the default is exceeded by the honest checks rather than by anything
clever.  It changes NOTHING about what is proved and nothing about the axioms a
proof rests on: `scripts/axiom_gate.sh` runs over this development unchanged and
still reports exactly `propext`, `Classical.choice` and `Quot.sound`.

It is set once here rather than sprinkled per theorem, because a limit that has
to be raised again at every batch is a property of the file, not of a line. -/
set_option maxRecDepth 40000

/-- Every mnemonic the coverage table names is one the AST roster names. -/
theorem table_mnemonics_subset_roster :
    (tableP0.map Row.mnemonic).all (fun m => rosterP0.contains m) = true := by decide

/-- And every mnemonic in the roster has a row: no silent omission. -/
theorem roster_covered_by_table :
    rosterP0.all (fun m => (tableP0.map Row.mnemonic).contains m) = true := by decide

/-- The table has exactly one row per implemented mnemonic, and no duplicates.
The count is `rosterSize` rather than a literal, so this theorem and
`roster_size_matches` below cannot drift apart — twenty-two today, because P1
batch 2 added `adc` and `sbb`. -/
theorem table_row_count : tableP0.length = rosterSize := by decide

theorem table_rows_distinct :
    (tableP0.map Row.mnemonic).eraseDups.length = tableP0.length := by decide

theorem roster_size_matches : rosterP0.length = rosterSize := by decide

/-- And the literal, stated ONCE, so that growing the roster is a visible
one-line change rather than a silent one.  P0 left here with twenty; batch 2
added `adc`/`sbb`, batch 5 `jrcxz`/`jecxz`, batch 6 `setcc`/`cmovcc`, batch 7 `sar`, batch 8 the four rotates, batch 9 the four bit-tests, batch 10 `movzx`/`movsx`, the six accumulator sign-extensions, `xchg` and `bswap`, batch 11 the three loop predicates and the five flag-control singles. -/
theorem roster_size_is_53 : rosterSize = 53 := by decide

/-! ### ⛔ THE PRODUCT THAT WAS GROWING, AND WHAT IT ACTUALLY WAS

P1 batch 9 handed on a scaling problem with a diagnosis: this module's kernel
time ran 378 → 1960 → 3130 → 6520 ms across batches 3, 5, 7 and 9, and the cause
was recorded as (assertions × vectors × PRE-STATES).

⭐ BATCH 10 MEASURED IT INSTEAD OF INHERITING IT, AND THE PRE-STATES ARE NOT IN
IT.  Adding batch 10's eight new theorems — three of them over (vector ×
pre-state) — cost **720 ms**.  Adding batch 10's THIRTY-THREE VECTORS, with no
new theorem at all, cost **2400 ms**.  The vector table grew 7% and the module
grew 37%.

So the growing factor is the VECTOR TABLE, and a batch multiplies it against
the table rows as well: 35 → 45 rows is +29%, 474 → 507 vectors is +7%.  Three
theorems here were each a (rows × vectors) sweep of STRING equalities — 22 815
of them at batch 10's 45 × 507, on `List Char` — and `hasMemDestVector` re-swept
the WHOLE vector table once per claiming row.

⚠️ The two figures above are batch 10's and are left at batch 10's values on
purpose: they are the MEASUREMENT that motivated the collapse, and a measurement
re-typed at each batch stops being one.  The shapes below are stated without
counts for the opposite reason — they describe what the code does, and a count
in that sentence is prose no gate reads, drifting one batch after it is written.

Collapsing the inner factor once instead of per row (`vectorMnemonics`,
`memDestMnemonics`) and hoisting the pre-states' 80-byte background pattern to a
closed constant (`Tests/Vectors.lean`, `baseMem`) takes the module 9640 → 8250
ms.  None of it weakens anything: `List.contains` and `List.all` cannot tell a
list from its duplicate-free image, and the hoisted bytes are identical.

⛔ AND THE HONEST PART: THAT RECOVERED 1390 OF THIS BATCH'S OWN 2400 ms, SO 1010
ms OF THE GROWTH IS STILL UNACCOUNTED FOR.  The three collapses were aimed at
the products that were easiest to SEE, and between them they explain a little
over half of what the vectors cost.  The remainder is somewhere in the ~20 other
theorems that scan the table, and the next head should measure per theorem
rather than reason about shapes — which is the mistake this note is correcting
in its own inherited diagnosis.  The ceiling is untouched at 19560 with 2.4×
headroom, so there is room to do that properly rather than under pressure. -/

/-- The mnemonics the differential vector table exercises, without duplicates.
Named so the three theorems below share one reduction rather than each
re-deriving it 45 times. -/
def vectorMnemonics : List String := (vectors.map Vec.mnemonic).eraseDups

/-- ⭐ EVERY ROW IS BACKED BY AT LEAST ONE DIFFERENTIAL VECTOR.  A tier claim for
a form nothing executes is a claim backed by nothing. -/
theorem every_row_has_a_vector :
    (tableP0.map Row.mnemonic).all
      (fun m => vectorMnemonics.contains m) = true := by decide

/-- And every vector's mnemonic is one the table knows about, so a form cannot
be tested while being absent from the published coverage. -/
theorem every_vector_has_a_row :
    vectorMnemonics.all
      (fun m => (tableP0.map Row.mnemonic).contains m) = true := by decide

/-- Every implemented mnemonic is exercised by at least one differential vector
— the count above is matched by the vector table, not merely by the roster. -/
theorem vectors_cover_the_roster :
    vectorMnemonics.length = rosterSize := by decide

/-- No form is in the `T-absent` tier: every roster form is modelled.
When P1 adds a refused form this theorem is the one that must change, and
changing it is a deliberate act rather than a silent drift. -/
theorem no_absent_forms_at_p0 :
    (tableP0.filter (fun r => r.tier == Tier.absent)).length = 0 := by decide

/-- Every form's decode trust is `xed` at P0 — nothing here is proved-decoded.
This theorem is what makes the decode-trust column an ASSERTION rather than a
decoration: when P4 lands a proved decoder, this fails and must be updated. -/
theorem all_decode_trust_is_xed_at_p0 :
    tableP0.all (fun r => r.decode == DecodeTrust.xed) = true := by decide

/-- The forms that draw from the undefined-bit oracle are EXACTLY the ones the
table marks `T-frame`.  This is the table's tier column checked against its own
undefined column — an internal consistency the reader would otherwise have to
verify by eye across twenty rows. -/
theorem frame_tier_iff_undefined_bits :
    tableP0.all (fun r => (r.tier == Tier.frame) == !r.undefined.isEmpty) = true := by decide

/-! ## The pre-state set's own coverage

⭐ THESE ASSERT PROPERTIES OF THE PRE-STATES, NOT OF THE MODEL, and that is the
gap they close.  Every other check here asks whether the table matches the AST.
None of them can see that a rule's boundary has stopped being crossed — the
coverage table would read exactly the same, every vector would still run, and
the differential run would still come back clean, because a rule nothing
exercises cannot disagree with anything.

The carry boundary was crossed by ACCIDENT before P1 batch 2 noticed
(`Tests/Vectors.lean`, `carryBoundary`): two adjacent constants in `adversarial`
happen to be complements. An accident is not a gate. -/

/-- Some pre-state puts `adc` exactly on the carry boundary at width q: the two
operands sum to `2^64 - 1`, so the carry-in ALONE decides the carry-out. -/
theorem pre_states_cross_the_carry_boundary_q :
    (preStates 1 8).any (fun s =>
      s.flags.cf && (s.regs.rax + s.regs.rcx == 0xFFFFFFFFFFFFFFFF)) = true := by decide

/-- And at width b, where the operands are truncated to a byte. -/
theorem pre_states_cross_the_carry_boundary_b :
    (preStates 1 8).any (fun s =>
      s.flags.cf && ((s.regs.rax &&& 0xFF) + (s.regs.rcx &&& 0xFF) == 0xFF)) = true := by decide

/-- The borrow boundary for `sbb`: minuend equals subtrahend with CF set, so the
borrow comes only from the carry-in. -/
theorem pre_states_cross_the_borrow_boundary :
    (preStates 1 8).any (fun s =>
      s.flags.cf && (s.regs.rax == s.regs.rcx)) = true := by decide

/-- ⚠️ AND BOTH VALUES OF CF ARE PRESENT.  A pre-state set in which CF is always
set, or never, makes every carry-reading form a constant function of its
operands and the differential run cannot tell `adc` from `add`. -/
theorem pre_states_sweep_cf :
    ((preStates 1 8).any (fun s => s.flags.cf)
      && (preStates 1 8).any (fun s => !s.flags.cf)) = true := by decide

/-! ### P1 BATCH 3 — the MEMORY OPERAND's own coverage

⛔ THE HOLE THESE CLOSE WAS FOUND BY LOOKING, NOT BY A FAILURE.  Until batch 3
`mkPre` wrote the SAME 32-byte pattern into the data window in every pre-state,
so every `_rm_` form shipped by batches 1 and 2 — twenty vectors — read one
single source value seventy-four times.  Nothing was wrong: the runs were green
and the green was real.  But a form whose source operand never moves is ONE test
reported as seventy-four, and no gate in this repository could see the
difference, because the coverage table counts FORMS and the differential run
counts CASES and neither counts VALUES.

The window's operand span now carries RCX, so a memory operand sweeps exactly as
a register one does.  These three theorems are what stop it silently reverting:
the first states the invariant, the second states that the invariant has TEETH
(a constant window satisfies the first only if RCX is also constant, and it is
not), the third states the margin still is not swept, so an over-wide access
remains visible. -/

/-- The memory operand every vector addresses IS the value RCX carries. -/
theorem memory_operand_mirrors_rcx :
    (preStates 1 8).all (fun s => s.mem.readSize .q 0x2000 == s.regs.rcx) = true := by decide

/-- ⚠️ AND IT REALLY SWEEPS.  Twenty distinct values at least — the whole
adversarial list — so a memory operand is a peer of a register operand and not a
constant wearing its shape. -/
theorem memory_operand_sweeps :
    20 ≤ ((preStates 1 8).map (fun s => s.mem.readSize .q 0x2000)).eraseDups.length := by
  decide

/-- The MARGIN on either side of the operand span keeps its fixed pattern, which
is what makes a store that ran off the end of its width visible as a difference
OUTSIDE the span rather than not at all. -/
theorem memory_window_margin_is_fixed :
    (preStates 1 8).all (fun s =>
      s.mem.read 0x1ff0 == 0xA0 && s.mem.read 0x2008 == 0xB8) = true := by decide

/-- ⭐ SOME VECTOR PUTS A MEMORY OPERAND IN A `cmp` DESTINATION.  This is the
shape a `cmp` that writes its result back is invisible without — the harness
selftest's hard arm was run with these vectors deleted and caught NOTHING
(docs/DIFFERENTIAL-P1-BATCH3.md), so this theorem is the standing statement of
a fact that was measured rather than assumed. -/
theorem vectors_have_a_memory_destination :
    vectors.any (fun v => match v.instr.op with
      | .bin .cmp _ d _ => d.isMem
      | _ => false) = true := by decide

/-- ⭐ AND SOME VECTOR IS RIP-RELATIVE.  `Ea.addr`'s `ripRel` branch existed from
P0 and until batch 3 no differential vector executed it: the only evidence was a
`lea` anchor, i.e. this model checked against itself. -/
theorem vectors_exercise_rip_relative :
    vectors.any (fun v => match v.instr.op with
      | .bin _ _ (.mem ea) _ => ea.ripRel
      | _ => false) = true := by decide

/-! ### The SHAPES column, which is prose, and prose overclaims

⛔ FOUND IN BATCH 3 BY READING THE TABLE INSTEAD OF THE MODEL.  The row for
`and`/`or`/`xor` claimed the operand shape `m,r (q)` — a memory DESTINATION —
and no such vector has ever existed: batch 1 shipped `and_rm_*` (a memory
SOURCE with a register destination) and the shapes string transposed it.  The
memory-destination logic forms are roster family 4, a batch that has not been
run yet.

Every theorem above is about MNEMONICS, so not one of them could see it: `and`
has a row, `and` has vectors, `and` is in the roster, and the table's most
detailed column was still describing coverage the repository does not have.
That is the over-claim direction this file's own header names FIRST and then
checks only at the granularity of the mnemonic.

The check below closes it at the granularity that failed.  It is deliberately
narrow — one shape, the one that was wrong — because a check that tried to parse
the whole prose column would be a parser, and a parser is a second thing to get
wrong.  ⭐ IT WAS DRIVEN RED: with the `m,r (q)` still in `logicShapes` this
theorem does not compile, which is how it is known to have teeth. -/

/-- Does this row's shapes column claim a memory DESTINATION?  The table writes
shapes destination-first, so `m,r` is "memory destination, register source" —
the transposition of `r,m`, and the reason the claim was easy to get backwards.

⚠️ The substring test is written on CHARACTER LISTS rather than with
`String.splitOn`, and not for taste: `splitOn` is defined by well-founded
recursion, the kernel does not unfold it, and `decide` fails on a proposition
that is TRUE — a gate that cannot be evaluated is not a weaker gate, it is a
build error wearing a gate's clothes. `isInfixOfChars` recurses structurally and
reduces. -/
private def isInfixOfChars (pat : List Char) : List Char → Bool
  | [] => pat.isEmpty
  | c :: rest => pat.isPrefixOf (c :: rest) || isInfixOfChars pat rest

def claimsMemDest (r : Row) : Bool :=
  isInfixOfChars "m,r".toList r.shapes.toList
  -- and the UNARY form of the same claim.  `inc`/`dec` have no source operand,
  -- so `m,r` cannot express their memory destination — and writing them as
  -- `m,r` anyway, to make them trip the first pattern, would be notation bent
  -- to fit its own gate, which is the failure this gate exists to catch one
  -- level up.
  --
  -- ⛔ THE FIRST ATTEMPT AT THIS PATTERN WAS `· m ` AND IT WAS WRONG, in a way
  -- worth keeping: it fired on `push`, whose shapes read `r · m · imm`, where
  -- `m` is a memory SOURCE and not a destination at all.  The shapes column had
  -- no notation distinguishing the two for unary forms — `inc`'s `m` is written
  -- and `push`'s is read — so the pattern could not mean what it needed to
  -- mean. ⇒ **A CHECK CANNOT BE MORE PRECISE THAN THE NOTATION IT READS**, and
  -- the fix belonged in the notation: a written memory destination is now
  -- `m(rmw)`.
  --
  -- ⭐ AND THE WRONG PATTERN EARNED ITS KEEP ON THE WAY OUT.  Firing on `push`
  -- is how it came out that `push` claimed `m` and `imm`, `pop` claimed `m`, and
  -- `neg`/`not` claimed `r/m`, with NOT ONE vector among them — four more rows
  -- over-claiming exactly as `and`/`or`/`xor` had, and four more the
  -- mnemonic-level theorems could not see.  All four are now narrowed to what
  -- is executed, with the roster family that will earn each back named in the
  -- row.
  -- ⭐ GENERALISED IN BATCH 6 from the literal `m(rmw)` to the PREFIX `m(`.
  -- `setcc`'s memory form is a WRITE that never reads its destination, so
  -- `m(rmw)` would be a false description of it and `m(w)` is the honest one —
  -- and a gate that only knew one spelling would have pushed the notation to
  -- lie, which is D16's failure exactly. The parenthesis is what makes a
  -- MEMORY-DESTINATION claim distinguishable from `r,m`'s memory source, and
  -- what goes inside it is free to say which kind of write it is.
  || isInfixOfChars "m(".toList r.shapes.toList

/-- Does this vector write (or, for `cmp`/`test`, address) a MEMORY
DESTINATION?

⚠️ IT ENUMERATES AST CONSTRUCTORS, so it goes stale the moment `Op` grows — it
did exactly that in batch 8, when `.rot` arrived and this function answered "no
vector" to a true claim.  It fails CLOSED, which is the right direction, but the
maintenance cost is real and it belongs in the same commit as the new
constructor.  Batch 10's four new constructors are below, added here rather than
after a gate refused them. -/
def isMemDestVector (v : Vec) : Bool :=
  (match v.instr.op with
    | .bin _ _ d _ => d.isMem
    | .mov _ d _ => d.isMem
    | .un _ _ d => d.isMem
    | .shift _ _ d _ => d.isMem
    -- ⭐ ADDED IN BATCH 8, AND THE GATE IS WHY.  The four rotate rows claim
    -- `m(rmw)` and have the vectors for it, but this function did not know the
    -- `.rot` constructor existed, so it answered "no vector" and the theorem
    -- failed.  A checker that enumerates constructors goes STALE the moment the
    -- AST grows, and it fails CLOSED — refusing a true claim — which is the
    -- right direction to fail but still a thing that must be fixed rather than
    -- worked around by weakening the row.
    | .rot _ _ d _ => d.isMem
    -- ⭐ ADDED WITH `.bit` ITSELF in batch 9, rather than after the gate refused
    -- a true claim as it did for `.rot` in batch 8.  The staleness is a
    -- property of enumerating a growing type; the remedy is to extend this
    -- function in the same commit that extends `Op`.
    | .bit _ _ d _ => d.isMem
    | .pop _ d => d.isMem
    -- P1 BATCH 10.  ⭐ ALL FOUR ANSWER `false`, AND THAT IS THE CLAIM RATHER
    -- THAN AN OMISSION: `movx`'s and `bswap`'s destinations are REGISTERS by
    -- the type (a `GPR`, not an `Operand`), `cext` has no operands at all, and
    -- `xchg` REFUSES a memory operand (D25).  Written out so that a later
    -- reader sees a decision rather than a gap — and so that the day `xchg`
    -- earns its memory forms, the line to change is here.
    | .movx .. => false
    | .cext _ => false
    | .xchg _ a b => a.isMem || b.isMem
    | .bswap .. => false
    | _ => false)

/-- The mnemonics that HAVE such a vector, collapsed ONCE.  Asking the question
per row re-swept the WHOLE vector table for every claiming row; the set it is
really asking about has at most `rosterSize` elements.  See the note above
`vectorMnemonics`. -/
def memDestMnemonics : List String :=
  ((vectors.filter isMemDestVector).map Vec.mnemonic).eraseDups

/-- Is there a differential vector for this mnemonic whose DESTINATION operand
is memory? -/
def hasMemDestVector (m : String) : Bool := memDestMnemonics.contains m

/-- ⭐ EVERY MEMORY-DESTINATION CLAIM IN THE TABLE IS BACKED BY A VECTOR THAT
ACTUALLY WRITES (or, for `cmp`/`test`, addresses) A MEMORY DESTINATION.
 -/
theorem mem_dest_claims_are_backed :
    tableP0.all (fun r => !claimsMemDest r || hasMemDestVector r.mnemonic) = true := by decide

/-! ### P1 BATCH 5 — the condition column, made checkable

⛔ THE ROW FOR `jcc` SAID "all 16 conditions" AND HAD VECTORS FOR TWO.  It is
the same defect as D15 and D16 in a column that reads like a count rather than a
claim: a sentence in the shapes string asserting coverage that nothing checked.
Sixteen is now a theorem. -/

/-- Every condition code has a differential vector. -/
theorem vectors_cover_every_condition :
    Cc.all.all (fun c => vectors.any (fun v => match v.instr.op with
      | .jcc c' _ => c' == c
      | _ => false)) = true := by decide

/-- And at BOTH relative encodings, which is what `rel8 · rel32` claims: some
condition-code vector is two bytes long and some is six. -/
theorem conditions_covered_at_both_encodings :
    (vectors.any (fun v => match v.instr.op with
       | .jcc _ _ => v.instr.len == 2 | _ => false)
     && vectors.any (fun v => match v.instr.op with
       | .jcc _ _ => v.instr.len == 6 | _ => false)) = true := by decide

/-- ⭐ THE 30 SPELLINGS THE `jcc` ROW CLAIMS.  K files the synonyms separately —
`jz` and `je` are two files and one instruction — so a coverage claim over K's
roster has to name them.  `Cc.synonyms` is that list and this counts it, so the
number in the shapes column cannot drift from the table behind it. -/
theorem thirty_branch_spellings :
    (Cc.all.flatMap Cc.synonyms).eraseDups.length = 30 := by decide

/-- ⚠️ AND SOME PRE-STATE HAS RCX NON-ZERO WITH ECX ZERO.  That single point is
the only place `jrcxz` and `jecxz` disagree, so without it the address-size
prefix is unexercised and a model reading one width for both would pass.
TWO constants in `adversarial` reach it — `0x100000000` and
`0x8000000000000000` — and either alone suffices, which is precisely why this
theorem names NEITHER: it asserts the point is reached, not how.  Removing both
makes the differential's `jecxz` arm catch zero and makes this theorem fail, so
for the first time here such an assertion is standing in FRONT of a coverage
loss rather than being written after one. -/
theorem pre_states_separate_rcx_from_ecx :
    (preStates 1 8).any (fun s =>
      s.regs.rcx != 0 && (s.regs.rcx &&& 0xFFFFFFFF) == 0) = true := by decide

/-! ### P1 BATCH 6 — 120 forms over two `step` cases

⭐ The same sixteen predicates spell every `Jcc`, `SETcc` and `CMOVcc`.  K files
90 mnemonics for them; `Cc` has 16 constructors because a predicate is the
instruction and the spelling is the assembler's.  These theorems are what make
that a counted claim rather than a pleasing sentence. -/

theorem vectors_cover_every_setcc_condition :
    Cc.all.all (fun c => vectors.any (fun v => match v.instr.op with
      | .setcc c' _ => c' == c
      | _ => false)) = true := by decide

theorem vectors_cover_every_cmov_condition :
    Cc.all.all (fun c => vectors.any (fun v => match v.instr.op with
      | .cmov c' _ _ _ => c' == c
      | _ => false)) = true := by decide

/-- Thirty spellings each, from the one suffix table. -/
theorem thirty_set_spellings :
    (Cc.all.flatMap Cc.setSpellings).eraseDups.length = 30 := by decide

theorem thirty_cmov_spellings :
    (Cc.all.flatMap Cc.cmovSpellings).eraseDups.length = 30 := by decide

/-- ⚠️ AND THE 32-BIT `cmov` FORMS ARE PRESENT, which is not a formality: the
unconditional write is observable only at width `d`, so a `cmov` vector set
without it cannot tell this model from one that skips the write when the
condition is false. -/
theorem cmov_covered_at_width_d :
    vectors.any (fun v => match v.instr.op with
      | .cmov _ sz _ _ => sz == Size.d
      | _ => false) = true := by decide

/-! ### P1 BATCH 7 — the shift group -/

/-- Every shift kind reaches BOTH destinations.  The memory forms are roster
families 8, 12 and 60 and had no vector before this batch. -/
theorem shifts_cover_both_destinations :
    [ShiftKind.shl, ShiftKind.shr, ShiftKind.sar].all (fun k =>
      vectors.any (fun v => match v.instr.op with
        | .shift k' _ d _ => k' == k && d.isMem
        | _ => false)
      && vectors.any (fun v => match v.instr.op with
        | .shift k' _ d _ => k' == k && !d.isMem
        | _ => false)) = true := by decide

/-- ⭐ SOME `sar` CASE ACTUALLY RUNS AT A COUNT ≥ ITS OPERAND WIDTH.  That is the
only place SAR's CF rule differs from SHR's — the SDM leaves SHL's and SHR's CF
undefined there and says nothing of the kind about SAR, so SAR's CF is the SIGN.

⛔ THE FIRST VERSION OF THIS THEOREM QUANTIFIED OVER VECTORS ALONE, matching only
an `.imm8` count, and it was WRONG IN THE DIRECTION THAT LOOKS SAFE.  Deleting
`sar_b9` made it FAIL — while the differential arm it guards still caught the
bug, 49 disagreements instead of 79, because `sarb %cl, %al` reaches the same
region whenever RCX's low five bits are ≥ 8, which many pre-states satisfy.

⇒ **AN ASSERTION NARROWER THAN THE COVERAGE IT GUARDS REPORTS A LOSS THAT HAS
NOT HAPPENED**, and a gate that cries wolf is one somebody eventually switches
off. It is the mirror of the over-claiming coverage column: there, prose claimed
more than the tests reached; here, a theorem claimed less.

So it quantifies over (vector × PRE-STATE), which is what "the tests reach this
region" actually means, and is the same shape as the carry-boundary and
RCX/ECX assertions. -/
theorem sar_reaches_count_ge_width :
    vectors.any (fun v => match v.instr.op with
      | .shift .sar sz _ amt =>
          (preStates 1 8).any (fun st =>
            let c : BitVec 8 := match amt with
              | .imm8 x => x
              | .cl => (st.getReg .b .rcx).setWidth 8
            sz.bits ≤ Flags.shiftCount sz c)
      | _ => false) = true := by decide

/-! ### P1 BATCH 8 — the rotate group -/

/-- ⭐ SOME ROTATE CASE RUNS AT A FULL TURN: a masked count that is a NON-ZERO
multiple of the operand width, where the data does not move and CF is written
anyway.  That single shape is the only place the masked and reduced counts
disagree for `rol`/`ror`, and a model keying its CF write on the reduced count
is correct everywhere else.

Quantified over (vector × pre-state) per D21, so a `cl` form supplying the same
count keeps it satisfied and the gate does not cry wolf. -/
theorem rotates_reach_a_full_turn :
    vectors.any (fun v => match v.instr.op with
      | .rot k sz _ amt =>
          (k == RotKind.rol || k == RotKind.ror)
          && (preStates 1 8).any (fun st =>
            let c : BitVec 8 := match amt with
              | .imm8 x => x
              | .cl => (st.getReg .b .rcx).setWidth 8
            let n := Flags.rotMasked sz c
            n ≠ 0 && Flags.rotReduced k sz n = 0)
      | _ => false) = true := by decide

/-- And `rcl`/`rcr` reach their OWN zero, which is a different count because they
reduce modulo width+1 — `rclb $9`, not `$8`. -/
theorem carry_rotates_reach_their_own_zero :
    vectors.any (fun v => match v.instr.op with
      | .rot k sz _ (.imm8 c) =>
          (k == RotKind.rcl || k == RotKind.rcr)
          && (let n := Flags.rotMasked sz c
              n ≠ 0 && Flags.rotReduced k sz n = 0)
      | _ => false) = true := by decide

/-! ### P1 BATCH 10 — the width-changing and two-destination moves

⭐ THIS BATCH WRITES NO FLAGS AT ALL, so none of the assertions below are about
a flag rule.  They are about the three things that CAN be lost silently here:
a destination width whose write PRESERVES rather than zero-extends, a source
whose sign bit is set (without which a sign extension and a zero extension are
the same function), and a register that was zero in every pre-state until this
batch put something in it. -/

/-- ⭐ SOME PRE-STATE HAS A NON-ZERO UPPER HALF IN RDX, and until this batch none
did — RDX was zero in all seventy-four.

`cwtd`/`cltd`/`cqto` are the first instructions in this model to write a
register their operands do not name, and `cltd`'s write is 32 bits wide, so it
CLEARS RDX's upper half (SDM Vol. 1 §3.4.1.1).  A model that merged instead —
which is what the 16-bit rule does and what a reader who saw one rule for three
mnemonics would write — is indistinguishable from the correct one whenever RDX
starts at zero.  Deleting `rdx := ~~~a` from `mkPre` makes the differential's
`cltd` arm catch NOTHING and makes this theorem FAIL; see
docs/DIFFERENTIAL-P1-BATCH10.md for both halves of that probe. -/
theorem pre_states_give_rdx_a_nonzero_upper_half :
    (preStates 1 8).any (fun s => (s.regs.rdx >>> 32) != 0) = true := by decide

/-- Both extensions are present.  With only one of the two in the table, the
`movx` constructor's `MovxKind` argument would be a constant and a model that
ignored it entirely would pass. -/
theorem movx_covers_both_extensions :
    ([MovxKind.zero, MovxKind.sign].all (fun k =>
      vectors.any (fun v => match v.instr.op with
        | .movx k' _ _ _ _ => k' == k
        | _ => false))) = true := by decide

/-- ⭐ AND SOME SIGN-EXTENDING CASE ACTUALLY READS A NEGATIVE SOURCE.  A
`movsx` whose source has a clear sign bit computes exactly what `movzx` does, so
without this the two extensions are one function under test and a `movsx`
implemented as `movzx` would agree everywhere.

Quantified over (vector × PRE-STATE) per D21: the sign bit is a property of the
STATE, not of the vector, so an assertion over vectors alone would be asserting
something it cannot see. -/
theorem movx_reaches_a_negative_source :
    vectors.any (fun v => match v.instr.op with
      | .movx .sign _ ssz _ src =>
          (preStates 1 8).any (fun st =>
            Value.msb ssz (st.readOperand ssz (st.rip + BitVec.ofNat 64 v.instr.len) src))
      | _ => false) = true := by decide

/-- ⭐ SOME WIDTH-CHANGING MOVE WRITES A 16-BIT DESTINATION OVER A REGISTER WITH
SOMETHING IN ITS UPPER BITS.  `.w` is the only destination width here that
PRESERVES what is above it; `.d` zero-extends and `.q` replaces.  A model that
extended to 64 bits and wrote all 64 is correct at `.d` and `.q` and wrong only
here — and only when there was something above bit 15 to destroy.

Over (vector × pre-state) for the same reason as above: "there is something in
the upper bits" is a fact about the state. -/
theorem movx_writes_a_preserving_destination :
    vectors.any (fun v => match v.instr.op with
      | .movx _ .w _ dst _ =>
          (preStates 1 8).any (fun st => (st.regs.get dst >>> 16) != 0)
      | _ => false) = true := by decide

/-- ⭐ SOME `xchg` RUNS AT WIDTH `d`, where the swap is observable in the bits it
does NOT move: each of the two writes zero-extends, so both registers lose their
upper halves.  At `b`, `w` and `q` a swap of values is the whole instruction. -/
theorem xchg_covered_at_width_d :
    vectors.any (fun v => match v.instr.op with
      | .xchg sz _ _ => sz == Size.d
      | _ => false) = true := by decide

/-- ⚠️ AND THE TWO OPERAND ORDERS ARE ONE ENCODING.  The coverage row claims
`acc,r` and `r,acc` — two roster forms — and says they are the same bytes.  This
is that sentence as an assertion: the vector table holds both spellings, and
their `bytes` agree.  `scripts/check_encodings.py` is what makes each of those
byte strings the assembler's rather than ours, so the two together say the
assembler emits one encoding for both orders. -/
theorem xchg_operand_orders_are_one_encoding :
    (match vectors.find? (fun v => v.id == "xchg_rr_w"),
           vectors.find? (fun v => v.id == "xchg_ar_w") with
     | some a, some b => a.bytes == b.bytes && a.instr.len == b.instr.len
     | _, _ => false) = true := by decide

/-- The two trios write DIFFERENT REGISTERS, and both are exercised: one vector
widens the accumulator in place, another fills RDX with its sign.  A model that
sent all six to the same register would otherwise be caught only by whichever
trio happened to have a vector. -/
theorem cext_covers_both_destinations :
    (vectors.any (fun v => match v.instr.op with
       | .cext k => k == CextKind.cbw || k == CextKind.cwde || k == CextKind.cdqe
       | _ => false)
     && vectors.any (fun v => match v.instr.op with
       | .cext k => k == CextKind.cwd || k == CextKind.cdq || k == CextKind.cqo
       | _ => false)) = true := by decide

/-! ### P1 BATCH 11 — what the loop group and the flag singles need to be TESTED

Two of the four assertions below are about the PRE-STATES rather than the
vectors, and that is the batch's shape: both new mechanisms were unobservable in
the state set as it stood, for two different reasons.  See docs/DECISIONS.md
D27. -/

/-- ⛔ SOME PRE-STATE SETS DF, AND UNTIL THIS BATCH NONE DID — in seventy-four
states `df` was `false`, and no instruction in the model could write it.

`cld` clears DF.  Against a state where DF is already clear, **`cld` and a
no-op are the same function**: the differential would have compared the flag,
found it equal, and reported agreement it never tested.  `Serialize.lean` has
diffed `df` since P0, which is what made the gap invisible — the comparator was
working perfectly on a bit that could not move.

Deleting `dfStates` from `preStates` makes the differential's `cld` arm catch
NOTHING and makes this theorem FAIL.  Both halves of that probe are in
docs/DIFFERENTIAL-P1-BATCH11.md. -/
theorem pre_states_set_df :
    ((preStates 1 8).any (fun s => s.flags.df)
      && (preStates 1 8).any (fun s => !s.flags.df)) = true := by decide

/-- ⛔ AND SOME PRE-STATE HAS ECX = 1 OVER A NON-ZERO UPPER HALF, which no
pre-state had either.  `addr32 loop` tests `ECX - 1`; a model that tested
`RCX - 1` differs from it on exactly the states where one is zero and the other
is not — that is, where the low 32 bits of RCX are 1 and the upper half is not
zero.  `adversarial` holds 1 (upper half zero) and `0x100000000` (low half
zero) and nothing that is both.

⚠️ This is the same defect as `pre_states_set_df` in a different dress: there a
COMPONENT no instruction wrote, here a COMBINATION no value reached. -/
theorem pre_states_reach_ecx_one_over_a_nonzero_upper_half :
    (preStates 1 8).any (fun s =>
      (Value.trunc .d s.regs.rcx == 1) && ((s.regs.rcx >>> 32) != 0)) = true := by decide

/-- Both counter widths are in the vector table.  With only the unprefixed form,
`addr32` would be a constant `false` in every executed vector and a model that
ignored the address-size prefix entirely would pass — which is exactly the bug
`jecxz` planted at batch 5, arriving again on a different instruction. -/
theorem loop_covers_both_counter_widths :
    (vectors.any (fun v => match v.instr.op with | .loop _ a32 _ => a32 | _ => false)
     && vectors.any (fun v => match v.instr.op with
          | .loop _ a32 _ => !a32 | _ => false)) = true := by decide

/-- All three loop predicates are exercised, and at both widths.  `loope` and
`loopne` are the only forms in the group that read a flag, and they read it with
opposite polarity: a model that confused them passes every `loop` vector. -/
theorem loop_covers_all_three_predicates :
    LoopKind.all.all (fun k =>
      vectors.any (fun v => match v.instr.op with
        | .loop k' _ _ => k' == k
        | _ => false)) = true := by decide

/-- ⭐ AND ONE LOOP VECTOR BRANCHES BACKWARDS, which is the shape every real loop
has and which no other branch vector in this repository has.  A displacement
whose sign is dropped — or added rather than subtracted — is invisible against a
table of forward jumps.  The test is on the top bit of the 64-bit `d`, which the
decoder has already sign-extended. -/
theorem some_loop_vector_branches_backwards :
    vectors.any (fun v => match v.instr.op with
      | .loop _ _ d => Value.msb .q d
      | _ => false) = true := by decide

/-- The five roster spellings of the three loop predicates, counted rather than
claimed — the same discipline `thirty_branch_spellings` applies to `Cc`.
`loopz` is `loope` and `loopnz` is `loopne`, and clang assembles each pair to
identical bytes, so the collapse is a fact about the machine. -/
theorem five_loop_spellings :
    (LoopKind.all.flatMap loopSpellings).eraseDups.length = 5 := by decide

/-- Every flag-control single is exercised, and the two that write DF are among
them.  Five one-byte instructions written from one `match` is exactly the shape
where one case silently does what its neighbour does. -/
theorem every_flag_single_has_a_vector :
    ([FlagOp.clc, .stc, .cmc, .cld, .std].all (fun k =>
      vectors.any (fun v => match v.instr.op with
        | .flagop k' => k' == k
        | _ => false))) = true := by decide

end X86.Tests
