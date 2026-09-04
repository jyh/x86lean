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
added `adc`/`sbb`, batch 5 `jrcxz`/`jecxz`, batch 6 `setcc`/`cmovcc`, batch 7 `sar`, batch 8 the four rotates, batch 9 the four bit-tests, batch 10 `movzx`/`movsx`, the six accumulator sign-extensions, `xchg` and `bswap`, batch 11 the three loop predicates and the five flag-control singles, batch 12 `nop`/`ud2`/`retq`/`leaveq`, batch 13 `sarx`/`shlx`/`shrx`/`movbe`, batch 14 the bit-counting six, batch 15 the string five (`movs`/`stos`/`lods`/`cmps`/`scas`), batch 16 the three repeat prefixes (`rep`/`repe`/`repne`, standing for the roster's five prefix spellings by `repSpellings`), batch 17 the multiply-divide four (`mul`/`imul`/`div`/`idiv`, `imul` being the only mnemonic here spread over TWO constructors), batch 18 `cmpxchg`, `xadd` and the double-shift pair `shld`/`shrd` (two names for ONE constructor, as `shl`/`shr`/`sar` are). -/
theorem roster_size_is_99 : rosterSize = 99 := by decide

/-- ⭐⭐ P1 BATCH 20 — THE VECTOR COUNT, PINNED IN THE KERNEL, so that
`scripts/kernel_cost.py` can divide by it.

Batch 17 wrote that this denominator "could be pinned the same way" as
`rosterSize` and did not pin it, because the unit it wanted also needed an
ASSERTION count, which cannot be pinned — an assertion count is a property of
this file's TEXT and of no term in it.  Both halves of that were true, and
together they blocked ONE DESIGN rather than the goal: a gate on each
DECLARATION needs no assertion count at all, because dividing by the number of
declarations is the only thing an assertion count was ever for.  See D62.

⚠️ THE LITERAL IS THE POINT, exactly as it is for `roster_size_is_84`.  Growing
the vector table is a visible one-line change here, and `kernel_cost.py` reads
THIS literal — a number Lean proves equal to `vectors.length` — rather than
counting the table itself and possibly getting it wrong. -/
def vectorCount : Nat := vectors.length

theorem vector_count_is_828 : vectorCount = 828 := by decide

/-- ⭐⭐ THE CLAIM THAT `movdqa` AND `movdqu` ARE ONE OPERATION BETWEEN REGISTERS,
AS A THEOREM RATHER THAN THE COMMENT THAT FIRST STATED IT.

`Op.vmov` carries `aligned` because the two are different OPCODES (`66 0f 6f`
against `f3 0f 6f`) and the model must not print one name for the other. What it
must ALSO not do is let that flag change the state transition, because the rule
that separates the two mnemonics is stated of a MEMORY operand (SDM Vol. 2B,
MOVDQA: "the operand must be aligned on a 16-byte boundary") and between two
registers there is no address to align.

⚠️ THIS IS THE KIND OF SENTENCE THIS REPOSITORY HAS TWICE FOUND TO BE UNGATED
PROSE (D65). It is cheap to state as a theorem over both flag values and every
register pair, so it is stated. On the day the memory forms land, this theorem
is the one that must GAIN a hypothesis — and it will fail loudly rather than
quietly licence a wrong `movdqa`. -/
theorem vmov_aligned_irrelevant (d s' : XmmReg) (n : Nat) (c : Cpu) :
    step ⟨.vmov true d s', n⟩ c = step ⟨.vmov false d s', n⟩ c := rfl

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

/-- ⭐⭐ P1 BATCH 21 — THE THREE VECTOR-COVERAGE FACTS IN ONE KERNEL REDUCTION,
for the reason measured at `memDestSweep`: the kernel's reduction cache spans a
declaration and not two, so `vectorMnemonics`'s `eraseDups` was paid three times.

⭐ THE DEDUP IS REAL, CONFIRMED BY A CONTROL AT THE SAME SHAPE (batch 21):
`vectorMnemonics.length = 83` costs **935 ms**, while forcing the same 775
`Vec.mnemonic` projections with NO dedup — `(vectors.map Vec.mnemonic).any (·
== "zzz") = false` — costs **69 ms**, and `.any (·.isEmpty)` **76 ms**.  So 93%
of this list's cost is the dedup and not the traversal, exactly as D62 said.
⚠️ What D62 got wrong was the SIZE of the prize, not its existence: three
payments of 935 ms is 2.8 s of a 37 900 ms module.  See `memDestSweep`.

⛔ REPLACING `eraseDups` WITH ANYTHING CHEAPER WAS PRICED AND REFUSED.  Both
dedup-free spellings cost the same ~30 000 string comparisons the dedup does
(83 rows x first-occurrence-in-775, or 775 vectors x position-in-83), and a
hand-written 83-element literal pinned by a theorem would pay the dedup once —
at the cost of a list edited by hand every batch.  **Paying it once is the whole
win available, and this shape takes it without new data to maintain.** -/
theorem vectorCoverage :
    ((tableP0.map Row.mnemonic).all (fun m => vectorMnemonics.contains m)
     && vectorMnemonics.all (fun m => (tableP0.map Row.mnemonic).contains m)
     && (vectorMnemonics.length == rosterSize)) = true := by decide

/-- ⭐ EVERY ROW IS BACKED BY AT LEAST ONE DIFFERENTIAL VECTOR.  A tier claim for
a form nothing executes is a claim backed by nothing. -/
theorem every_row_has_a_vector :
    (tableP0.map Row.mnemonic).all
      (fun m => vectorMnemonics.contains m) = true := by
  have h := vectorCoverage; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1

/-- And every vector's mnemonic is one the table knows about, so a form cannot
be tested while being absent from the published coverage. -/
theorem every_vector_has_a_row :
    vectorMnemonics.all
      (fun m => (tableP0.map Row.mnemonic).contains m) = true := by
  have h := vectorCoverage; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1.2

/-- Every implemented mnemonic is exercised by at least one differential vector
— the count above is matched by the vector table, not merely by the roster. -/
theorem vectors_cover_the_roster :
    vectorMnemonics.length = rosterSize := by
  have h := vectorCoverage; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.2

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

/-! ### P1 BATCH 14 — the zero source, and the encodings that do not exist

⭐ THE ZERO SOURCE IS THE ONLY STATE IN WHICH FOUR OF THIS BATCH'S SIX FORMS SAY
ANYTHING UNUSUAL: `bsf`/`bsr` leave the destination undefined there, and
`lzcnt`/`tzcnt` answer the operand width and set CF there.  Batch 14 claimed it
needed no new pre-state because `preStates`' diagonal arm already reaches it.
⛔ THAT CLAIM IS ASSERTED HERE RATHER THAN BELIEVED — it is exactly the shape of
claim D14, D26 and D27 each caught being false after the fact, and each time the
run had been green. -/

/-- A pre-state in which the REGISTER source of an `r,r` form is zero. -/
theorem bit_counting_reaches_a_zero_register_source :
    (preStates 1 8).any (fun s => s.regs.rcx == 0) = true := by decide

/-- ⭐ AND ONE IN WHICH THE MEMORY SOURCE IS ZERO TOO, which is a separate fact:
the `r,m` vectors read the eight bytes at RBX, not RCX, and a batch that checked
only the register shape would have left half its forms never reaching their
interesting state.  `mkPre` writes `c` to that span, so this asks whether some
pre-state has BOTH the pointer and zero bytes behind it. -/
theorem bit_counting_reaches_a_zero_memory_source :
    (preStates 1 8).any (fun s =>
      s.regs.rbx == 0x2000 && s.readMem .q 0x2000 == 0) = true := by decide

/-- ⚠️ AND A NON-ZERO SOURCE IS REACHED AS WELL, in both shapes.  Without this
the two theorems above would be satisfied by a pre-state set that was ALL zeros,
in which `bsf` is undefined everywhere and nothing is tested. -/
theorem bit_counting_reaches_a_nonzero_source :
    ((preStates 1 8).any (fun s => s.regs.rcx != 0)
      && (preStates 1 8).any (fun s => s.regs.rbx == 0x2000 && s.readMem .q 0x2000 != 0)) = true := by
  decide

/-- ⭐ THE FORMS THIS MODEL DECLINES, STATED AS THE EXACT LIST.  Six (kind,
width) pairs have no encoding: none of the six mnemonics has an 8-bit form, and
`blsi` is VEX-encoded with VEX.W selecting 32 or 64, so it has no 16-bit one.

⛔ STATED AS THE PAIRS AND NOT AS A COUNT, for the reason
`mem_dest_rewrite_changed_exactly_the_three_operand_rows` is: a count of seven
is satisfied by any seven pairs changing hands, and the pair that would actually
go wrong here — `blsi` at `.w` — is the one a reader is most likely to forget. -/
theorem bitcnt_declined_forms_are_exactly_the_unencodable_ones :
    (([BitCntKind.popcnt, .lzcnt, .tzcnt, .bsf, .bsr, .blsi].flatMap (fun k =>
        [Size.b, .w, .d, .q].filterMap (fun sz =>
          if bitcntEncodable k sz then none else some (k, sz))))
      = [(.popcnt, .b), (.lzcnt, .b), (.tzcnt, .b), (.bsf, .b), (.bsr, .b),
         (.blsi, .b), (.blsi, .w)]) := by decide

/-- And every (kind, width) pair the model DOES accept has a differential vector
at both operand shapes — so `r,r · r,m` in the coverage table is backed rather
than asserted. -/
theorem bitcnt_encodable_forms_all_have_both_shapes :
    ([BitCntKind.popcnt, .lzcnt, .tzcnt, .bsf, .bsr, .blsi].all (fun k =>
      [Size.b, .w, .d, .q].all (fun sz =>
        !bitcntEncodable k sz ||
          (vectors.any (fun v => match v.instr.op with
             | .bitcnt k' sz' _ (.reg _ _) => k' == k && sz' == sz
             | _ => false)
           && vectors.any (fun v => match v.instr.op with
             | .bitcnt k' sz' _ (.mem _) => k' == k && sz' == sz
             | _ => false))))) = true := by decide

/-! ### P1 BATCH 17 — the multiply-divide group's own claims

⚠️ THE FIRST OF THESE IS THE ONE BATCH 16 WOULD HAVE WANTED.  `imulrEncodable`
looks exactly like `bitcntEncodable` and this time the resemblance is honest —
both record forms with NO ENCODING — so the theorem is written in the same
shape, and the difference from batch 16's `repApplies` (a roster PARTITION,
whose rejected pairs all assemble) is left stated in the AST rather than
rediscovered here. -/

theorem imulr_declined_widths_are_exactly_the_byte :
    ([Size.b, .w, .d, .q].filter (fun sz => !imulrEncodable sz)) = [.b] := by decide

/-- ⭐ EVERY ONE-OPERAND MEMBER OF THE GROUP HAS A VECTOR AT EVERY WIDTH.  The
coverage row says `r — b/w/l/q`, and this is what backs it: four kinds times
four widths, all sixteen present with a register source. -/
theorem muldiv_all_kinds_and_widths_have_a_register_vector :
    (MulDivKind.all.all (fun k =>
      [Size.b, .w, .d, .q].all (fun sz =>
        vectors.any (fun v => match v.instr.op with
          | .muldiv k' sz' (.reg _ _) => k' == k && sz' == sz
          | _ => false)))) = true := by decide

/-- ⭐⭐ AND THE MEMORY CLAIM IS BACKED AT EXACTLY THE WIDTHS IT NAMES — `b` and
`q`, no more and no less.

⛔ THIS IS THE GATE THE `shapes` COLUMN NEEDED AND `mem_dest_claims_are_backed`
CANNOT GIVE: a memory operand that is a SOURCE is invisible to every
memory-DESTINATION gate in this file, so `mul`'s `m` claim had nothing reading
it.  Writing `m — b/w/l/q` would have been an over-claim no gate could see,
which is D47's shape in the column beside the one D47 was about.  Stated as an
EQUALITY so it fails in both directions: adding a `.w` memory vector without
widening the row breaks it too. -/
theorem muldiv_memory_vectors_are_exactly_b_and_q :
    (MulDivKind.all.map (fun k =>
      [Size.b, .w, .d, .q].filter (fun sz =>
        vectors.any (fun v => match v.instr.op with
          | .muldiv k' sz' (.mem _) => k' == k && sz' == sz
          | _ => false))))
      = [[.b, .q], [.b, .q], [.b, .q], [.b, .q]] := by decide

/-- `imul`'s two- and three-operand forms have a vector at each ENCODABLE width,
and none at `.b` — the other direction of `imulr_declined_widths_are_exactly_
the_byte`, over the vector table rather than over the table of encodings. -/
theorem imulr_vectors_exist_exactly_where_encodable :
    ([Size.b, .w, .d, .q].all (fun sz =>
      (vectors.any (fun v => match v.instr.op with
        | .imulr sz' _ _ none => sz' == sz
        | _ => false) == imulrEncodable sz)
      && (vectors.any (fun v => match v.instr.op with
        | .imulr sz' _ _ (some _) => sz' == sz
        | _ => false) == imulrEncodable sz))) = true := by decide

/-! ### P1 BATCH 18 — the three claims this batch would otherwise have made only
in prose

⛔ EACH OF THESE IS A SENTENCE A COMMENT ALREADY SAYS, TURNED INTO SOMETHING THAT
FAILS.  The repository's own law: a column — or a sentence — no gate reads is
wrong wherever nobody looked, and a TRUE disclaimer is worse than none, because
it reassures. -/

/-- ⛔⛔ NO `cmpxchg` VECTOR NAMES THE ACCUMULATOR AS ITS DESTINATION, and the
whole batch rests on it.  `cmpxchg` compares AL/AX/EAX/RAX — not an operand —
with the destination, so a vector whose destination is RAX compares the
accumulator with itself, ZF is 1 in every pre-state, and the branch that writes
the accumulator is UNREACHABLE.  Both observation arms would then agree with the
model everywhere and report a pass while measuring half an instruction.

⚠️ It is stated as an ALL over the vector table rather than as a note beside the
seven vectors, because the failure it guards against is a vector added LATER by
someone who read the seven and copied the shape without the reason. -/
theorem cmpxchg_vectors_never_target_the_accumulator :
    vectors.all (fun v => match v.instr.op with
      | .cmpxchg _ (.reg r _) _ => r != .rax
      | _ => true) = true := by decide

/-- ⛔⛔ D52, FROM THE VECTOR SIDE: at `.w` the double shifts have MEMORY vectors
with an IMMEDIATE count and none with CL — because `step` refuses that
combination and the oracle does not, so a vector there would be a refusal
disagreement rather than a test.

⚠️ IT IS AN EQUALITY AND SO FAILS IN BOTH DIRECTIONS.  A CL vector appearing at
`.w` in memory is the over-claim; the immediate vectors QUIETLY DISAPPEARING is
the under-claim, and that half is the one nobody looks for — it would leave the
refusal looking like a decision to skip the width entirely. -/
theorem dshift_memory_vectors_at_w_are_immediate_only :
    ((vectors.any (fun v => match v.instr.op with
        | .dshift _ .w (.mem _) _ (.imm8 _) => true
        | _ => false))
    , (vectors.any (fun v => match v.instr.op with
        | .dshift _ .w (.mem _) _ .cl => true
        | _ => false))) = (true, false) := by decide

/-- ⭐ THE FIVE IMMEDIATES ARE THE FIVE BRANCHES, AS A SET.  `$0` is the
no-operation, `$1` the one count at which OF is defined, `$5` the ordinary case,
`$16` the exact boundary at `.w` where the answer is the source, and `$20` past
it, where the destination is undefined.  Written as an equality on the sorted set
so that losing one — the cheapest way for this batch's coverage to rot — is a
failure rather than a smaller number nobody notices.

⚠️ Stated as TWO `all`s rather than as a sorted list, because `List.mergeSort`
is defined by well-founded recursion and the kernel does not unfold it — the
`String.splitOn` trap of `memDestHere`, in a different function.  Both directions
are here for the reason the equality was wanted: one says no branch is missing,
the other says no immediate is present that is not one of the five. -/
theorem dshift_immediates_are_the_five_branches :
    (([0, 1, 5, 16, 20] : List Nat).all (fun c =>
        vectors.any (fun v => match v.instr.op with
          | .dshift _ _ _ _ (.imm8 i) => i.toNat == c
          | _ => false))
     && vectors.all (fun v => match v.instr.op with
          | .dshift _ _ _ _ (.imm8 i) => ([0, 1, 5, 16, 20] : List Nat).contains i.toNat
          | _ => true)) = true := by decide

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

/-- ⭐⭐ P1 BATCH 13 REWROTE THIS PREDICATE, AND THE REASON IS THE THIRD
INSTANCE OF D16/D32: **a check cannot be more precise than the notation it
reads**, and this one had become LESS precise than the notation it reads.

The old predicate was two independent substring tests — the literal `m,r`
anywhere in the column, OR an `m` + optional width + `(` anywhere in it.  Both
were written when every shape in the table had TWO operands, where a substring
`m,r` can only be "memory destination, register source".

⛔ BATCH 13's `sarx`/`shlx`/`shrx` HAVE THREE OPERANDS. Their shapes read
`r,r,r · r,m,r` — destination, source, count — and `r,m,r` CONTAINS `m,r`, whose
`m` is the SOURCE. The old predicate read a memory-destination claim out of a
row for a form that cannot write memory at all, `mem_dest_claims_are_backed`
went RED on a TRUE claim, and the cheap way out would have been to respell the
shapes column until the pattern stopped firing — notation bent to fit its own
gate, which is precisely the failure this gate exists to catch one level up.

⇒ The rule the column actually follows is POSITIONAL, and it is now written as
one: **shapes are destination-first, so a memory destination is an `m` in the
FIRST operand position of some shape.** A shape starts at the beginning of the
column or after the ` · ` separator.

⚠️ AND FIRST-POSITION `m` ALONE IS NOT ENOUGH, which is the part inherited from
the older comment below and kept: `push`'s shapes read `r · m · imm`, where the
lone `m` is a memory SOURCE. A memory DESTINATION is a first-position `m`
followed by something that marks it as written — a further operand (`m,r`,
`m,imm`) or a parenthesised kind (`m(rmw)`, `m8(w)`). A bare `m` is a read. -/
private def memDestHere : List Char → Bool
  | 'm' :: rest =>
      match (rest.dropWhile Char.isDigit) with
      | ',' :: _ => true      -- `m,r`, `m,imm` — a destination with a source
      | '(' :: _ => true      -- `m(rmw)`, `m8(w)` — a destination with a kind
      | _ => false            -- a bare `m`: a memory SOURCE (push)
  | _ => false

/-- Scan the shapes column, tracking whether the cursor is at the START of a
shape.  Spaces do not end a shape start (the separator is written ` · `), the
middle dot begins a new shape, and anything else means the cursor is inside one.

⚠️ Written by structural recursion on the character list, for the same reason
`isInfixOfChars` was: `String.splitOn` is defined by well-founded recursion, the
kernel does not unfold it, and `decide` fails on a proposition that is TRUE — a
gate that cannot be evaluated is a build error wearing a gate's clothes. -/
private def memDestFromShapeStart : List Char → Bool → Bool
  | [], _ => false
  | ' ' :: rest, atStart => memDestFromShapeStart rest atStart
  | '·' :: rest, _ => memDestFromShapeStart rest true
  | c :: rest, atStart =>
      (atStart && memDestHere (c :: rest)) || memDestFromShapeStart rest false

def claimsMemDest (r : Row) : Bool :=
  memDestFromShapeStart r.shapes.toList true
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
  -- lie, which is D16's failure exactly.
  -- ⛔ AND THE PREFIX `m(` WAS STILL A SPELLING, WHICH IS D32.  Batch 6
  -- generalised the literal `m(rmw)` to the prefix `m(` expressly so that
  -- `setcc`'s memory WRITE could be described honestly as `m(w)` — and the row
  -- it was written for spells it **`m8(w)`**, with the operand width between the
  -- `m` and the parenthesis.  So the generalisation missed its own motivating
  -- case, `setcc`'s memory-destination claim went UNREAD for six batches, and a
  -- comment three lines up named `setcc` as the reason the pattern was widened.
  --
  -- ⭐ AND IT WAS INVISIBLE BECAUSE A SECOND DEFECT CANCELLED IT.
  -- `isMemDestVector` had no `.setcc` case either, so it answered "no vector" to
  -- a claim that has SIXTEEN.  Repairing either half alone turns the gate RED;
  -- the green depended on both being wrong at once.  ⇒ **Two defects that cancel
  -- read exactly like a passing gate, and the one that is easy to find is the
  -- one that keeps the other hidden.**  Verified by repairing this clause alone
  -- and watching `mem_dest_claims_are_backed` fail.
  --
  -- ⭐⭐ AND BATCH 13 FOUND THE REMAINING HALF OF THAT LESSON: both of D32's
  -- repaired clauses were still POSITION-BLIND, which no two-operand row could
  -- reveal.  See the doc comment above `memDestHere`.

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
    -- ⭐ P2 VECTOR WAVE, BATCH 2, added in the SAME COMMIT as the constructors,
    -- which is what this function's own doc comment asks for.  Both are
    -- register-to-register only: there is no memory destination to report, and
    -- when the memory forms land this is one of the lines that must change.
    | .vmov .. | .vbin .. => false
    -- ⭐ P2 VECTOR WAVE, BATCH 3.  A vector STORE is a memory destination; a
    -- vector LOAD is not.  This is the first time the two vector mnemonics
    -- differ from each other in this function, which is the shape of the whole
    -- batch: `movdqa` and `movdqu` stop being interchangeable once an address
    -- exists.
    | .vload .. => false
    | .vstore .. => true
    -- P2 VECTOR WAVE, BATCH 5: neither direction of `movd`/`movq` touches memory.
    | .vmovg .. | .vmovq .. => false
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
    -- ⭐ P1 BATCH 12: `.setcc` HAD NO CASE AND ITS ROW CLAIMS `m8(w)`, with
    -- sixteen vectors backing it.  It fell into the catch-all and answered
    -- "no vector" to a true claim — the batch-8 `.rot` defect exactly, surviving
    -- six batches longer because the shapes pattern above could not read the
    -- claim either.  See D32.
    | .setcc _ d => d.isMem
    -- ⭐ P1 BATCH 17.  Both new constructors answer `false`, and each is a
    -- DECISION rather than an omission — the deleted catch-all made this line a
    -- compile error, for the fourth time, and it is the fourth time it has
    -- worked.  `.muldiv`'s memory operand is a SOURCE: `divq (%rbx)` reads the
    -- divisor from memory and writes RDX and RAX, so there is no operand-encoded
    -- memory DESTINATION however wide the result.  ⚠️ That is the same
    -- distinction the comment below draws for `push` — the shapes column spells
    -- `mul`'s `m` as a source, and the notation exists to make exactly this
    -- difference visible.  `.imulr`'s destination is a `GPR` by its type.
    | .muldiv .. => false
    | .imulr .. => false
    -- ⭐ P1 BATCH 18, AND THE EXHAUSTIVE MATCH EARNED ITS KEEP A FIFTH TIME:
    -- three new constructors, three compile errors here, three answers written
    -- down instead of assumed.  All three take an `Operand` destination and all
    -- three can be memory, so all three ask it.
    --
    -- ⚠️ `.dshift`'s ANSWER IS `d.isMem` AND NOT "d.isMem AND THE MODEL ANSWERS
    -- FOR IT".  The `.w`-in-memory-with-a-big-count case is REFUSED by `step`,
    -- but the vectors that reach this predicate are `l` and `q` with `cl` and
    -- every width with an immediate, all of which really do write memory — and a
    -- predicate that tried to encode the refusal here would be answering a
    -- question about `step` in a function about the vector table.
    | .cmpxchg _ d _ => d.isMem
    | .xadd _ d _ => d.isMem
    | .dshift _ _ d _ _ => d.isMem
    -- ⛔ AND THE CATCH-ALL IS GONE.  `_ => false` made this function ABSORB every
    -- new `Op` constructor silently, which is how `.rot` (batch 8) and `.setcc`
    -- (here) each got a wrong answer with nothing to say so.  The match is now
    -- EXHAUSTIVE, so growing `Op` is a COMPILE ERROR on this line and the answer
    -- for a new form has to be written down.  The remaining constructors answer
    -- `false`, and each is a decision rather than an omission: `lea`, `cmov`,
    -- `movx` and `bswap` have REGISTER destinations by their types; `jmp`,
    -- `jcc`, `jcxz`, `loop`, `call`, `ret` and `flagop` have no operand
    -- destination at all; `nop` and `ud2` touch nothing; `leave` writes RBP, a
    -- register.  `push` and `call` DO write the stack, and they still answer
    -- `false` because this predicate asks about an operand-encoded memory
    -- DESTINATION — the shapes column spells `push`'s `m` as a memory SOURCE,
    -- and that distinction is the one the notation was fixed to make.
    | .lea .. => false
    | .push .. => false
    | .jmp .. => false
    | .jcc .. => false
    | .jcxz .. => false
    | .cmov .. => false
    | .call .. => false
    | .loop .. => false
    | .flagop _ => false
    | .nop _ => false
    | .ud2 => false
    | .ret => false
    | .leave => false
    -- ⭐ P1 BATCH 13.  `.movbe` IS THE FIRST NEW MEMORY-DESTINATION FORM SINCE
    -- THE CATCH-ALL WAS DELETED, and the deletion did its job: adding the
    -- constructor made this match non-exhaustive and the build FAILED here
    -- before this line existed.  That is the batch-8 (`.rot`) and batch-12
    -- (`.setcc`) defect refusing to happen a third time.
    --
    -- ⭐⭐ AND THE OTHER HALF OF D32 WAS EXERCISED FOR FREE.  With the `m(w)`
    -- claim in the coverage row and this line still absent,
    -- `mem_dest_claims_are_backed` went RED — so the gate is measured
    -- load-bearing for this batch rather than assumed to be.
    | .movbe _ d _ => d.isMem
    -- `.shiftx` writes a GPR by its type, exactly as `.movx` and `.bswap` do;
    -- its MEMORY operand is the source.  `false` is the decision, not a gap.
    | .shiftx .. => false
    -- P1 BATCH 14.  The bit-counting group's destination is always a GPR; its
    -- MEMORY operand is the source.  `false` is the decision, not a gap.
    | .bitcnt .. => false
    -- ⭐ P1 BATCH 15.  THE STRING GROUP IS THE FIRST WHOSE ANSWER HERE CANNOT BE
    -- READ OFF AN OPERAND FIELD, because it has none: the destination is `[rdi]`
    -- or `rAX` by OPCODE.  So the answer is per-kind, and each one is a
    -- decision rather than a default.
    --
    -- `movs` and `stos` WRITE `[rdi]`.  `cmps` and `scas` ADDRESS `[rdi]` as
    -- their destination operand and write nothing — the `cmp`/`test` case
    -- exactly, and the reason this predicate's name says "dest" and not
    -- "writes".  `lods` alone has a register destination.
    | .strop k _ => match k with
      | .movs | .stos | .cmps | .scas => true
      | .lods => false
    -- ⭐ P1 BATCH 16.  THE PREFIX CHANGES NOTHING HERE, and saying so is the
    -- point: a repeat prefix is loop control, and the memory destination of
    -- `rep movs` is the memory destination of `movs`.  ⚠️ It is written as a
    -- DELEGATION to the same per-kind table rather than as a second copy of it,
    -- so the two can never disagree about which of the five write memory —
    -- which is the only way this line could go wrong.
    | .repstrop _ k _ => match k with
      | .movs | .stos | .cmps | .scas => true
      | .lods => false
    -- ⭐ P1 BATCH 21.  `cmpxchg8b`'s memory operand is written on the EQUAL
    -- branch and read on both, so it is a memory destination in exactly the
    -- `cmp`/`test` sense this predicate's name is about — and unlike every
    -- other constructor here the answer needs no operand test at all, because
    -- the encoding admits no register form (`step` declines one).
    | .cmpxchg8b d => d.isMem)

/-- The mnemonics that HAVE such a vector, collapsed ONCE.  Asking the question
per row re-swept the WHOLE vector table for every claiming row; the set it is
really asking about has at most `rosterSize` elements.  See the note above
`vectorMnemonics`. -/
def memDestMnemonics : List String :=
  ((vectors.filter isMemDestVector).map Vec.mnemonic).eraseDups

/-- Is there a differential vector for this mnemonic whose DESTINATION operand
is memory? -/
def hasMemDestVector (m : String) : Bool := memDestMnemonics.contains m

/-- ⭐ THE OLD PREDICATE, KEPT AS DATA SO THE REWRITE IS AUDITABLE.

Rewriting a gate is the one change that can WEAKEN it silently: the new form is
green, the old form was green, and nothing says which rows changed hands.  A
one-off script that answers "only the three I meant" is not evidence anybody can
re-run — so the old rule stays here and the disagreement is a THEOREM.

⚠️ This is deliberately the pre-batch-13 predicate, warts and all: the literal
`m,r` anywhere plus `m` + optional width + `(` anywhere, neither of them
position-aware.

⛔ BATCH 14: it reached this shape carrying a BYTE-IDENTICAL COPY of
`isInfixOfChars` under a primed name.  The rewrite that introduced it had just
stopped using the original in `claimsMemDest`, so the original became dead and
the copy became the only live one — two definitions that agreed at birth, one
of them unreachable, and nothing to hold them together on the next edit.  The
copy is gone; this rule calls the original, which is live again. -/
private def looseMemDestShape : List Char → Bool
  | [] => false
  | c :: rest =>
    (c == 'm' && (rest.dropWhile Char.isDigit).head? == some '(')
      || looseMemDestShape rest

-- ⚠️ P1 BATCH 21 — NOT `private` ANY MORE, and the reason is a gate rather than
-- a convenience.  `scripts/sharing_redprobe.sh` plants a defect in each of
-- `memDestSweep`'s three conjuncts alone and requires the kernel to report
-- `false`; the first conjunct cannot be stated without this rule.  The
-- alternative was a copy of it in the probe — which is precisely the
-- byte-identical duplicate batch 14 deleted three declarations above.
def claimsMemDestLoose (r : Row) : Bool :=
  isInfixOfChars "m,r".toList r.shapes.toList || looseMemDestShape r.shapes.toList

set_option maxHeartbeats 8000000 in
/-- ⭐⭐ P1 BATCH 21 — THE THREE MEM-DEST SWEEPS, IN ONE KERNEL REDUCTION.

This declaration proves NOTHING new.  It is the conjunction of the three
theorems below, stated so that the kernel reduces `claimsMemDest`,
`claimsMemDestLoose` and `memDestMnemonics` ONCE for the whole group instead of
once per theorem.  Each of the three keeps its own name and its own statement,
byte-for-byte, and is derived from this one — so if this conjunction were
weaker than any of them, the derivation would not typecheck.  **Nothing is
weakened by construction, and that is the reason for this shape rather than a
merged statement.**

⭐ WHY, MEASURED (batch 21, per-declaration profiler, load 3.0-3.2):

    apart   mem_dest_rewrite_…        10 600 ms
            mem_dest_claims_are_backed 9 720 ms
            mem_dest_vectors_are_claimed 5 250 ms   = 25 570 ms
    merged  this declaration                        = 11 200 ms

⇒ 🔑 **THE KERNEL'S REDUCTION CACHE SPANS A DECLARATION AND NOT TWO.**  A `def`
naming a closed constant collapses the work inside one theorem — measured
separately, the 39 `hasMemDestVector` calls in `mem_dest_claims_are_backed`
cost 70 ms of its 9 720, so `memDestMnemonics` was already reduced once there —
but every new theorem mentioning it starts from cold.  The note above
`memDestMnemonics` says the collapse is "asked once instead of per row"; that
was true and it was only half the sharing available.

⛔ AND THIS IS WHERE THE MODULE'S MONEY WAS, WHICH IS NOT WHERE BATCH 20 SAID.
D62 named `vectorMnemonics`'s quadratic `eraseDups` as "the honest fix", worth
~3.5 s.  Measured: that dedup is real (935 ms against a 76 ms control at the
same 775 projections without it) and it is worth 2.8 s of a 37 900 ms module —
**7%**.  The sweep sharing here is worth 14 370 ms — **38%**.  The item D62
called bigger was the smaller one, and the difference was never measured
because a whole-module total cannot see it. -/
theorem memDestSweep :
    ((tableP0.filterMap (fun r =>
        match claimsMemDestLoose r, claimsMemDest r with
        | true,  false => some (r.mnemonic, true)
        | false, true  => some (r.mnemonic, false)
        | _,     _     => none)
      -- ⭐ P2 VECTOR WAVE, BATCH 3 adds the last two, and their direction is the
      -- interesting one: the LOOSE rule says no and the STRICT rule says yes.
      -- `claimsMemDestLoose` looks for the literal `m,r` — `r` being a
      -- GENERAL-PURPOSE register — so it is blind to a vector store, whose shape
      -- is `m,x`. The strict rule reads the shape's START and gets it right.
      -- ⇒ The old rule was not merely imprecise, it was VOCABULARY-BOUND, and a
      -- second register file is what exposed that. Recorded here rather than
      -- repaired: `claimsMemDestLoose` exists only to be compared against, and
      -- teaching it `x` would erase the very divergence this theorem exists to
      -- pin down.
      == [("sarx", true), ("shlx", true), ("shrx", true),
          ("cmps", false), ("scas", false), ("repe", false), ("repne", false),
          ("movdqa", false), ("movdqu", false)])
     && tableP0.all (fun r => !claimsMemDest r || hasMemDestVector r.mnemonic)
     && ((memDestMnemonics.filter (fun m =>
            !(tableP0.any (fun r => r.mnemonic == m && claimsMemDest r)))) == [])) = true := by
  decide

/-- ⭐ THE REWRITE CHANGED EXACTLY THREE ROWS, AND THEY ARE THE THREE IT WAS
WRITTEN FOR.  `sarx`, `shlx` and `shrx` are the table's only three-operand
forms; the old rule read the `m,r` inside their `r,m,r` as a memory
DESTINATION, and that `m` is the source.  Every other row answers the same as
it did before.

⛔ AND THE THEOREM IS STATED AS "the rows where the two rules DISAGREE are
exactly this list", not as "they agree on 58 rows": a count would be satisfied
by any three rows changing hands.

⭐ BATCH 14 MADE IT ONE TRAVERSAL AND STRICTLY STRONGER.  It was a conjunction
of two `decide`s — "loose-minus-tight is these three" and "tight implies loose"
— which swept the table twice and evaluated BOTH string predicates on every row
in BOTH sweeps.  Written as a single `filterMap` it evaluates each predicate
once per row, and it says MORE: the second component records which rule claimed
the row, so a row that changed hands the other way (tight yes, loose no) appears
as `(_, false)` and breaks the equality.  That is the old second conjunct,
carried per-row instead of as a separate sweep.

⛔⛔ AND IT SAVED NO KERNEL TIME AT ALL — 17.9s BEFORE, 17.9s AFTER.  The
rewrite was made on a plausible diagnosis (four predicate evaluations per row
for a question about one) and the diagnosis was WRONG about where the money
goes.  Measuring the two disjuncts of `claimsMemDestLoose` separately: the
`m,r` infix scan alone costs ~6.1s and `looseMemDestShape` alone costs ~6.1s,
so BOTH are full character-list sweeps of the shapes column and the traversal
count was never the driver.  ⇒ **The cost is reading the artifact in the
kernel, and D15 already decided to pay it.**  There is no cheap version of this
gate; there is only the gate or a gate on a shadow of the artifact.  The
rewrite is kept because it is a STRONGER statement and it deleted a duplicated
definition, not because it was an optimisation — it was not one.  See
docs/DECISIONS.md D38.

⭐⭐ P1 BATCH 15 ADDED THE FIRST `(_, false)` ENTRIES, AND THAT IS THE COMPONENT
BATCH 14 ADDED SPECULATIVELY.  `cmps` and `scas` are claimed by the POSITIONAL
rule and missed by the loose one: their shapes are `m,m` and `m,acc`, and
`claimsMemDestLoose` looks for the literal string `m,r` or an `m(`, neither of
which is there.  The loose rule was never general — it was keyed to the exact
spelling the table happened to use for `cmp` — and these two rows are where that
finally shows.

⇒ The name of this theorem is now half wrong and deliberately kept: it says
`the_three_operand_rows`, and the list has five entries. ⚠️ The RIGHT reading is
the statement, not the name — "the rows where the two rules disagree are exactly
these" — and the name is left as the record of what the list contained when it
was written. **Renaming it would erase the only evidence in this file that the
set has grown for a second, unrelated reason.**

⭐ AND IT WAS THE `(_, false)` SLOT THAT CAUGHT THEM. Batch 14 added that
component with no row exercising it, on the argument that a row changing hands
the other way should break the equality. One batch later, two rows did. -/
theorem mem_dest_rewrite_changed_exactly_the_three_operand_rows :
    tableP0.filterMap (fun r =>
        match claimsMemDestLoose r, claimsMemDest r with
        | true,  false => some (r.mnemonic, true)
        | false, true  => some (r.mnemonic, false)
        | _,     _     => none)
      = [("sarx", true), ("shlx", true), ("shrx", true),
         ("cmps", false), ("scas", false),
         -- P1 BATCH 16: `repe` and `repne` join for the same reason `cmps` and
         -- `scas` did — they ADDRESS a memory destination and write none, so
         -- the loose rule (which reads a bare `m` anywhere) and the strict one
         -- (first position, `m,` or `m(`) disagree about them.  ⚠️ `rep` does
         -- NOT join: its first shape is `m(w),m`, a real write, on which both
         -- rules agree.
         ("repe", false), ("repne", false),
         -- ⭐ P2 VECTOR WAVE, BATCH 3: the vector STORES.  A different reason
         -- again — not "addresses without writing" but "writes through a
         -- vocabulary the loose rule does not have": its literal is `m,r`, and a
         -- vector store's shape is `m,x`.
         ("movdqa", false), ("movdqu", false)] := by
  have h := memDestSweep; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1

/-- ⭐ EVERY MEMORY-DESTINATION CLAIM IN THE TABLE IS BACKED BY A VECTOR THAT
ACTUALLY WRITES (or, for `cmp`/`test`, addresses) A MEMORY DESTINATION.
 -/
theorem mem_dest_claims_are_backed :
    tableP0.all (fun r => !claimsMemDest r || hasMemDestVector r.mnemonic) = true := by
  have h := memDestSweep; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1.2

/-- ⭐⭐ P1 BATCH 15 — THE OTHER DIRECTION, WHICH WAS MISSING FOR FOURTEEN
BATCHES.  `mem_dest_claims_are_backed` catches a row claiming more than the
vectors do.  Nothing caught a row claiming LESS: a form whose vectors write
memory while its shapes column never says so was invisible, because the only
gate read the claim and went looking for the vector, never the reverse.

⛔ AND THIS BATCH WOULD HAVE BEEN THE FIRST TO FALL IN IT.  The string rows were
first written as `implicit [rdi] ← [rsi]` — accurate English, and containing no
first-position `m`, so `claimsMemDest` was false for `movs` and `stos` while
their vectors plainly write memory.  Every gate in this file stayed green on a
coverage table that had stopped saying what the model does.

⇒ This is batch 14's rule for the `undefined` column arriving in the `shapes`
column: **a table checked in one direction is only half checked**, and the half
nobody checks is the half where the claim is too SMALL — which is exactly the
half a reader trusts, because an under-claim never looks like a mistake. -/
theorem mem_dest_vectors_are_claimed :
    (memDestMnemonics.filter (fun m =>
      !(tableP0.any (fun r => r.mnemonic == m && claimsMemDest r)))) = [] := by
  have h := memDestSweep; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.2

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

/-- ⭐⭐ P1 BATCH 12: SOME PRE-STATE HOLDS A **RETURNABLE FRAME** — a canonical
address at RSP and an RBP that points into the watched stack window.

⛔ AND UNTIL THIS BATCH NONE DID, WHICH MADE `retq` UNTESTABLE RATHER THAN
UNTESTED.  The stack window's background pattern puts `0x3736353433323130` at
RSP = 0x8000; bits 63:47 of that are not all equal, so it is NOT CANONICAL and
`retq` refuses in every one of the seventy-eight states that existed before.
**A `retq` that jumped without ever popping would have passed all of them** —
measured, not argued: deleting `frameStates` makes that arm catch ZERO and the
selftest report "the comparator does not work".  RBP was 0 in all seventy-eight,
so `leaveq` popped from an address outside both watched windows.

⚠️ THIRD DRESS OF ONE DEFECT.  `pre_states_set_df` is a COMPONENT no instruction
wrote; the theorem below is a COMBINATION no value reached; this is a WINDOW
CONTENT no state varied.  The rule is not about registers, or flags, or states —
it is that a gate watching something that cannot move reports an agreement it
never tested.  This is the first batch to look for it BEFORE shipping the form
rather than after.

The `any` is deliberately not an `all` and not a count: dropping ONE of the two
frame states leaves the coverage real and must not fire (D21's calibration). -/
theorem pre_states_have_a_returnable_frame :
    ((preStates 1 8).any (fun s => canonical (s.mem.readSize .q (s.regs.get .rsp)))
      && (preStates 1 8).any (fun s => s.regs.get .rbp != 0)) = true := by decide

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

/-! ### P1 BATCH 16 — the repeat prefixes -/

/-- ⭐ THE (prefix, string op) PARTITION, ASSERTED RATHER THAN LEFT IMPLICIT.
`repApplies` is written as data beside the AST expressly so this theorem can
name the exact set; a chain of `halt` branches inside `step` would have made
"which pairs this model claims" a thing to be reconstructed by reading.

⚠️ IT IS A ROSTER PARTITION, NOT AN ENCODING FACT — every rejected pair
assembles, and `repne movsq` is even EXECUTED by the oracle (as an unprefixed
string op). See `RepPrefix` and docs/DECISIONS.md D46. -/
theorem rep_applies_is_exactly_the_roster_partition :
    (RepPrefix.all.flatMap (fun r =>
      [StringOp.movs, .stos, .lods, .cmps, .scas].filterMap (fun k =>
        if repApplies r k then some (r, k) else none)))
      = [(.rep, .movs), (.rep, .stos), (.rep, .lods),
         (.repe, .cmps), (.repe, .scas),
         (.repn, .cmps), (.repn, .scas)] := by decide

/-- The five roster spellings of the three repeat prefixes, counted rather than
claimed — the same discipline `five_loop_spellings` applies to `LoopKind`.
`repz` is `repe` and `repnz` is `repne`; that the collapse is a fact about the
machine is checked against an assembler by the `SYNONYMS` table of
`scripts/check_encodings.py`, because there are no `repz` vectors for a theorem
to quantify over and there must not be (docs/DECISIONS.md D48). -/
theorem five_rep_spellings :
    (RepPrefix.all.flatMap repSpellings).eraseDups.length = 5 := by decide

/-- Every prefix reaches every string op the roster files under it, at every
width — seven (prefix, op) pairs at four widths, twenty-eight vectors, with no
pair reached by accident of another's spelling. -/
theorem vectors_cover_every_rep_pair :
    (RepPrefix.all.all (fun r =>
      [StringOp.movs, .stos, .lods, .cmps, .scas].all (fun k =>
        !repApplies r k ||
        [Size.b, .w, .d, .q].all (fun sz =>
          vectors.any (fun v => match v.instr.op with
            | .repstrop r' k' sz' => r' == r && k' == k && sz' == sz
            | _ => false))))) = true := by decide

/-- ⛔ AND NO VECTOR EXERCISES A PAIR THE MODEL DECLINES.  The other direction:
a vector for `repne movsq` would be a differential case against a form `step`
halts on, which reads as agreement (both models decline) while testing nothing.
-/
theorem no_vector_uses_a_declined_rep_pair :
    vectors.all (fun v => match v.instr.op with
      | .repstrop r k _ => repApplies r k
      | _ => true) = true := by decide

/-- Every flag-control single is exercised, and the two that write DF are among
them.  Five one-byte instructions written from one `match` is exactly the shape
where one case silently does what its neighbour does. -/
theorem every_flag_single_has_a_vector :
    ([FlagOp.clc, .stc, .cmc, .cld, .std].all (fun k =>
      vectors.any (fun v => match v.instr.op with
        | .flagop k' => k' == k
        | _ => false))) = true := by decide

/-! ## ⭐⭐ P2 ITEM 1 (BATCH 22) — the named gap, made unreachable rather than hoped for

`X86/Semantics.lean`'s note on `Ea.addr` records a DEPARTURE from ACL2 x86isa:
its `ea-to-la` requires the resulting LINEAR address to be canonical and faults
if it is not, while this model checks canonicity on branch targets only (D9) and
on no data address at all.  That gap is older than this batch and this batch
does not close it.

⛔ WHAT WOULD MAKE IT MATTER IS A SEGMENT BASE, because a base is the first thing
in this model that can move a data address a long way from where the operands
put it.  So the departure is bounded by an assertion rather than by a sentence:
over the whole (segmented vector × pre-state) cross product, every linear address
this model computes is canonical, so the two models cannot disagree about a
fault neither of them can reach here.  The day a swept base or a large
displacement makes it reachable, THIS goes red before the oracle does.

⚠️ AND THE EXTRACTION HAS NO WILDCARD ARM, because a `match` with a `_ => []`
default is the shape whose gaps all fall the silent way: a constructor it forgot
would make these sweeps EMPTY, and an empty sweep is green.  `opOperands` in
`X86/Coverage.lean` is exhaustive over all thirty-six `Op` constructors, so the
completeness question is answered by the compiler on every build.  The byte-side
cross-check that this replaced — and why — is in the note on that function. -/

/-- The vectors that carry a segment override at all. -/
def segVectors : List Vec := vectors.filter (fun v => !(segEas v.instr).isEmpty)

/-- And there are some, so the sweep below is not vacuous. -/
theorem some_vector_carries_a_segment : segVectors.length = 8 := by decide

/-- ⭐ EVERY LINEAR ADDRESS THIS MODEL COMPUTES THROUGH A SEGMENT IS CANONICAL,
over every pre-state.  This is what bounds the departure named in
`X86/Semantics.lean`. -/
theorem segmentedAddressesAreCanonical :
    (segVectors.all (fun v =>
      (preStates 1 8).all (fun s =>
        (segEas v.instr).all (fun e =>
          canonical (e.addr s (s.rip + BitVec.ofNat 64 v.instr.len)))))) = true := by decide

/-- ⭐⭐ AND THE ADDRESSES LAND WHERE THE WINDOWS ARE — the claim D72 says the
whole observability of this batch rests on.  Every segmented access resolves
into a WATCHED window in every pre-state; a displacement chosen for realism
alone would fail here rather than pass by reading zeros on both sides. -/
theorem segmentedAddressesLandInAWatchedWindow :
    (segVectors.all (fun v =>
      match v.instr.op with
      -- `lea` performs no access, so it is exempt BY NAME rather than by the
      -- sweep quietly not applying to it.
      | .lea _ _ _ => true
      | _ =>
        (preStates 1 8).all (fun s =>
          (segEas v.instr).all (fun e =>
            let a := e.addr s (s.rip + BitVec.ofNat 64 v.instr.len)
            -- ⚠️ EIGHT BYTES, not the operand's own width: 8 is the widest
            -- access any of these forms makes, so demanding that the whole
            -- eight fit is STRICTER than the truth for the narrow ones, which
            -- is the direction a bound may err in.
            windows.any (fun w =>
              w.base ≤ a && a + 8 ≤ w.base + BitVec.ofNat 64 w.len))))) = true := by
  decide

end X86.Tests
