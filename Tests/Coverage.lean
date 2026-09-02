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
one-line change rather than a silent one.  P0 left here with twenty. -/
theorem roster_size_is_22 : rosterSize = 22 := by decide

/-- ⭐ EVERY ROW IS BACKED BY AT LEAST ONE DIFFERENTIAL VECTOR.  A tier claim for
a form nothing executes is a claim backed by nothing. -/
theorem every_row_has_a_vector :
    (tableP0.map Row.mnemonic).all
      (fun m => (vectors.map Vec.mnemonic).contains m) = true := by decide

/-- And every vector's mnemonic is one the table knows about, so a form cannot
be tested while being absent from the published coverage. -/
theorem every_vector_has_a_row :
    (vectors.map Vec.mnemonic).all
      (fun m => (tableP0.map Row.mnemonic).contains m) = true := by decide

/-- Every implemented mnemonic is exercised by at least one differential vector
— the count above is matched by the vector table, not merely by the roster. -/
theorem vectors_cover_the_roster :
    (vectors.map Vec.mnemonic).eraseDups.length = rosterSize := by decide

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

end X86.Tests
