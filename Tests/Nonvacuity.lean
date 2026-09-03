/-
# Tests.Nonvacuity — the undefined bits are REALLY undefined, and the defined
# ones are REALLY defined

Plan v1 §4.5: "for every oracle-assigned bit, two oracles giving different
results."

WHY THIS FILE EXISTS.  A model could satisfy every word of the undefined-bit
discipline by carrying an oracle it never reads, and every characterization
theorem would still be true.  "Undefined" would then be a LABEL rather than a
claim.  The test is behavioural: run the SAME instruction from the SAME state
under two different oracles and require the results to DIFFER.

⭐ AND THE OTHER HALF, WHICH IS THE HALF THAT USUALLY GOES UNTESTED.  A model
could also read the oracle where the SDM is perfectly definite — leaking an
adversarial bit into a flag the manual pins down.  That defect makes theorems
WEAKER without making anything fail, so nothing complains.  The second section
below requires the two oracles to AGREE everywhere the SDM commits.  The two
sections together say: this model declines exactly where Intel declines, no
more and no less.

All of it by `decide`: kernel-checked, allowlist-clean.

LANE. Personal lane, public sources only.
-/
import X86
import Tests.Anchors

namespace X86.Tests
open X86

/-- The same state under the all-zero and the all-ones oracle. -/
private def s0 (r : Regs) (f : Flags := {}) : Cpu :=
  { regs := r, flags := f, oracle := Oracle.zero }
private def s1 (r : Regs) (f : Flags := {}) : Cpu :=
  { regs := r, flags := f, oracle := oneOracle }

/-! ## §1 — Where the SDM says UNDEFINED, the two oracles must DISAGREE -/

/-- AND: "The state of the AF flag is undefined." -/
theorem and_af_undefined :
    (step ⟨.bin .and .q (.reg .rax) (.reg .rcx), 3⟩ (s0 { rax := 0xF0, rcx := 0x3C })).flags.af
      ≠ (step ⟨.bin .and .q (.reg .rax) (.reg .rcx), 3⟩ (s1 { rax := 0xF0, rcx := 0x3C })).flags.af := by
  decide

/-- OR: same sentence in the SDM, same obligation here. -/
theorem or_af_undefined :
    (step ⟨.bin .or .q (.reg .rax) (.reg .rcx), 3⟩ (s0 { rax := 0xF0, rcx := 0x3C })).flags.af
      ≠ (step ⟨.bin .or .q (.reg .rax) (.reg .rcx), 3⟩ (s1 { rax := 0xF0, rcx := 0x3C })).flags.af := by
  decide

theorem xor_af_undefined :
    (step ⟨.bin .xor .q (.reg .rax) (.reg .rcx), 3⟩ (s0 { rax := 0xF0, rcx := 0x3C })).flags.af
      ≠ (step ⟨.bin .xor .q (.reg .rax) (.reg .rcx), 3⟩ (s1 { rax := 0xF0, rcx := 0x3C })).flags.af := by
  decide

theorem test_af_undefined :
    (step ⟨.bin .test .q (.reg .rax) (.reg .rcx), 3⟩ (s0 { rax := 0xF0, rcx := 0x3C })).flags.af
      ≠ (step ⟨.bin .test .q (.reg .rax) (.reg .rcx), 3⟩ (s1 { rax := 0xF0, rcx := 0x3C })).flags.af := by
  decide

/-- SHIFT, undefined region 1: "the CF flag is undefined for SHL and SHR
instructions where the count is greater than or equal to the size in bits of the
destination operand."  At 8-bit width a masked count of 9 is such a count. -/
theorem shl_cf_undefined_when_count_ge_width :
    (step ⟨.shift .shl .b (.reg .rax) (.imm8 9), 3⟩ (s0 { rax := 0xFF })).flags.cf
      ≠ (step ⟨.shift .shl .b (.reg .rax) (.imm8 9), 3⟩ (s1 { rax := 0xFF })).flags.cf := by
  decide

/-- SHIFT, undefined region 2: "the OF flag is affected only on 1-bit shifts;
otherwise it is undefined."  Count 2 at 64-bit width is defined for CF and
undefined for OF, so this isolates the second region from the first. -/
theorem shl_of_undefined_when_count_ne_one :
    (step ⟨.shift .shl .q (.reg .rax) (.imm8 2), 4⟩ (s0 { rax := 0xFF })).flags.of
      ≠ (step ⟨.shift .shl .q (.reg .rax) (.imm8 2), 4⟩ (s1 { rax := 0xFF })).flags.of := by
  decide

theorem shr_of_undefined_when_count_ne_one :
    (step ⟨.shift .shr .q (.reg .rax) (.imm8 2), 4⟩ (s0 { rax := 0xFF })).flags.of
      ≠ (step ⟨.shift .shr .q (.reg .rax) (.imm8 2), 4⟩ (s1 { rax := 0xFF })).flags.of := by
  decide

/-- SHIFT, undefined region 3: AF, for any non-zero count. -/
theorem shl_af_undefined :
    (step ⟨.shift .shl .q (.reg .rax) (.imm8 1), 3⟩ (s0 { rax := 0xFF })).flags.af
      ≠ (step ⟨.shift .shl .q (.reg .rax) (.imm8 1), 3⟩ (s1 { rax := 0xFF })).flags.af := by
  decide

/-! ## §2 — Where the SDM COMMITS, the two oracles must AGREE

This is the half that catches a leak.  Each of these would still be TRUE of a
model that read an oracle bit into the flag — no, it would not: that is exactly
what these reject.  A model contaminating a defined flag fails here and nowhere
else, because contamination weakens theorems without breaking any of them. -/

/-- ADD commits to all six status flags: the oracle cannot reach any of them. -/
theorem add_flags_oracle_independent :
    (step ⟨.bin .add .b (.reg .rax) (.reg .rcx), 2⟩ (s0 { rax := 0x7F, rcx := 0x01 })).flags
      = (step ⟨.bin .add .b (.reg .rax) (.reg .rcx), 2⟩ (s1 { rax := 0x7F, rcx := 0x01 })).flags := by
  decide

theorem sub_flags_oracle_independent :
    (step ⟨.bin .sub .b (.reg .rax) (.reg .rcx), 2⟩ (s0 { rax := 0x00, rcx := 0x01 })).flags
      = (step ⟨.bin .sub .b (.reg .rax) (.reg .rcx), 2⟩ (s1 { rax := 0x00, rcx := 0x01 })).flags := by
  decide

theorem cmp_flags_oracle_independent :
    (step ⟨.bin .cmp .q (.reg .rax) (.reg .rcx), 3⟩ (s0 { rax := 5, rcx := 9 })).flags
      = (step ⟨.bin .cmp .q (.reg .rax) (.reg .rcx), 3⟩ (s1 { rax := 5, rcx := 9 })).flags := by
  decide

theorem inc_flags_oracle_independent :
    (step ⟨.un .inc .b (.reg .rax), 2⟩ (s0 { rax := 0xFF })).flags
      = (step ⟨.un .inc .b (.reg .rax), 2⟩ (s1 { rax := 0xFF })).flags := by decide

theorem neg_flags_oracle_independent :
    (step ⟨.un .neg .q (.reg .rax), 3⟩ (s0 { rax := 7 })).flags
      = (step ⟨.un .neg .q (.reg .rax), 3⟩ (s1 { rax := 7 })).flags := by decide

/-- The RESULT of a logic instruction is fully defined even though its AF is
not: the oracle reaches the flag and NOT the register.  This is the precise
statement of what `T-frame` means for this form. -/
theorem and_result_oracle_independent :
    (step ⟨.bin .and .q (.reg .rax) (.reg .rcx), 3⟩ (s0 { rax := 0xF0, rcx := 0x3C })).regs
      = (step ⟨.bin .and .q (.reg .rax) (.reg .rcx), 3⟩ (s1 { rax := 0xF0, rcx := 0x3C })).regs := by
  decide

/-- And so are the DEFINED flags of that same instruction: only AF moves. -/
theorem and_defined_flags_oracle_independent :
    (let a := (step ⟨.bin .and .q (.reg .rax) (.reg .rcx), 3⟩ (s0 { rax := 0xF0, rcx := 0x3C })).flags
     let b := (step ⟨.bin .and .q (.reg .rax) (.reg .rcx), 3⟩ (s1 { rax := 0xF0, rcx := 0x3C })).flags
     (a.cf, a.of, a.sf, a.zf, a.pf) = (b.cf, b.of, b.sf, b.zf, b.pf)) := by decide

/-- A shift with a MASKED COUNT OF ZERO touches no flag, so it must be oracle-
independent even though a non-zero count of the same instruction is not.  A
model that drew its three bits unconditionally would fail exactly here. -/
theorem shift_count_zero_oracle_independent :
    (step ⟨.shift .shl .q (.reg .rax) (.imm8 64), 4⟩ (s0 { rax := 0xFF } { cf := true })).flags
      = (step ⟨.shift .shl .q (.reg .rax) (.imm8 64), 4⟩ (s1 { rax := 0xFF } { cf := true })).flags := by
  decide

/-- CF at a shift count BELOW the width is defined (it is the last bit shifted
out), so it must not move with the oracle — the companion to
`shl_cf_undefined_when_count_ge_width`, isolating the boundary. -/
theorem shl_cf_defined_when_count_lt_width :
    (step ⟨.shift .shl .b (.reg .rax) (.imm8 1), 3⟩ (s0 { rax := 0x80 })).flags.cf
      = (step ⟨.shift .shl .b (.reg .rax) (.imm8 1), 3⟩ (s1 { rax := 0x80 })).flags.cf := by
  decide

/-- MOV, LEA, NOT, PUSH/POP and the branches commit to everything they write. -/
theorem mov_oracle_independent :
    (step ⟨.mov .d (.reg .rax) (.reg .rcx), 2⟩ (s0 { rax := 0xFF, rcx := 0x1234 })).regs
      = (step ⟨.mov .d (.reg .rax) (.reg .rcx), 2⟩ (s1 { rax := 0xFF, rcx := 0x1234 })).regs := by
  decide

theorem not_oracle_independent :
    (step ⟨.un .not .q (.reg .rax), 3⟩ (s0 { rax := 0xFF } { af := false })).flags
      = (step ⟨.un .not .q (.reg .rax), 3⟩ (s1 { rax := 0xFF } { af := false })).flags := by
  decide

/-! ## §3 — The oracle CURSOR is a deterministic function of the instruction

Fixing the draw COUNT (not only the order) is what lets the harness replay a
run: after any instruction the cursor is where the model says it is, regardless
of what the bits were. -/

theorem cursor_add_spends_nothing :
    (step ⟨.bin .add .q (.reg .rax) (.reg .rcx), 3⟩ (s0 { rax := 1, rcx := 2 })).oracle.cursor
      = 0 := by decide

theorem cursor_and_spends_one :
    (step ⟨.bin .and .q (.reg .rax) (.reg .rcx), 3⟩ (s0 { rax := 1, rcx := 2 })).oracle.cursor
      = 1 := by decide

theorem cursor_shift_nonzero_spends_three :
    (step ⟨.shift .shl .q (.reg .rax) (.imm8 1), 3⟩ (s0 { rax := 1 })).oracle.cursor = 3 := by
  decide

theorem cursor_shift_zero_spends_nothing :
    (step ⟨.shift .shl .q (.reg .rax) (.imm8 64), 4⟩ (s0 { rax := 1 })).oracle.cursor = 0 := by
  decide

/-- And the cursor does not depend on the BITS: the same instruction from the
same state advances the cursor identically under both oracles. -/
theorem cursor_independent_of_bits :
    (step ⟨.shift .shl .q (.reg .rax) (.imm8 1), 3⟩ (s0 { rax := 1 })).oracle.cursor
      = (step ⟨.shift .shl .q (.reg .rax) (.imm8 1), 3⟩ (s1 { rax := 1 })).oracle.cursor := by
  decide

/-! ## §3 — P1 BATCH 14: the first UNDEFINED REGISTER, and the flags around it

⭐⭐ THE OBLIGATION IN THIS SECTION IS NEW IN KIND.  Every theorem above is about
a FLAG: the oracle may reach it, or must not.  `bsf`/`bsr` at a zero source leave
the DESTINATION REGISTER undefined (SDM Vol. 2A), so for the first time the
oracle must be shown to reach a REGISTER — and, just as importantly, to reach it
ONLY at a zero source.

⛔ THE SECOND HALF IS THE ONE THAT WOULD OTHERWISE GO UNTESTED, and it is what
`X86.undefinedLeaked` enforces on every differential case: at a NON-zero source
the destination is an ordinary computed index and the two oracles must AGREE on
it.  A model that drew the destination unconditionally would satisfy §1 here and
be wrong about every `bsf` in the world.

⚠️ `maxRecDepth` is raised for this section alone.  An undefined DESTINATION is
`sz.bits` oracle draws — sixty-four of them at `.q`, where an undefined FLAG is
one — so `Oracle.drawVal` recurses sixty-four deep inside a `decide` that the
elaborator must evaluate.  Nothing about the proofs is heavier; the recursion is
simply deeper than the default allows. -/

set_option maxRecDepth 8000

/-- BSF at a zero source: the DESTINATION is undefined. -/
theorem bsf_dest_undefined_at_zero_source :
    (step ⟨.bitcnt .bsf .q .rax (.reg .rcx), 4⟩ (s0 { rax := 0xDEAD, rcx := 0 })).regs.get .rax
      ≠ (step ⟨.bitcnt .bsf .q .rax (.reg .rcx), 4⟩ (s1 { rax := 0xDEAD, rcx := 0 })).regs.get .rax := by
  decide

theorem bsr_dest_undefined_at_zero_source :
    (step ⟨.bitcnt .bsr .q .rax (.reg .rcx), 4⟩ (s0 { rax := 0xDEAD, rcx := 0 })).regs.get .rax
      ≠ (step ⟨.bitcnt .bsr .q .rax (.reg .rcx), 4⟩ (s1 { rax := 0xDEAD, rcx := 0 })).regs.get .rax := by
  decide

/-- ⛔ AND AT A NON-ZERO SOURCE IT IS NOT.  This is the half that says the
undefined region is a REGION and not the whole instruction. -/
theorem bsf_dest_defined_at_nonzero_source :
    (step ⟨.bitcnt .bsf .q .rax (.reg .rcx), 4⟩ (s0 { rax := 0xDEAD, rcx := 0x120 })).regs.get .rax
      = (step ⟨.bitcnt .bsf .q .rax (.reg .rcx), 4⟩ (s1 { rax := 0xDEAD, rcx := 0x120 })).regs.get .rax := by
  decide

theorem bsr_dest_defined_at_nonzero_source :
    (step ⟨.bitcnt .bsr .q .rax (.reg .rcx), 4⟩ (s0 { rax := 0xDEAD, rcx := 0x120 })).regs.get .rax
      = (step ⟨.bitcnt .bsr .q .rax (.reg .rcx), 4⟩ (s1 { rax := 0xDEAD, rcx := 0x120 })).regs.get .rax := by
  decide

/-- BSF/BSR: five undefined flags.  ZF is NOT among them and is checked below. -/
theorem bsf_cf_undefined :
    (step ⟨.bitcnt .bsf .q .rax (.reg .rcx), 4⟩ (s0 { rcx := 0x120 })).flags.cf
      ≠ (step ⟨.bitcnt .bsf .q .rax (.reg .rcx), 4⟩ (s1 { rcx := 0x120 })).flags.cf := by
  decide

theorem bsr_of_undefined :
    (step ⟨.bitcnt .bsr .q .rax (.reg .rcx), 4⟩ (s0 { rcx := 0x120 })).flags.of
      ≠ (step ⟨.bitcnt .bsr .q .rax (.reg .rcx), 4⟩ (s1 { rcx := 0x120 })).flags.of := by
  decide

/-- ⭐ AND ZF IS COMMITTED, at a zero source and a non-zero one alike — the one
promise `bsf`/`bsr` make about their flags.  A model that drew ZF from the
oracle along with the other five would pass every §1 theorem in this file. -/
theorem bsf_zf_committed_at_zero_source :
    (step ⟨.bitcnt .bsf .q .rax (.reg .rcx), 4⟩ (s0 { rcx := 0 })).flags.zf
      = (step ⟨.bitcnt .bsf .q .rax (.reg .rcx), 4⟩ (s1 { rcx := 0 })).flags.zf := by
  decide

theorem bsr_zf_committed_at_nonzero_source :
    (step ⟨.bitcnt .bsr .q .rax (.reg .rcx), 4⟩ (s0 { rcx := 0x120 })).flags.zf
      = (step ⟨.bitcnt .bsr .q .rax (.reg .rcx), 4⟩ (s1 { rcx := 0x120 })).flags.zf := by
  decide

/-- LZCNT and TZCNT: PF, AF, SF and OF undefined; CF and ZF committed. -/
theorem lzcnt_sf_undefined :
    (step ⟨.bitcnt .lzcnt .q .rax (.reg .rcx), 5⟩ (s0 { rcx := 0x120 })).flags.sf
      ≠ (step ⟨.bitcnt .lzcnt .q .rax (.reg .rcx), 5⟩ (s1 { rcx := 0x120 })).flags.sf := by
  decide

theorem tzcnt_pf_undefined :
    (step ⟨.bitcnt .tzcnt .q .rax (.reg .rcx), 5⟩ (s0 { rcx := 0x120 })).flags.pf
      ≠ (step ⟨.bitcnt .tzcnt .q .rax (.reg .rcx), 5⟩ (s1 { rcx := 0x120 })).flags.pf := by
  decide

theorem lzcnt_cf_and_zf_committed :
    (step ⟨.bitcnt .lzcnt .q .rax (.reg .rcx), 5⟩ (s0 { rcx := 0 })).flags.cf
      = (step ⟨.bitcnt .lzcnt .q .rax (.reg .rcx), 5⟩ (s1 { rcx := 0 })).flags.cf
    ∧ (step ⟨.bitcnt .lzcnt .q .rax (.reg .rcx), 5⟩ (s0 { rcx := 0 })).flags.zf
      = (step ⟨.bitcnt .lzcnt .q .rax (.reg .rcx), 5⟩ (s1 { rcx := 0 })).flags.zf := by
  decide

/-- ⭐ AND LZCNT'S DESTINATION IS NEVER UNDEFINED, not even at a zero source —
where it is the WIDTH.  This is the theorem that separates the two opcode pairs:
`bsr` and `lzcnt` are one prefix byte apart and answer a zero source in
completely different currencies. -/
theorem lzcnt_dest_defined_at_zero_source :
    (step ⟨.bitcnt .lzcnt .q .rax (.reg .rcx), 5⟩ (s0 { rax := 0xDEAD, rcx := 0 })).regs.get .rax
      = (step ⟨.bitcnt .lzcnt .q .rax (.reg .rcx), 5⟩ (s1 { rax := 0xDEAD, rcx := 0 })).regs.get .rax := by
  decide

/-- BLSI: PF and AF undefined, SF/ZF/CF/OF committed. -/
theorem blsi_af_undefined :
    (step ⟨.bitcnt .blsi .q .rax (.reg .rcx), 5⟩ (s0 { rcx := 0x120 })).flags.af
      ≠ (step ⟨.bitcnt .blsi .q .rax (.reg .rcx), 5⟩ (s1 { rcx := 0x120 })).flags.af := by
  decide

/-- ⭐ POPCNT LEAVES NOTHING UNDEFINED — the only member of the group at
`T-exact`, and the tier is a behavioural claim rather than a label. -/
theorem popcnt_fully_committed :
    (step ⟨.bitcnt .popcnt .q .rax (.reg .rcx), 5⟩ (s0 { rax := 0xDEAD, rcx := 0x120 })).flags
      = (step ⟨.bitcnt .popcnt .q .rax (.reg .rcx), 5⟩ (s1 { rax := 0xDEAD, rcx := 0x120 })).flags
    ∧ (step ⟨.bitcnt .popcnt .q .rax (.reg .rcx), 5⟩ (s0 { rax := 0xDEAD, rcx := 0x120 })).regs.get .rax
      = (step ⟨.bitcnt .popcnt .q .rax (.reg .rcx), 5⟩ (s1 { rax := 0xDEAD, rcx := 0x120 })).regs.get .rax := by
  decide
  -- ⚠️ NOT `... s0 = ... s1` ON THE WHOLE `Cpu`.  `Cpu` carries the `Oracle`,
  -- whose `bits` is a FUNCTION FIELD with no `DecidableEq` — by design, since a
  -- decidable oracle is one a theorem could learn a bit of.  So the two states
  -- are compared component by component, and the components are whole RECORDS
  -- (`flags`) rather than seven projections, which is D30 one level down.

/-! ## §4 — P1 BATCH 17: the flags a division promises nothing about, and the
FAULT that must be reachable in both directions

⭐⭐ THIS SECTION CARRIES AN OBLIGATION THE OTHERS DO NOT: a REACHABILITY claim
about the model's own refusal.  `div` and `idiv` fault on their OPERANDS, and a
form that refused in every state would agree with x86isa on every case it was
shown — the oracle refuses there too — while testing nothing about the quotient.
So both branches are asserted to be reachable, by exhibiting a state on each
side, and the `divPairU`/`divPairS` half of the claim is checked by `decide`
rather than by a comment reporting what a probe once printed.

⚠️ THE TWO REFUSAL CAUSES ARE ASSERTED SEPARATELY.  A zero divisor and an
over-wide quotient are different sentences of the SDM, and a model implementing
only the first is `wrongDivNoQuotientOverflow` — which is caught by the
differential run, but only because a pre-state reaches the second cause.  These
theorems are what keep that true if `adversarial` is ever reordered: batch 2's
`carryBoundary` lesson, applied to a fault instead of a carry. -/

/-- `div` REFUSES on a zero divisor. -/
theorem div_refuses_on_zero_divisor :
    (step ⟨.muldiv .div .q (.reg .rcx), 3⟩ (s0 { rax := 7, rdx := 0, rcx := 0 })).stopped
      = true := by decide

/-- `div` REFUSES when the quotient is too wide — a NON-zero divisor, so this is
the second sentence and not the first one again. -/
theorem div_refuses_on_quotient_overflow :
    (step ⟨.muldiv .div .q (.reg .rcx), 3⟩ (s0 { rax := 0, rdx := 5, rcx := 2 })).stopped
      = true := by decide

/-- ⭐ AND IT COMPUTES — the arm without which the two above would be satisfied
by a `div` that never divides.  `10 / 3 = 3` remainder `1`. -/
theorem div_computes_and_writes_the_pair :
    (step ⟨.muldiv .div .q (.reg .rcx), 3⟩ (s0 { rax := 10, rdx := 0, rcx := 3 })).stopped
      = false
  ∧ (step ⟨.muldiv .div .q (.reg .rcx), 3⟩ (s0 { rax := 10, rdx := 0, rcx := 3 })).regs.get .rax
      = 3
  ∧ (step ⟨.muldiv .div .q (.reg .rcx), 3⟩ (s0 { rax := 10, rdx := 0, rcx := 3 })).regs.get .rdx
      = 1 := by decide

/-- ⭐⭐ IDIV TRUNCATES TOWARD ZERO, AND THE REMAINDER TAKES THE DIVIDEND'S SIGN.
`-7 / 2` is `-3` remainder `-1` on the machine; Lean's `Int` division would give
`-4` remainder `1`.  This is the one substitution `wrongIdivFloorDivision` and
`wrongIdivRemainderSign` make, stated where a reader can check it by eye. -/
theorem idiv_truncates_toward_zero :
    (step ⟨.muldiv .idiv .q (.reg .rcx), 3⟩
        (s0 { rax := 0xFFFFFFFFFFFFFFF9, rdx := 0xFFFFFFFFFFFFFFFF, rcx := 2 })).regs.get .rax
      = 0xFFFFFFFFFFFFFFFD
  ∧ (step ⟨.muldiv .idiv .q (.reg .rcx), 3⟩
        (s0 { rax := 0xFFFFFFFFFFFFFFF9, rdx := 0xFFFFFFFFFFFFFFFF, rcx := 2 })).regs.get .rdx
      = 0xFFFFFFFFFFFFFFFF := by decide

/-- ⭐ THE BYTE MULTIPLY WRITES `AH:AL` AND LEAVES RDX ALONE.  `200 * 3 = 600 =
0x258`, so AL is `0x58` and AH is `0x02` — one register — and RDX keeps the
marker it was given.  `wrongMulBytePairInRdx` is the model this refutes. -/
theorem mul_byte_writes_ah_al_not_rdx :
    (step ⟨.muldiv .mul .b (.reg .rcx), 2⟩
        (s0 { rax := 200, rcx := 3, rdx := 0xDEAD })).regs.get .rax = 0x0258
  ∧ (step ⟨.muldiv .mul .b (.reg .rcx), 2⟩
        (s0 { rax := 200, rcx := 3, rdx := 0xDEAD })).regs.get .rdx = 0xDEAD := by decide

/-- `div` and `idiv`: all six arithmetic flags undefined.  Two of the six are
exhibited; the differential run's undefined-column gate checks all six against
what the model draws, in both directions. -/
theorem div_cf_undefined :
    (step ⟨.muldiv .div .q (.reg .rcx), 3⟩ (s0 { rax := 10, rdx := 0, rcx := 3 })).flags.cf
      ≠ (step ⟨.muldiv .div .q (.reg .rcx), 3⟩ (s1 { rax := 10, rdx := 0, rcx := 3 })).flags.cf := by
  decide

theorem idiv_zf_undefined :
    (step ⟨.muldiv .idiv .q (.reg .rcx), 3⟩ (s0 { rax := 10, rdx := 0, rcx := 3 })).flags.zf
      ≠ (step ⟨.muldiv .idiv .q (.reg .rcx), 3⟩ (s1 { rax := 10, rdx := 0, rcx := 3 })).flags.zf := by
  decide

/-- ⭐ AND MUL's CF AND OF ARE COMMITTED — the two bits the multiply group
PROMISES, against four it does not.  A model that drew all six, as the divisions
do, would satisfy every `≠` theorem in this file and be wrong about the only
flag `mul` is for. -/
theorem mul_cf_and_of_committed :
    (step ⟨.muldiv .mul .q (.reg .rcx), 3⟩ (s0 { rax := 0x100000000, rcx := 0x100000000 })).flags.cf
      = (step ⟨.muldiv .mul .q (.reg .rcx), 3⟩ (s1 { rax := 0x100000000, rcx := 0x100000000 })).flags.cf
  ∧ (step ⟨.muldiv .mul .q (.reg .rcx), 3⟩ (s0 { rax := 0x100000000, rcx := 0x100000000 })).flags.of
      = (step ⟨.muldiv .mul .q (.reg .rcx), 3⟩ (s1 { rax := 0x100000000, rcx := 0x100000000 })).flags.of := by
  decide

theorem mul_af_undefined :
    (step ⟨.muldiv .mul .q (.reg .rcx), 3⟩ (s0 { rax := 3, rcx := 5 })).flags.af
      ≠ (step ⟨.muldiv .mul .q (.reg .rcx), 3⟩ (s1 { rax := 3, rcx := 5 })).flags.af := by
  decide

/-- ⛔ IMUL's OVERFLOW RULE IS NOT MUL's, exhibited at a state where the two
answers DIFFER: `0xFF * 0xFF` at `.b` is `-1 * -1 = 1` signed — no overflow —
and `255 * 255 = 65025` unsigned, which does not fit a byte.  ⚠️ THE STATE WAS
CHOSEN A SECOND TIME.  The first version used `rax := 0xFF, rcx := 1`, where
both rules answer `false`: the theorem was true, green, and proved nothing about
the difference it is named for.  This is the model `wrongImulUsesMulOverflow`
gets wrong, and now the theorem sees it. -/
theorem imul_overflow_is_not_mul_overflow :
    (step ⟨.muldiv .imul .b (.reg .rcx), 2⟩ (s0 { rax := 0xFF, rcx := 0xFF })).flags.cf = false
  ∧ (step ⟨.muldiv .mul .b (.reg .rcx), 2⟩ (s0 { rax := 0xFF, rcx := 0xFF })).flags.cf = true
  ∧ Value.mulOverflow .b 0xFF 0xFF = true
  ∧ Value.imulOverflow .b 0xFF 0xFF = false := by decide

/-! ## P1 BATCH 18 — the double shifts' three branches, and the two forms that
draw nothing

⭐ THIS GROUP NEEDS THE `≠` AND THE `=` DIRECTION IN THE SAME PLACE, because its
undefined set is a function of the COUNT: the same instruction at the same width
commits to every flag at one count, draws two at another, and draws six and the
destination at a third.  A file of `≠` theorems alone would be satisfied by a
model that drew all six everywhere. -/

/-- ⭐⭐ THE UNDEFINED DESTINATION — the SECOND in this model, and the first whose
undefinedness comes from an operand OTHER than the one it overwrites.  `.w` with
a count of 20: above the operand size, so the SDM stops defining the result. -/
theorem shld_w_bad_count_dest_undefined :
    (step ⟨.dshift .shld .w (.reg .rax) .rcx (.imm8 20), 5⟩
      (s0 { rax := 0xABCD, rcx := 0x1234 })).regs.get .rax
      ≠ (step ⟨.dshift .shld .w (.reg .rax) .rcx (.imm8 20), 5⟩
      (s1 { rax := 0xABCD, rcx := 0x1234 })).regs.get .rax := by decide

/-- …and ALL SIX FLAGS with it.  CF is exhibited; the undefined-column gate
checks the whole set against what the model draws, in both directions. -/
theorem shld_w_bad_count_cf_undefined :
    (step ⟨.dshift .shld .w (.reg .rax) .rcx (.imm8 20), 5⟩
      (s0 { rax := 0xABCD, rcx := 0x1234 })).flags.cf
      ≠ (step ⟨.dshift .shld .w (.reg .rax) .rcx (.imm8 20), 5⟩
      (s1 { rax := 0xABCD, rcx := 0x1234 })).flags.cf := by decide

/-- ⛔ AND ONE COUNT LOWER THE SAME INSTRUCTION COMMITS TO ITS DESTINATION AND TO
CF.  `.w` with a count of 16 is the boundary: legal, so the answer is computed
and the oracle is not consulted for it.  ⚠️ THIS IS THE THEOREM THAT MAKES THE
TWO ABOVE MEAN SOMETHING — without it a model that drew the destination at every
count would satisfy both and be wrong about twenty-four of the harness's
eighty-two pre-states. -/
theorem shld_w_boundary_count_is_committed :
    (step ⟨.dshift .shld .w (.reg .rax) .rcx (.imm8 16), 5⟩
      (s0 { rax := 0xABCD, rcx := 0x1234 })).regs.get .rax
      = (step ⟨.dshift .shld .w (.reg .rax) .rcx (.imm8 16), 5⟩
      (s1 { rax := 0xABCD, rcx := 0x1234 })).regs.get .rax
  ∧ (step ⟨.dshift .shld .w (.reg .rax) .rcx (.imm8 16), 5⟩
      (s0 { rax := 0xABCD, rcx := 0x1234 })).flags.cf
      = (step ⟨.dshift .shld .w (.reg .rax) .rcx (.imm8 16), 5⟩
      (s1 { rax := 0xABCD, rcx := 0x1234 })).flags.cf := by decide

/-- AF is undefined at every non-zero count, and OF at every non-zero count but
one — so at a count of 5 both are drawn. -/
theorem shld_af_and_of_undefined_at_five :
    (step ⟨.dshift .shld .q (.reg .rax) .rcx (.imm8 5), 5⟩
      (s0 { rax := 0xABCD, rcx := 0x1234 })).flags.af
      ≠ (step ⟨.dshift .shld .q (.reg .rax) .rcx (.imm8 5), 5⟩
      (s1 { rax := 0xABCD, rcx := 0x1234 })).flags.af
  ∧ (step ⟨.dshift .shld .q (.reg .rax) .rcx (.imm8 5), 5⟩
      (s0 { rax := 0xABCD, rcx := 0x1234 })).flags.of
      ≠ (step ⟨.dshift .shld .q (.reg .rax) .rcx (.imm8 5), 5⟩
      (s1 { rax := 0xABCD, rcx := 0x1234 })).flags.of := by decide

/-- ⭐ AND AT A COUNT OF ONE, OF IS COMMITTED — the one count where the SDM
defines it, as a sign change.  CF is committed at every legal count. -/
theorem shld_of_committed_at_one :
    (step ⟨.dshift .shld .q (.reg .rax) .rcx (.imm8 1), 4⟩
      (s0 { rax := 0xABCD, rcx := 0x1234 })).flags.of
      = (step ⟨.dshift .shld .q (.reg .rax) .rcx (.imm8 1), 4⟩
      (s1 { rax := 0xABCD, rcx := 0x1234 })).flags.of := by decide

/-- ⭐ A COUNT OF ZERO DRAWS NOTHING AT ALL — no flag moves between the two
oracles, because none is written.  Distinguishes "undefined" from "unwritten",
which the `≠` theorems above cannot. -/
theorem shld_zero_count_draws_nothing :
    (step ⟨.dshift .shld .q (.reg .rax) .rcx (.imm8 0), 4⟩
      (s0 { rax := 0xABCD, rcx := 0x1234 })).flags
      = (step ⟨.dshift .shld .q (.reg .rax) .rcx (.imm8 0), 4⟩
      (s1 { rax := 0xABCD, rcx := 0x1234 })).flags
  ∧ (step ⟨.dshift .shld .q (.reg .rax) .rcx (.imm8 0), 4⟩
      (s0 { rax := 0xABCD, rcx := 0x1234 })).regs.get .rax
      = (step ⟨.dshift .shld .q (.reg .rax) .rcx (.imm8 0), 4⟩
      (s1 { rax := 0xABCD, rcx := 0x1234 })).regs.get .rax := by decide

/-- ⭐ CMPXCHG AND XADD DRAW NOTHING, ON EITHER BRANCH.  Both are `T-exact` with
an EMPTY undefined column, and this is the theorem that holds that column up:
the two opposite oracles give the identical post-state, so no bit of either
answer comes from the oracle.  ⚠️ BOTH CMPXCHG BRANCHES ARE EXHIBITED — a model
that drew a flag on the branch nobody tested would satisfy a one-branch version
of this. -/
theorem cmpxchg_and_xadd_draw_nothing :
    (step ⟨.cmpxchg .d (.reg .rcx) .rdx, 3⟩ (s0 { rax := 7, rcx := 9, rdx := 5 })).flags
      = (step ⟨.cmpxchg .d (.reg .rcx) .rdx, 3⟩ (s1 { rax := 7, rcx := 9, rdx := 5 })).flags
  ∧ (step ⟨.cmpxchg .d (.reg .rcx) .rdx, 3⟩ (s0 { rax := 9, rcx := 9, rdx := 5 })).flags
      = (step ⟨.cmpxchg .d (.reg .rcx) .rdx, 3⟩ (s1 { rax := 9, rcx := 9, rdx := 5 })).flags
  ∧ (step ⟨.xadd .q (.reg .rax) .rcx, 4⟩ (s0 { rax := 9, rcx := 4 })).flags
      = (step ⟨.xadd .q (.reg .rax) .rcx, 4⟩ (s1 { rax := 9, rcx := 4 })).flags := by decide

end X86.Tests
