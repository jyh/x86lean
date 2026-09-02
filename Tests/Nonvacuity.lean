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

end X86.Tests
