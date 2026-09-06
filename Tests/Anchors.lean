/-
# Tests.Anchors — concrete SDM anchor examples, checked by the KERNEL

Plan v1 §4.1: "per form, concrete I/O pairs from the SDM's own examples, by
`decide`."  Every statement below is a `theorem` closed by `decide`, so the Lean
KERNEL evaluates the model on the example and checks the answer.  Nothing here
is `#eval`, `native_decide`, or `#guard`: those run the COMPILED model, and the
compiled model is a different artifact from the one the theorems are about.

⛔ AXIOM DISCIPLINE.  `decide` on a closed decidable proposition produces
`Decidable.decide … = true` by kernel reduction and adds NO axiom.  That is why
these are here and not in the native tier.

WHAT AN ANCHOR IS FOR.  A characterization theorem says `step` equals a record
update; it cannot say the record update is the RIGHT one.  An anchor pins the
model to a value a reader can check against the manual by hand.  The two
together are the whole of what this repository can prove on its own; the
differential run against ACL2 x86isa is what checks it against another model.

LANE. Personal lane, public sources only.
-/
import X86

namespace X86.Tests
open X86

/-- A concrete state, built positionally so an anchor reads as a small program. -/
def mk (regs : Regs := {}) (flags : Flags := {}) (mem : Mem := {})
    (rip : BitVec 64 := 0) (o : Oracle := Oracle.zero) : Cpu :=
  { regs := regs, flags := flags, mem := mem, rip := rip, oracle := o }

/-- The all-ones oracle: every undefined bit reads `true`.  Paired with
`Oracle.zero` in `Tests/Nonvacuity.lean` to show the undefined bits are really
undefined. -/
def oneOracle : Oracle := { bits := fun _ => true }

/-! ## The register encoding order (SDM Vol. 2A Table 2-2)

A wrong `GPR.index` is a silent, total-model bug that no type and no
characterization theorem can catch, because every register is a `GPR` either
way.  It gets its own anchor. -/

theorem reg_encoding :
    (GPR.all.map (fun r => r.index.val)) = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] := by
  decide

theorem reg_names_q :
    (GPR.all.map (fun r => r.name .q)) =
      ["rax","rcx","rdx","rbx","rsp","rbp","rsi","rdi",
       "r8","r9","r10","r11","r12","r13","r14","r15"] := by
  decide

/-! ## MOV and the 32-bit zero-extension rule (SDM Vol. 1 §3.4.1.1)

`mov eax, ecx` clears the upper 32 bits of RAX; `mov ax, cx` does not clear
anything above bit 15.  These two anchors are the same instruction at two widths
and they must disagree — that disagreement IS the rule. -/

private def s_mov : Cpu :=
  mk { rax := 0xFFFFFFFFFFFFFFFF, rcx := 0x00000000AABBCCDD }

theorem mov_d_zero_extends :
    (step ⟨.mov .d (.reg .rax) (.reg .rcx), 2⟩ s_mov).regs.rax = 0x00000000AABBCCDD := by
  decide

theorem mov_w_preserves_high :
    (step ⟨.mov .w (.reg .rax) (.reg .rcx), 3⟩ s_mov).regs.rax = 0xFFFFFFFFFFFFCCDD := by
  decide

theorem mov_b_preserves_high :
    (step ⟨.mov .b (.reg .rax) (.reg .rcx), 2⟩ s_mov).regs.rax = 0xFFFFFFFFFFFFFFDD := by
  decide

/-- RIP advances by the instruction's own length, not by a constant. -/
theorem mov_advances_rip :
    (step ⟨.mov .d (.reg .rax) (.reg .rcx), 2⟩ s_mov).rip = 2 := by decide

/-- MOV writes no flag. -/
theorem mov_flags_untouched :
    (step ⟨.mov .q (.reg .rax) (.reg .rcx), 3⟩
      (mk { rax := 1 } { cf := true, zf := true })).flags
      = { cf := true, zf := true } := by decide

/-! ## ADD — SDM Vol. 2A, ADD

The canonical carry/overflow corner: at 8 bits, `0x7F + 0x01 = 0x80` is a SIGNED
overflow with NO carry, and `0xFF + 0x01 = 0x00` is a carry with NO signed
overflow.  A model that conflates CF and OF passes neither. -/

theorem add_b_signed_overflow_no_carry :
    (step ⟨.bin .add .b (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0x7F, rcx := 0x01 })).flags
      = { cf := false, of := true, sf := true, zf := false, af := true, pf := false,
          df := false } := by
  decide

theorem add_b_carry_no_signed_overflow :
    (step ⟨.bin .add .b (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0xFF, rcx := 0x01 })).flags
      = { cf := true, of := false, sf := false, zf := true, af := true, pf := true,
          df := false } := by
  decide

/-- The result really is truncated to the operand width: `0xFF + 0x01` at 8 bits
leaves `0x00` in AL and the upper 56 bits of RAX untouched. -/
theorem add_b_result_truncates :
    (step ⟨.bin .add .b (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0xAAAAAAAAAAAAAAFF, rcx := 0x01 })).regs.rax
      = 0xAAAAAAAAAAAAAA00 := by
  decide

/-- 64-bit carry out of the top: the width where an off-by-one in `addCF` hides. -/
theorem add_q_carry :
    (step ⟨.bin .add .q (.reg .rax) (.reg .rcx), 3⟩
      (mk { rax := 0xFFFFFFFFFFFFFFFF, rcx := 0x01 })).flags.cf = true := by
  decide

/-- PF is the parity of the LOW BYTE at EVERY width.  `0x0100` has an even
number of set bits overall and ZERO set bits in its low byte, so PF is set at
16 bits — a model that took the parity of the whole result would also say `true`
here, so the discriminating case is the next one. -/
theorem add_w_parity_low_byte :
    (step ⟨.bin .add .w (.reg .rax) (.reg .rcx), 4⟩
      (mk { rax := 0x00FF, rcx := 0x0001 })).flags.pf = true := by
  decide

/-- The discriminator: result `0x0101` has an EVEN number of set bits overall
(two) but an ODD number in its low byte (one), so PF must be FALSE. -/
theorem add_w_parity_is_low_byte_only :
    (step ⟨.bin .add .w (.reg .rax) (.reg .rcx), 4⟩
      (mk { rax := 0x0100, rcx := 0x0001 })).flags.pf = false := by
  decide

/-- AF is the carry out of BIT 3: `0x08 + 0x08 = 0x10` sets it, `0x07 + 0x08`
does not. -/
theorem add_af_set : (step ⟨.bin .add .b (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0x08, rcx := 0x08 })).flags.af = true := by decide

theorem add_af_clear : (step ⟨.bin .add .b (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0x07, rcx := 0x08 })).flags.af = false := by decide

/-! ## SUB / CMP — SDM Vol. 2A -/

/-- CF on subtraction is a BORROW. -/
theorem sub_borrow :
    (step ⟨.bin .sub .b (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0x00, rcx := 0x01 })).flags.cf = true := by decide

theorem sub_no_borrow :
    (step ⟨.bin .sub .b (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0x01, rcx := 0x01 })).flags.cf = false := by decide

/-- `0x80 - 0x01` at 8 bits: signed overflow (−128 − 1). -/
theorem sub_signed_overflow :
    (step ⟨.bin .sub .b (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0x80, rcx := 0x01 })).flags.of = true := by decide

/-- CMP sets exactly the flags SUB does and writes NO register. -/
theorem cmp_matches_sub_flags :
    (step ⟨.bin .cmp .b (.reg .rax) (.reg .rcx), 2⟩ (mk { rax := 0x00, rcx := 0x01 })).flags
      = (step ⟨.bin .sub .b (.reg .rax) (.reg .rcx), 2⟩ (mk { rax := 0x00, rcx := 0x01 })).flags := by
  decide

theorem cmp_writes_no_register :
    (step ⟨.bin .cmp .b (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0x00, rcx := 0x01 })).regs.rax = 0x00 := by decide

/-! ## The logic group — CF and OF CLEARED, AF from the oracle -/

theorem and_clears_cf_of :
    (step ⟨.bin .and .q (.reg .rax) (.reg .rcx), 3⟩
      (mk { rax := 0xF0, rcx := 0x3C } { cf := true, of := true })).flags
      = { cf := false, of := false, sf := false, zf := false, pf := true, af := false,
          df := false } := by
  decide

theorem xor_self_is_zero :
    (step ⟨.bin .xor .q (.reg .rax) (.reg .rax), 3⟩ (mk { rax := 0xDEADBEEF })).regs.rax = 0 := by
  decide

theorem test_writes_no_register :
    (step ⟨.bin .test .q (.reg .rax) (.reg .rcx), 3⟩
      (mk { rax := 0xF0, rcx := 0x0F })).regs.rax = 0xF0 := by decide

theorem test_sets_zf_when_disjoint :
    (step ⟨.bin .test .q (.reg .rax) (.reg .rcx), 3⟩
      (mk { rax := 0xF0, rcx := 0x0F })).flags.zf = true := by decide

/-! ## P1 BATCH 2 — the carry, at the two states where it alone decides

Each of these is a state in which `adc` and `add` give DIFFERENT answers, or
`sbb` and `sub` do. That is the whole content of the batch: everywhere else the
new template degenerates to the old one, and `adc_no_carry_is_add` in
X86/Theorems.lean proves the degeneration. -/

/-- ⭐ `0xFF + 0x00 + CF` AT WIDTH b: without the carry it is 0xFF and no carry
out; with it, the byte wraps to 0 and CF is SET. A model that ignored the
carry-in would answer 0xFF here and agree with the oracle on every operand pair
that does not sit on this boundary. -/
theorem adc_carry_alone_overflows :
    ((step ⟨.bin .adc .b (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0xFF, rcx := 0x00 } { cf := true })).regs.rax = 0x00)
    ∧ ((step ⟨.bin .adc .b (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0xFF, rcx := 0x00 } { cf := true })).flags.cf = true) := by decide

theorem adc_without_carry_does_not :
    ((step ⟨.bin .adc .b (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0xFF, rcx := 0x00 })).regs.rax = 0xFF)
    ∧ ((step ⟨.bin .adc .b (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0xFF, rcx := 0x00 })).flags.cf = false) := by decide

/-- ⭐ `0x00 - 0x00 - CF`: without the carry, zero and no borrow; with it, 0xFF
and CF set. The mirror of the above, and the state `sub` can never reach. -/
theorem sbb_carry_alone_borrows :
    ((step ⟨.bin .sbb .b (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0x00, rcx := 0x00 } { cf := true })).regs.rax = 0xFF)
    ∧ ((step ⟨.bin .sbb .b (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0x00, rcx := 0x00 } { cf := true })).flags.cf = true) := by decide

/-- ⚠️ THE CARRY READ IS THE INCOMING ONE. Here the instruction both reads CF
(as an addend) and writes it (as a carry-out), and the two values DIFFER: CF
goes in set and comes out clear. An implementation that read CF after writing
it, or wrote before reading, would produce 0x02 or a set CF; only reading first
gives 0x02… — concretely, `0x00 + 0x01 + 1 = 0x02` with CF cleared on the way
out, and the anchor pins both halves. -/
theorem adc_reads_cf_before_writing_it :
    ((step ⟨.bin .adc .b (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0x00, rcx := 0x01 } { cf := true })).regs.rax = 0x02)
    ∧ ((step ⟨.bin .adc .b (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0x00, rcx := 0x01 } { cf := true })).flags.cf = false) := by decide

/-- The 32-bit carry form still zero-extends: `adcl` with a carry into the low
bit clears the upper 32 bits like every other 32-bit write. -/
theorem adcl_zero_extends :
    (step ⟨.bin .adc .d (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0xDEADBEEF_00000001, rcx := 0x00000001 } { cf := true })).regs.rax
      = 0x00000003 := by decide

/-- And AF still comes from the same identity with a carry in the way: the low
nibble `0xF + 0x0 + 1` carries out of bit 3. -/
theorem adc_aux_carry_sees_the_carry_in :
    (step ⟨.bin .adc .b (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0x0F, rcx := 0x00 } { cf := true })).flags.af = true := by decide

/-! ## P1 BATCH 1 — the four behaviours P0's vectors never reached

Anchors, not vectors: each is a concrete SDM sentence checked by `decide`, so it
fails at BUILD time rather than waiting for an oracle. They exist because the
batch's whole content is operand shapes and widths, and a shape that is never
exercised is a coverage-table row with nothing behind it. -/

/-- ⭐ A 32-BIT ALU WRITE ZERO-EXTENDS (SDM Vol. 1 §3.4.1.1).  P0 proved this for
`mov` and nowhere else; batch 1 is where it reaches the logic group. `andl`
with an all-ones mask keeps the low 32 bits and CLEARS the upper 32 — a model
that merged instead of zero-extending would keep `0xDEADBEEF` up there and every
`r,r` and `r,imm` vector at width `q` would still pass. -/
theorem andl_zero_extends :
    (step ⟨.bin .and .d (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0xDEADBEEF_12345678, rcx := 0xFFFFFFFF })).regs.rax
      = 0x12345678 := by decide

/-- And the contrast that gives it meaning: a 16-BIT write PRESERVES the upper
bits.  Same instruction, same operands, one width apart. -/
theorem andw_preserves_upper :
    (step ⟨.bin .and .w (.reg .rax) (.reg .rcx), 3⟩
      (mk { rax := 0xDEADBEEF_12345678, rcx := 0xFFFF })).regs.rax
      = 0xDEADBEEF_12340000 + 0x5678 := by decide

/-- ⭐ THE HIGH-8 REGISTERS.  `andb %cl, %ah` writes bits 15:8 of RAX and
touches nothing else in the register — not the low byte, not the upper 48 bits.
Nothing in P0 read or wrote AH/CH/DH/BH at all. -/
theorem and_high8_dest :
    (step ⟨.bin .and .b (.reg .rax true) (.reg .rcx), 2⟩
      (mk { rax := 0xDEADBEEF_1234FF78, rcx := 0x0F })).regs.rax
      = 0xDEADBEEF_12340F78 := by decide

/-- And a high-8 SOURCE reads bits 15:8, not the low byte: with CH = 0x34 and
CL = 0x78, `andb %ch, %al` masks with 0x34 and `andb %cl, %al` would mask with
0x78. -/
theorem and_high8_src :
    (step ⟨.bin .and .b (.reg .rax) (.reg .rcx true), 2⟩
      (mk { rax := 0xFF, rcx := 0x3478 })).regs.rax = 0x34 := by decide

/-- ⭐ THE SIGN-EXTENDED IMMEDIATE.  `andq $-1, %rcx` encodes `$-1` as ONE byte
(`48 83 e1 ff`) and the decoder hands the model the 64-bit value it stands for
(X86/Syntax.lean: "immediates are already sign- or zero-extended … the semantics
never re-extends").  This anchor is what that sentence costs if it is wrong: a
model that zero-extended the imm8 would mask with 0xFF and clear the top 56
bits of RCX instead of leaving the register alone. -/
theorem and_imm8_sign_extended :
    (step ⟨.bin .and .q (.reg .rcx) (.imm 0xFFFFFFFF_FFFFFFFF), 4⟩
      (mk { rcx := 0xDEADBEEF_12345678 })).regs.rcx = 0xDEADBEEF_12345678 := by decide

/-- ⭐ A MEMORY SOURCE WITH A REGISTER DESTINATION, and the frame that goes with
it: `orq (%rbx), %rax` reads eight bytes little-endian and writes NO memory.
P0's only memory reads were `mov` and `pop`. -/
theorem or_reg_mem_reads_le :
    (step ⟨.bin .or .q (.reg .rax) (.mem { base := some .rbx }), 3⟩
      (mk { rax := 0, rbx := 0x100 }
         {} ((Mem.empty.write 0x100 0x78).write 0x101 0x56))).regs.rax
      = 0x5678 := by decide

theorem or_reg_mem_writes_no_memory :
    (step ⟨.bin .or .q (.reg .rax) (.mem { base := some .rbx }), 3⟩
      (mk { rax := 0xFF, rbx := 0x100 }
         {} (Mem.empty.write 0x100 0x11))).mem.read 0x100 = 0x11 := by decide

-- ⛔ THERE WAS A NINTH ANCHOR HERE AND IT SAID NOTHING.  It was written to
-- record that the accumulator short form and the general form are the same
-- instruction to a post-decode model, and what it actually asserted was
-- `step i c = step i c` by `rfl` — true of every term in Lean, provable of a
-- model that did the opposite.  It type-checked, it was green, and it was a
-- coverage row with nothing behind it, which is the defect this batch's anchors
-- exist to prevent.  The claim is real but it is a claim about the VECTOR
-- TABLE, not about `step`: `and_acc_b` and `and_ri_b` carry different bytes
-- from the assembler, and Tests/Coverage.lean is where a fact about the table
-- belongs.  Deleted rather than repaired, and left named so it is not
-- reinvented.

/-! ## INC / DEC / NEG / NOT -/

/-- ⭐ INC DOES NOT TOUCH CF.  With CF set on the way in, an `inc` that overflows
its width leaves CF SET (it was) while a corresponding `add 1` would clear it.
This anchor is the reason `inc` is its own instruction in this model. -/
theorem inc_preserves_cf_true :
    (step ⟨.un .inc .b (.reg .rax), 2⟩ (mk { rax := 0x05 } { cf := true })).flags.cf = true := by
  decide

theorem inc_preserves_cf_false_where_add_would_carry :
    (step ⟨.un .inc .b (.reg .rax), 2⟩ (mk { rax := 0xFF } { cf := false })).flags.cf = false := by
  decide

theorem add_one_would_carry_there :
    (step ⟨.bin .add .b (.reg .rax) (.imm 1), 3⟩ (mk { rax := 0xFF } { cf := false })).flags.cf
      = true := by decide

/-- NEG: CF is set exactly when the operand was non-zero. -/
theorem neg_cf_nonzero :
    (step ⟨.un .neg .q (.reg .rax), 3⟩ (mk { rax := 1 })).flags.cf = true := by decide

theorem neg_cf_zero :
    (step ⟨.un .neg .q (.reg .rax), 3⟩ (mk { rax := 0 })).flags.cf = false := by decide

theorem neg_result :
    (step ⟨.un .neg .b (.reg .rax), 2⟩ (mk { rax := 0x01 })).regs.rax = 0xFF := by decide

/-- NOT touches no flag at all. -/
theorem not_flags_untouched :
    (step ⟨.un .not .q (.reg .rax), 3⟩
      (mk { rax := 0 } { cf := true, zf := true, of := true })).flags
      = { cf := true, zf := true, of := true } := by decide

theorem not_result :
    (step ⟨.un .not .b (.reg .rax), 2⟩ (mk { rax := 0x0F })).regs.rax = 0xF0 := by decide

/-! ## SHL / SHR — SDM Vol. 2A

The count is masked to 5 bits (6 at 64-bit operand size), and a MASKED count of
zero affects no flag even when the written count was not zero. -/

/-- `shl rax, 64` masks to a count of 0: RAX is unchanged and the flags are
untouched.  A model that shifted by 64 would produce 0. -/
theorem shl_q_count_64_is_noop :
    (step ⟨.shift .shl .q (.reg .rax) (.imm8 64), 4⟩
      (mk { rax := 0xDEADBEEF } { cf := true })).regs.rax = 0xDEADBEEF := by decide

theorem shl_q_count_64_leaves_flags :
    (step ⟨.shift .shl .q (.reg .rax) (.imm8 64), 4⟩
      (mk { rax := 0xDEADBEEF } { cf := true })).flags.cf = true := by decide

/-- At 32-bit operand size the mask is 5 bits, so a count of 32 is also a
no-op — and a count of 64 masks to 0 as well, but for a DIFFERENT reason. -/
theorem shl_d_count_32_is_noop :
    (step ⟨.shift .shl .d (.reg .rax) (.imm8 32), 4⟩ (mk { rax := 0x1 })).regs.rax = 0x1 := by
  decide

/-- CF is the last bit shifted OUT of the top. -/
theorem shl_b_cf_from_top :
    (step ⟨.shift .shl .b (.reg .rax) (.imm8 1), 3⟩ (mk { rax := 0x80 })).flags.cf = true := by
  decide

theorem shl_b_cf_clear :
    (step ⟨.shift .shl .b (.reg .rax) (.imm8 1), 3⟩ (mk { rax := 0x40 })).flags.cf = false := by
  decide

/-- OF on a 1-bit SHL is `MSB(result) XOR CF`. -/
theorem shl_b_of_one_bit :
    (step ⟨.shift .shl .b (.reg .rax) (.imm8 1), 3⟩ (mk { rax := 0x40 })).flags.of = true := by
  decide

/-- SHR shifts in zeros and CF is the last bit shifted out of the BOTTOM. -/
theorem shr_b_result :
    (step ⟨.shift .shr .b (.reg .rax) (.imm8 1), 3⟩ (mk { rax := 0x81 })).regs.rax = 0x40 := by
  decide

theorem shr_b_cf :
    (step ⟨.shift .shr .b (.reg .rax) (.imm8 1), 3⟩ (mk { rax := 0x81 })).flags.cf = true := by
  decide

/-- OF on a 1-bit SHR is the MSB of the ORIGINAL operand. -/
theorem shr_b_of_one_bit :
    (step ⟨.shift .shr .b (.reg .rax) (.imm8 1), 3⟩ (mk { rax := 0x81 })).flags.of = true := by
  decide

/-- The shift count in CL is the LOW BYTE of RCX, and it is masked like any
other count. -/
theorem shl_cl_uses_low_byte :
    (step ⟨.shift .shl .q (.reg .rax) .cl, 3⟩
      (mk { rax := 1, rcx := 0xFFFFFFFFFFFFFF04 })).regs.rax = 0x10 := by decide

/-! ## LEA — no memory is read, and the width rule still applies -/

theorem lea_computes_address :
    (step ⟨.lea .q .rax { base := some .rbx, index := some .rcx, scale := .s4, disp := 8 }, 5⟩
      (mk { rbx := 0x1000, rcx := 0x10 })).regs.rax = 0x1048 := by decide

/-- `lea eax, [...]` zero-extends, exactly as any other 32-bit write does. -/
theorem lea_d_zero_extends :
    (step ⟨.lea .d .rax { base := some .rbx, disp := 8 }, 4⟩
      (mk { rax := 0xFFFFFFFFFFFFFFFF, rbx := 0x1000 })).regs.rax = 0x1008 := by decide

/-- RIP-relative addressing is against the address of the NEXT instruction. -/
theorem lea_rip_relative :
    (step ⟨.lea .q .rax { ripRel := true, disp := 0x10 }, 7⟩ (mk (rip := 0x1000))).regs.rax
      = 0x1017 := by decide

/-! ## Memory: little-endian, and the round trip -/

theorem mem_little_endian_store :
    ((step ⟨.mov .d (.mem { base := some .rbx }) (.reg .rax), 3⟩
        (mk { rax := 0x11223344, rbx := 0x2000 })).mem.read 0x2000) = 0x44 := by decide

theorem mem_little_endian_store_high :
    ((step ⟨.mov .d (.mem { base := some .rbx }) (.reg .rax), 3⟩
        (mk { rax := 0x11223344, rbx := 0x2000 })).mem.read 0x2003) = 0x11 := by decide

theorem mem_round_trip :
    ((step ⟨.mov .q (.reg .rcx) (.mem { base := some .rbx }), 3⟩
       (step ⟨.mov .q (.mem { base := some .rbx }) (.reg .rax), 3⟩
         (mk { rax := 0x0123456789ABCDEF, rbx := 0x2000 }))).regs.rcx)
      = 0x0123456789ABCDEF := by decide

/-! ## PUSH / POP -/

theorem push_decrements_rsp :
    (step ⟨.push .q (.reg .rax), 1⟩ (mk { rax := 0x42, rsp := 0x8000 })).regs.rsp = 0x7FF8 := by
  decide

/-- `push rsp` pushes the OLD RSP (SDM Vol. 2A, PUSH). -/
theorem push_rsp_pushes_old_value :
    ((step ⟨.push .q (.reg .rsp), 1⟩ (mk { rsp := 0x8000 })).mem.readSize .q 0x7FF8)
      = 0x8000 := by decide

theorem push_pop_round_trip :
    ((step ⟨.pop .q (.reg .rcx), 1⟩
       (step ⟨.push .q (.reg .rax), 1⟩ (mk { rax := 0xCAFEBABE, rsp := 0x8000 }))).regs.rcx)
      = 0xCAFEBABE := by decide

theorem push_pop_restores_rsp :
    ((step ⟨.pop .q (.reg .rcx), 1⟩
       (step ⟨.push .q (.reg .rax), 1⟩ (mk { rax := 0xCAFEBABE, rsp := 0x8000 }))).regs.rsp)
      = 0x8000 := by decide

/-- ⭐ `pop rsp` ends with the LOADED value, not with the incremented pointer. -/
theorem pop_rsp_loads :
    ((step ⟨.pop .q (.reg .rsp), 1⟩
       (step ⟨.push .q (.reg .rax), 1⟩ (mk { rax := 0xDEAD0000, rsp := 0x8000 }))).regs.rsp)
      = 0xDEAD0000 := by decide

/-! ## Control flow -/

theorem jmp_rel_is_from_next_instruction :
    (step ⟨.jmp (.rel 0x10), 5⟩ (mk (rip := 0x1000))).rip = 0x1015 := by decide

theorem jmp_indirect :
    (step ⟨.jmp (.indirect (.reg .rax)), 2⟩ (mk { rax := 0x4000 } (rip := 0x1000))).rip
      = 0x4000 := by decide

theorem jcc_taken :
    (step ⟨.jcc .e 0x10, 6⟩ (mk {} { zf := true } (rip := 0x1000))).rip = 0x1016 := by decide

theorem jcc_not_taken :
    (step ⟨.jcc .e 0x10, 6⟩ (mk {} { zf := false } (rip := 0x1000))).rip = 0x1006 := by decide

/-- All sixteen condition codes against a single flag setting, as one table.
CF=1, ZF=1, SF=0, OF=1, PF=0. -/
theorem cc_table :
    (Cc.all.map (fun c => c.eval { cf := true, zf := true, sf := false, of := true, pf := false }))
      = [ true,  false,   -- o  no
          true,  false,   -- b  ae
          true,  false,   -- e  ne
          true,  false,   -- be a
          false, true,    -- s  ns
          false, true,    -- p  np
          true,  false,   -- l  ge   (SF ≠ OF)
          true,  false ]  -- le g
      := by decide

theorem call_pushes_return_address :
    ((step ⟨.call (.rel 0x100), 5⟩ (mk { rsp := 0x8000 } (rip := 0x1000))).mem.readSize .q 0x7FF8)
      = 0x1005 := by decide

theorem call_jumps :
    (step ⟨.call (.rel 0x100), 5⟩ (mk { rsp := 0x8000 } (rip := 0x1000))).rip = 0x1105 := by decide

/-! ## Canonical addresses — SDM Vol. 1 §3.3.7.1, Vol. 2A JMP/CALL

⭐ THESE ANCHORS EXIST BECAUSE THE DIFFERENTIAL RUN FOUND THE GAP THEY PIN.
Before it, this model set RIP to whatever an indirect branch named, and every
theorem about that was true — of a wrong model.  ACL2 x86isa disagreed on 80
cases, all of them non-canonical branch targets. -/

/-- The canonicality boundary itself: `0x00007FFF_FFFFFFFF` is the largest
canonical low address and `0x00008000_00000000` is the first non-canonical one. -/
theorem canonical_boundary_low :
    canonical 0x00007FFFFFFFFFFF = true := by decide

theorem noncanonical_just_above :
    canonical 0x0000800000000000 = false := by decide

/-- And the high half: `0xFFFF8000_00000000` is canonical again (bit 47 set,
sign-extended), while `0xFFFF7FFF_FFFFFFFF` is not. -/
theorem canonical_boundary_high :
    canonical 0xFFFF800000000000 = true := by decide

theorem noncanonical_just_below :
    canonical 0xFFFF7FFFFFFFFFFF = false := by decide

/-- A branch to a non-canonical target HALTS this model instead of landing. -/
theorem jmp_noncanonical_halts :
    (step ⟨.jmp (.indirect (.reg .rax)), 2⟩
      (mk { rax := 0x5555555555555555 } (rip := 0x400000))).ms
      = some (.unimplemented "non-canonical branch target (#GP(0) in hardware)") := by decide

/-- ...and does not move RIP. -/
theorem jmp_noncanonical_does_not_land :
    (step ⟨.jmp (.indirect (.reg .rax)), 2⟩
      (mk { rax := 0x5555555555555555 } (rip := 0x400000))).rip = 0x400000 := by decide

/-- ⭐ A REFUSED CALL DOES NOT PUSH.  RSP is untouched — the check precedes the
push, which is the ordering the differential run made observable by disagreeing
on `rsp` and the stack window as well as on `rip`. -/
theorem call_noncanonical_does_not_push :
    (step ⟨.call (.indirect (.reg .rax)), 2⟩
      (mk { rax := 0x5555555555555555, rsp := 0x8000 } (rip := 0x400000))).regs.rsp
      = 0x8000 := by decide

/-- A canonical indirect call still works, so the check did not break the form. -/
theorem call_canonical_still_pushes :
    (step ⟨.call (.indirect (.reg .rax)), 2⟩
      (mk { rax := 0x401000, rsp := 0x8000 } (rip := 0x400000))).regs.rsp = 0x7FF8 := by decide

/-! ## Totality: a form no encoding can express STOPS the model -/

theorem two_memory_operands_halt :
    (step ⟨.mov .q (.mem { base := some .rax }) (.mem { base := some .rbx }), 3⟩ (mk {})).ms
      = some (.illegalOperands "mov: two memory operands") := by decide

theorem stopped_model_does_not_move :
    (step ⟨.mov .q (.reg .rax) (.imm 5), 3⟩
      { (mk { rax := 1 }) with ms := some (.unimplemented "x") }).regs.rax = 1 := by decide

/-! ## P1 BATCH 3 — CMP and TEST: the forms whose destination is the FLAGS

The template is P0's and nothing here is new semantics.  What is new is the
OPERAND SHAPE: a memory operand in the destination position, read and never
written.  Every earlier memory destination in this repository was written, so
"the destination is not written" had never been an anchored claim about a
memory operand at all — only about a register.

Each anchor below is written so that the WRONG model gives a DIFFERENT answer.
An anchor whose planted error produces the same number is a row in the coverage
table with nothing behind it (see the deleted ninth anchor above). -/

/-- ⭐ CMP WITH A MEMORY DESTINATION WRITES NO MEMORY.  `cmpq %rax, (%rbx)` with
`(%rbx) = 0x11` and `rax = 1` computes `0x10`; a model that wrote its result
back would leave `0x10` at the address.  It reads `0x11`. -/
theorem cmp_mem_dest_writes_no_memory :
    (step ⟨.bin .cmp .q (.mem { base := some .rbx }) (.reg .rax), 3⟩
      (mk { rax := 1, rbx := 0x100 } {} (Mem.empty.write 0x100 0x11))).mem.read 0x100
      = 0x11 := by decide

/-- And the same for TEST, whose result `0xFF &&& 0x0F = 0x0F` also differs from
the value in memory, so the anchor can tell a write-back from a no-op. -/
theorem test_mem_dest_writes_no_memory :
    (step ⟨.bin .test .q (.mem { base := some .rbx }) (.reg .rax), 3⟩
      (mk { rax := 0x0F, rbx := 0x100 } {} (Mem.empty.write 0x100 0xFF))).mem.read 0x100
      = 0xFF := by decide

/-- ⭐ THE DIRECTION IS OBSERVABLE.  `cmpq %rax, (%rbx)` is `(%rbx) − %rax`, not
the other way round: `0x10 − 0x20` borrows, so CF is set.  Under the flipped
reading `0x20 − 0x10` it would be clear, which is what makes this an anchor
rather than a restatement. -/
theorem cmp_mem_dest_direction :
    (step ⟨.bin .cmp .q (.mem { base := some .rbx }) (.reg .rax), 3⟩
      (mk { rax := 0x20, rbx := 0x100 } {} (Mem.empty.write 0x100 0x10))).flags.cf
      = true := by decide

/-- The register-destination direction, for contrast: `cmpq (%rbx), %rax` is
`%rax − (%rbx)`, and with the same two numbers in the same places CF is CLEAR.
The pair is the claim; either theorem alone is satisfied by a coin. -/
theorem cmp_reg_dest_direction :
    (step ⟨.bin .cmp .q (.reg .rax) (.mem { base := some .rbx }), 3⟩
      (mk { rax := 0x20, rbx := 0x100 } {} (Mem.empty.write 0x100 0x10))).flags.cf
      = false := by decide

/-- ⭐ A 32-BIT CMP WRITES NO REGISTER, and at width `d` that is a sharp claim
rather than a soft one: a 32-bit write ZERO-EXTENDS (SDM Vol. 1 §3.4.1.1), so a
`cmpl` that wrote its result back would not merely change the low half, it would
erase the upper one.  RAX comes out untouched. -/
theorem cmpl_writes_no_register :
    (step ⟨.bin .cmp .d (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0xDEADBEEF_12345678, rcx := 1 })).regs.rax
      = 0xDEADBEEF_12345678 := by decide

theorem testl_writes_no_register :
    (step ⟨.bin .test .d (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0xDEADBEEF_12345678, rcx := 0xFF })).regs.rax
      = 0xDEADBEEF_12345678 := by decide

/-- TEST at a memory destination with an immediate still sets ZF from the AND:
`0xF0 &&& 0x0F = 0`. -/
theorem test_mem_imm_sets_zf :
    (step ⟨.bin .test .b (.mem { base := some .rbx }) (.imm 0x0F), 3⟩
      (mk { rbx := 0x100 } {} (Mem.empty.write 0x100 0xF0))).flags.zf = true := by decide

/-- A HIGH-8 DESTINATION IS READ FROM BITS 15:8.  `testb %cl, %ah` with
`RAX = 0xFF00` and `CL = 1` ands `0xFF` with `1` and leaves ZF CLEAR; a model
reading AL (which is `0x00`) would set it. -/
theorem test_high8_dest_reads_bits_15_8 :
    (step ⟨.bin .test .b (.reg .rax true) (.reg .rcx), 2⟩
      (mk { rax := 0xFF00, rcx := 1 })).flags.zf = false := by decide

/-! ### RIP-relative addressing, which no differential vector had ever executed

`Ea.addr` has implemented `ripRel` since P0 and the only evidence for it was one
`lea` anchor — this model checked against itself.  P1 batch 3 gives it a vector
(`cmp_rip_q`), and these two anchors pin the one thing that vector could not say
on its own: WHICH address it is.

The address is `nextRip + disp`, i.e. RIP AFTER the instruction (SDM Vol. 2A
§2.2.1.6).  The off-by-`len` version of this bug is the classic one, so both
candidate addresses are populated and they hold DIFFERENT bytes: `0x1010` is
`rip + disp` (wrong) and holds `0xAA`; `0x101B` is `rip + 11 + disp` (right) and
holds `0x55`. -/

private def ripDecoy : Mem := (Mem.empty.write 0x1010 0xAA).write 0x101B 0x55

/-- Comparing against `0x55` gives ZF: the byte read was the one at
`nextRip + disp`. -/
theorem rip_relative_reads_after_the_instruction :
    (step ⟨.bin .cmp .b (.mem { ripRel := true, disp := 0x10 }) (.imm 0x55), 11⟩
      (mk {} {} ripDecoy (rip := 0x1000))).flags.zf = true := by decide

/-- And comparing against `0xAA` — the byte sitting at the WRONG address, the
one an off-by-`len` model would have read — does not. -/
theorem rip_relative_does_not_read_at_rip :
    (step ⟨.bin .cmp .b (.mem { ripRel := true, disp := 0x10 }) (.imm 0xAA), 11⟩
      (mk {} {} ripDecoy (rip := 0x1000))).flags.zf = false := by decide

/-! ## P1 BATCH 4 — the READ-MODIFY-WRITE to a memory destination

Batch 3 put a memory operand in a destination that is read and never written.
These forms read it, compute, WRITE IT BACK and set flags — and until batch 4
the only memory this repository ever wrote was `mov`, `push` and `call`, none of
which touch a flag and none of which read the location first.

The width of the store is the whole risk, so most of these anchors are about a
NEIGHBOUR rather than about the value. -/

private def win : Mem :=
  (List.range 16).foldl (fun m i => m.write (0x100 + BitVec.ofNat 64 i)
    (BitVec.ofNat 8 (0xA0 + i))) Mem.empty

/-- `andb %al, (%rbx)` writes exactly ONE byte: `0xA0 &&& 0x0F = 0x00`. -/
theorem and_mem_b_writes_the_byte :
    (step ⟨.bin .and .b (.mem { base := some .rbx }) (.reg .rax), 2⟩
      (mk { rax := 0x0F, rbx := 0x100 } {} win)).mem.read 0x100 = 0x00 := by decide

/-- ⭐ AND IT TOUCHES NO NEIGHBOUR.  The byte above keeps its pattern.  This is
the anchor for the bug the harness plants as batch 4's hard half — a store that
ignores its operand width — and it is a claim no register-destination form can
make, because a register write has no neighbours. -/
theorem and_mem_b_leaves_the_neighbour :
    (step ⟨.bin .and .b (.mem { base := some .rbx }) (.reg .rax), 2⟩
      (mk { rax := 0x0F, rbx := 0x100 } {} win)).mem.read 0x101 = 0xA1 := by decide

/-- ⭐ THE ASYMMETRY THAT MATTERS MOST HERE.  A 32-BIT WRITE TO A REGISTER
ZERO-EXTENDS into the upper half (SDM Vol. 1 §3.4.1.1); a 32-bit write to MEMORY
touches FOUR BYTES and the four above it are none of its business.  A model that
carried the register rule across to the memory path would zero `0x104`.  It
holds `0xA4`. -/
theorem and_mem_l_does_not_zero_extend_into_memory :
    (step ⟨.bin .and .d (.mem { base := some .rbx }) (.reg .rax), 2⟩
      (mk { rax := 0xFFFFFFFF, rbx := 0x100 } {} win)).mem.read 0x104 = 0xA4 := by decide

/-- And the contrast, at a register destination, where the zero-extension is
required: `andl` with an all-ones mask leaves the low half and ERASES the
upper. -/
theorem andl_reg_does_zero_extend :
    (step ⟨.bin .and .d (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0xDEADBEEF_12345678, rcx := 0xFFFFFFFF })).regs.rax
      = 0x12345678 := by decide

/-- `andq` at a memory destination writes all EIGHT bytes: the byte at `0x107`
is inside the operand and is cleared. -/
theorem and_mem_q_writes_eight_bytes :
    (step ⟨.bin .and .q (.mem { base := some .rbx }) (.reg .rax), 3⟩
      (mk { rax := 0, rbx := 0x100 } {} win)).mem.read 0x107 = 0x00 := by decide

/-- The flags come from the memory value, at a memory destination as anywhere
else: AND clears CF and OF (SDM Vol. 2A, AND). -/
theorem and_mem_clears_cf_of :
    let r := step ⟨.bin .and .b (.mem { base := some .rbx }) (.reg .rax), 2⟩
      (mk { rax := 0x0F, rbx := 0x100 }
         { cf := true, of := true } win)
    (r.flags.cf, r.flags.of) = (false, false) := by decide

/-- ⭐ INC AT A MEMORY DESTINATION STILL DOES NOT TOUCH CF (SDM Vol. 2A, INC:
"The CF flag is not affected").  That rule was anchored at a register in P0; the
memory path is a different line of `step` and gets its own. -/
theorem inc_mem_preserves_cf :
    (step ⟨.un .inc .q (.mem { base := some .rbx }), 3⟩
      (mk { rbx := 0x100 } { cf := true } win)).flags.cf = true := by decide

/-- `incb (%rbx)` on `0xFF` wraps to zero and sets ZF — and still leaves the
neighbour alone, which is the width claim again on the unary path. -/
theorem inc_mem_b_wraps_and_keeps_the_neighbour :
    let r := step ⟨.un .inc .b (.mem { base := some .rbx }), 2⟩
      (mk { rbx := 0x100 } {} (win.write 0x100 0xFF))
    (r.mem.read 0x100, r.flags.zf, r.mem.read 0x101) = (0x00, true, 0xA1) := by decide

/-- `decq (%rbx)` reads the location, subtracts one, and stores it back — the
read-modify-write in one statement. -/
theorem dec_mem_reads_then_writes :
    (step ⟨.un .dec .q (.mem { base := some .rbx }), 3⟩
      (mk { rbx := 0x100 } {} (Mem.empty.write 0x100 0x10))).mem.read 0x100
      = 0x0F := by decide

/-! ## P1 BATCH 5 — the branches, and the one whose condition is a REGISTER

Thirty of family 7's branch mnemonics are spellings of the sixteen predicates in
`Cc`, and those are anchored by P0 and by `vectors_cover_every_condition`.  What
is new is `JRCXZ`/`JECXZ`, and everything sharp about it is the WIDTH of the
register it reads. -/

/-- `jrcxz` branches when RCX is zero. -/
theorem jrcxz_branches_on_zero :
    (step ⟨.jcxz false 0x10, 2⟩ (mk { rcx := 0 } (rip := 0x400000))).rip
      = 0x400012 := by decide

/-- and falls through when it is not. -/
theorem jrcxz_falls_through_on_nonzero :
    (step ⟨.jcxz false 0x10, 2⟩ (mk { rcx := 1 } (rip := 0x400000))).rip
      = 0x400002 := by decide

/-- ⭐ THE PAIR THE ADDRESS-SIZE PREFIX EXISTS FOR, and the only place the two
mnemonics disagree.  With `RCX = 0x1_00000000` the low 32 bits are zero and the
whole register is not: `jrcxz` FALLS THROUGH and `jecxz` BRANCHES.

A model that read one width for both — the obvious way to write this
instruction once — is correct everywhere except here.  It is this batch's
planted hard half.  `pre_states_separate_rcx_from_ecx` is what keeps a pre-state
on this point — and it is not a formality: removing the two `adversarial`
constants that reach it makes the differential arm catch nothing AND makes that
theorem fail, which is the gate doing its job before the loss instead of after. -/
theorem jrcxz_reads_all_64_bits :
    (step ⟨.jcxz false 0x10, 2⟩
      (mk { rcx := 0x1_00000000 } (rip := 0x400000))).rip = 0x400002 := by decide

theorem jecxz_reads_only_the_low_32 :
    (step ⟨.jcxz true 0x0F, 3⟩
      (mk { rcx := 0x1_00000000 } (rip := 0x400000))).rip = 0x400012 := by decide

/-- Neither writes a flag (SDM Vol. 2A, JCC: "Flags Affected: None"). -/
theorem jcxz_writes_no_flag :
    let f : Flags := { cf := true, zf := true }
    (step ⟨.jcxz false 0x10, 2⟩ (mk { rcx := 0 } f (rip := 0x400000))).flags = f := by decide

/-- And it takes the canonical-target check like every other branch: a
displacement that lands outside canonical space HALTS rather than jumping. -/
theorem jcxz_noncanonical_target_refuses :
    (step ⟨.jcxz false 0x0000_8000_0000_0000, 2⟩
      (mk { rcx := 0 } (rip := 0x400000))).ms
      = some (.unimplemented "non-canonical branch target (#GP(0) in hardware)") := by decide

/-- ⭐ THE rel32 ENCODING'S LENGTH IS PART OF THE ANSWER.  A `jcc` at rel32 is
SIX bytes, and the target is `rip + 6 + d`, not `rip + 2 + d`: the same
displacement under the rel8 length would land four bytes short.  P0 had only
rel8 vectors, so nothing had yet distinguished the two. -/
theorem jcc_rel32_target_uses_its_own_length :
    (step ⟨.jcc .e 0xC2, 6⟩ (mk {} { zf := true } (rip := 0x400000))).rip
      = 0x4000C8 := by decide

theorem jcc_rel8_target_uses_its_own_length :
    (step ⟨.jcc .e 0x10, 2⟩ (mk {} { zf := true } (rip := 0x400000))).rip
      = 0x400012 := by decide

/-- The two compound conditions, which are where a Jcc table goes wrong: `jle`
is `ZF || SF ≠ OF`, so it is taken on SF ≠ OF even with ZF clear... -/
theorem jle_taken_on_sign_overflow_mismatch :
    (step ⟨.jcc .le 0x10, 2⟩
      (mk {} { sf := true, of := false } (rip := 0x400000))).rip = 0x400012 := by decide

/-- ...and `jg` is its exact negation on the same state. -/
theorem jg_not_taken_there :
    (step ⟨.jcc .g 0x10, 2⟩
      (mk {} { sf := true, of := false } (rip := 0x400000))).rip = 0x400002 := by decide

/-! ## P1 BATCH 6 — SETcc and CMOVcc: the predicates, read through other opcodes

120 roster forms and two `step` cases.  What needs anchoring is not the
conditions — `Jcc` already established those and `Cc.eval` is shared — but the
two things these opcodes do that a branch does not: SETcc writes ONE BYTE, and
CMOVcc writes its destination whether or not the condition holds. -/

/-- SETcc writes 1 when the condition holds... -/
theorem setcc_writes_one :
    (step ⟨.setcc .e (.reg .rax), 3⟩
      (mk { rax := 0 } { zf := true })).regs.rax = 1 := by decide

/-- ...and 0 when it does not — not "leaves the destination alone". -/
theorem setcc_writes_zero_not_nothing :
    (step ⟨.setcc .e (.reg .rax), 3⟩
      (mk { rax := 0xFF } { zf := false })).regs.rax = 0 := by decide

/-- ⭐ AND IT WRITES EXACTLY ONE BYTE.  With RAX = `0xDEADBEEF_12345678`, `sete`
on a true condition leaves `0xDEADBEEF_12345601`: the upper 56 bits are
untouched, so this is an 8-bit write and NOT a 32-bit one that would
zero-extend. -/
theorem setcc_is_a_byte_write :
    (step ⟨.setcc .e (.reg .rax), 3⟩
      (mk { rax := 0xDEADBEEF_12345678 } { zf := true })).regs.rax
      = 0xDEADBEEF_12345601 := by decide

/-- A high-8 destination writes bits 15:8 and nothing else. -/
theorem setcc_high8 :
    (step ⟨.setcc .ne (.reg .rax true), 3⟩
      (mk { rax := 0xFFFF } { zf := true })).regs.rax = 0x00FF := by decide

/-- At a memory destination it is still one byte: the neighbour keeps its
pattern. -/
theorem setcc_mem_writes_one_byte :
    let r := step ⟨.setcc .e (.mem { base := some .rbx }), 3⟩
      (mk { rbx := 0x100 } { zf := true } ((Mem.empty.write 0x100 0xAA).write 0x101 0xBB))
    (r.mem.read 0x100, r.mem.read 0x101) = (0x01, 0xBB) := by decide

/-- CMOVcc moves when the condition holds. -/
theorem cmov_moves_when_taken :
    (step ⟨.cmov .e .q .rax (.reg .rcx), 4⟩
      (mk { rax := 1, rcx := 0x2222 } { zf := true })).regs.rax = 0x2222 := by decide

/-- ⭐ AND THE ONE THAT IS NOT OBVIOUS: AT WIDTH `d` THE DESTINATION IS WRITTEN
EVEN WHEN THE CONDITION IS FALSE, so the 32-bit zero-extension happens anyway
(SDM Vol. 1 §3.4.1.1).  `cmovel %ecx, %eax` with ZF CLEAR moves nothing and
still clears the upper half of RAX.

A model written as "if the condition holds, move" gives `0xDEADBEEF_12345678`
here.  This is the batch's planted hard half, and the reason every `cmov` vector
is at width `l`. -/
theorem cmov_not_taken_still_zero_extends_at_d :
    (step ⟨.cmov .e .d .rax (.reg .rcx), 3⟩
      (mk { rax := 0xDEADBEEF_12345678, rcx := 0x2222 } { zf := false })).regs.rax
      = 0x12345678 := by decide

/-- The contrast that gives it meaning: at width `q` a false condition really is
a no-op, and at width `w` the upper bits survive.  Without these two the theorem
above is satisfied by a model that zero-extends everything. -/
theorem cmov_not_taken_is_a_noop_at_q :
    (step ⟨.cmov .e .q .rax (.reg .rcx), 4⟩
      (mk { rax := 0xDEADBEEF_12345678, rcx := 0x2222 } { zf := false })).regs.rax
      = 0xDEADBEEF_12345678 := by decide

theorem cmov_not_taken_preserves_upper_at_w :
    (step ⟨.cmov .e .w .rax (.reg .rcx), 4⟩
      (mk { rax := 0xDEADBEEF_12345678, rcx := 0x2222 } { zf := false })).regs.rax
      = 0xDEADBEEF_12345678 := by decide

/-- And a TAKEN 32-bit cmov zero-extends the moved value, like every other
32-bit write. -/
theorem cmov_taken_zero_extends_at_d :
    (step ⟨.cmov .e .d .rax (.reg .rcx), 3⟩
      (mk { rax := 0xDEADBEEF_12345678, rcx := 0xFFFFFFFF_00002222 } { zf := true })).regs.rax
      = 0x2222 := by decide

/-- Neither instruction writes a flag (SDM Vol. 2A, SETcc and CMOVcc). -/
theorem setcc_and_cmov_write_no_flag :
    let f : Flags := { cf := true, zf := true, of := true }
    ((step ⟨.setcc .e (.reg .rax), 3⟩ (mk {} f)).flags = f
     ∧ (step ⟨.cmov .e .q .rax (.reg .rcx), 4⟩ (mk {} f)).flags = f) := by
  exact ⟨by decide, by decide⟩

/-! ## P1 BATCH 7 — SAR, and the flag rule the SDM writes differently for it -/

/-- SAR propagates the SIGN, where SHR brings in zeros.  `0x80` at width b,
shifted right by 1: `0xC0` arithmetic, `0x40` logical. -/
theorem sar_b_propagates_the_sign :
    (step ⟨.shift .sar .b (.reg .rax) (.imm8 1), 2⟩
      (mk { rax := 0x80 })).regs.rax = 0xC0 := by decide

theorem shr_b_brings_in_zero :
    (step ⟨.shift .shr .b (.reg .rax) (.imm8 1), 2⟩
      (mk { rax := 0x80 })).regs.rax = 0x40 := by decide

/-- ⭐ AND THE SIGN IT PROPAGATES IS THE SIGN AT THE OPERAND'S WIDTH, not at 64.
With RAX = `0x0000_0000_0000_0080`, `sarb` sees a NEGATIVE byte and fills with
ones inside the byte; the upper 56 bits are a byte-write's business and stay
zero.  A model that sign-extended from bit 63 would leave `0x40`. -/
theorem sar_b_sign_is_the_operand_width :
    (step ⟨.shift .sar .b (.reg .rax) (.imm8 1), 2⟩
      (mk { rax := 0x0000_0000_0000_0080 })).regs.rax = 0x00000000_000000C0 := by decide

/-- A positive operand behaves exactly like SHR. -/
theorem sar_positive_matches_shr :
    (step ⟨.shift .sar .q (.reg .rax) (.imm8 4), 4⟩ (mk { rax := 0x1000 })).regs.rax
      = (step ⟨.shift .shr .q (.reg .rax) (.imm8 4), 4⟩ (mk { rax := 0x1000 })).regs.rax
      := by decide

/-- ⭐ SAR's CF AT A COUNT ≥ THE OPERAND WIDTH IS THE SIGN, AND IS NOT DRAWN
FROM THE ORACLE.  `sarb $9` on a negative byte: the count masks to 9, which is
≥ 8, and every bit shifted out — including the last — is the sign.  CF is 1.

The oracle here is `Oracle.zero`, so a model that drew an oracle bit (as SHL and
SHR must at this count) would give 0.  That is the difference, and it is this
batch's planted hard half. -/
theorem sar_cf_at_large_count_is_the_sign :
    (step ⟨.shift .sar .b (.reg .rax) (.imm8 9), 3⟩ (mk { rax := 0x80 })).flags.cf
      = true := by decide

/-- And on a POSITIVE byte at the same count it is 0 — so the theorem above is
about the sign and not about a constant. -/
theorem sar_cf_at_large_count_positive :
    (step ⟨.shift .sar .b (.reg .rax) (.imm8 9), 3⟩ (mk { rax := 0x7F })).flags.cf
      = false := by decide

/-- The result at that count is all sign bits. -/
theorem sar_at_large_count_is_all_sign :
    (step ⟨.shift .sar .b (.reg .rax) (.imm8 9), 3⟩ (mk { rax := 0x80 })).regs.rax
      = 0xFF := by decide

/-- SDM: "the OF flag is cleared for SAR with a count of 1" — a CONSTANT, unlike
SHL's and SHR's, because an arithmetic right shift cannot change the sign. -/
theorem sar_of_is_cleared_at_count_one :
    (step ⟨.shift .sar .q (.reg .rax) (.imm8 1), 3⟩
      (mk { rax := 0x8000000000000000 } { of := true })).flags.of = false := by decide

/-- A shift at a MEMORY destination is a read-modify-write like batch 4's, and
still touches only its own width: `sarb $1` on `0x80` at `0x100` writes `0xC0`
and leaves the neighbour. -/
theorem sar_mem_is_a_byte_rmw :
    let r := step ⟨.shift .sar .b (.mem { base := some .rbx }) (.imm8 1), 2⟩
      (mk { rbx := 0x100 } {} ((Mem.empty.write 0x100 0x80).write 0x101 0xBB))
    (r.mem.read 0x100, r.mem.read 0x101) = (0xC0, 0xBB) := by decide

/-! ## P1 BATCH 8 — the rotates, where the count is reduced twice

Everything sharp here is the difference between the MASKED count and the
REDUCED one, and the difference between rotating a `w`-bit value and a
`w+1`-bit one. -/

theorem rol_b_one : (step ⟨.rot .rol .b (.reg .rax) (.imm8 1), 2⟩
      (mk { rax := 0x80 })).regs.rax = 0x01 := by decide

theorem rol_b_one_cf : (step ⟨.rot .rol .b (.reg .rax) (.imm8 1), 2⟩
      (mk { rax := 0x80 })).flags.cf = true := by decide

theorem ror_b_one : (step ⟨.rot .ror .b (.reg .rax) (.imm8 1), 2⟩
      (mk { rax := 0x01 })).regs.rax = 0x80 := by decide

/-- ⭐ RCL ROTATES A NINE-BIT RING AT WIDTH b.  `0x80` with CF clear: the top bit
goes INTO CF and a zero comes out of it, so the byte becomes `0x00` and CF is 1
— a plain `rol` would have produced `0x01`. -/
theorem rcl_b_one_takes_the_top_bit_into_cf :
    let r := step ⟨.rot .rcl .b (.reg .rax) (.imm8 1), 2⟩ (mk { rax := 0x80 })
    (r.regs.rax, r.flags.cf) = (0x00, true) := by decide

/-- ...and the carry comes back out at the bottom on the next rotate. -/
theorem rcl_b_one_brings_cf_in_at_the_bottom :
    let r := step ⟨.rot .rcl .b (.reg .rax) (.imm8 1), 2⟩
      (mk { rax := 0x00 } { cf := true })
    (r.regs.rax, r.flags.cf) = (0x01, false) := by decide

theorem rcr_b_one_takes_the_bottom_bit_into_cf :
    let r := step ⟨.rot .rcr .b (.reg .rax) (.imm8 1), 2⟩ (mk { rax := 0x01 })
    (r.regs.rax, r.flags.cf) = (0x00, true) := by decide

theorem rcr_b_one_brings_cf_in_at_the_top :
    let r := step ⟨.rot .rcr .b (.reg .rax) (.imm8 1), 2⟩
      (mk { rax := 0x00 } { cf := true })
    (r.regs.rax, r.flags.cf) = (0x80, false) := by decide

/-- ⭐ THE QUIRK, AND THIS BATCH'S PLANTED HARD HALF.  `rolb $8` has a masked
count of 8 and a reduced count of 0: the DATA DOES NOT MOVE, and CF IS STILL
WRITTEN, because the SDM's rule is "IF COUNT ≠ 0 THEN CF ← LSB(DEST)" and COUNT
there is the MASKED count.  `0x81` stays `0x81` and CF becomes 1. -/
theorem rol_b8_moves_nothing_but_writes_cf :
    let r := step ⟨.rot .rol .b (.reg .rax) (.imm8 8), 3⟩
      (mk { rax := 0x81 } { cf := false })
    (r.regs.rax, r.flags.cf) = (0x81, true) := by decide

/-- ⭐ AND ITS OPPOSITE ONE OPCODE AWAY.  `rclb $9` reduces modulo NINE, not
eight, so its reduced count is also 0 — but `rcl`'s CF rule is the rotate loop
itself, and a loop that does not execute writes nothing.  Data unchanged AND CF
unchanged.  Same count, same width, opposite answer. -/
theorem rcl_b9_moves_nothing_and_leaves_cf :
    let r := step ⟨.rot .rcl .b (.reg .rax) (.imm8 9), 3⟩
      (mk { rax := 0x81 } { cf := false })
    (r.regs.rax, r.flags.cf) = (0x81, false) := by decide

/-- ⭐ RCR's OF IS COMPUTED BEFORE THE ROTATE.  `rcrb $1` on `0x80` with CF
clear: OF is `MSB(original) XOR CF-in` = 1.  Computed AFTER, as RCL's is, it
would be `MSB(0x40) XOR 0` = 0.  The SDM writes the same sentence above RCR's
loop and below RCL's. -/
theorem rcr_of_is_computed_before_the_rotate :
    (step ⟨.rot .rcr .b (.reg .rax) (.imm8 1), 2⟩
      (mk { rax := 0x80 })).flags.of = true := by decide

/-- ⚠️ A ROTATE TOUCHES ONLY CF AND OF.  SF, ZF, PF and AF come out exactly as
they went in — the sharpest difference from the shifts, which recompute all
four from the result. -/
theorem rotate_leaves_the_arithmetic_flags :
    let f : Flags := { sf := true, zf := true, pf := true, af := true }
    let r := step ⟨.rot .rol .q (.reg .rax) (.imm8 5), 4⟩ (mk { rax := 0x1234 } f)
    (r.flags.sf, r.flags.zf, r.flags.pf, r.flags.af) = (true, true, true, true) := by decide

/-- A rotate at a memory destination is a read-modify-write of its own width. -/
theorem rol_mem_is_a_byte_rmw :
    let r := step ⟨.rot .rol .b (.mem { base := some .rbx }) (.imm8 1), 2⟩
      (mk { rbx := 0x100 } {} ((Mem.empty.write 0x100 0x80).write 0x101 0xBB))
    (r.mem.read 0x100, r.mem.read 0x101) = (0x01, 0xBB) := by decide

/-! ## P1 BATCH 9 — the bit-test group

The test is identical in all four; what differs is what happens afterwards.  So
the anchors are about the AFTERWARDS, and about the one flag that survives. -/

/-- CF takes the selected bit: bit 5 of `0x20` is 1. -/
theorem bt_cf_takes_the_bit :
    (step ⟨.bit .bt .q (.reg .rax) (.imm 5), 5⟩ (mk { rax := 0x20 })).flags.cf
      = true := by decide

theorem bt_cf_clear_when_bit_clear :
    (step ⟨.bit .bt .q (.reg .rax) (.imm 5), 5⟩ (mk { rax := 0x00 })).flags.cf
      = false := by decide

/-- ⭐ `bt` WRITES NOTHING — it is to this group what `cmp` is to the ALU.  With
bit 5 clear, a `bts` would leave `0x20`; `bt` leaves `0x00`. -/
theorem bt_writes_no_register :
    (step ⟨.bit .bt .q (.reg .rax) (.imm 5), 5⟩ (mk { rax := 0x00 })).regs.rax
      = 0x00 := by decide

theorem bts_sets_the_bit :
    (step ⟨.bit .bts .q (.reg .rax) (.imm 5), 5⟩ (mk { rax := 0x00 })).regs.rax
      = 0x20 := by decide

theorem btr_clears_the_bit :
    (step ⟨.bit .btr .q (.reg .rax) (.imm 5), 5⟩ (mk { rax := 0xFF })).regs.rax
      = 0xDF := by decide

theorem btc_complements_the_bit :
    (step ⟨.bit .btc .q (.reg .rax) (.imm 5), 5⟩ (mk { rax := 0xFF })).regs.rax
      = 0xDF := by decide

theorem btc_complements_back :
    (step ⟨.bit .btc .q (.reg .rax) (.imm 5), 5⟩ (mk { rax := 0xDF })).regs.rax
      = 0xFF := by decide

/-- ⭐ AND ALL FOUR REPORT THE OLD BIT, NOT THE NEW ONE.  `bts` on a clear bit
sets it AND leaves CF at 0 — the test happens before the write.  A model that
read CF back out of the result would say 1. -/
theorem bts_reports_the_bit_before_setting_it :
    (step ⟨.bit .bts .q (.reg .rax) (.imm 5), 5⟩ (mk { rax := 0x00 })).flags.cf
      = false := by decide

/-- ⚠️ THE OFFSET IS TAKEN MODULO THE OPERAND WIDTH at a register destination:
bit 64 of a 64-bit operand is bit 0. -/
theorem bit_offset_wraps_modulo_width :
    (step ⟨.bit .bt .q (.reg .rax) (.reg .rcx), 4⟩
      (mk { rax := 0x01, rcx := 64 })).flags.cf = true := by decide

/-- And at width w it wraps at 16, not at 64 — the modulus is the OPERAND's
width, not the register's. -/
theorem bit_offset_wraps_at_the_operand_width :
    (step ⟨.bit .bt .w (.reg .rax) (.reg .rcx), 4⟩
      (mk { rax := 0x01, rcx := 16 })).flags.cf = true := by decide

/-- ⭐ ZF IS THE ONLY ARITHMETIC FLAG THAT SURVIVES (SDM Vol. 2A: "the ZF flag is
unaffected").  `btr` clearing the last set bit produces a ZERO destination and
ZF stays exactly as it was — here, false.  Every other read-modify-write in this
model would set it. -/
theorem bit_ops_leave_zf_alone :
    (step ⟨.bit .btr .q (.reg .rax) (.imm 5), 5⟩
      (mk { rax := 0x20 } { zf := false })).flags.zf = false := by decide

/-- ...and a set ZF survives just as well, so the theorem above is about
PRESERVATION and not about a constant. -/
theorem bit_ops_preserve_a_set_zf :
    (step ⟨.bit .btr .q (.reg .rax) (.imm 5), 5⟩
      (mk { rax := 0x20 } { zf := true })).flags.zf = true := by decide

/-- At a memory destination `bts` is a read-modify-write of its own width and
leaves the neighbouring byte alone. -/
theorem bts_mem_is_a_width_bounded_rmw :
    let r := step ⟨.bit .bts .w (.mem { base := some .rbx }) (.imm 5), 5⟩
      (mk { rbx := 0x100 } {} ((Mem.empty.write 0x100 0x00).write 0x102 0xBB))
    (r.mem.read 0x100, r.mem.read 0x102) = (0x20, 0xBB) := by decide

/-! ## P1 BATCH 10 — the width-changing and two-destination moves

Not one of these instructions writes a flag, so every anchor below is about a
VALUE.  The three destination widths are the subject: `.w` preserves what is
above it, `.d` zero-extends over it, `.q` replaces the register. -/

/-- `movzbl %cl, %eax` with CL = 0xFF: zero extension, and the 32-bit write
clears the upper half of RAX even though the value needs only eight bits. -/
theorem movzx_bl_zero_extends :
    (step ⟨.movx .zero .d .b .rax (.reg .rcx), 3⟩
      (mk { rax := 0xFFFFFFFFFFFFFFFF, rcx := 0xFF })).regs.rax = 0xFF := by decide

/-- `movsbl %cl, %eax` with CL = 0xFF (that is, -1 as a byte): the sign fills
the destination's 32 bits — and NOT the register's 64, because the 32-bit write
zero-extends over what the extension produced. ⭐ THE TWO RULES COMPOSE IN THAT
ORDER, and a model that applied them the other way round would leave
0xFFFFFFFFFFFFFFFF. -/
theorem movsx_bl_sign_extends_then_the_write_zero_extends :
    (step ⟨.movx .sign .d .b .rax (.reg .rcx), 3⟩
      (mk { rax := 0, rcx := 0xFF })).regs.rax = 0xFFFFFFFF := by decide

/-- ⭐ AND AT `.w` THE SAME SOURCE PRESERVES.  `movsbw %cl, %ax` writes sixteen
bits, so the bits above them survive — the one destination width in this batch
where a 64-bit write would be observably wrong. -/
theorem movsx_bw_preserves_above_sixteen :
    (step ⟨.movx .sign .w .b .rax (.reg .rcx), 4⟩
      (mk { rax := 0xAAAAAAAAAAAA0000, rcx := 0xFF })).regs.rax
      = 0xAAAAAAAAAAAAFFFF := by decide

/-- `movslq %ecx, %rax` (Intel MOVSXD): 32 bits of source, sign-extended to 64.
0x80000000 is the most negative 32-bit value. -/
theorem movslq_sign_extends_to_64 :
    (step ⟨.movx .sign .q .d .rax (.reg .rcx), 3⟩
      (mk { rax := 0, rcx := 0x80000000 })).regs.rax
      = 0xFFFFFFFF80000000 := by decide

/-- The high-8 source really is bits 15:8. -/
theorem movzx_reads_the_high8_source :
    (step ⟨.movx .zero .d .b .rax (.reg .rcx true), 3⟩
      (mk { rax := 0, rcx := 0xAB00 })).regs.rax = 0xAB := by decide

/-- ⚠️ AND NOT ONE OF THEM TOUCHES A FLAG (SDM Vol. 2A, MOVZX/MOVSX: "Flags
Affected: None"). -/
theorem movx_writes_no_flag :
    let f : Flags := { cf := true, zf := true, sf := true, of := true, pf := true, af := true }
    (step ⟨.movx .sign .q .b .rax (.reg .rcx), 4⟩ (mk { rcx := 0xFF } f)).flags = f := by
  decide

/-- `cltq` (CDQE): RAX takes the sign extension of EAX. -/
theorem cltq_widens_the_accumulator :
    (step ⟨.cext .cdqe, 2⟩ (mk { rax := 0x80000000 })).regs.rax
      = 0xFFFFFFFF80000000 := by decide

/-- `cwtl` (CWDE) writes EAX — thirty-two bits — so it CLEARS the upper half of
RAX as well as widening AX. -/
theorem cwtl_clears_the_upper_half :
    (step ⟨.cext .cwde, 1⟩ (mk { rax := 0xFFFFFFFF00008000 })).regs.rax
      = 0xFFFF8000 := by decide

/-- `cbtw` (CBW) writes AX only, so everything above bit 15 survives. -/
theorem cbtw_preserves_above_sixteen :
    (step ⟨.cext .cbw, 2⟩ (mk { rax := 0xAAAAAAAAAAAA0080 })).regs.rax
      = 0xAAAAAAAAAAAAFF80 := by decide

/-- ⭐ `cqto` (CQO) FILLS RDX AND LEAVES RAX ALONE — the first instruction in
this model whose destination is a register its operands do not name. -/
theorem cqto_fills_rdx_and_leaves_rax :
    let r := step ⟨.cext .cqo, 2⟩ (mk { rax := 0x8000000000000000, rdx := 0x1234 })
    (r.regs.rdx, r.regs.rax) = (0xFFFFFFFFFFFFFFFF, 0x8000000000000000) := by decide

/-- A non-negative accumulator gives a ZERO rdx, so the theorem above is about
the sign and not about a constant. -/
theorem cqto_zeroes_rdx_when_positive :
    (step ⟨.cext .cqo, 2⟩ (mk { rax := 0x1, rdx := 0xFFFF })).regs.rdx = 0 := by decide

/-- ⭐ AND `cltd` (CDQ) WRITES EDX, WHICH CLEARS RDX'S UPPER HALF.  With EAX
non-negative the whole of RDX becomes zero — including bits the instruction
"wrote nothing to" under a 16-bit reading of the same rule.  This is the anchor
for the pre-state change in `Tests/Vectors.lean`: with RDX zero beforehand, this
theorem and its wrong twin agree. -/
theorem cltd_clears_rdx_upper_half :
    (step ⟨.cext .cdq, 1⟩ (mk { rax := 0x1, rdx := 0xFFFFFFFFFFFFFFFF })).regs.rdx
      = 0 := by decide

/-- `cwtd` (CWD) writes DX only: sixteen bits, and RDX's upper 48 survive. -/
theorem cwtd_preserves_above_sixteen :
    (step ⟨.cext .cwd, 2⟩ (mk { rax := 0x8000, rdx := 0xAAAAAAAAAAAA0000 })).regs.rdx
      = 0xAAAAAAAAAAAAFFFF := by decide

/-- XCHG swaps. -/
theorem xchg_swaps :
    let r := step ⟨.xchg .q (.reg .rax) (.reg .rcx), 2⟩ (mk { rax := 1, rcx := 2 })
    (r.regs.rax, r.regs.rcx) = (2, 1) := by decide

/-- ⭐ AND AT WIDTH `.d` IT IS TWO WRITES, NOT A SWAP OF VALUES: each one
zero-extends, so BOTH registers lose their upper halves. -/
theorem xchg_d_zero_extends_both :
    let r := step ⟨.xchg .d (.reg .rax) (.reg .rcx), 1⟩
      (mk { rax := 0x1111111100000001, rcx := 0x2222222200000002 })
    (r.regs.rax, r.regs.rcx) = (2, 1) := by decide

/-- ⭐ `xchg %eax, %eax` MOVES NO DATA AND IS NOT A NO-OP: the 32-bit write
clears the upper half.  The assembler agrees — it encodes this as `87 c0`
rather than `90`, because `90` is NOP and NOP does not touch RAX
(docs/DECISIONS.md D24). -/
theorem xchg_same_register_still_zero_extends :
    (step ⟨.xchg .d (.reg .rax) (.reg .rax), 2⟩
      (mk { rax := 0xFFFFFFFF0000ABCD })).regs.rax = 0xABCD := by decide

/-- At width `.b` the swap touches one byte of each register and nothing else. -/
theorem xchg_b_touches_one_byte_each :
    let r := step ⟨.xchg .b (.reg .rax) (.reg .rcx), 2⟩
      (mk { rax := 0xFFFFFFFFFFFFFF01, rcx := 0xEEEEEEEEEEEEEE02 })
    (r.regs.rax, r.regs.rcx) = (0xFFFFFFFFFFFFFF02, 0xEEEEEEEEEEEEEE01) := by decide

/-- ⭐⭐ P2 ITEM 2 REPLACED A REFUSAL ANCHOR WITH A BEHAVIOUR ONE.

This anchor asserted the D25 decline — `xchg` at memory stops the model — and
that state no longer exists.  `Ea.lock` is the atomicity vocabulary D25 said the
model lacked, so the form EXECUTES: the register takes the memory's value and
the memory takes the register's, in one step, with the atomicity RECORDED and
not verified (`TRUSTBASE.md`).

⛔ THE ANCHOR IS REWRITTEN RATHER THAN DELETED, because what it was really
holding is that the swap does not half-happen: the old version said "stops and
changes nothing else", and its replacement says both directions of the exchange
land.  A refusal anchor that could no longer fire would be a green about a model
nobody runs. -/
theorem xchg_memory_swaps_both_ways :
    let s0 := mk { rax := 1, rbx := 0x100 }
    let s1 := { s0 with mem := s0.mem.writeSize .q 0x100 0xDEADBEEF }
    let r := step ⟨.xchg .q (.mem { base := some .rbx }) (.reg .rax), 3⟩ s1
    (r.stopped, r.regs.rax, r.mem.readSize .q 0x100) = (false, 0xDEADBEEF, 1) := by decide

/-- ⛔ AND A `lock` ON A FORM THE MANUAL DOES NOT LIST IS #UD.  `mov` is the one
a reader most expects to be lockable — `lock movq %rax, (%rbx)` looks exactly
like the atomic store somebody wants — and it is not on the SDM's list. -/
theorem lock_on_mov_is_ud :
    let r := step ⟨.mov .q (.mem { base := some .rbx, lock := true }) (.reg .rax), 4⟩
      (mk { rax := 1, rbx := 0x100 })
    (r.stopped, r.mem.readSize .q 0x100) = (true, 0) := by decide

/-- And a `lock` on a form the manual DOES list executes exactly as the
unlocked form does — the flag changes what the model RECORDS, not what it
computes. -/
theorem lock_on_add_executes :
    let ea : Ea := { base := some .rbx }
    let s0 := mk { rax := 1, rbx := 0x100 }
    (step ⟨.bin .add .q (.mem { ea with lock := true }) (.reg .rax), 4⟩ s0).mem.readSize .q 0x100
      = (step ⟨.bin .add .q (.mem ea) (.reg .rax), 3⟩ s0).mem.readSize .q 0x100 := by decide

/-- BSWAP reverses the bytes. -/
theorem bswap_q_reverses_eight_bytes :
    (step ⟨.bswap .q .rax, 3⟩ (mk { rax := 0x0102030405060708 })).regs.rax
      = 0x0807060504030201 := by decide

/-- ⭐ AND `bswapl` REVERSES FOUR AND THEN ZERO-EXTENDS, so the upper half of the
register is gone rather than reversed into. -/
theorem bswap_d_reverses_four_and_zero_extends :
    (step ⟨.bswap .d .rax, 2⟩ (mk { rax := 0xFFFFFFFF01020304 })).regs.rax
      = 0x04030201 := by decide

/-- ⛔ AND THE WIDTHS THE SDM LEAVES UNDEFINED ARE REFUSED, not answered.  "The
result of BSWAP with a 16-bit operand size is undefined": the oracle is the
wrong instrument, because what is undefined is the whole result and not some of
its bits. -/
theorem bswap_refuses_sixteen_bits :
    (step ⟨.bswap .w .rax, 3⟩ (mk { rax := 0x1234 })).stopped = true := by decide

/-! ## P1 BATCH 11 — the loop group and the flag-control singles -/

/-- ⭐ THE ORDER, AS ONE EXAMPLE: A COUNTER OF 1 FALLS THROUGH.  `loop` decrements
first and tests the RESULT, so RCX = 1 becomes 0 and the branch is NOT taken —
RIP is the fall-through address.  A model that tested the incoming counter would
branch here, and this is one of exactly two counter values at which the two
readings differ. -/
theorem loop_counter_one_falls_through :
    let r := step ⟨.loop .loop false 0x10, 2⟩ (mk { rcx := 1 } (rip := 0x400000))
    (r.regs.rcx, r.rip) = (0, 0x400002) := by decide

/-- ⭐ AND THE OTHER ONE: A COUNTER OF 0 BRANCHES, having wrapped to all-ones.
This is the pair that says "decrement, then test" is a claim with observable
content rather than a way of phrasing it. -/
theorem loop_counter_zero_wraps_and_branches :
    let r := step ⟨.loop .loop false 0x10, 2⟩ (mk { rcx := 0 } (rip := 0x400000))
    (r.regs.rcx, r.rip) = (0xFFFFFFFFFFFFFFFF, 0x400012) := by decide

/-- ⛔ THE COUNTER IS DECREMENTED ON THE FALL-THROUGH PATH TOO.  `loope` with ZF
clear does not branch — and RCX has still moved.  A "if taken then decrement and
jump" implementation leaves RCX at 5 here. -/
theorem loope_decrements_even_when_not_taken :
    let r := step ⟨.loop .loope false 0x10, 2⟩
      (mk { rcx := 5 } { zf := false } (rip := 0x400000))
    (r.regs.rcx, r.rip) = (4, 0x400002) := by decide

theorem loope_branches_when_zf_set :
    let r := step ⟨.loop .loope false 0x10, 2⟩
      (mk { rcx := 5 } { zf := true } (rip := 0x400000))
    (r.regs.rcx, r.rip) = (4, 0x400012) := by decide

theorem loopne_branches_when_zf_clear :
    let r := step ⟨.loop .loopne false 0x10, 2⟩
      (mk { rcx := 5 } { zf := false } (rip := 0x400000))
    (r.regs.rcx, r.rip) = (4, 0x400012) := by decide

/-- ⭐ `addr32 loop` COUNTS IN ECX AND ZERO-EXTENDS THE WRITE-BACK, so the upper
half of RCX is CLEARED by an instruction whose only job was to decrement a
counter (SDM Vol. 1 §3.4.1.1).  Without the prefix the same state decrements the
whole register and the upper half survives — the two lines below are the same
counter value under the two widths. -/
theorem addr32_loop_counts_in_ecx_and_clears_the_upper_half :
    let r := step ⟨.loop .loop true 0x10, 3⟩
      (mk { rcx := 0xDEADBEEF00000005 } (rip := 0x400000))
    (r.regs.rcx, r.rip) = (4, 0x400013) := by decide

theorem loop_without_the_prefix_keeps_the_upper_half :
    let r := step ⟨.loop .loop false 0x10, 2⟩
      (mk { rcx := 0xDEADBEEF00000005 } (rip := 0x400000))
    (r.regs.rcx, r.rip) = (0xDEADBEEF00000004, 0x400012) := by decide

/-- ⭐ AND THE STATE THAT SEPARATES THE TWO TESTS.  With ECX = 1 and RCX ≠ 1 the
prefixed form FALLS THROUGH (the 32-bit counter reached zero) while the
unprefixed form BRANCHES (the 64-bit counter did not).  This is the exact state
`loopCounterStates` was added to the pre-state set to reach: nothing in
`adversarial` had a non-zero upper half over a low half of 1. -/
theorem addr32_and_plain_loop_disagree_at_ecx_one :
    let s := mk { rcx := 0xDEADBEEF00000001 } (rip := 0x400000)
    let a := step ⟨.loop .loop true 0x10, 3⟩ s
    let b := step ⟨.loop .loop false 0x10, 2⟩ s
    (a.rip, b.rip) = (0x400003, 0x400012) := by decide

/-- The flag-control singles, one bit each. -/
theorem clc_clears_cf_and_stc_sets_it :
    let c := step ⟨.flagop .clc, 1⟩ (mk (flags := { cf := true }))
    let t := step ⟨.flagop .stc, 1⟩ (mk (flags := { cf := false }))
    (c.flags.cf, t.flags.cf) = (false, true) := by decide

theorem cmc_complements_cf :
    let a := step ⟨.flagop .cmc, 1⟩ (mk (flags := { cf := true }))
    let b := step ⟨.flagop .cmc, 1⟩ (mk (flags := { cf := false }))
    (a.flags.cf, b.flags.cf) = (false, true) := by decide

/-- ⭐ `cld` AND `std` ARE THE MODEL'S ONLY WRITERS OF DF, and this is the anchor
that says so with DF actually SET beforehand — the state no pre-state reached
until this batch (docs/DECISIONS.md D27).  Against a DF-clear state, `cld` and a
no-op are the same function. -/
theorem cld_clears_df_and_std_sets_it :
    let c := step ⟨.flagop .cld, 1⟩ (mk (flags := { df := true }))
    let t := step ⟨.flagop .std, 1⟩ (mk (flags := { df := false }))
    (c.flags.df, t.flags.df) = (false, true) := by decide

/-- ⛔ AND THEY DO NOT CROSS: `cld` leaves CF, `clc` leaves DF.  Written from one
five-case template, that is the one thing that could silently go wrong. -/
theorem the_flag_singles_do_not_cross :
    let c := step ⟨.flagop .cld, 1⟩ (mk (flags := { cf := true, df := true }))
    let t := step ⟨.flagop .clc, 1⟩ (mk (flags := { cf := true, df := true }))
    (c.flags.cf, c.flags.df, t.flags.cf, t.flags.df) = (true, false, false, true) := by decide

/-! ## P1 BATCH 12 — the near-free four

Each of these is an SDM sentence evaluated in the kernel.  They are cheap because
none of the four writes a flag; the batch's cost was in the STATE the last two
need, which is asserted in `Tests/Coverage.lean` rather than here. -/

/-- ⭐ NOP IS INERT AT EVERY SHAPE, INCLUDING THE MEMORY ONE, and the RIP it
advances is the DECODED LENGTH rather than a constant.  `nopl (%rbx)` is checked
against a state whose data window is non-zero: the registers, the flags and the
memory must all come out untouched, which is what "does not issue a memory
operation" (SDM Vol. 2A, NOP) means operationally. -/
theorem nop_is_inert_at_every_shape :
    let m := Mem.empty.write 0x2000 0xAB
    let s := mk (flags := { cf := true, zf := true }) (mem := m) (rip := 0x400000)
    let short := step ⟨.nop none, 1⟩ s
    let long  := step ⟨.nop (some (.mem { base := some .rbx })), 3⟩ s
    (short.rip, long.rip, long.flags.cf, long.flags.zf, long.mem.read 0x2000,
      long.regs.get .rbx)
      = (0x400001, 0x400003, true, true, 0xAB, 0) := by decide

/-- ⭐ UD2 REFUSES AND DOES NOT ADVANCE RIP.  The second half is the claim worth
anchoring: a fault is not a completed instruction, so the RIP both models report
is the one the instruction started at. -/
theorem ud2_faults_without_advancing_rip :
    let s := step ⟨.ud2, 2⟩ (mk (rip := 0x400000))
    (s.ms.isSome, s.rip) = (true, 0x400000) := by decide

/-- RET near: RIP comes off the stack and RSP moves up by eight
(SDM Vol. 2A, RET). -/
theorem retq_pops_the_return_address :
    let m := Mem.empty.writeSize .q 0x8000 0x401000
    let r : Regs := ({} : Regs).set .rsp 0x8000
    let s := step ⟨.ret, 1⟩ (mk (regs := r) (mem := m) (rip := 0x400000))
    (s.rip, s.regs.get .rsp, s.ms.isSome) = (0x401000, 0x8008, false) := by decide

/-- ⛔ AND ON A NON-CANONICAL RETURN ADDRESS IT REFUSES **WITHOUT MOVING RSP**.
x86isa raises #GP(0) before committing the pop, so a model that popped and then
refused would disagree with it on `rsp` as well as on `rip` — the disagreement
that says the ORDER is observable.  `0x3736353433323130` is not an arbitrary
choice: it is what the differential harness's own stack background actually
reads as at RSP, and therefore the value seventy-eight of the eighty pre-states
present to `retq`. -/
theorem retq_refuses_a_noncanonical_return_without_moving_rsp :
    let m := Mem.empty.writeSize .q 0x8000 0x3736353433323130
    let r : Regs := ({} : Regs).set .rsp 0x8000
    let s := step ⟨.ret, 1⟩ (mk (regs := r) (mem := m) (rip := 0x400000))
    (s.ms.isSome, s.regs.get .rsp, s.rip) = (true, 0x8000, 0x400000) := by decide

/-- ⭐ LEAVE IS `mov rsp, rbp` THEN `pop rbp`, IN THAT ORDER.  RSP ends at
RBP + 8 and RBP takes the value that was AT the old RBP — not at the old RSP,
which is the whole content of the ordering.  The two are distinguishable here
only because RBP and RSP hold different addresses and the memory under each
differs; against a state with RBP = 0 they coincide. -/
theorem leaveq_moves_rsp_then_pops_rbp :
    let m := (Mem.empty.writeSize .q 0x7ff0 0xDEADBEEF).writeSize .q 0x8000 0x1111
    let r : Regs := (({} : Regs).set .rsp 0x8000).set .rbp 0x7ff0
    let s := step ⟨.leave, 1⟩ (mk (regs := r) (mem := m) (rip := 0x400000))
    (s.regs.get .rsp, s.regs.get .rbp, s.rip) = (0x7ff8, 0xDEADBEEF, 0x400001) := by decide

/-! ## P1 BATCH 13 — the flagless shifts and the byte-swapping move

Two forms whose RESULT this model already computed and whose content is in what
they do NOT do.  The anchors below are therefore mostly NEGATIVE claims — no
flag moves, no memory is written — and a negative claim is exactly the kind a
differential run cannot make on its own, because a state component that never
changes on either side agrees for free (D27). -/

/-- ⭐⭐ SHLX/SHRX/SARX COMPUTE THE SAME RESULT AS SHL/SHR/SAR AND WRITE NO FLAG.

Both halves in one theorem, against a state whose six arithmetic flags are ALL
SET, so "no flag moves" is a claim with something to lose: the `.shift` form
below is run from the identical state and clears CF, which is what says the
flags in the `.shiftx` line were preserved rather than never touched.

SDM Vol. 2A, SARX/SHLX/SHRX: "Flags Affected: None." -/
theorem shiftx_matches_the_shift_and_writes_no_flag :
    let f : Flags := { cf := true, pf := true, af := true, zf := true,
                       sf := true, of := true }
    let r : Regs := (({} : Regs).set .rcx 0x123456789ABCDEF0).set .rdx 5
    let s := mk (regs := r) (flags := f) (rip := 0x400000)
    let x := step ⟨.shiftx .shl .q .rax (.reg .rcx) .rdx, 5⟩ s
    -- `0x468ACF13579BDE00` is `0x123456789ABCDEF0 <<< 5` at 64 bits — the value
    -- the theorem below shows the ordinary `shlq $5` computes from the same
    -- state.  It is written as a literal rather than as `y.regs.get .rcx`
    -- because a proposition mentioning BOTH `step`s defeats `Decidable`
    -- synthesis through the `let` chain; the pairing is made by the two
    -- theorems reading the same literal.
    -- ⭐ THE WHOLE `Flags` RECORD, not seven projections: a projection list has
    -- to be kept in step with the record and a field added later would go
    -- unchecked here — the `flagFields` lesson (D30) one level up.
    (x.regs.get .rax, x.flags, x.rip) = (0x468ACF13579BDE00, f, 0x400005) := by decide

/-- ⛔ AND THE CONTROL FOR THE THEOREM ABOVE: the ordinary `.shift`, run from the
IDENTICAL state, DOES move a flag.  Without this the "every flag came out as it
went in" claim would be satisfied by a state no shift rule can reach — D27's
rule applied to an anchor rather than to a pre-state set. -/
theorem the_shift_it_is_compared_against_does_move_a_flag :
    let f : Flags := { cf := true, pf := true, af := true, zf := true,
                       sf := true, of := true }
    let r : Regs := (({} : Regs).set .rcx 0x123456789ABCDEF0).set .rdx 5
    let s := mk (regs := r) (flags := f) (rip := 0x400000)
    let y := step ⟨.shift .shl .q (.reg .rcx) (.imm8 5), 4⟩ s
    -- the SAME result value, and CF moved
    (y.regs.get .rcx, y.flags.cf) = (0x468ACF13579BDE00, false) := by decide

/-- ⭐ THE COUNT IS MASKED — 6 bits at `.q`, 5 at `.d` — AND IT IS THE COUNT
REGISTER'S LOW BITS, not the operand's.  A count of 64 masks to 0 and copies;
a count of 65 masks to 1.  SDM Vol. 2A: "the count is masked to 5 bits (or 6
bits with a 64-bit operand size)". -/
theorem shiftx_masks_its_count :
    let mkS (cnt : BitVec 64) : Cpu :=
      mk (regs := (({} : Regs).set .rcx 0x8000000000000001).set .rdx cnt)
    let at64 := step ⟨.shiftx .shr .q .rax (.reg .rcx) .rdx, 5⟩ (mkS 64)
    let at65 := step ⟨.shiftx .shr .q .rax (.reg .rcx) .rdx, 5⟩ (mkS 65)
    -- and at `.d` the SAME count of 64 masks to 0 in five bits, while 33 masks
    -- to 1 — the 5/6 split, stated where it can be wrong
    let d32 := step ⟨.shiftx .shr .d .rax (.reg .rcx) .rdx, 5⟩ (mkS 32)
    let d33 := step ⟨.shiftx .shr .d .rax (.reg .rcx) .rdx, 5⟩ (mkS 33)
    (at64.regs.get .rax, at65.regs.get .rax, d32.regs.get .rax, d33.regs.get .rax)
      = (0x8000000000000001, 0x4000000000000000, 0x00000001, 0x00000000) := by decide

/-- ⭐ AND THE ZERO COUNT IS NOT A NO-OP AT `.d`: the destination write
zero-extends (SDM Vol. 1 §3.4.1.1), so `shlxl` with a masked count of zero
CLEARS the upper half of the destination while moving the source unchanged into
the lower half.  `.shift` needs a special zero-count branch because its flags
must not move; this form has no such branch, and this is the state that says the
absence is correct rather than merely untested. -/
theorem shiftx_at_zero_count_still_zero_extends :
    let r : Regs := ((({} : Regs).set .rax 0xFFFFFFFFFFFFFFFF).set .rcx 0x12345678).set .rdx 0
    let s := step ⟨.shiftx .shl .d .rax (.reg .rcx) .rdx, 5⟩ (mk (regs := r))
    s.regs.get .rax = 0x0000000012345678 := by decide

/-- ⛔ AND THE NARROW WIDTHS ARE DECLINED.  VEX.W selects 32 or 64 bits and there
is no 8- or 16-bit encoding, so the model refuses rather than answering for an
instruction that cannot be written down. -/
theorem shiftx_declines_the_widths_with_no_encoding :
    ((step ⟨.shiftx .shl .b .rax (.reg .rcx) .rdx, 5⟩ (mk)).ms.isSome,
     (step ⟨.shiftx .shl .w .rax (.reg .rcx) .rdx, 5⟩ (mk)).ms.isSome)
      = (true, true) := by decide

/-- ⭐⭐ MOVBE REVERSES AT THE OPERAND WIDTH, AND THE WIDTH RULE APPLIES ON TOP.

The three loads from the SAME eight bytes are the whole instruction: `movbew`
reverses two bytes and MERGES into AX, `movbel` reverses four and ZERO-EXTENDS,
`movbeq` reverses eight.  A model that reversed 64 bits and truncated afterwards
agrees with this one at `.q` and disagrees at both narrow widths — which is why
all three widths are anchored and not just the widest.

SDM Vol. 2A, MOVBE; SDM Vol. 1 §3.4.1.1 for the destination width rule. -/
theorem movbe_reverses_at_the_operand_width :
    let m := Mem.empty.writeSize .q 0x2000 0x1122334455667788
    let r : Regs := (({} : Regs).set .rbx 0x2000).set .rax 0xFFFFFFFFFFFFFFFF
    let s := mk (regs := r) (mem := m) (rip := 0x400000)
    let q := step ⟨.movbe .q (.reg .rax) (.mem { base := some .rbx }), 5⟩ s
    let d := step ⟨.movbe .d (.reg .rax) (.mem { base := some .rbx }), 4⟩ s
    let w := step ⟨.movbe .w (.reg .rax) (.mem { base := some .rbx }), 5⟩ s
    (q.regs.get .rax, d.regs.get .rax, w.regs.get .rax)
      = (0x8877665544332211, 0x0000000088776655, 0xFFFFFFFFFFFF8877) := by decide

/-- ⭐ THE STORE DIRECTION WRITES EXACTLY ITS OWN WIDTH.  `movbew %ax, (%rbx)`
puts two reversed bytes at the address and leaves the other six alone — the
margin is what says the store did not run long.  "Flags Affected: None" is
checked from an all-set flag state, as above. -/
theorem movbe_stores_at_its_own_width_and_writes_no_flag :
    let f : Flags := { cf := true, pf := true, af := true, zf := true,
                       sf := true, of := true }
    let m := Mem.empty.writeSize .q 0x2000 0xAAAAAAAAAAAAAAAA
    let r : Regs := (({} : Regs).set .rbx 0x2000).set .rax 0x1122334455667788
    let s := mk (regs := r) (flags := f) (mem := m) (rip := 0x400000)
    let w := step ⟨.movbe .w (.mem { base := some .rbx }) (.reg .rax), 5⟩ s
    let q := step ⟨.movbe .q (.mem { base := some .rbx }) (.reg .rax), 5⟩ s
    (w.mem.readSize .q 0x2000, q.mem.readSize .q 0x2000, w.flags, w.rip)
      = (0xAAAAAAAAAAAA8877, 0x8877665544332211, f, 0x400005) := by decide

/-- ⛔ AND THE SHAPES WITH NO ENCODING ARE DECLINED: register-to-register (both
encodings put the memory operand in ModR/M's r/m field), two memory operands,
an immediate, and the 8-bit width. -/
theorem movbe_declines_the_shapes_with_no_encoding :
    let M : Operand := .mem { base := some .rbx }
    ((step ⟨.movbe .q (.reg .rax) (.reg .rcx), 5⟩ (mk)).ms.isSome,
     (step ⟨.movbe .q M M, 5⟩ (mk)).ms.isSome,
     (step ⟨.movbe .q (.reg .rax) (.imm 7), 5⟩ (mk)).ms.isSome,
     (step ⟨.movbe .b (.reg .rax) M, 5⟩ (mk)).ms.isSome)
      = (true, true, true, true) := by decide

/-! ## P1 BATCH 15 — the string group

⭐ THESE EXIST BECAUSE THE FRAME THEOREMS IN `X86/Theorems.lean` WOULD ALL HOLD
OF A NO-OP.  "`movs` writes no flag" and "`cmps` writes no memory" are true of
an instruction that does nothing at all, and every one of them was proved on the
first attempt — which is a reason to pin the VALUES, not a reason to move on.
Each anchor below is a concrete I/O pair a reader can check against the SDM by
hand. -/

/-- A state with a source at 0x1000 and a destination at 0x2000, distinct
contents in each, and the accumulator holding a third value. -/
private def strState (df : Bool) : Cpu :=
  let m := (Mem.empty.writeSize .q 0x1000 0x8877665544332211).writeSize .q 0x2000 0xEEEEEEEEEEEEEEEE
  let r : Regs := ((({} : Regs).set .rsi 0x1000).set .rdi 0x2000).set .rax 0x00000000AABBCCDD
  mk (regs := r) (flags := { df := df }) (mem := m) (rip := 0x400000)

/-- ⭐ MOVSQ COPIES EIGHT BYTES AND ADVANCES BOTH POINTERS BY EIGHT. -/
theorem movsq_copies_and_advances_both_pointers :
    let w := step ⟨.strop .movs .q, 2⟩ (strState false)
    (w.mem.readSize .q 0x2000, w.regs.get .rsi, w.regs.get .rdi, w.rip)
      = (0x8877665544332211, 0x1008, 0x2008, 0x400002) := by decide

/-- ⭐ WITH DF SET THE POINTERS GO BACKWARD — and the COPY still happens at the
ORIGINAL addresses.  ⚠️ This is the anchor for the ordering: a model that
decremented first would have written at 0x1ff8 and left 0x2000 untouched. -/
theorem movsq_with_df_copies_first_then_decrements :
    let w := step ⟨.strop .movs .q, 2⟩ (strState true)
    (w.mem.readSize .q 0x2000, w.regs.get .rsi, w.regs.get .rdi)
      = (0x8877665544332211, 0x0FF8, 0x1FF8) := by decide

/-- ⭐ MOVSB COPIES ONE BYTE AND ADVANCES BY ONE — and the seven bytes above the
destination are UNTOUCHED, which is what says the width reaches the store and
not only the pointer. -/
theorem movsb_copies_one_byte :
    let w := step ⟨.strop .movs .b, 1⟩ (strState false)
    (w.mem.readSize .q 0x2000, w.regs.get .rdi)
      = (0xEEEEEEEEEEEEEE11, 0x2001) := by decide

/-- ⭐ LODSL ZERO-EXTENDS INTO RAX; LODSW MERGES.  The two widths in one
statement, because the difference between them is the whole content of the
SDM Vol. 1 §3.4.1.1 rule this form depends on. -/
theorem lods_zero_extends_at_32_and_merges_at_16 :
    let l := step ⟨.strop .lods .d, 1⟩ (strState false)
    let w := step ⟨.strop .lods .w, 2⟩ (strState false)
    (l.regs.get .rax, w.regs.get .rax, l.regs.get .rdi)
      = (0x0000000044332211, 0x00000000AABB2211, 0x2000) := by decide

/-- ⭐ STOSQ WRITES THE ACCUMULATOR TO [RDI] AND LEAVES RSI ALONE. -/
theorem stosq_writes_rax_and_leaves_rsi :
    let w := step ⟨.strop .stos .q, 2⟩ (strState false)
    (w.mem.readSize .q 0x2000, w.regs.get .rsi, w.regs.get .rdi)
      = (0x00000000AABBCCDD, 0x1000, 0x2008) := by decide

/-- ⭐⭐ CMPSQ COMPUTES `[RSI] − [RDI]`, NOT THE REVERSE.  `0x8877…11` minus
`0xEEEE…EE` BORROWS, so CF is set; the opposite order would not borrow and CF
would be clear.  ⛔ THIS IS THE ANCHOR FOR THE AT&T PRINT-ORDER TRAP, and CF is
the bit that distinguishes the two readings. -/
theorem cmpsq_subtracts_source_minus_destination :
    let w := step ⟨.strop .cmps .q, 2⟩ (strState false)
    (w.flags.cf, w.mem.readSize .q 0x2000, w.regs.get .rsi, w.regs.get .rdi)
      = (true, 0xEEEEEEEEEEEEEEEE, 0x1008, 0x2008) := by decide

/-- ⭐ SCASQ COMPUTES `RAX − [RDI]` AND MOVES ONLY RDI.  `0xAABBCCDD` minus
`0xEEEE…EE` also borrows; what separates this from `cmps` is that RSI does not
move and the value read is the ACCUMULATOR's, not memory's. -/
theorem scasq_subtracts_rax_minus_destination :
    let w := step ⟨.strop .scas .q, 2⟩ (strState false)
    (w.flags.cf, w.regs.get .rsi, w.regs.get .rdi)
      = (true, 0x1000, 0x2008) := by decide

/-! ### P1 BATCH 16 — the repeat prefixes

⭐ EVERY NUMBER BELOW WAS MEASURED AGAINST x86isa BEFORE IT WAS WRITTEN, not
derived from the SDM's prose and checked afterwards.  The probe is recorded in
docs/DIFFERENTIAL-P1-BATCH16.md; these are the same facts as `decide`-checked
statements about this model. -/

/-- A repeat state: the string state above with a COUNT. -/
private def repState (df : Bool) (rcx : BitVec 64) : Cpu :=
  let s := strState df
  { s with regs := s.regs.set .rcx rcx }

/-- ⭐⭐ THE FINDING, ANCHORED AT THE ONLY VALUE THAT SHOWS IT.  `rep movsq` with
RCX = 1 does the copy, leaves RCX = 0 — and leaves RIP AT THE INSTRUCTION.  The
fall-through is the NEXT step's job.  ⚠️ Compare `rep_movsq_rcx_zero_falls_
through` below: the same model, one step later, is what advances RIP. -/
theorem rep_movsq_last_iteration_does_not_advance_rip :
    let w := step ⟨.repstrop .rep .movs .q, 3⟩ (repState false 1)
    (w.mem.readSize .q 0x2000, w.regs.get .rcx, w.rip)
      = (0x8877665544332211, 0, 0x400000) := by decide

/-- ⭐ AND WITH THE COUNT ALREADY ZERO IT IS A PURE FALL-THROUGH: no copy, no
pointer move, and RCX does NOT wrap to all-ones. -/
theorem rep_movsq_rcx_zero_falls_through :
    let w := step ⟨.repstrop .rep .movs .q, 3⟩ (repState false 0)
    (w.mem.readSize .q 0x2000, w.regs.get .rcx, w.regs.get .rdi, w.rip)
      = (0xEEEEEEEEEEEEEEEE, 0, 0x2000, 0x400003) := by decide

/-- ⭐ THE TWO STEPS COMPOSED ARE THE WHOLE LOOP.  Running `rep movsq` twice
from RCX = 1 reaches the state a reader expects a single `rep` to reach — one
copy, RCX = 0, RIP past the instruction.  ⚠️ This is the anchor that says the
one-iteration decomposition is a faithful loop and not merely a different
answer: `run` is the model's own multi-step driver. -/
theorem rep_movsq_two_steps_complete_the_loop :
    let w := run [⟨.repstrop .rep .movs .q, 3⟩, ⟨.repstrop .rep .movs .q, 3⟩]
      (repState false 1)
    (w.mem.readSize .q 0x2000, w.regs.get .rcx, w.regs.get .rdi, w.rip)
      = (0x8877665544332211, 0, 0x2008, 0x400003) := by decide

/-- ⭐ THE COUNT IS DECREMENTED AT 64 BITS EVEN AT THE BYTE WIDTH.  `rep movsb`
with RCX = 0x1_0000_0000 leaves 0x0_FFFF_FFFF — a value whose low half alone
would have wrapped the other way. -/
theorem rep_movsb_decrements_the_whole_of_rcx :
    let w := step ⟨.repstrop .rep .movs .b, 2⟩ (repState false 0x100000000)
    w.regs.get .rcx = 0xFFFFFFFF := by decide

/-- ⭐⭐ `repe` STOPS ON ZF = 0 AND `repne` CONTINUES ON IT — the same state, the
same comparison, opposite RIPs.  `0x8877…11` ≠ `0xEEEE…EE`, so the comparison
clears ZF: `repe` is done and `repne` goes round again.  ⚠️ Written as ONE
statement over both prefixes because the risk in this pair is not that either is
wrong alone, it is that both read the same predicate. -/
theorem repe_and_repne_take_opposite_exits_on_the_same_comparison :
    let e := step ⟨.repstrop .repe .cmps .q, 3⟩ (repState false 3)
    let n := step ⟨.repstrop .repn .cmps .q, 3⟩ (repState false 3)
    (e.flags.zf, e.rip, n.flags.zf, n.rip, e.regs.get .rcx, n.regs.get .rcx)
      = (false, 0x400003, false, 0x400000, 2, 2) := by decide

/-- ⭐ AND THE PREDICATE READS THE COMPARISON'S OWN ZF, NOT THE INCOMING ONE.
The state here arrives with ZF already SET, and `repe` still exits — because the
comparison it just made cleared it.  A model testing the incoming flag would
have gone round again. -/
theorem repe_reads_the_zf_it_just_wrote :
    let s := repState false 3
    let w := step ⟨.repstrop .repe .cmps .q, 3⟩ { s with flags := { s.flags with zf := true } }
    (w.flags.zf, w.rip) = (false, 0x400003) := by decide

/-- ⭐ A PREFIX THIS MODEL DOES NOT CLAIM HALTS.  `F2` on `movs` assembles and
x86isa executes it as an unprefixed string op; the roster does not file it, so
this model declines rather than copying the oracle's treatment of a shape
nobody filed. -/
theorem repne_movs_is_declined :
    (step ⟨.repstrop .repn .movs .q, 3⟩ (repState false 3)).stopped = true := by decide

/-! ## P1 BATCH 17 — the multiply-divide anchors

⭐ THE NUMBERS BELOW ARE ARITHMETIC A READER CAN CHECK IN THEIR HEAD, which is
what an anchor is for: a differential run says the model agrees with x86isa, and
these say what it agrees ON. -/

private def mdState (rax rdx rcx : BitVec 64) : Cpu :=
  mk (regs := (((({} : Regs).set .rax rax).set .rdx rdx).set .rcx rcx)) (rip := 0x400000)

/-- `mulq`: `2^32 * 2^32 = 2^64`, the smallest product that does not fit — RAX
zero, RDX one, and CF/OF set. -/
theorem mul_q_smallest_overflow :
    let w := step ⟨.muldiv .mul .q (.reg .rcx), 3⟩ (mdState 0x100000000 0 0x100000000)
    (w.regs.get .rax, w.regs.get .rdx, w.flags.cf, w.flags.of, w.rip)
      = (0, 1, true, true, 0x400003) := by decide

/-- ⭐ `imulq` ON THE SAME MAGNITUDES WITH A SIGN: `-1 * -1 = 1`.  The high half
is zero and there is no overflow — where `mulq` on the same BITS would report
`0xFFFFFFFFFFFFFFFE` in RDX and set CF. -/
theorem imul_q_minus_one_squared :
    let w := step ⟨.muldiv .imul .q (.reg .rcx), 3⟩
      (mdState 0xFFFFFFFFFFFFFFFF 0 0xFFFFFFFFFFFFFFFF)
    (w.regs.get .rax, w.regs.get .rdx, w.flags.cf)
      = (1, 0, false) := by decide

theorem mul_q_minus_one_squared_is_a_different_answer :
    let w := step ⟨.muldiv .mul .q (.reg .rcx), 3⟩
      (mdState 0xFFFFFFFFFFFFFFFF 0 0xFFFFFFFFFFFFFFFF)
    (w.regs.get .rax, w.regs.get .rdx, w.flags.cf)
      = (1, 0xFFFFFFFFFFFFFFFE, true) := by decide

/-- ⭐ THE BYTE MULTIPLY'S PAIR IS ONE REGISTER: `0xFF * 0xFF = 0xFE01` lands
whole in AX, and RDX is untouched. -/
theorem mul_b_writes_ax :
    let w := step ⟨.muldiv .mul .b (.reg .rcx), 2⟩ (mdState 0xFF 0xDEADBEEF 0xFF)
    (w.regs.get .rax, w.regs.get .rdx) = (0xFE01, 0xDEADBEEF) := by decide

/-- `divq`: `(1 << 64 + 0) / 3` — a dividend that genuinely uses RDX.  Quotient
`0x5555555555555555`, remainder `1`. -/
theorem div_q_uses_rdx :
    let w := step ⟨.muldiv .div .q (.reg .rcx), 3⟩ (mdState 0 1 3)
    (w.regs.get .rax, w.regs.get .rdx, w.stopped)
      = (0x5555555555555555, 1, false) := by decide

/-- ⛔ AND ONE STEP FURTHER IT IS A FAULT: the same dividend divided by `1` has
a quotient of `2^64`, which does not fit RAX.  The divisor is NON-ZERO, so this
anchors the SECOND #DE sentence, and RAX, RDX and RIP are left exactly as they
were found. -/
theorem div_q_quotient_overflow_writes_nothing :
    let w := step ⟨.muldiv .div .q (.reg .rcx), 3⟩ (mdState 0 1 1)
    (w.stopped, w.regs.get .rax, w.regs.get .rdx, w.rip)
      = (true, 0, 1, 0x400000) := by decide

/-- ⭐⭐ IDIV's ROUNDING, ANCHORED WHERE LEAN AND THE MACHINE DISAGREE.
`-7 / 2` is `-3` remainder `-1` (truncate toward zero, remainder takes the
dividend's sign); `Int`'s `/` and `%` give `-4` and `1`. -/
theorem idiv_q_negative_dividend_truncates :
    let w := step ⟨.muldiv .idiv .q (.reg .rcx), 3⟩
      (mdState 0xFFFFFFFFFFFFFFF9 0xFFFFFFFFFFFFFFFF 2)
    (w.regs.get .rax, w.regs.get .rdx)
      = (0xFFFFFFFFFFFFFFFD, 0xFFFFFFFFFFFFFFFF) := by decide

/-- ⛔ IDIV's ASYMMETRIC RANGE: `-2^63 / -1` is `2^63`, which is not a signed
64-bit value, so it is #DE — the one overflow that a symmetric range check would
miss. -/
theorem idiv_q_int_min_over_minus_one_faults :
    (step ⟨.muldiv .idiv .q (.reg .rcx), 3⟩
      (mdState 0x8000000000000000 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF)).stopped
      = true := by decide

/-- ⭐ IMUL's THREE-OPERAND FORM IGNORES ITS DESTINATION, anchored: `3 * 7 = 21`
with RAX holding a marker that does not appear in the answer. -/
theorem imul3_q_ignores_dest :
    let w := step ⟨.imulr .q .rax (.reg .rcx) (some 7), 7⟩ (mdState 0xDEADBEEF 0 3)
    (w.regs.get .rax, w.flags.cf) = (21, false) := by decide

/-- …and the TWO-operand form does read it: `3 * 7` again, with the roles
swapped, so the same product arrives by the other route. -/
theorem imul2_q_reads_dest :
    let w := step ⟨.imulr .q .rax (.reg .rcx) none, 4⟩ (mdState 7 0 3)
    (w.regs.get .rax, w.flags.cf) = (21, false) := by decide

/-! ## P1 BATCH 18 — the compare-exchange pair and the double shifts

⭐ THE FIRST FOUR ANCHOR A BRANCH, NOT A NUMBER.  `cmpxchg`'s answer is a choice
between two destinations, so what a reader needs pinned is which choice happens
and what each one writes — including the half of the SDM's else-branch this
model does NOT perform (D53). -/

/-- ⭐ THE UNEQUAL BRANCH: the accumulator takes the destination, and the
DESTINATION IS NOT TOUCHED.  ⛔ THE WIDTH IS `.d` DELIBERATELY, and it is the
only width at which this theorem has content: a 32-bit register write
zero-extends, so a model obeying the SDM's `DEST := TEMP` literally would leave
RCX at `0x0000000012345678` instead of `0xDEADBEEF12345678`.  Eighty
differential cases said so before this theorem existed. -/
theorem cmpxchg_l_unequal_leaves_dest_upper_half :
    let w := step ⟨.cmpxchg .d (.reg .rcx) .rdx, 3⟩ (mdState 7 0 0xDEADBEEF12345678)
    (w.regs.get .rcx, w.regs.get .rax, w.flags.zf)
      = (0xDEADBEEF12345678, 0x12345678, false) := by decide

/-- …and the EQUAL branch writes the source into the destination, zero-extended
as any 32-bit register write is, leaving the accumulator alone. -/
theorem cmpxchg_l_equal_writes_src :
    let w := step ⟨.cmpxchg .d (.reg .rcx) .rdx, 3⟩ (mdState 0x12345678 0xAA 0x12345678)
    (w.regs.get .rcx, w.regs.get .rax, w.flags.zf) = (0xAA, 0x12345678, true) := by decide

/-- ⭐ XADD WRITES BOTH: `RAX := RAX + RCX`, `RCX := old RAX`.  `9 + 4 = 13`, and
RCX comes back holding `9`. -/
theorem xadd_q_writes_both :
    let w := step ⟨.xadd .q (.reg .rax) .rcx, 4⟩ (mdState 9 0 4)
    (w.regs.get .rax, w.regs.get .rcx, w.flags.cf) = (13, 9, false) := by decide

/-- ⭐ SHLD BRINGS IN THE SOURCE'S TOP BITS.  At `.q`, `shldq $4` on
`0x1234567800000000` with source `0xFEDCBA9876543210` gives
`0x4567800000000000` shifted up by 4 with the source's top nibble `F` arriving at
the bottom: `0x2345678000000000 ||| 0xF`.  CF is the last bit to leave the top —
bit 60 of the destination, which is `1`. -/
theorem shld_q_brings_in_source_top :
    let w := step ⟨.dshift .shld .q (.reg .rax) .rcx (.imm8 4), 5⟩
      (mdState 0x1234567800000000 0 0xFEDCBA9876543210)
    (w.regs.get .rax, w.flags.cf) = (0x234567800000000F, true) := by decide

/-- …and SHRD brings in the source's BOTTOM bits at the top, the mirror image.
CF is the last bit to leave the bottom — bit 3 of the destination. -/
theorem shrd_q_brings_in_source_bottom :
    let w := step ⟨.dshift .shrd .q (.reg .rax) .rcx (.imm8 4), 5⟩
      (mdState 0x1234567800000000 0 0xFEDCBA9876543210)
    (w.regs.get .rax, w.flags.cf) = (0x0123456780000000, false) := by decide

/-- ⭐ THE BOUNDARY, ANCHORED: a count EQUAL to the operand size is a legal
count, and it makes the destination the SOURCE.  Reachable at `.w` alone — a
five-bit mask allows 16 and a 16-bit operand is 16 wide. -/
theorem shld_w_count_equals_width_is_source :
    let w := step ⟨.dshift .shld .w (.reg .rax) .rcx (.imm8 16), 5⟩
      (mdState 0xFFFF0000ABCD 0 0x1234)
    (w.regs.get .rax, w.stopped) = (0xFFFF00001234, false) := by decide

/-- ⭐⭐ D54, ANCHORED: A COUNT OF ZERO TOUCHES NO FLAG AND STILL ZERO-EXTENDS
THE DESTINATION.  The SDM says "no operation"; ACL2 x86isa and K both write the
destination, and K's rule for this case is commented `// Intel Bug`.

⚠️ RAX's UPPER HALF IS NON-ZERO ON PURPOSE.  With `rax := 0xABCD` — the first
version of this anchor — the write-back and the no-op give the same answer and
the theorem would be true of both models.  `0xDEADBEEF0000ABCD` is what makes it
say something, and it is the D14 shape: a state that does not vary in the bits
the claim is about is a test that passes by construction.

⚠️ THE FLAGS ARE ALL SET so a model that recomputed them from the result would
clear four and this theorem would see that too. -/
theorem shld_zero_count_writes_dest_and_no_flag :
    let s := mk (regs := ((({} : Regs).set .rax 0xDEADBEEF0000ABCD).set .rcx 0x1234))
      (flags := { cf := true, pf := true, af := true, zf := true, sf := true, of := true })
      (rip := 0x400000)
    let w := step ⟨.dshift .shld .d (.reg .rax) .rcx (.imm8 0), 4⟩ s
    (w.regs.get .rax, w.flags, w.rip) = (0x0000ABCD, s.flags, 0x400004) := by decide

/-! ## ⭐⭐ P2 BATCH 37 — MOVMSKPS, AND THE CONTROL THAT SAYS PMOVMSKB DID NOT MOVE

`Op.vmovmsk` was built for `pmovmskb` alone and its lane count was a literal
sixteen; batch 37 made both the count and the sign-bit offset come from
`VMovMskKind.laneBits`.  A generalisation like that has TWO ways to be wrong — the
new kind, and the old one — so the old kind is anchored here beside the new one,
on the SAME source, and the two answers must differ. -/

/-- The source, chosen so that neither a lane-order nor a lane-width error can
hide: the four dword lanes have signs 1,0,1,0 from the top, and the sixteen byte
lanes are NOT a palindrome.
  lane 3 = 0x80000000 · lane 2 = 0x7fffffff · lane 1 = 0xffffffff · lane 0 = 1 -/
private def s_movmsk : Cpu :=
  (mk {} {} {} 0 Oracle.zero).setXmm .x1 0x800000007fffffffffffffff00000001

/-- ⭐ MOVMSKPS: one sign bit per 32-bit lane, lane 0 in result bit 0.
Signs from lane 3 down are 1,0,1,0, so the mask is `0b1010`.
⚠️ DECIDED ON K FIRST: `movmskps_r32_xmm.k` reads bits 128/160/192/224 of the
256-bit parent, which big-endian are xmm bits 127, 95, 63, 31. -/
theorem movmskps_is_the_dword_sign_mask :
    ((step ⟨.vmovmsk .ps .rax .x1, 3⟩ s_movmsk).regs.get .rax) = 0xA := by decide

/-- ⭐⭐ THE CONTROL, IN THE SAME RUN AT THE SAME FIELD: `pmovmskb` on the SAME
source must still give the PRE-BATCH-37 answer.  Bytes 15..0 have signs
1000 0111 1111 0000, so the mask is `0x87F0`.  If the generalisation broke the
byte lane count or the shift, this is what says so — and it fires ALONE, measured
by planting `laneBits .b := 16` and watching only this and the derived-count
theorem go red. -/
theorem pmovmskb_survived_the_generalisation :
    ((step ⟨.vmovmsk .b .rax .x1, 4⟩ s_movmsk).regs.get .rax) = 0x87F0 := by decide

/-- ⭐ AND THE TWO MUST DISAGREE HERE, or both anchors above would be satisfied by
one frozen answer and neither would be evidence about its own kind.
[[feedback-a-probe-must-create-its-condition]] -/
theorem movmsk_kinds_disagree_on_this_source :
    ((step ⟨.vmovmsk .ps .rax .x1, 3⟩ s_movmsk).regs.get .rax)
      ≠ ((step ⟨.vmovmsk .b .rax .x1, 4⟩ s_movmsk).regs.get .rax) := by decide

/-- ⛔ THE LANE COUNT IS DERIVED FROM `laneBits`, so state what it derives TO.
A third kind cannot be added without this line being read. -/
theorem movmsk_lane_counts_are_derived :
    (VMovMskKind.all.map (fun k => 128 / k.laneBits)) = [16, 4] := by decide

/-! ## ⭐⭐⭐ P2 BATCH 37 — SHUFPS AND SHUFPD, THE ONLY NEW SEMANTICS IN THE BATCH

The immediate `0x1b` is LLVM's own example, so the expected answer below is read
off a THIRD source rather than re-derived from the rule being tested: `objdump`
renders `shufps $0x1b,%xmm1,%xmm0` as `xmm0 = xmm0[3,2],xmm1[1,0]` and
`shufpd $0x1,%xmm1,%xmm0` as `xmm0 = xmm0[1],xmm1[0]`. -/

/-- Both operands have four DISTINCT non-zero lanes, and the two registers share
no lane value.  ⛔ THAT IS WHAT MAKES THE OPERAND ORDER VISIBLE: with `a = b` —
or with either operand zero — a model that read the SOURCE where this one reads
the DESTINATION is bit-identical to this one, and the anchor would pass about the
wrong function. -/
private def s_shufp : Cpu :=
  ((mk {} {} {} 0 Oracle.zero).setXmm .x0 0x000000A3000000A2000000A1000000A0).setXmm
    .x1 0x000000B3000000B2000000B1000000B0

/-- ⭐ `shufps $0x1b`: `imm = 0b00_01_10_11`, so lane0 ← DEST[3], lane1 ← DEST[2],
lane2 ← SRC[1], lane3 ← SRC[0] — i.e. `A3 A2 B1 B0` from lane 0 up, which is
LLVM's `xmm0[3,2],xmm1[1,0]`. -/
theorem shufps_matches_the_disassembler :
    ((step ⟨.vshufp .ps .x0 .x1 0x1b, 4⟩ s_shufp).getXmm .x0)
      = 0x000000B0000000B1000000A2000000A3 := by decide

/-- ⭐ `shufpd $0x1`: `imm[0] = 1` ⇒ qword0 ← DEST[1]; `imm[1] = 0` ⇒ qword1 ←
SRC[0].  LLVM's `xmm0[1],xmm1[0]`. -/
theorem shufpd_matches_the_disassembler :
    ((step ⟨.vshufp .pd .x0 .x1 0x1, 5⟩ s_shufp).getXmm .x0)
      = 0x000000B1000000B0000000A3000000A2 := by decide

/-- ⛔⛔ THE ANCHOR THAT REFUTES THE OPERAND SWAP, stated as a DISAGREEMENT rather
than as a second expected value: shuffling `x1` by `x0` must not give what
shuffling `x0` by `x1` gives.  The swap is the plausible wrong model for a
two-source shuffle — `vshufpsAux`'s `if i < 2 then a else b` is the only line that
decides it — and no vector in the table pairs a form with its own operands
reversed, so nothing else here would say. -/
theorem shufps_is_not_its_operand_swap :
    ((step ⟨.vshufp .ps .x0 .x1 0x1b, 4⟩ s_shufp).getXmm .x0)
      ≠ ((step ⟨.vshufp .ps .x1 .x0 0x1b, 4⟩ s_shufp).getXmm .x1) := by decide

/-- ⚠️ AND `shufpd` READS ONLY THE IMMEDIATE'S LOW TWO BITS, so the SDM's
`imm8[7:2]` are ignored.  Stated because a vector varying those bits would look
like coverage and witness nothing. -/
theorem shufpd_ignores_the_high_immediate_bits :
    ((step ⟨.vshufp .pd .x0 .x1 0x1, 5⟩ s_shufp).getXmm .x0)
      = ((step ⟨.vshufp .pd .x0 .x1 0xFD, 5⟩ s_shufp).getXmm .x0) := by decide

/-- ⚠️ ...AND `shufps` READS ALL EIGHT, which is the other half of that claim and
what stops the sentence above reading as a fact about shuffles in general. -/
theorem shufps_reads_the_whole_immediate :
    ((step ⟨.vshufp .ps .x0 .x1 0x1b, 4⟩ s_shufp).getXmm .x0)
      ≠ ((step ⟨.vshufp .ps .x0 .x1 0xdb, 4⟩ s_shufp).getXmm .x0) := by decide

end X86.Tests
