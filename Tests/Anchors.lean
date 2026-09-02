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

/-! ## Totality: a form no encoding can express STOPS the model -/

theorem two_memory_operands_halt :
    (step ⟨.mov .q (.mem { base := some .rax }) (.mem { base := some .rbx }), 3⟩ (mk {})).ms
      = some (.illegalOperands "mov: two memory operands") := by decide

theorem stopped_model_does_not_move :
    (step ⟨.mov .q (.reg .rax) (.imm 5), 3⟩
      { (mk { rax := 1 }) with ms := some (.unimplemented "x") }).regs.rax = 1 := by decide

end X86.Tests
