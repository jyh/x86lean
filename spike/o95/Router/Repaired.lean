/-
# Router.Repaired — A.4 REPAIRED (E1, E2, E3, E5 all in their repaired forms) and its refinement against vir's
`F_exit` under I6. Written private as unpublished O94 content; published 2026-11-01 (SPIKE-PLAN.md).

The bytes are clang's for `asm/repaired.s` (code at 0 there, at 0x1000 here; every branch is RIP-relative).
The repairs against `Router.AsWritten`: `jb` for `jl` (E2: the length compared UNSIGNED), and the bucket TESTED
before it is written (E3: `cmpl $0` / `jle drop_rate_limited`, then `subl $1`). The data addresses do not move
(the `leaq` is still at 0x1016, so the ACL table is still at 0x301d).

  0x1040 drop_truncated · 0x1041 drop_unauthorized · 0x1042 drop_rate_limited · 0x1043 emit_slice (I6's OK exit)
-/
import Router.AsWritten

namespace Router
open X86

def repaired : Program := { code := [
  (0x1000, ⟨.bin .cmp .q (.reg .rsi) (.imm 24), 4⟩),
  (0x1004, ⟨.jcc .b (BitVec.ofInt 64 0x3a), 2⟩),                                   -- jb  drop_truncated (E2 REPAIRED)
  (0x1006, ⟨.mov .d (.reg .rax) (.mem { base := some .rdi }), 2⟩),
  (0x1008, ⟨.bin .cmp .d (.reg .rax) (.imm 0x4D534731), 5⟩),
  (0x100d, ⟨.jcc .ne (BitVec.ofInt 64 0x32), 2⟩),                                  -- jne drop_unauthorized
  (0x100f, ⟨.mov .d (.reg .rcx) (.mem { base := some .rdi, disp := 4 }), 3⟩),
  (0x1012, ⟨.mov .d (.reg .r8) (.mem { base := some .rdi, disp := 8 }), 4⟩),
  (0x1016, ⟨.lea .q .r9 { ripRel := true, disp := 0x2000 }, 7⟩),                   -- E1 REPAIRED (vir errata)
  (0x101d, ⟨.bit .bt .q (.mem { base := some .r9, index := some .rcx, scale := .s8 }) (.reg .r8), 5⟩),
  (0x1022, ⟨.jcc .ae (BitVec.ofInt 64 0x1d), 2⟩),                                  -- jnc drop_unauthorized
  (0x1024, ⟨.bin .cmp .d (.mem { base := some .rdx, index := some .rcx, scale := .s4, disp := 0x3000 }) (.imm 0), 8⟩),
  (0x102c, ⟨.jcc .le (BitVec.ofInt 64 0x14), 2⟩),                                  -- jle drop_rate_limited (E3 REPAIRED)
  (0x102e, ⟨.bin .sub .d (.mem { base := some .rdx, index := some .rcx, scale := .s4, disp := 0x3000 }) (.imm 1), 8⟩),
  (0x1036, ⟨.lea .q .rax { base := some .rdi, disp := 24 }, 4⟩),
  (0x103a, ⟨.bin .sub .q (.reg .rsi) (.imm 24), 4⟩),                               -- E5 REPAIRED (I6)
  (0x103e, ⟨.jmp (.rel (BitVec.ofInt 64 0x03)), 2⟩)] }                             -- jmp emit_slice

/-! ### CONTROLS FIRST, concrete, by `decide`: the OK path, and each of E2 and E3 now taking F's exit. -/
set_option maxRecDepth 20000 in
theorem rep_ok_control :
    let t := runP repaired 17 (start 100 MAGIC 0 0 1 5)
    t.stopped = true ∧ t.rip = 0x1043 ∧ t.getReg .q .rax = 0x10000 + 24 ∧ t.getReg .q .rsi = 100 - 24
      ∧ t.readMem .d cell = 4 := by decide

set_option maxRecDepth 20000 in
/-- E2 repaired: `len = 2^63` passes the length guard (F's `24 ≤ len` holds) and reaches emit_slice. -/
theorem rep_e2_control :
    let t := runP repaired 17 (start 0x8000000000000000 MAGIC 0 0 1 5)
    t.stopped = true ∧ t.rip = 0x1043 := by decide

set_option maxRecDepth 20000 in
/-- E3 repaired: tokens = 0 reaches drop_rate_limited with the cell UNWRITTEN (memory byte-identical). -/
theorem rep_e3_control :
    let s := start 100 MAGIC 0 0 1 0
    let t := runP repaired 13 s
    t.stopped = true ∧ t.rip = 0x1042 ∧ t.mem.bytes = s.mem.bytes := by decide

end Router
