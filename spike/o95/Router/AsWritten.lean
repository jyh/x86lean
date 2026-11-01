/-
# Router.AsWritten — A.4 AS WRITTEN (E1 and E5 in their repaired forms per vir's errata and I6; E2 and E3 KEPT), and
P5's two witnesses. Written private as unpublished O94 content; published 2026-11-01 (SPIKE-PLAN.md).

The bytes are clang's for `asm/aswritten.s` (code at 0 there, at 0x1000 here; every branch is RIP-relative, so the
bytes do not move). Exits are the four labels just past the code. The program defines no instruction there, so
`runP` STOPS, and the exit is the `rip` it stopped at.

  0x1038 drop_truncated · 0x1039 drop_unauthorized · 0x103a drop_rate_limited · 0x103b emit_slice (the OK exit, I6)
-/
import X86

namespace Router
open X86

def accl : BitVec 64 := 0x301d      -- `leaq 0x2000(%rip),%r9` at 0x1016, length 7: next rip 0x101d
def bucketDisp : BitVec 64 := 0x3000

def asWritten : Program := { code := [
  (0x1000, ⟨.bin .cmp .q (.reg .rsi) (.imm 24), 4⟩),
  (0x1004, ⟨.jcc .l (BitVec.ofInt 64 0x32), 2⟩),                                   -- jl  drop_truncated (E2 KEPT)
  (0x1006, ⟨.mov .d (.reg .rax) (.mem { base := some .rdi }), 2⟩),
  (0x1008, ⟨.bin .cmp .d (.reg .rax) (.imm 0x4D534731), 5⟩),
  (0x100d, ⟨.jcc .ne (BitVec.ofInt 64 0x2a), 2⟩),                                  -- jne drop_unauthorized
  (0x100f, ⟨.mov .d (.reg .rcx) (.mem { base := some .rdi, disp := 4 }), 3⟩),
  (0x1012, ⟨.mov .d (.reg .r8) (.mem { base := some .rdi, disp := 8 }), 4⟩),
  (0x1016, ⟨.lea .q .r9 { ripRel := true, disp := 0x2000 }, 7⟩),                   -- E1 REPAIRED (vir errata)
  (0x101d, ⟨.bit .bt .q (.mem { base := some .r9, index := some .rcx, scale := .s8 }) (.reg .r8), 5⟩),
  (0x1022, ⟨.jcc .ae (BitVec.ofInt 64 0x15), 2⟩),                                  -- jnc drop_unauthorized
  (0x1024, ⟨.bin .sub .d (.mem { base := some .rdx, index := some .rcx, scale := .s4, disp := 0x3000 }) (.imm 1), 8⟩),
  (0x102c, ⟨.jcc .l (BitVec.ofInt 64 0x0c), 2⟩),                                   -- jl  drop_rate_limited (E3 KEPT)
  (0x102e, ⟨.lea .q .rax { base := some .rdi, disp := 24 }, 4⟩),
  (0x1032, ⟨.bin .sub .q (.reg .rsi) (.imm 24), 4⟩),                               -- E5 REPAIRED (I6)
  (0x1036, ⟨.jmp (.rel (BitVec.ofInt 64 0x03)), 2⟩)] }                             -- jmp emit_slice

/-- A start state: RIP at the routine, RDI the buffer, RSI its length, RDX the bucket array's base; the buffer's three
dwords (magic, sender, topic), the ACL byte that holds sender 0's topic bits, and sender 0's token count. -/
def start (len : BitVec 64) (magic sender topic aclByte tokens : BitVec 64) : Cpu :=
  let c : Cpu := { rip := 0x1000, oracle := Oracle.zero }
  let c := c.setReg .q .rdi 0x10000
  let c := c.setReg .q .rsi len
  let c := c.setReg .q .rdx 0x8000
  let c := c.writeMem .d 0x10000 magic
  let c := c.writeMem .d 0x10004 sender
  let c := c.writeMem .d 0x10008 topic
  let c := c.writeMem .b (accl + sender * 8) aclByte
  c.writeMem .d (0x8000 + bucketDisp + sender * 4) tokens

def MAGIC : BitVec 64 := 0x4D534731
def cell : BitVec 64 := 0x8000 + 0x3000      -- sender 0's bucket cell

/-! ### CONTROL FIRST: the OK path runs to `emit_slice` with I6's state. Without this, a witness below could be an
artifact of a mis-placed program (a wrong length moves every later address), so it is proved before them. -/
set_option maxRecDepth 20000 in
theorem ok_control :
    let t := runP asWritten 16 (start 100 MAGIC 0 0 1 5)
    t.stopped = true ∧ t.rip = 0x103b ∧ t.getReg .q .rax = 0x10000 + 24 ∧ t.getReg .q .rsi = 100 - 24
      ∧ t.readMem .d cell = 4 := by decide

/-! ### P5, E2: `len = 2^63` takes `jl` to drop_truncated, while F's guard `len(b0) ≥ 24` (UNSIGNED) passes -/
theorem e2_witness :
    let t := runP asWritten 3 (start 0x8000000000000000 MAGIC 0 0 1 5)
    t.stopped = true ∧ t.rip = 0x1038 ∧ (0x8000000000000000 : BitVec 64).toNat ≥ 24 := by decide

/-! ### P5, E3: tokens = 0 reaches drop_rate_limited with the bucket cell ALREADY written (0 → 0xFFFFFFFF), while I6
requires memory unchanged on every drop exit -/
set_option maxRecDepth 20000 in
theorem e3_witness :
    let t := runP asWritten 13 (start 100 MAGIC 0 0 1 0)
    t.stopped = true ∧ t.rip = 0x103a ∧ t.readMem .d cell = 0xFFFFFFFF
      ∧ (start 100 MAGIC 0 0 1 0).readMem .d cell = 0 := by decide

end Router
