/-
# X86.Effects — the instruction library a compiler lowers to (vir's C3 (a), STATUS-paris row 64)

vir's compiler object (`object-COMPILER/OBJECT-COMPILER.md` at vir a5edcc7, §3) asks x86lean for effect
equations in the `{ s with … }` form for: mov (sizes 8 and 64), movzx byte loads, lea, add, sub, and, or,
xor, shl, shr, cmp, test, jcc, jmp, call, ret, imul and setcc. Every one of those mnemonics has a row in
`docs/COVERAGE.md`, so this file adds PROOFS only and no differential work.

`X86/Theorems.lean` already proves most of the list. This file adds the ones it lacks (the census, by statement
shape, at master a370c1c):
- `stepP_of_at`: the lift from `step` to `stepP` at a fetched address, so a block proof needs one lemma rather
  than one lifted copy per form (`Program.lean` carries five such copies);
- `step_add_reg_op` (add r,imm · r,m · r,r with the high-8 destination); only `add r,r` existed;
- `step_test_reg_op` (test r,imm · r,m); only `test r,r` existed;
- `step_imulr` (imul r,r · r,m · r,r,imm · r,m,imm); only a refusal and a frame lemma existed;
- `step_setcc_reg` and `step_setcc_mem`; nothing existed.

⚠️ IMUL IS T-FRAME: SF, ZF, AF and PF are undefined after it (SDM Vol. 2A IMUL) and the model draws all four from
the undefined-bit oracle. The equation states those four draws, so a proof that branches on one of those flags
after an imul has to carry an oracle bit, and a compiler that wants a defined flag must not read one there.

LANE. Personal lane, public sources only. Every theorem here rests on the three standard axioms at most (the axiom
gate enumerates this module through `X86.lean`).
-/
import X86.Theorems
import X86.Program

namespace X86

variable {s : Cpu} {len : Nat}

-- The same local simp set `X86/Theorems.lean` declares (its line 47): `Live s` is `s.ms = none`, and the guard
-- in `step` reads `s.stopped`, so `stopped` must unfold for `h` to close the halted branch.
attribute [local simp] Cpu.stopped Cpu.readOperand Cpu.writeOperand Cpu.setReg

/-- **THE LIFT.** A live state whose `rip` fetches `i` steps by `step i`. A block proof composes per-instruction
equations through this one lemma. -/
theorem stepP_of_at {p : Program} {i : Instr} (hs : s.stopped = false) (hi : p.at? s.rip = some i) :
    stepP p s = step i s := by
  simp only [Cpu.stopped] at hs
  simp [stepP, hs, hi]

/-- **ADD r, op** (SDM Vol. 2A ADD): the `adc_reg_op` equation with no incoming carry. -/
theorem step_add_reg_op (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s)
    (hl : o.locked = false) :
    step ⟨.bin .add sz (.reg r h8) o, len⟩ s =
      { s with
        regs := s.regs.set r (if h8
          then Value.writeHigh8 (s.regs.get r)
            (Flags.addResult sz (s.getReg sz r h8)
              (s.readOperand sz (s.rip + BitVec.ofNat 64 len) o))
          else Value.writeView sz (s.regs.get r)
            (Flags.addResult sz (s.getReg sz r h8)
              (s.readOperand sz (s.rip + BitVec.ofNat 64 len) o))),
        flags := Flags.add sz (s.getReg sz r h8)
          (s.readOperand sz (s.rip + BitVec.ofNat 64 len) o) s.flags,
        rip := s.rip + BitVec.ofNat 64 len } := by
  cases h8 <;> cases o <;>
    simp [step, h, Cpu.getReg, hl, wellFormed2, Operand.isMem, Cpu.setFlags, Cpu.setRip] <;> simp_all

/-- **TEST r, op** (SDM Vol. 2A TEST): the flags of the AND, no register written, AF drawn (T-frame). -/
theorem step_test_reg_op (sz : Size) (r : GPR) (h8 : Bool) (o : Operand) (h : Live s)
    (hl : o.locked = false) :
    step ⟨.bin .test sz (.reg r h8) o, len⟩ s =
      { s with
        flags := Flags.logic sz
          (Value.trunc sz (s.getReg sz r h8 &&&
            s.readOperand sz (s.rip + BitVec.ofNat 64 len) o))
          (s.oracle.bits s.oracle.cursor) s.flags,
        oracle := { s.oracle with cursor := s.oracle.cursor + 1 },
        rip := s.rip + BitVec.ofNat 64 len } := by
  cases h8 <;> cases o <;>
    simp [step, h, Cpu.getReg, hl, wellFormed2, Operand.isMem, Cpu.setFlags, Cpu.setRip, Cpu.undefBit,
      Oracle.draw] <;> simp_all

/-- **SETcc r8** (SDM Vol. 2A SETcc): the low byte of `r` is 1 when the condition holds and 0 otherwise. -/
theorem step_setcc_reg (c : Cc) (r : GPR) (h : Live s) :
    step ⟨.setcc c (.reg r), len⟩ s =
      { s with
        regs := s.regs.set r (Value.writeView .b (s.regs.get r) (if c.eval s.flags then 1 else 0)),
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.writeOperand, Cpu.setReg, Cpu.setRip]

/-- **SETcc m8** (SDM Vol. 2A SETcc): one byte written at the effective address. -/
theorem step_setcc_mem (c : Cc) (ea : Ea) (h : Live s) (hl : ea.lock = false) :
    step ⟨.setcc c (.mem ea), len⟩ s =
      { s with
        mem := s.mem.writeSize .b (ea.addr s (s.rip + BitVec.ofNat 64 len)) (if c.eval s.flags then 1 else 0),
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, hl, Cpu.writeOperand, Cpu.writeMem, Cpu.setRip]

/-- **IMUL r, op[, imm]** (SDM Vol. 2A IMUL, the two- and three-operand forms, w/l/q): the low half of the
signed product into `dst`; CF = OF = the overflow; SF, ZF, AF, PF the four oracle draws, in that order. -/
theorem step_imulr (sz : Size) (dst : GPR) (src : Operand) (imm : Option Val) (h : Live s)
    (henc : imulrEncodable sz = true) (hl : src.locked = false) :
    step ⟨.imulr sz dst src imm, len⟩ s =
      let b := s.readOperand sz (s.rip + BitVec.ofNat 64 len) src
      let x := match imm with | none => s.getReg sz dst | some _ => b
      let y := match imm with | none => b | some i => Value.trunc sz i
      let c := s.oracle.cursor
      { s with
        regs := s.regs.set dst (Value.writeView sz (s.regs.get dst) (Value.imulPair sz x y).1),
        flags := Flags.mulFlags (Value.imulOverflow sz x y)
          (s.oracle.bits c) (s.oracle.bits (c + 1)) (s.oracle.bits (c + 2)) (s.oracle.bits (c + 3)) s.flags,
        oracle := { s.oracle with cursor := c + 4 },
        rip := s.rip + BitVec.ofNat 64 len } := by
  cases imm <;> cases src <;> simp_all [step, Cpu.undefBit, Oracle.draw, Cpu.setFlags, Cpu.setReg,
    Cpu.setRip, Nat.add_assoc]

/-- **IMUL's OF, as its own fact.** OF (and CF) after an imul are the overflow, DEFINED, so a checked multiply's
`jo` to an overflow exit needs no oracle bit. Stated separately so a block proof need not unfold `mulFlags`. -/
theorem step_imulr_of (sz : Size) (dst : GPR) (src : Operand) (imm : Option Val) (h : Live s)
    (henc : imulrEncodable sz = true) (hl : src.locked = false) :
    (step ⟨.imulr sz dst src imm, len⟩ s).flags.of =
      Value.imulOverflow sz
        (match imm with | none => s.getReg sz dst | some _ => s.readOperand sz (s.rip + BitVec.ofNat 64 len) src)
        (match imm with
          | none => s.readOperand sz (s.rip + BitVec.ofNat 64 len) src
          | some i => Value.trunc sz i) := by
  rw [step_imulr sz dst src imm h henc hl]
  cases imm <;> simp [Flags.mulFlags]

/-! ## (2) — A STRAIGHT-LINE BLOCK, AND ITS CONDITIONAL EXIT

A compiler's simulation step is a BLOCK: a list of instructions run in order, then either a fall-through or a `jcc`
to one exit. `BlockFetches p is s` says the run of `is` from `s` never stops early and fetches exactly `is`, in
order; under it, `runP` over the block IS the left fold of `step`, so each instruction's `{ s with … }` equation
rewrites the block one instruction at a time. The lemmas name no program. -/

/-- Running `is` from `s` fetches exactly `is`, in order, from states that have not stopped. -/
def BlockFetches (p : Program) : List Instr → Cpu → Prop
  | [], _ => True
  | i :: is, s => s.stopped = false ∧ p.at? s.rip = some i ∧ BlockFetches p is (step i s)

/-- The block's effect: `step` folded over its instructions. -/
def runBlock (is : List Instr) (s : Cpu) : Cpu := is.foldl (fun t i => step i t) s

@[simp] theorem runBlock_nil (s : Cpu) : runBlock [] s = s := rfl
@[simp] theorem runBlock_cons (i : Instr) (is : List Instr) (s : Cpu) :
    runBlock (i :: is) s = runBlock is (step i s) := rfl

/-- One fetched instruction, then the rest of the run. -/
theorem runP_succ_at {p : Program} {i : Instr} (n : Nat) (hs : s.stopped = false) (hi : p.at? s.rip = some i) :
    runP p (n + 1) s = runP p n (step i s) := by
  rw [runP_succ, stepP_of_at hs hi]

/-- **THE BLOCK LEMMA.** Under `BlockFetches`, `runP` over the block's length is `runBlock`. -/
theorem runP_block (p : Program) : ∀ (is : List Instr) (s : Cpu),
    BlockFetches p is s → runP p is.length s = runBlock is s
  | [], _, _ => rfl
  | i :: is, s, ⟨hs, hi, hrest⟩ => by
    rw [List.length_cons, runP_succ_at _ hs hi, runBlock_cons]
    exact runP_block p is (step i s) hrest

/-- **A BLOCK, THEN MORE.** The block's states are a prefix of the run: `n` more steps continue from its end. -/
theorem runP_block_then (p : Program) (is : List Instr) (s : Cpu) (n : Nat) (h : BlockFetches p is s) :
    runP p (is.length + n) s = runP p n (runBlock is s) := by
  rw [runP_add, runP_block p is s h]

/-- **THE CONDITIONAL EXIT.** A block ending in `jcc c d` lands at the jump target when `c` holds and at the next
instruction otherwise, with everything else as the block left it (`step_jcc`'s equation, composed). -/
theorem runP_block_jcc (p : Program) (is : List Instr) (c : Cc) (d : Val) (jlen : Nat) (s : Cpu)
    (h : BlockFetches p (is ++ [⟨.jcc c d, jlen⟩]) s) :
    runP p (is.length + 1) s = step ⟨.jcc c d, jlen⟩ (runBlock is s) := by
  have hb := runP_block p _ s h
  simp only [List.length_append, List.length_singleton] at hb
  rw [hb]
  simp [runBlock, List.foldl_append]

/-! ## (3) — CALL AND RET UNDER ONE CONVENTION

The convention is the hardware's own: `call rel` pushes the return address at `rsp - 8`, the body runs, and a `ret`
fetched with `rsp` back at that slot and the slot intact returns to the instruction after the call, with `rsp`
restored. What the body may do to the rest of memory is the CALLER's frame question, not this lemma's: a compiler
proves the slot intact from a disjointness premise (the stack region apart from every live cell), which its layout
discharges. That premise is a HYPOTHESIS here, through `hslot`, and is never assumed.

The 8-byte round trip it needs (`readSize_writeSize_q`) is a memory fact x86lean did not state. Its three byte
lemmas are ported, with their proofs, from vir's `bridge/VIRBridge/Mem.lean` (github.com/jyh/vir, master 9613d47;
`writeN_frame`, `writeN_in`, `readN_bytes`, `readN_writeN`), same author, Apache-2.0 like this repository. -/

/-- A store of `n` bytes at `a` leaves every byte outside its span as it was. -/
theorem writeN_frame (m : Mem) (a b v : BitVec 64) : ∀ n : Nat, (∀ j : Nat, j < n → a + BitVec.ofNat 64 j ≠ b) →
    (m.writeN a v n).read b = m.read b
  | 0, _ => rfl
  | n + 1, h => by
    show ((m.write a (v.setWidth 8)).writeN (a + 1) (v >>> 8) n).read b = m.read b
    rw [writeN_frame _ (a + 1) b (v >>> 8) n (fun j hj e => h (j + 1) (by omega) (by rw [← e]; bv_omega))]
    exact Mem.read_write_ne _ _ _ _ (fun e => h 0 (by omega) (by rw [e]; bv_omega))

/-- Inside its span (`n ≤ 8`), a store of `n` bytes reads back byte `k` of the value at `a + k`. -/
theorem writeN_in (m : Mem) : ∀ (n : Nat) (a v : BitVec 64) (k : Nat), k < n → n ≤ 8 →
    (m.writeN a v n).read (a + BitVec.ofNat 64 k) = (v >>> (8 * k)).setWidth 8
  | 0, _, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | n + 1, a, v, k, hk, hn => by
    show ((m.write a (v.setWidth 8)).writeN (a + 1) (v >>> 8) n).read (a + BitVec.ofNat 64 k) = _
    cases k with
    | zero =>
      rw [writeN_frame _ (a + 1) _ (v >>> 8) n (fun j hj e => by bv_omega),
        show a + BitVec.ofNat 64 0 = a by simp, Mem.read_write_same]
      simp
    | succ k =>
      rw [show a + BitVec.ofNat 64 (k + 1) = a + 1 + BitVec.ofNat 64 k by bv_omega,
        writeN_in _ n (a + 1) (v >>> 8) k (by omega) (by omega), ← BitVec.shiftRight_add]
      congr 2; omega

/-- A read of `n` bytes from a memory whose byte at `a + k` is `v`'s byte `k`: `v`'s low `8n` bits. -/
theorem readN_bytes (m : Mem) : ∀ (n : Nat) (a v : BitVec 64),
    (∀ k : Nat, k < n → m.read (a + BitVec.ofNat 64 k) = (v >>> (8 * k)).setWidth 8) →
    ∀ i : Nat, (m.readN a n).getLsbD i = (decide (i < 8 * n) && v.getLsbD i)
  | 0, _, _, _, i => by simp [Mem.readN]
  | n + 1, a, v, h, i => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, BitVec.ushiftRight_zero, BitVec.add_zero] at h0
    have ih := readN_bytes m n (a + 1) (v >>> 8) (fun k hk => by
      rw [show a + 1 + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (k + 1) by bv_omega, h (k + 1) (by omega),
        ← BitVec.shiftRight_add]
      congr 2; omega)
    show (((m.readN (a + 1) n) <<< 8) ||| (m.read a).setWidth 64).getLsbD i = _
    rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, h0, BitVec.getLsbD_setWidth]
    by_cases hi : i < 8
    · simp [hi, show i < 64 by omega, show i < 8 * (n + 1) by omega]
    · rw [ih (i - 8), BitVec.getLsbD_ushiftRight, show 8 + (i - 8) = i by omega]
      by_cases h64 : i < 64
      · simp [hi, h64, show (i - 8 < 8 * n) ↔ (i < 8 * (n + 1)) by omega]
      · simp [hi, h64, BitVec.getLsbD_of_ge v i (by omega)]

/-- **THE ROUND TRIP.** A quadword written at `a` reads back at `a`. -/
theorem readSize_writeSize_q (m : Mem) (a v : BitVec 64) : (m.writeSize .q a v).readSize .q a = v := by
  show (m.writeN a v 8).readN a 8 = v
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [readN_bytes _ 8 a v (fun k hk => writeN_in m 8 a v k hk (Nat.le_refl _)) i]
  simp [show i < 8 * 8 by omega]

/-- **CALL, BODY, RET.** From a `call rel d` at `s.rip`: if some run of the body from the post-call state reaches a
state `u` satisfying `B` that fetches a `ret`, with `rsp` back at the pushed slot and the slot still holding the
return address, then one more step returns to the instruction after the call with `rsp` restored, and memory,
flags and every other register are exactly as the body left them. -/
theorem call_ret {p : Program} {s : Cpu} {len rl : Nat} (d : Val) (B : Cpu → Prop)
    (hs : s.stopped = false) (hcall : p.at? s.rip = some ⟨.call (.rel d), len⟩)
    (hr : canonical (s.rip + BitVec.ofNat 64 len) = true)
    (hbody : ∃ n, B (runP p n (step ⟨.call (.rel d), len⟩ s)) ∧
      (runP p n (step ⟨.call (.rel d), len⟩ s)).stopped = false ∧
      p.at? (runP p n (step ⟨.call (.rel d), len⟩ s)).rip = some ⟨.ret, rl⟩ ∧
      (runP p n (step ⟨.call (.rel d), len⟩ s)).regs.get .rsp = s.regs.get .rsp - 8 ∧
      (runP p n (step ⟨.call (.rel d), len⟩ s)).mem.readSize .q (s.regs.get .rsp - 8) =
        s.rip + BitVec.ofNat 64 len) :
    ∃ n u, B u ∧ runP p n s =
      { u with regs := u.regs.set .rsp (s.regs.get .rsp), rip := s.rip + BitVec.ofNat 64 len } := by
  obtain ⟨n, hB, hus, hret, hrsp, hslot⟩ := hbody
  refine ⟨1 + n + 1, runP p n (step ⟨.call (.rel d), len⟩ s), hB, ?_⟩
  have hlive : Live (runP p n (step ⟨.call (.rel d), len⟩ s)) := live_of_not_stopped (by rw [hus]; exact Bool.false_ne_true)
  rw [runP_add, runP_add, show runP p 1 s = step ⟨.call (.rel d), len⟩ s by
      rw [runP_succ, runP_zero, stepP_of_at hs hcall], runP_succ, runP_zero, stepP_of_at hus hret,
    step_ret_taken hlive (by simp only [Cpu.readMem]; rw [hrsp, hslot]; exact hr)]
  simp only [Cpu.setReg, Cpu.readMem, hrsp, hslot, BitVec.sub_add_cancel]
  rfl

/-! ## (4) — THE DRIVER, MACHINE HALF

vir's C0 (a) driver is a fixed loop: call the compiled step, test its exit code, `jcc` to the exit, else jump back
to the head. The LOOP rule is already `Spec.loop` (X86/Logic.lean: an invariant and a `Nat` variant, no step
count). What a driver proof additionally needs is ONE ITERATION as a machine fact: the call returns (`call_ret`),
then the check block runs and its `jcc` decides (`runP_block_jcc`). `driver_iteration` is that composition and names
no program; the L2 half (that the step refines the L2 step relation, and the variant) is vir's, and feeds
`Spec.loop` through it. -/

/-- **ONE DRIVER ITERATION.** `call rel d`, the body (as in `call_ret`), then a check block `blk` ending in
`jcc c dj`: some run from the call is exactly that `jcc`'s step applied to the block's end, from the returned
state. With `step_jcc` it lands at the exit when `c` holds and at the instruction after the `jcc` otherwise. -/
theorem driver_iteration {p : Program} {s : Cpu} {len rl jlen : Nat} (d : Val) (B : Cpu → Prop)
    (blk : List Instr) (c : Cc) (dj : Val)
    (hs : s.stopped = false) (hcall : p.at? s.rip = some ⟨.call (.rel d), len⟩)
    (hr : canonical (s.rip + BitVec.ofNat 64 len) = true)
    (hbody : ∃ n, B (runP p n (step ⟨.call (.rel d), len⟩ s)) ∧
      (runP p n (step ⟨.call (.rel d), len⟩ s)).stopped = false ∧
      p.at? (runP p n (step ⟨.call (.rel d), len⟩ s)).rip = some ⟨.ret, rl⟩ ∧
      (runP p n (step ⟨.call (.rel d), len⟩ s)).regs.get .rsp = s.regs.get .rsp - 8 ∧
      (runP p n (step ⟨.call (.rel d), len⟩ s)).mem.readSize .q (s.regs.get .rsp - 8) =
        s.rip + BitVec.ofNat 64 len)
    (hblk : ∀ u, B u → BlockFetches p (blk ++ [⟨.jcc c dj, jlen⟩])
      { u with regs := u.regs.set .rsp (s.regs.get .rsp), rip := s.rip + BitVec.ofNat 64 len }) :
    ∃ n u, B u ∧ runP p n s = step ⟨.jcc c dj, jlen⟩
      (runBlock blk { u with regs := u.regs.set .rsp (s.regs.get .rsp), rip := s.rip + BitVec.ofNat 64 len }) := by
  obtain ⟨n, u, hB, hrun⟩ := call_ret d B hs hcall hr hbody
  refine ⟨n + (blk.length + 1), u, hB, ?_⟩
  rw [runP_add, hrun]
  exact runP_block_jcc p blk c dj jlen _ (hblk u hB)

end X86
