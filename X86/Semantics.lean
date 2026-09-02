/-
# X86.Semantics — `step : Instr → Cpu → Cpu`

Plan v1 §3.0: a definitional, executable, SMALL-STEP OPERATIONAL semantics.
Each form is a TOTAL state transformer.  Totality is not achieved by inventing
behaviour: an instruction this model declines to give a meaning to sets `Cpu.ms`
and changes nothing else (the ACL2 x86isa model-state discipline).

WHAT MAKES IT AN INTERPRETER RATHER THAN A RELATION: `step` computes, so the
same definition that the theorems are about is the one the differential harness
RUNS against ACL2 x86isa and (P1) against real hardware.  A relational or
axiomatic semantics could not be differentially tested at all, and a separate
executable "reference" would be a second model to keep honest.

WHERE HOARE LOGIC LIVES: on top, never underneath.  The characterization lemmas
in `X86/Theorems.lean` have the shape `step i s = { s with … }`, which is
exactly what a machine-code Hoare triple (Myreen's `SPEC`) or a big-step block
semantics consumes.  Every such rule is a THEOREM about `step`, so any logic
layered on it is sound by construction.

⚠️ THE ORACLE DRAW ORDER IS PART OF THE MODEL.  A shift with a non-zero masked
count draws exactly THREE bits, in the order CF, OF, AF, whether or not each is
needed; the logic group draws exactly ONE (AF).  Fixing the COUNT as well as the
order is what makes the oracle cursor a deterministic function of the
instruction stream, which is what lets the harness replay a run.

LANE. Personal lane, public sources only.  SDM read per instruction, cited at
each case.
-/
import X86.Flags

namespace X86

/-- The effective address of a memory operand.  All arithmetic is `BitVec 64`,
so it wraps at 2^64 exactly as 64-bit-mode address computation does.
`nextRip` is the address of the FOLLOWING instruction, which is what
RIP-relative addressing is defined against (SDM Vol. 2A §2.2.1.6). -/
def Ea.addr (ea : Ea) (s : Cpu) (nextRip : BitVec 64) : Val :=
  if ea.ripRel then nextRip + ea.disp
  else
    let b := match ea.base with | some r => s.regs.get r | none => 0
    let i := match ea.index with | some r => s.regs.get r * ea.scale.toVal | none => 0
    b + i + ea.disp

/-- CANONICAL ADDRESS (SDM Vol. 1 §3.3.7.1).  In 64-bit mode only the low 48
bits of a linear address are implemented; bits 63:48 must be a sign extension of
bit 47.  A branch to a non-canonical target raises #GP(0) (SDM Vol. 2A, JMP and
CALL, "64-Bit Mode Exceptions").

⭐ THIS PREDICATE EXISTS BECAUSE THE DIFFERENTIAL RUN FOUND ITS ABSENCE.  The
first run against ACL2 x86isa produced 80 unexplained disagreements, every one
of them an indirect `jmp` or `call` to a non-canonical target: this model set
RIP to it, and x86isa raised #GP.  No anchor and no characterization theorem
could have caught that — the model was self-consistently wrong, which is exactly
the failure a second model is for. -/
def canonical (v : BitVec 64) : Bool :=
  -- bits 63:47 are all equal: shifting them down leaves all-zeros or all-ones
  (v >>> 47) == 0 || (v >>> 47) == 0x1FFFF

namespace Cpu

/-- Set RIP to a branch target, CHECKING that the target is canonical.

A non-canonical target HALTS this model rather than raising #GP, because
exceptions need the fault machinery that system mode brings and system mode is a
v0.x non-goal (plan v1 §1).  Halting is the honest answer: the model declines to
say what happens, which is different from — and much safer than — quietly
jumping somewhere impossible.

⚠️ NAMED GAP, since it is now the only unchecked RIP write: the FALL-THROUGH
`rip + len` is not checked.  x86isa checks it too (`:rip-increment-error`).  It
is unreachable in the P0 vectors (RIP is 0x400000 and instructions are short) so
the differential run has not exercised it, and an unexercised fix is a guess —
it is recorded in docs/DECISIONS.md as a P1 item rather than written blind. -/
def setRipChecked (s : Cpu) (v : BitVec 64) : Cpu :=
  if canonical v then { s with rip := v }
  else s.halt (.unimplemented "non-canonical branch target (#GP(0) in hardware)")

/-- Read an operand at width `sz`. -/
def readOperand (s : Cpu) (sz : Size) (nextRip : BitVec 64) : Operand → Val
  | .reg r h8 => s.getReg sz r h8
  | .mem ea => s.readMem sz (ea.addr s nextRip)
  | .imm v => Value.trunc sz v

/-- Write an operand at width `sz`.  An immediate destination cannot be
encoded, so it stops the model rather than being silently dropped. -/
def writeOperand (s : Cpu) (sz : Size) (nextRip : BitVec 64) : Operand → Val → Cpu
  | .reg r h8, v => s.setReg sz r v h8
  | .mem ea, v => s.writeMem sz (ea.addr s nextRip) v
  | .imm _, _ => s.halt (.illegalOperands "immediate destination")

/-- Draw `n` oracle bits at once, in order, as a list.  Used so a case can name
its draws positionally and the COUNT is visible at the call site. -/
def undefBits (s : Cpu) : Nat → List Bool × Cpu
  | 0 => ([], s)
  | n + 1 =>
    let (b, s₁) := s.undefBit
    let (bs, s₂) := s₁.undefBits n
    (b :: bs, s₂)

end Cpu

/-- Two memory operands cannot be encoded in one instruction: there is one
ModR/M byte (SDM Vol. 2A §2.1.5). -/
def wellFormed2 (dst src : Operand) : Bool := !(dst.isMem && src.isMem)

namespace Cpu

/-- The stack pointer, and the two stack primitives.  In 64-bit mode the stack
pointer moves by the OPERAND size (SDM Vol. 2A, PUSH: "in 64-bit mode the
default operand size is 64 bits"), which is why `sz` is threaded rather than
assumed. -/
def push (s : Cpu) (sz : Size) (v : Val) : Cpu :=
  let sp := s.regs.get .rsp - BitVec.ofNat 64 sz.bytes
  (s.writeMem sz sp v).setReg .q .rsp sp

def popValue (s : Cpu) (sz : Size) : Val × Cpu :=
  let sp := s.regs.get .rsp
  let v := s.readMem sz sp
  (v, s.setReg .q .rsp (sp + BitVec.ofNat 64 sz.bytes))

end Cpu

/-- The small-step transition.  A stopped model does not move. -/
def step (i : Instr) (s : Cpu) : Cpu :=
  if s.stopped then s else
  -- the address of the NEXT instruction: what RIP-relative addressing and every
  -- relative branch are defined against.
  let nr : BitVec 64 := s.rip + BitVec.ofNat 64 i.len
  match i.op with

  -- MOV (SDM Vol. 2A, MOV): "Flags Affected: None."
  | .mov sz dst src =>
      if !wellFormed2 dst src then s.halt (.illegalOperands "mov: two memory operands")
      else
        let v := s.readOperand sz nr src
        (s.writeOperand sz nr dst v).setRip nr

  -- ADD SUB AND OR XOR CMP TEST (SDM Vol. 2A, each entry's "Flags Affected").
  | .bin k sz dst src =>
      if !wellFormed2 dst src then s.halt (.illegalOperands "two memory operands")
      else
        let a := s.readOperand sz nr dst
        let b := s.readOperand sz nr src
        match k with
        | .add =>
            let res := Flags.addResult sz a b
            let s := s.setFlags (Flags.add sz a b s.flags)
            (s.writeOperand sz nr dst res).setRip nr
        | .sub =>
            let res := Flags.subResult sz a b
            let s := s.setFlags (Flags.sub sz a b s.flags)
            (s.writeOperand sz nr dst res).setRip nr
        -- ADC / SBB (SDM Vol. 2A).  ⚠️ The carry is read from the INCOMING
        -- flags, before any of them are written: `s.flags.cf`, not the flags of
        -- the state being built.  Reading it after would make the instruction
        -- depend on its own output.
        | .adc =>
            let cin := s.flags.cf
            let res := Flags.adcResult sz a b cin
            let s := s.setFlags (Flags.adc sz a b cin s.flags)
            (s.writeOperand sz nr dst res).setRip nr
        | .sbb =>
            let cin := s.flags.cf
            let res := Flags.sbbResult sz a b cin
            let s := s.setFlags (Flags.sbb sz a b cin s.flags)
            (s.writeOperand sz nr dst res).setRip nr
        -- CMP is SUB with the result DISCARDED (SDM Vol. 2A, CMP).
        | .cmp =>
            (s.setFlags (Flags.sub sz a b s.flags)).setRip nr
        | .and =>
            let res := Value.trunc sz (a &&& b)
            let (afU, s) := s.undefBit          -- SDM: "the AF flag is undefined"
            let s := s.setFlags (Flags.logic sz res afU s.flags)
            (s.writeOperand sz nr dst res).setRip nr
        | .or =>
            let res := Value.trunc sz (a ||| b)
            let (afU, s) := s.undefBit
            let s := s.setFlags (Flags.logic sz res afU s.flags)
            (s.writeOperand sz nr dst res).setRip nr
        | .xor =>
            let res := Value.trunc sz (a ^^^ b)
            let (afU, s) := s.undefBit
            let s := s.setFlags (Flags.logic sz res afU s.flags)
            (s.writeOperand sz nr dst res).setRip nr
        -- TEST is AND with the result DISCARDED (SDM Vol. 2A, TEST).
        | .test =>
            let res := Value.trunc sz (a &&& b)
            let (afU, s) := s.undefBit
            (s.setFlags (Flags.logic sz res afU s.flags)).setRip nr

  -- INC DEC NEG NOT (SDM Vol. 2A; note INC/DEC do NOT touch CF, and NOT touches
  -- no flag at all).
  | .un k sz dst =>
      let a := s.readOperand sz nr dst
      match k with
      | .inc =>
          let res := Flags.addResult sz a 1
          let s := s.setFlags (Flags.inc sz a s.flags)
          (s.writeOperand sz nr dst res).setRip nr
      | .dec =>
          let res := Flags.subResult sz a 1
          let s := s.setFlags (Flags.dec sz a s.flags)
          (s.writeOperand sz nr dst res).setRip nr
      | .neg =>
          let res := Flags.subResult sz 0 a
          let s := s.setFlags (Flags.neg sz a s.flags)
          (s.writeOperand sz nr dst res).setRip nr
      | .not =>
          -- SDM Vol. 2A, NOT: "Flags Affected: None."
          let res := Value.trunc sz (~~~a)
          (s.writeOperand sz nr dst res).setRip nr

  -- SHL SHR (SDM Vol. 2A).  Count 0 (AFTER masking) affects no flag.
  | .shift k sz dst amt =>
      let cnt : BitVec 8 :=
        match amt with
        | .imm8 v => v
        | .cl => (s.getReg .b .rcx).setWidth 8
      let n := Flags.shiftCount sz cnt
      let a := s.readOperand sz nr dst
      let res : Val :=
        match k with
        | .shl => Value.trunc sz (a <<< n)
        | .shr => (Value.trunc sz a) >>> n
        -- SAR (SDM Vol. 2A, SAL/SAR/SHL/SHR): the vacated bits take the SIGN.
        | .sar => Value.sar sz a n
      if n = 0 then
        -- "If the count is 0, the flags are not affected."  The destination is
        -- still written back (the instruction is a read-modify-write), with the
        -- value it already had.
        (s.writeOperand sz nr dst res).setRip nr
      else
        -- THREE draws, in the fixed order CF, OF, AF.  See the file header.
        let (cfU, s) := s.undefBit
        let (ofU, s) := s.undefBit
        let (afU, s) := s.undefBit
        let s := s.setFlags (Flags.shiftFlags k sz a res n cfU ofU afU s.flags)
        (s.writeOperand sz nr dst res).setRip nr

  -- ROL ROR RCL RCR (SDM Vol. 2A).  ONE oracle draw (OF) whenever the masked
  -- count is non-zero, drawn whether or not it is needed — the same discipline
  -- the shifts follow, and for the same reason: the cursor must be a function
  -- of the instruction stream alone.  A masked count of zero touches nothing.
  | .rot k sz dst amt =>
      let cnt : BitVec 8 :=
        match amt with
        | .imm8 v => v
        | .cl => (s.getReg .b .rcx).setWidth 8
      let n := Flags.rotMasked sz cnt
      let t := Flags.rotReduced k sz n
      let a := s.readOperand sz nr dst
      let res := Flags.rotResult k sz a s.flags.cf t
      if n = 0 then
        (s.writeOperand sz nr dst res).setRip nr
      else
        let (ofU, s) := s.undefBit
        let s := s.setFlags (Flags.rotFlags k sz a res n t ofU s.flags)
        (s.writeOperand sz nr dst res).setRip nr

  -- BT / BTS / BTR / BTC (SDM Vol. 2A).  ⚠️ ZF IS THE ONLY ARITHMETIC FLAG THAT
  -- SURVIVES: "the ZF flag is unaffected... the OF, SF, AF and PF flags are
  -- undefined".  Four oracle draws, in the fixed order PF, AF, SF, OF.
  --
  -- ⛔ NAMED GAP: the MEMORY destination with a REGISTER offset is not here.
  -- That shape is not a bit within the addressed operand — it is an index into
  -- a BIT STRING, signed, reaching outside the operand entirely, and the
  -- effective address moves with it.  Modelling it is a real piece of work and
  -- guessing at it would be worse than declining, so the four `m,r` forms of
  -- roster family 31/41 are NOT claimed (docs/DECISIONS.md D23).  The forms
  -- here take the offset MODULO the operand width, which is what the SDM
  -- specifies for a register destination and for an immediate offset.
  | .bit k sz dst off =>
      let a := s.readOperand sz nr dst
      let n := (s.readOperand sz nr off).toNat % sz.bits
      let bit := a.getLsbD n
      let res : Val :=
        match k with
        | .bt  => a
        | .bts => Value.trunc sz (a ||| (BitVec.ofNat 64 1 <<< n))
        | .btr => Value.trunc sz (a &&& ~~~(BitVec.ofNat 64 1 <<< n))
        | .btc => Value.trunc sz (a ^^^ (BitVec.ofNat 64 1 <<< n))
      let (pfU, s) := s.undefBit
      let (afU, s) := s.undefBit
      let (sfU, s) := s.undefBit
      let (ofU, s) := s.undefBit
      let s := s.setFlags { s.flags with
        cf := bit, pf := pfU, af := afU, sf := sfU, of := ofU }
      match k with
      -- BT writes nothing, exactly as `cmp` does.
      | .bt => s.setRip nr
      | _ => (s.writeOperand sz nr dst res).setRip nr

  -- LEA (SDM Vol. 2A, LEA): computes the effective address and writes it under
  -- the ordinary register-width rules, so `lea eax, [...]` zero-extends.
  -- "Flags Affected: None."
  | .lea sz dst ea =>
      ((s.setReg sz dst (ea.addr s nr)).setRip nr)

  -- PUSH POP (SDM Vol. 2A).  "Flags Affected: None."
  | .push sz src =>
      -- the value is read BEFORE RSP moves, so `push rsp` pushes the OLD RSP.
      let v := s.readOperand sz nr src
      (s.push sz v).setRip nr
  | .pop sz dst =>
      -- RSP is incremented BEFORE the destination's effective address is
      -- computed (SDM Vol. 2A, POP: the address is computed after the
      -- increment), and a `pop rsp` therefore ends with the LOADED value.
      let (v, s) := s.popValue sz
      (s.writeOperand sz nr dst v).setRip nr

  -- JMP Jcc CALL (SDM Vol. 2A).  "Flags Affected: None" for all three.
  | .jmp t =>
      match t with
      | .rel d => s.setRipChecked (nr + d)
      | .indirect o => s.setRipChecked (s.readOperand .q nr o)
  | .jcc c d =>
      if c.eval s.flags then s.setRipChecked (nr + d) else s.setRip nr
  -- JRCXZ / JECXZ (SDM Vol. 2A, JCC).  ⚠️ THE ONLY BRANCH WHOSE CONDITION IS A
  -- REGISTER, and the width of the register it reads is what the address-size
  -- prefix selects: `jecxz` tests ECX — the LOW 32 BITS — and `jrcxz` tests all
  -- of RCX.  A model that read the same width for both is wrong exactly when
  -- RCX's upper half is non-zero and its lower half is zero, which is one point
  -- in the state space and is this batch's planted hard half.
  -- "Flags Affected: None."
  | .jcxz addr32 d =>
      let c := if addr32 then Value.trunc .d (s.regs.get .rcx) else s.regs.get .rcx
      if c == 0 then s.setRipChecked (nr + d) else s.setRip nr
  -- SETcc (SDM Vol. 2A, SETcc): ONE BYTE, 1 or 0.  "Flags Affected: None."
  | .setcc c dst =>
      (s.writeOperand .b nr dst (if c.eval s.flags then 1 else 0)).setRip nr

  -- CMOVcc (SDM Vol. 2A, CMOVcc).  ⚠️ THE WRITE IS UNCONDITIONAL; only the
  -- VALUE is conditional.  On a false condition the destination is rewritten
  -- with what it already held — which is a no-op at widths w and q and is NOT
  -- one at width d, where the write zero-extends and clears the upper half
  -- (SDM Vol. 1 §3.4.1.1).  Writing this as "if the condition holds, move" is
  -- the natural mistake and it is wrong on exactly the 32-bit forms.
  | .cmov c sz dst src =>
      let v := if c.eval s.flags then s.readOperand sz nr src else s.getReg sz dst
      ((s.setReg sz dst v).setRip nr)

  -- ══ P1 BATCH 10 ═══════════════════════════════════════════════════════
  -- The width-changing and two-destination moves.  NOT ONE OF THEM TOUCHES A
  -- FLAG (SDM Vol. 2A: "Flags Affected: None" on every entry in this block), so
  -- there is not one oracle draw in the whole batch — which makes every
  -- disagreement it can produce a DATA-path disagreement.

  -- MOVZX / MOVSX / MOVSXD (SDM Vol. 2A).  Read at `ssz`, extend to 64, write
  -- at `dsz` under the ordinary register-width rules.  The write is what makes
  -- `movzbl` clear the upper half of RAX and `movzbw` preserve it: the
  -- extension is the same computation in both, and `setReg dsz` is the only
  -- thing that differs.
  | .movx k dsz ssz dst src =>
      let v := s.readOperand ssz nr src
      let e := match k with
        | .zero => Value.zext ssz v
        | .sign => Value.sext ssz v
      ((s.setReg dsz dst e).setRip nr)

  -- CBW/CWDE/CDQE and CWD/CDQ/CQO (SDM Vol. 2A).  ⚠️ THE SECOND TRIO IS THE
  -- FIRST THING IN THIS MODEL TO WRITE A REGISTER OTHER THAN THE ONE ITS
  -- OPERANDS NAME: it fills rDX with the accumulator's sign and leaves the
  -- accumulator alone.  And `cltd`'s write is 32 bits wide, so it CLEARS
  -- RDX's upper half — invisible unless the pre-state put something there,
  -- which is why `mkPre` now gives RDX a value (docs/DECISIONS.md D26).
  | .cext k =>
      let a := s.regs.get .rax
      match k with
      | .cbw  => ((s.setReg .w .rax (Value.sext .b a)).setRip nr)
      | .cwde => ((s.setReg .d .rax (Value.sext .w a)).setRip nr)
      | .cdqe => ((s.setReg .q .rax (Value.sext .d a)).setRip nr)
      | .cwd  => ((s.setReg .w .rdx (if Value.msb .w a then Size.mask .w else 0)).setRip nr)
      | .cdq  => ((s.setReg .d .rdx (if Value.msb .d a then Size.mask .d else 0)).setRip nr)
      | .cqo  => ((s.setReg .q .rdx (if Value.msb .q a then Size.mask .q else 0)).setRip nr)

  -- XCHG (SDM Vol. 2A).  ⚠️ BOTH VALUES ARE READ BEFORE EITHER IS WRITTEN.
  -- With two distinct registers the order does not matter; with the SAME
  -- register twice it is the difference between a swap and a clobber, and with
  -- a memory operand whose base is the other operand it would be the difference
  -- between the old address and the new one.  Reading first costs one `let` and
  -- removes the question.
  --
  -- ⛔ A MEMORY OR IMMEDIATE OPERAND IS REFUSED, not approximated.  `xchg` with
  -- a memory operand asserts LOCK unconditionally (SDM Vol. 2A, XCHG) — an
  -- atomicity claim a single-threaded model cannot make — and an immediate
  -- cannot be a destination at all.  D25.
  | .xchg sz a b =>
      if a.isMem || b.isMem then
        s.halt (.unimplemented "xchg with a memory operand (implicit LOCK)")
      else if a.isImm || b.isImm then
        s.halt (.illegalOperands "xchg: immediate operand")
      else
        let va := s.readOperand sz nr a
        let vb := s.readOperand sz nr b
        let s := s.writeOperand sz nr a vb
        ((s.writeOperand sz nr b va).setRip nr)

  -- BSWAP (SDM Vol. 2A).  ⛔ "the result of BSWAP with a 16-bit operand size is
  -- undefined" — so this model REFUSES `.b` and `.w` rather than answering.
  -- The undefined-bit oracle is the wrong instrument here: it says "this model
  -- declines to commit to these BITS", and what the SDM declines to define is
  -- the whole RESULT.  D25.
  | .bswap sz dst =>
      match sz with
      | .d | .q => ((s.setReg sz dst (Value.bswap sz (s.getReg sz dst))).setRip nr)
      | _ => s.halt (.unimplemented "bswap at a 16-bit or 8-bit operand size (SDM: undefined)")

  -- ══ P1 BATCH 11 ═══════════════════════════════════════════════════════
  -- The loop group and the flag-control singles.  Between them they are the
  -- batch's whole shape: the loops write a REGISTER and read a flag but write
  -- none, and the flag-control singles write ONE FLAG BIT and nothing else.

  -- LOOP / LOOPE / LOOPNE (SDM Vol. 2A, LOOP/LOOPcc).  "Flags Affected: None."
  --
  -- ⚠️ THE ORDER IS DECREMENT, THEN TEST, AND THE WRITE-BACK IS UNCONDITIONAL.
  -- ACL2 x86isa's `x86-loop` writes the decremented counter on BOTH the taken
  -- and the not-taken path, and its branch condition reads the DECREMENTED
  -- value; the SDM says the same ("Each time the LOOP instruction is executed,
  -- the count register is decremented, then checked for 0").  A model that
  -- tested the incoming counter is wrong at exactly two points — a counter of 1
  -- (which must FALL THROUGH after decrementing to 0) and a counter of 0 (which
  -- must BRANCH, having wrapped to all-ones) — and right everywhere else.
  --
  -- ⚠️ AND `addr32` IS A WIDTH ON BOTH THE READ AND THE WRITE.  With the prefix
  -- the counter is ECX, the decrement wraps at 32 bits, and the write-back
  -- zero-extends and clears RCX's upper half.  Reading ECX but writing RCX — or
  -- writing 32 bits but wrapping at 64 — are both invisible unless the upper
  -- half is non-zero AND the low half is at its boundary.
  | .loop k addr32 d =>
      let sz : Size := if addr32 then .d else .q
      -- ZF is read from the INCOMING flags; nothing here writes a flag, but the
      -- counter write-back is sequenced first below, so naming it now is what
      -- makes the independence explicit rather than accidental.
      let zf := s.flags.zf
      let cnt := s.getReg sz .rcx
      let cnt' := Value.trunc sz (cnt - 1)
      -- the write-back happens on BOTH paths, so it is sequenced before the test
      let s := s.setReg sz .rcx cnt'
      let taken :=
        match k with
        | .loop   => cnt' != 0
        | .loope  => cnt' != 0 && zf
        | .loopne => cnt' != 0 && !zf
      if taken then s.setRipChecked (nr + d) else s.setRip nr

  -- CLC / STC / CMC / CLD / STD (SDM Vol. 2A).  Each writes ONE flag; "all
  -- other flags are unaffected" (ACL2 x86isa `x86-cmc/clc/stc/cld/std` says the
  -- same, one `!flgi` per opcode).  ⭐ `cld` and `std` are the ONLY writers of
  -- `df` in this model, and `df` is the one flag the comparator has been
  -- diffing since P0 with nothing able to move it.  D27.
  | .flagop k =>
      let f := s.flags
      let f := match k with
        | .clc => { f with cf := false }
        | .stc => { f with cf := true }
        | .cmc => { f with cf := !f.cf }
        | .cld => { f with df := false }
        | .std => { f with df := true }
      (s.setFlags f).setRip nr

  -- ── P1 BATCH 12 ───────────────────────────────────────────────────────────
  -- NOP (SDM Vol. 2A).  "Flags Affected: None", no register altered, and — for
  -- the multi-byte form — "does not issue a memory operation".  ⚠️ THE OPERAND
  -- IS DELIBERATELY NOT READ.  `nop (%rbx)` must not fault, must not touch the
  -- watched window, and must not depend on what the window holds; reading it
  -- "harmlessly" would still be wrong, because a read from an unmapped page is
  -- a fault in hardware and the whole point of the form is that it is inert.
  | .nop _ => s.setRip nr

  -- UD2 (SDM Vol. 2A): "Generates an invalid opcode exception."  ⭐ THIS IS THE
  -- ONE HALT THAT IS A MODELLED ANSWER RATHER THAN A DECLINED ONE, which is why
  -- it carries `byDesign` and not `unimplemented`: the record's `refused=1` says
  -- the same thing x86isa's `#UD` fault says, and the two models AGREE.
  | .ud2 => s.halt (.byDesign "ud2: #UD is the instruction's meaning")

  -- RET near (SDM Vol. 2A, RET).  "Flags Affected: None."
  --
  -- ⚠️ THE CANONICAL CHECK COMES FIRST, AND RSP DOES NOT MOVE IF IT FAILS —
  -- the same discipline `call` was forced into by its first differential run.
  -- x86isa raises #GP(0) on the target before committing the pop, so a refused
  -- `retq` that had already incremented RSP would disagree on `rsp` as well as
  -- on `rip`, and the disagreement on `rsp` is the one that says the ORDER is
  -- observable rather than an implementation detail.
  | .ret =>
      let sp := s.regs.get .rsp
      let tgt := s.readMem .q sp
      if canonical tgt then
        { s.setReg .q .rsp (sp + 8) with rip := tgt }
      else s.halt (.unimplemented "non-canonical return address (#GP(0) in hardware)")

  -- LEAVE (SDM Vol. 2A): "Set RSP to RBP, then POP RBP."  Written as those two
  -- steps in that order rather than as one closed form, because the order is
  -- the instruction: the POP reads from the NEW RSP (that is, from RBP), and a
  -- model that popped first would read the caller's stack instead of the
  -- frame's.  "Flags Affected: None."
  | .leave =>
      let s := s.setReg .q .rsp (s.regs.get .rbp)
      let (v, s) := s.popValue .q
      (s.setReg .q .rbp v).setRip nr

  | .call t =>
      match t with
      | .rel d =>
          -- ⚠️ THE CHECK COMES FIRST.  x86isa raises #GP(0) BEFORE the return
          -- address is pushed, so a refused call must not have pushed either —
          -- the first run disagreed on `rsp` and on the stack window as well as
          -- on `rip`, which is what says the ordering is observable and not a
          -- detail.
          if canonical (nr + d) then (s.push .q nr).setRip (nr + d)
          else s.halt (.unimplemented "non-canonical branch target (#GP(0) in hardware)")
      | .indirect o =>
          -- the target is read BEFORE the return address is pushed, so a
          -- `call [rsp]` reads the pre-push stack.
          let tgt := s.readOperand .q nr o
          if canonical tgt then (s.push .q nr).setRip tgt
          else s.halt (.unimplemented "non-canonical branch target (#GP(0) in hardware)")

/-- Run `n` steps of a straight-line list of decoded instructions, taking each
in order.  P0 does not fetch-and-decode from memory (that is P4's Lean decoder);
this is the shape the differential harness drives. -/
def run (is : List Instr) (s : Cpu) : Cpu := is.foldl (fun s i => step i s) s

@[simp] theorem run_nil (s : Cpu) : run [] s = s := rfl
@[simp] theorem run_cons (i : Instr) (is : List Instr) (s : Cpu) :
    run (i :: is) s = run is (step i s) := rfl

/-- A stopped model does not move: the property that makes `Cpu.ms` a real
halt rather than a flag nobody honours. -/
@[simp] theorem step_stopped (i : Instr) (s : Cpu) (h : s.stopped = true) :
    step i s = s := by simp [step, h]

end X86
