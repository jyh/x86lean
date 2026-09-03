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

/-- P1 BATCH 14: BSF and BSR, which differ in ONE expression.

⭐ THEY ARE ONE FUNCTION BECAUSE EVERYTHING THAT IS SUBTLE ABOUT THEM IS SHARED:
five undefined flags drawn in a fixed order, ZF from the SOURCE, and the
UNDEFINED DESTINATION at a zero source.  `rev` selects which index the non-zero
case reports.  Writing the two arms out separately would have duplicated the
undefined-destination branch — the one thing in this batch that had never been
written before — and a duplicate born in agreement diverges on the next edit.

⚠️ It is also what lets the characterization theorems reduce: a combined
`| .bsf | .bsr =>` arm inside `step`'s match compiles to a matcher that does NOT
unfold for either constructor, so `step_bsf_zf` could not be proved through it. -/
def bitScanStep (rev : Bool) (sz : Size) (dst : GPR) (a : Val)
    (nr : BitVec 64) (s : Cpu) : Cpu :=
  let (cfU, s) := s.undefBit
  let (pfU, s) := s.undefBit
  let (afU, s) := s.undefBit
  let (sfU, s) := s.undefBit
  let (ofU, s) := s.undefBit
  let s := s.setFlags (Flags.bitScan sz a cfU pfU afU sfU ofU s.flags)
  if Value.isZero sz a then
    -- the SDM's "the content of the destination operand is undefined", drawn
    -- rather than invented.  `sz.bits` bits, so the draw is the operand's width.
    let (u, s) := s.undefVal sz.bits
    (s.setReg sz dst u).setRip nr
  else
    let idx := if rev then Value.bitScanReverse sz a else Value.bitScanForward sz a
    (s.setReg sz dst (BitVec.ofNat 64 idx)).setRip nr

/-- ⭐ P1 BATCH 16: ONE ITERATION OF A STRING OPERATION, WITHOUT THE RIP WRITE.

This is P1 batch 15's `.strop` body verbatim, with the single `setRip nr` at the
end of each arm lifted out to the caller.  It is factored rather than copied
because batch 16 needs the SAME five iterations under a repeat prefix, and a
second copy of five subtly-ordered arms — the access-before-update rule, the
`.q` pointer write against the `sz` data access, `cmps`'s reversed operand order
— is five chances for the two copies to drift.  ⚠️ The refactor is guarded: the
twenty batch-15 vectors and their characterization lemmas run against it
unchanged, so a slip here is a RED differential and not a silent regression.

⛔ IT DELIBERATELY DOES NOT TOUCH RIP.  Both callers write RIP exactly once and
explicitly, so "which address this instruction leaves behind" is a decision
visible at the call site rather than an absence to be inferred.  Batch 16 is the
first form in this model whose RIP is sometimes its OWN address, and an
implicit-fallthrough spelling of that would be indistinguishable from a
forgotten write. -/
def stringIter (k : StringOp) (sz : Size) (s : Cpu) : Cpu :=
  let step : BitVec 64 := BitVec.ofNat 64 sz.bytes
  let d : BitVec 64 := if s.flags.df then 0 - step else step
  let si := s.regs.get .rsi
  let di := s.regs.get .rdi
  match k with
  | .movs =>
      let v := s.readMem sz si
      let s := s.writeMem sz di v
      ((s.setReg .q .rsi (si + d)).setReg .q .rdi (di + d))
  | .stos =>
      let v := s.getReg sz .rax
      let s := s.writeMem sz di v
      s.setReg .q .rdi (di + d)
  -- ⚠️ LODS WRITES THE ACCUMULATOR THROUGH THE ORDINARY WIDTH RULE, so
  -- `lodsl` ZERO-EXTENDS into RAX while `lodsw` and `lodsb` MERGE (SDM
  -- Vol. 1 §3.4.1.1).  This is the one place in the group where `setReg`'s
  -- width behaviour is wanted rather than bypassed.
  | .lods =>
      let v := s.readMem sz si
      let s := s.setReg sz .rax v
      s.setReg .q .rsi (si + d)
  -- ⛔ SOURCE MINUS DESTINATION: `[RSI] − [RDI]`, not the AT&T print order.
  | .cmps =>
      let a := s.readMem sz si
      let b := s.readMem sz di
      let s := s.setFlags (Flags.sub sz a b s.flags)
      ((s.setReg .q .rsi (si + d)).setReg .q .rdi (di + d))
  -- SCAS is `RAX − [RDI]`, and only RDI moves.
  | .scas =>
      let a := s.getReg sz .rax
      let b := s.readMem sz di
      let s := s.setFlags (Flags.sub sz a b s.flags)
      s.setReg .q .rdi (di + d)

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

  -- ══ P1 BATCH 13 ═══════════════════════════════════════════════════════
  -- The flagless shifts and the byte-swapping move.  Both are forms whose
  -- RESULT this model already knew how to compute — `Flags.shiftCount` and the
  -- three shift expressions came from batches 7/8, `Value.byteRev` from batch
  -- 10 — and whose content is entirely in what they do NOT do.

  -- SARX / SHLX / SHRX (SDM Vol. 2A).  "Flags Affected: None."
  --
  -- ⭐ THE SAME COUNT MASK AS `.shift`, AND IT IS THE SAME SENTENCE OF THE SDM:
  -- "the count is masked to 5 bits (or 6 bits with a 64-bit operand)".  So
  -- `Flags.shiftCount` is called here rather than re-derived — a second copy of
  -- the mask would be a second place for the 5/6 split to be wrong, and the
  -- split is the part of a shift that is easy to get wrong.
  --
  -- ⚠️ THE COUNT IS READ AT WIDTH `.b` AND NOT AT `sz`, and that is not a
  -- shortcut: the mask keeps at most six bits, and the low six bits of a
  -- register are the low six bits of its low byte whatever the operand size.
  -- Reading the count at `sz` would be equally correct and would say something
  -- false about where the count comes from — the count register's width is not
  -- the operand's width.
  --
  -- ⛔ AND THERE IS NO `n = 0` BRANCH, unlike `.shift`.  `.shift` needs one
  -- because "if the count is 0, the flags are not affected"; this form affects
  -- no flags at any count, so a zero count is an ordinary case that copies the
  -- source to the destination — and the destination write still ZERO-EXTENDS at
  -- `.d`, so `shlxl` with a count of zero is observably not a no-op.
  | .shiftx k sz dst src cnt =>
      match sz with
      | .d | .q =>
          let n := Flags.shiftCount sz ((s.getReg .b cnt).setWidth 8)
          let a := s.readOperand sz nr src
          let res : Val :=
            match k with
            | .shl => Value.trunc sz (a <<< n)
            | .shr => (Value.trunc sz a) >>> n
            | .sar => Value.sar sz a n
          (s.setReg sz dst res).setRip nr
      | _ => s.halt (.illegalOperands
          "sarx/shlx/shrx at an 8- or 16-bit operand size (VEX.W selects 32 or 64 only)")

  -- MOVBE (SDM Vol. 2A).  "Flags Affected: None."
  --
  -- ⚠️ THE REVERSAL IS AT THE OPERAND WIDTH, NOT AT 64 BITS.  `movbew` reverses
  -- TWO bytes, `movbel` four, `movbeq` eight — and the destination write then
  -- applies the ordinary width rule on top, so `movbel` zero-extends and
  -- `movbew` merges (SDM Vol. 1 §3.4.1.1).  A model that reversed eight bytes
  -- and truncated would be wrong at both narrow widths and right at `.q`.
  --
  -- ⛔ EXACTLY ONE MEMORY OPERAND.  Both encodings put the memory operand in
  -- ModR/M's r/m field, so `movbe r, r` has no encoding; declining is the same
  -- refusal `wellFormed2` makes for two memory operands, one direction further.
  | .movbe sz dst src =>
      if !(dst.isMem != src.isMem) || dst.isImm || src.isImm then
        s.halt (.illegalOperands "movbe requires exactly one memory operand")
      else match sz with
      | .w | .d | .q =>
          let a := s.readOperand sz nr src
          (s.writeOperand sz nr dst (Value.bswap sz a)).setRip nr
      | .b => s.halt (.illegalOperands "movbe at an 8-bit operand size (no encoding)")

  -- POPCNT (SDM Vol. 2B) · LZCNT/TZCNT · BSF/BSR · BLSI (SDM Vol. 2A).
  --
  -- ⛔⛔ BSF AND BSR AT A ZERO SOURCE ARE THIS MODEL'S FIRST UNDEFINED
  -- DESTINATION.  "If the content source operand is 0, the content of the
  -- destination operand is undefined" — a REGISTER, not a flag.  Real silicon
  -- leaves the destination unmodified and AMD documents that it does; Intel
  -- does not, and this model follows its stated source rather than the folklore.
  -- Writing the old value back would be INVENTING A FACT in exactly the sense
  -- X86/Oracle.lean's header forbids, and it is the more tempting invention
  -- because it happens to match the machine on the desk.
  --
  -- ⚠️ THE ZERO SOURCE IS REACHABLE, not hypothetical: `adversarial` contains 0,
  -- so every `bsf`/`bsr` vector runs this branch at one pre-state in eleven.
  --
  -- ⚠️ THE FIVE FLAG DRAWS HAPPEN BEFORE THE BRANCH, unconditionally, so that
  -- the flags always read the same five positions of the stream whichever way
  -- the source falls.  ⛔ THE TOTAL a `bsf` consumes IS still data-dependent —
  -- a zero source draws `sz.bits` more for the destination — and saying
  -- otherwise would be a comment claiming a property the code does not have.
  -- What matters is the weaker fact, and it holds: the cursor depends on the
  -- SOURCE, never on the oracle's own BITS, so the two opposite-oracle runs
  -- that derive the undefined set always take the same branch and end at the
  -- same position (`cursor_independent_of_bits`, `Tests/Nonvacuity.lean`).
  | .bitcnt k sz dst src =>
      if !(bitcntEncodable k sz) then
        s.halt (.illegalOperands
          "the bit-counting group has no 8-bit form, and blsi has no 16-bit form")
      else
        let a := s.readOperand sz nr src
        match k with
        | .popcnt =>
            let res : Val := BitVec.ofNat 64 (Value.popCount sz a)
            ((s.setFlags (Flags.popcnt sz a s.flags)).setReg sz dst res).setRip nr
        | .lzcnt =>
            let res : Val := BitVec.ofNat 64 (Value.clz sz a)
            let (pfU, s) := s.undefBit
            let (afU, s) := s.undefBit
            let (sfU, s) := s.undefBit
            let (ofU, s) := s.undefBit
            ((s.setFlags (Flags.bitCount sz a res pfU afU sfU ofU s.flags)).setReg
              sz dst res).setRip nr
        | .tzcnt =>
            let res : Val := BitVec.ofNat 64 (Value.ctz sz a)
            let (pfU, s) := s.undefBit
            let (afU, s) := s.undefBit
            let (sfU, s) := s.undefBit
            let (ofU, s) := s.undefBit
            ((s.setFlags (Flags.bitCount sz a res pfU afU sfU ofU s.flags)).setReg
              sz dst res).setRip nr
        | .bsf => bitScanStep false sz dst a nr s
        | .bsr => bitScanStep true sz dst a nr s
        | .blsi =>
            let res := Value.blsi sz a
            let (pfU, s) := s.undefBit
            let (afU, s) := s.undefBit
            ((s.setFlags (Flags.blsi sz a res pfU afU s.flags)).setReg sz dst res).setRip nr

  -- MOVS / STOS / LODS / CMPS / SCAS (SDM Vol. 2A/2B).  See `StringOp`.
  --
  -- ⭐ THE DELTA IS THE WHOLE GROUP'S SHARED CONTENT, and it is the first thing
  -- in this model that READS DF.  "If the DF flag is 0, the pointer is
  -- incremented; if the DF flag is 1, it is decremented" — by the OPERAND
  -- WIDTH, not by a fixed eight.  ⚠️ DF was a dead bit in this repository for
  -- ten batches (D27) and is written by `cld`/`std` since batch 11; this is
  -- where it finally changes an ANSWER rather than a field of the output.
  --
  -- ⛔ THE ACCESS HAPPENS AT THE CURRENT POINTER AND THE UPDATE COMES AFTER.
  -- Measured, not assumed: with DF set, the oracle's `movsq` still WROTE at
  -- RDI's original 0x2000 and only then left RDI at 0x1ff8.  A model that
  -- decremented first would touch the eight bytes below on every backward step
  -- and agree with this one on every forward one.
  --
  -- ⚠️ THE POINTER WRITE IS `.q` AND THE DATA ACCESS IS `sz`; the two widths in
  -- each line are different on purpose.  See the note on the constructor.
  --
  -- "Flags Affected: None" for MOVS, STOS and LODS.  CMPS and SCAS set all six
  -- arithmetic flags and leave NONE undefined — the whole group draws nothing
  -- from the oracle, which is why every row of it is `T-exact`.
  | .strop k sz => (stringIter k sz s).setRip nr

  -- ⭐⭐ P1 BATCH 16: THE REPEAT PREFIXES (SDM Vol. 2B, REP/REPE/REPZ/REPNE/
  -- REPNZ).  ONE ITERATION PER `step`, and the loop-back is a RIP that does not
  -- move.
  --
  -- ⛔⛔ COUNT EXHAUSTION DOES NOT ADVANCE RIP, AND THIS IS THE ONE THING HERE
  -- THAT IS NOT WHAT IT LOOKS LIKE.  The obvious model — and the SDM's own
  -- pseudocode read as a single step — decrements RCX, notices it has reached
  -- zero, and falls through to the next instruction.  x86isa does not: measured,
  -- `rep movsq` with RCX = 1 performs the copy, leaves RCX = 0, and leaves RIP
  -- AT THE INSTRUCTION.  It takes one FURTHER step, which finds RCX already
  -- zero, to move past it.  So the count is tested only ON ENTRY, and the
  -- SDM's loop is decomposed with its `while` test at the TOP.
  --
  -- ⚠️ A MODEL THAT ADVANCED ON THE DECREMENT REACHING ZERO IS RIGHT EVERYWHERE
  -- EXCEPT RCX = 1.  It agrees on every RCX = 0 case (no iteration at all) and
  -- on every RCX ≥ 2 case (the count does not reach zero), so exactly one value
  -- of one register separates the two models — and `adversarial` contains 1, so
  -- the pre-states reach it.  `wrongRepAdvanceOnCountZero` in Main.lean is that
  -- model, and it is caught.  Had the sweep skipped 1, this whole branch would
  -- have been green and wrong, which is D43 in the shape it takes when the
  -- state DOES happen to express the difference.
  --
  -- THE ZF PREDICATE READS THE FLAGS THE ITERATION JUST WROTE (`RepPrefix.
  -- terminates` on `s'.flags.zf`, not `s.flags.zf`).  `repe cmpsq` on differing
  -- operands ended the repeat in the same step it made the comparison.
  --
  -- ⚠️ AND THE COUNT WRITE IS `.q`, like the pointer writes beside it: `rep
  -- movsb` decrements the whole of RCX.  Measured at RCX = 0x1_0000_0001, which
  -- became 0x1_0000_0000 — a value whose low half alone would have wrapped.
  --
  -- "Flags Affected: None" for the prefix itself; the flags are whatever the
  -- iteration left, and on the RCX = 0 path they are untouched.
  | .repstrop r k sz =>
      if !repApplies r k then
        s.halt (.unimplemented "repeat prefix not filed for this string op")
      else
        let cx := s.regs.get .rcx
        -- RCX = 0 ON ENTRY: no iteration at all.  No memory access, no flag
        -- write, no pointer move, and RCX is NOT decremented — it does not wrap
        -- to all-ones.  This is the only path that always advances.
        if cx == 0 then s.setRip nr
        else
          let s' := (stringIter k sz s).setReg .q .rcx (cx - 1)
          s'.setRip (if r.terminates s'.flags.zf then nr else s.rip)

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
