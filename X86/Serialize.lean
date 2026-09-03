/-
# X86.Serialize — the canonical state record the differential harness compares

Plan v1 §4.3: "(form, random + adversarial state) executed on Lean (compiled),
x86isa, K; FULL-DELTA compare; every disagreement filed with its class."

THE FORMAT IS DELIBERATELY DULL: space-separated `key=value` on one line, hex
without underscores, lowercase.  It has to be written by Lean and read by Common
Lisp (ACL2), and later by whatever drives the hardware co-simulation, so every
clever encoding is a second parser to keep honest.  A dull format is the cheapest
thing in this file.

WHAT A RECORD OBSERVES: the sixteen GPRs, RIP, the seven flags, the model-state
field, and the bytes in the vector's declared WATCH WINDOWS.  Memory is watched
by window rather than by whole-memory diff because the two models do not share a
representation — ours is a finite map with a zero background, x86isa's is its
own — so "the whole of memory" is not a comparable object, while "these bytes"
is.  A window that is too small hides a disagreement, so the generator makes
each vector's windows cover its operands' spans plus a margin, and the margin
being non-empty is itself a check: a store that ran off the end of its span
shows up as a difference in the margin.

LANE. Personal lane, public sources only.
-/
import X86.Semantics

namespace X86

/-- Lowercase hex, no prefix, fixed width in nibbles. -/
def hexPad (v : BitVec 64) (nib : Nat) : String :=
  let digits := "0123456789abcdef".toList
  let rec go (i : Nat) (acc : List Char) : List Char :=
    match i with
    | 0 => acc
    | k + 1 =>
      let d := ((v >>> (4 * k)).toNat % 16)
      go k (acc ++ [digits[d]!])
  String.ofList (go nib [])

def hex64 (v : BitVec 64) : String := hexPad v 16
def hex8 (v : BitVec 8) : String := hexPad (v.setWidth 64) 2

/-- A memory window to observe: a base address and a byte count. -/
structure Window where
  base : BitVec 64
  len : Nat
  deriving Repr, Inhabited

/-- Render the watched bytes of one window. -/
def renderWindow (m : Mem) (w : Window) : String :=
  let bytes := (List.range w.len).map (fun i => hex8 (m.read (w.base + BitVec.ofNat 64 i)))
  s!"mem@{hex64 w.base}={String.intercalate "" bytes}"

/-- ⭐ THE WIRE FORMAT, FOLDED OVER `flagFields` (D30).

This string used to hand-enumerate the seven flags, and it is the one place in
the model where a missing flag is INVISIBLE: absent from the record, absent from
the diff, and therefore reported as agreement on every case for ever.  It now
reads the single table, whose completeness is a compile-time arity check
(`flagFields_covers_Flags`).  The rendered bytes are unchanged — the table's
order IS this function's old order, and the batch that made this change proved
it by diffing 40482 emitted records before and after. -/
def Flags.render (f : Flags) : String :=
  let b (x : Bool) : String := if x then "1" else "0"
  String.intercalate " " (flagFields.map (fun r => s!"{r.name}={b (r.get f)}"))

def Cpu.renderRegs (s : Cpu) : String :=
  String.intercalate " "
    (GPR.all.map (fun r => s!"{r.name .q}={hex64 (s.regs.get r)}"))

def MsErr.render : MsErr → String
  | .illegalOperands w => s!"illegal-operands:{w}"
  | .unimplemented w => s!"unimplemented:{w}"
  | .byDesign w => s!"by-design:{w}"

/-- One state, on one line.

⚠️ THE RECORD CARRIES `refused=0|1`, NOT THE REASON.  Both models can decline to
give an instruction a meaning, but they say so in their own vocabulary: this one
sets `Cpu.ms` with a string, while ACL2 x86isa raises `#GP(0)` into its `fault`
field with a keyword.  Comparing the REASONS would report a disagreement on
every refusal, which is the opposite of the truth — the two models are agreeing
that the instruction faults.  What is comparable is the REFUSAL ITSELF, so that
is what the record carries; the reason stays in `Cpu.ms` for a human reading a
single case. -/
def Cpu.render (s : Cpu) (ws : List Window) : String :=
  String.intercalate " "
    ([s.renderRegs, s!"rip={hex64 s.rip}", s.flags.render,
      s!"refused={if s.ms.isSome then "1" else "0"}"]
      ++ ws.map (renderWindow s.mem))

/-! ### The undefined mask, DERIVED rather than declared

The set of flags this model refuses to commit to, for a given (instruction,
state), is computed by running the SAME step under the all-zero and the all-ones
oracle and seeing which flags moved.  Deriving it means the harness's notion of
"undefined here" cannot drift from the semantics' notion — there is only one
notion, and it is the semantics'.  A declared list in the harness would be a
second source of truth and would go stale the first time a form changed tier. -/

def zeroOracle : Oracle := { bits := fun _ => false }
def onesOracle : Oracle := { bits := fun _ => true }

/-- The names of the flags that differ between the two oracle runs. -/
def undefinedFlags (i : Instr) (s : Cpu) : List String :=
  let a := (step i { s with oracle := zeroOracle }).flags
  let b := (step i { s with oracle := onesOracle }).flags
  flagFields.filterMap (fun r => if r.get a == r.get b then none else some r.name)

/-! ### ⛔⛔ P1 BATCH 14 — AN UNDEFINED REGISTER, AND HOW THE LEAK CHECK KEPT ITS
TEETH

Until this batch every undefined region in the model was a FLAG, and the leak
check could be stated in one line: the two oracle runs must agree on everything
that is not a flag.  `bsf`/`bsr` at a zero source break that — the SDM leaves
the DESTINATION REGISTER undefined — and the tempting repair is to widen the
derived set to registers and be done.

⛔ THAT REPAIR WOULD HAVE GUTTED THE CHECK.  If the undefined registers are
DERIVED from the same two runs the check compares, then no register can ever
leak: an oracle bit reaching `rcx` by mistake would be re-read as "`rcx` is
undefined here", the differential would classify the resulting disagreement as
`undefined-region`, and a real spec bug would be filed as an explained one.  The
check would report a pass in exactly the case it exists to catch.

⇒ SO THERE ARE TWO SOURCES AND THEY MUST AGREE.  `declaredUndefRegs` reads the
AST and the SDM rule — `bsf`/`bsr`, and only at a zero source.
`undefinedRegs` runs the two oracles and reports what actually moved.  The leak
check is their EQUALITY, which has teeth in both directions:

* a register that moves and is NOT declared is the old leak, unchanged — an
  oracle bit somewhere nothing admits;
* a register that is declared and does NOT move is a FALSE UNDEFINED CLAIM, and
  that is the new hazard this batch introduced: it would license the harness to
  explain away a genuine disagreement in that register for ever.

Neither direction existed as a possibility before this batch, and both are
probed — see the `bsf`/`bsr` arms of `scripts/axiom_gate_selftest.sh`. -/

/-- The registers a form DECLARES undefined, read from the AST and the SDM rule
rather than from the model's behaviour. -/
def declaredUndefGPRs (i : Instr) (s : Cpu) : List GPR :=
  let nr : BitVec 64 := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  -- SDM Vol. 2A, BSF/BSR: "If the content of the source operand is 0, the
  -- content of the destination operand is undefined."  ⚠️ ONLY THEN — at a
  -- non-zero source the destination is an ordinary computed index, and
  -- declaring it undefined there would be the false claim described above.
  | .bitcnt .bsf sz dst src =>
      if bitcntEncodable .bsf sz && Value.isZero sz (s.readOperand sz nr src)
      then [dst] else []
  | .bitcnt .bsr sz dst src =>
      if bitcntEncodable .bsr sz && Value.isZero sz (s.readOperand sz nr src)
      then [dst] else []
  -- ⭐⭐ P1 BATCH 18 — THE SECOND UNDEFINED DESTINATION, AND IT IS UNDEFINED FOR
  -- A DIFFERENT REASON THAN THE FIRST.  `bsf`/`bsr`'s destination is undefined
  -- when the SOURCE VALUE is zero; `shld`/`shrd`'s is undefined when the COUNT
  -- OPERAND, after masking, exceeds the operand size — a property of a different
  -- operand, and one that can only happen at `.w`, where a 5-bit mask reaches 31
  -- and the operand is 16 wide.  Over this harness's eighty-two pre-states a
  -- CL-driven count lands there in THIRTY-FIVE.
  --
  -- ⚠️ THE MEMORY DESTINATION IS NOT HERE, AND ITS ABSENCE IS THE MODEL'S
  -- REFUSAL RATHER THAN AN OMISSION: `step` halts on that combination
  -- (`dshiftMemUndefined`), so there is no undefined memory to declare and
  -- `undefinedLeaked`'s demand that the two oracle runs agree on every watched
  -- byte is left with its full teeth.  The day this model answers for it, THIS
  -- is one of the two places that has to grow, and the other is
  -- `undefinableFields` in the comparator.
  | .dshift _ sz dst _ amt =>
      let cnt : BitVec 8 :=
        match amt with
        | .imm8 v => v
        | .cl => (s.getReg .b .rcx).setWidth 8
      let n := Flags.shiftCount sz cnt
      if dshiftEncodable sz && !dshiftMemUndefined sz dst.isMem n && sz.bits < n then
        (match dst with | .reg r _ => [r] | _ => [])
      else []
  | _ => []

/-- The same set as NAMES, in `GPR.all` order so that it and `undefinedRegs`
are comparable as lists rather than needing a set equality the kernel would
have to work harder for. -/
def declaredUndefRegs (i : Instr) (s : Cpu) : List String :=
  let ds := declaredUndefGPRs i s
  GPR.all.filterMap (fun r => if ds.contains r then some (r.name .q) else none)

/-- The registers that actually MOVE between the two opposite oracle runs. -/
def undefinedRegs (i : Instr) (s : Cpu) : List String :=
  let a := (step i { s with oracle := zeroOracle }).regs
  let b := (step i { s with oracle := onesOracle }).regs
  GPR.all.filterMap (fun r => if a.get r == b.get r then none else some (r.name .q))

/-- Do the two oracle runs agree on everything the model does not DECLARE
undefined?  If they do not, an undefined bit has leaked into a register no form
admits, or into RIP, memory or the model state — a defect of a different and
worse kind than an undefined flag, because nothing in the tier table admits it.
A declared register that does not move is reported here too, for the reason in
the note above.  The harness checks this on every vector. -/
def undefinedLeaked (i : Instr) (s : Cpu) (ws : List Window) : Bool :=
  let a := step i { s with oracle := zeroOracle }
  let b := step i { s with oracle := onesOracle }
  !(undefinedRegs i s == declaredUndefRegs i s
    && a.rip == b.rip
    && (match a.ms, b.ms with | none, none => true | some x, some y => x == y | _, _ => false)
    && (ws.map (renderWindow a.mem)) == (ws.map (renderWindow b.mem)))

end X86
