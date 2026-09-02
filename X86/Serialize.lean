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

def Flags.render (f : Flags) : String :=
  let b (x : Bool) : String := if x then "1" else "0"
  s!"cf={b f.cf} pf={b f.pf} af={b f.af} zf={b f.zf} sf={b f.sf} of={b f.of} df={b f.df}"

def Cpu.renderRegs (s : Cpu) : String :=
  String.intercalate " "
    (GPR.all.map (fun r => s!"{r.name .q}={hex64 (s.regs.get r)}"))

def MsErr.render : MsErr → String
  | .illegalOperands w => s!"illegal-operands:{w}"
  | .unimplemented w => s!"unimplemented:{w}"

/-- One state, on one line. -/
def Cpu.render (s : Cpu) (ws : List Window) : String :=
  let ms := match s.ms with | none => "none" | some e => e.render
  String.intercalate " "
    ([s.renderRegs, s!"rip={hex64 s.rip}", s.flags.render, s!"ms={ms}"]
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
  let chk (n : String) (x y : Bool) : List String := if x == y then [] else [n]
  chk "cf" a.cf b.cf ++ chk "pf" a.pf b.pf ++ chk "af" a.af b.af ++
  chk "zf" a.zf b.zf ++ chk "sf" a.sf b.sf ++ chk "of" a.of b.of ++ chk "df" a.df b.df

/-- Do the two oracle runs agree on everything OUTSIDE the flags?  If they do
not, an undefined bit has leaked into a register, RIP, memory or the model
state — a defect of a different and worse kind than an undefined flag, because
nothing in the tier table admits it.  The harness checks this on every vector. -/
def undefinedLeaked (i : Instr) (s : Cpu) (ws : List Window) : Bool :=
  let a := step i { s with oracle := zeroOracle }
  let b := step i { s with oracle := onesOracle }
  !(a.renderRegs == b.renderRegs
    && a.rip == b.rip
    && (match a.ms, b.ms with | none, none => true | some x, some y => x == y | _, _ => false)
    && (ws.map (renderWindow a.mem)) == (ws.map (renderWindow b.mem)))

end X86
