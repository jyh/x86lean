/-
# X86.Syntax — the instruction AST for the P0 scalar roster

Plan v1 §3.2.  ONE inductive keyed by mnemonic with a shared operand pair, not
one constructor per (mnemonic, operand-shape) pair: 20 mnemonics × 4 shapes
would be 80 constructors and 80 nearly identical proofs, and the shapes are the
same shapes for every mnemonic — that is what a ModR/M byte IS (SDM Vol. 2A
§2.1.5).

WHAT THE DECODER HAS ALREADY DONE by the time an `Instr` exists (plan v1 §3.4:
phase 1 consumes Intel XED's structured output, and decode trust is a NAMED item
in TRUSTBASE.md and a COLUMN in the coverage table):

* prefixes are resolved — the operand `Size` is a datum on the instruction;
* REX.R/X/B are folded into the `GPR` values;
* immediates are already sign- or zero-extended to 64 bits per their form, so
  `Operand.imm` carries the final value and the semantics never re-extends;
* the encoded LENGTH is on the instruction, because RIP-relative addressing and
  every relative branch are defined against the address of the NEXT instruction
  (SDM Vol. 2A §2.2.1.6) and that address is `rip + len`.

`Instr.len` being a datum rather than a computed property is precisely the
decode-trust boundary: a wrong length is a wrong model and no theorem here can
catch it.  The differential harness can, and does.

LANE. Personal lane, public sources only.
-/
import X86.State

namespace X86

/-- SIB scale factor (SDM Vol. 2A §2.1.5, Table 2-3). -/
inductive Scale where
  | s1 | s2 | s4 | s8
  deriving DecidableEq, Repr, Inhabited, BEq

def Scale.toVal : Scale → Val
  | .s1 => 1 | .s2 => 2 | .s4 => 4 | .s8 => 8

/-- An effective address: `base + index*scale + disp`, or `next_rip + disp` when
RIP-relative.  Segment bases are not modelled (v0.x non-goal: FS/GS-relative
addressing arrives with the thread-local-storage forms in P1). -/
structure Ea where
  base : Option GPR := none
  index : Option GPR := none
  scale : Scale := .s1
  /-- The displacement, ALREADY sign-extended to 64 bits by the decoder. -/
  disp : Val := 0
  /-- RIP-relative (ModR/M mod=00, r/m=101 in 64-bit mode). -/
  ripRel : Bool := false
  deriving DecidableEq, Repr, Inhabited, BEq

/-- An operand.  The operand WIDTH is not here: it is one datum on the
instruction, because these forms all have a single operand size. -/
inductive Operand where
  /-- A general-purpose register; `high8` selects AH/CH/DH/BH. -/
  | reg (r : GPR) (high8 : Bool := false)
  /-- A memory operand at an effective address. -/
  | mem (ea : Ea)
  /-- An immediate, ALREADY extended to 64 bits by the decoder. -/
  | imm (v : Val)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Is this operand a memory reference?  Two memory operands cannot be encoded
in one instruction (there is one ModR/M byte), so this is the well-formedness
test `step` uses before it gives anything a meaning. -/
def Operand.isMem : Operand → Bool
  | .mem _ => true
  | _ => false

def Operand.isImm : Operand → Bool
  | .imm _ => true
  | _ => false

/-- The two-operand arithmetic/logic mnemonics.  `cmp` and `test` are here
rather than beside them because they are exactly `sub` and `and` with the result
DISCARDED — the flags are the whole instruction (SDM Vol. 2A, CMP and TEST). -/
inductive BinKind where
  | add | sub | and | or | xor | cmp | test
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The one-operand mnemonics. -/
inductive UnKind where
  | inc | dec | neg | not
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The shift mnemonics in the P0 roster (rotates and the arithmetic right shift
are P1). -/
inductive ShiftKind where
  | shl | shr
  deriving DecidableEq, Repr, Inhabited, BEq

/-- A shift count: an 8-bit immediate, or CL. -/
inductive ShiftAmt where
  | imm8 (v : BitVec 8)
  | cl
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The sixteen condition codes (SDM Vol. 1 Appendix B / Vol. 2A "Jcc").
Synonyms are collapsed to one constructor per PREDICATE, not one per mnemonic:
`jz`/`je` are the same instruction and a model that distinguishes them is
modelling the assembler, not the machine.  The mnemonic strings a disassembler
prints are in `Cc.mnemonic`. -/
inductive Cc where
  | o | no | b | ae | e | ne | be | a
  | s | ns | p | np | l | ge | le | g
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Evaluate a condition code against the flags (SDM Vol. 2A, "Jcc" table). -/
def Cc.eval : Cc → Flags → Bool
  | .o,  f => f.of
  | .no, f => !f.of
  | .b,  f => f.cf                      -- below / carry / not above-or-equal
  | .ae, f => !f.cf
  | .e,  f => f.zf
  | .ne, f => !f.zf
  | .be, f => f.cf || f.zf
  | .a,  f => !f.cf && !f.zf
  | .s,  f => f.sf
  | .ns, f => !f.sf
  | .p,  f => f.pf
  | .np, f => !f.pf
  | .l,  f => f.sf != f.of
  | .ge, f => f.sf == f.of
  | .le, f => f.zf || (f.sf != f.of)
  | .g,  f => !f.zf && (f.sf == f.of)

def Cc.mnemonic : Cc → String
  | .o => "jo" | .no => "jno" | .b => "jb" | .ae => "jae"
  | .e => "je" | .ne => "jne" | .be => "jbe" | .a => "ja"
  | .s => "js" | .ns => "jns" | .p => "jp" | .np => "jnp"
  | .l => "jl" | .ge => "jge" | .le => "jle" | .g => "jg"

/-- Every condition code, for the generated coverage table and for exhaustive
tests. -/
def Cc.all : List Cc :=
  [.o, .no, .b, .ae, .e, .ne, .be, .a, .s, .ns, .p, .np, .l, .ge, .le, .g]

/-- A branch target. -/
inductive JmpTarget where
  /-- Relative to the address of the NEXT instruction; `d` is already
  sign-extended to 64 bits by the decoder. -/
  | rel (d : Val)
  /-- Indirect through a register or memory operand (always 64-bit in 64-bit
  mode for `jmp`/`call` near forms — SDM Vol. 2A, JMP/CALL). -/
  | indirect (o : Operand)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The P0 roster: TWENTY mnemonics, in the plan v1 §5 order.
`mov add sub and or xor cmp test shl shr lea inc dec neg not push pop jmp jcc call`. -/
inductive Op where
  | mov   (sz : Size) (dst src : Operand)
  | bin   (k : BinKind) (sz : Size) (dst src : Operand)
  | un    (k : UnKind) (sz : Size) (dst : Operand)
  | shift (k : ShiftKind) (sz : Size) (dst : Operand) (amt : ShiftAmt)
  | lea   (sz : Size) (dst : GPR) (ea : Ea)
  | push  (sz : Size) (src : Operand)
  | pop   (sz : Size) (dst : Operand)
  | jmp   (t : JmpTarget)
  | jcc   (c : Cc) (d : Val)
  | call  (t : JmpTarget)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- A DECODED instruction: an operation plus its encoded length in bytes.  See
the header on why `len` is a datum and what it costs in trust. -/
structure Instr where
  op : Op
  /-- Encoded length in bytes, from the decoder (XED). -/
  len : Nat
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The mnemonic a disassembler prints, used by the coverage table and by the
differential harness's disagreement reports. -/
def Op.mnemonic : Op → String
  | .mov .. => "mov"
  | .bin k .. => match k with
    | .add => "add" | .sub => "sub" | .and => "and" | .or => "or"
    | .xor => "xor" | .cmp => "cmp" | .test => "test"
  | .un k .. => match k with
    | .inc => "inc" | .dec => "dec" | .neg => "neg" | .not => "not"
  | .shift k .. => match k with | .shl => "shl" | .shr => "shr"
  | .lea .. => "lea"
  | .push .. => "push"
  | .pop .. => "pop"
  | .jmp .. => "jmp"
  | .jcc c _ => c.mnemonic
  | .call .. => "call"

/-- The twenty mnemonic NAMES of the P0 roster, as data.  `Tests/Coverage.lean`
checks that this list and the set of `Op.mnemonic` values agree, so the coverage
table cannot drift from the AST. -/
def rosterP0 : List String :=
  ["mov", "add", "sub", "and", "or", "xor", "cmp", "test", "shl", "shr",
   "lea", "inc", "dec", "neg", "not", "push", "pop", "jmp", "jcc", "call"]

end X86
