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
  /-- P1 BATCH 2: ADC and SBB, the two forms that READ CF as well as writing it
  (SDM Vol. 2A, ADC: "Adds the destination operand, the source operand, and the
  carry (CF) flag").  They are in `BinKind` rather than a kind of their own
  because their operand shapes are the same shapes — but they are a different
  TEMPLATE, because their result depends on a flag, which no P0 form's does. -/
  | adc | sbb
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The one-operand mnemonics. -/
inductive UnKind where
  | inc | dec | neg | not
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The shift mnemonics in the P0 roster (rotates and the arithmetic right shift
are P1). -/
inductive ShiftKind where
  | shl | shr
  /-- P1 BATCH 7: SAR, the ARITHMETIC right shift — the one shift that
  propagates the sign rather than zeros.  `sal` is NOT here: it is an alias of
  `shl` with the same opcode (`/4`), so a post-decode model cannot distinguish
  them and should not (X86/Syntax.lean's header). -/
  | sar
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

/-- ⭐ EVERY ASSEMBLER SPELLING OF EACH CONDITION (SDM Vol. 1 Appendix B).
`Cc` has one constructor per PREDICATE, because `jz` and `je` are the same
instruction and a model that distinguishes them is modelling the assembler.  But
K's tree files them SEPARATELY — 30 branch mnemonics for these 16 predicates —
so a coverage claim over K's roster has to say which spellings a predicate
accounts for.  That is what this table is: it turns "the synonyms are covered"
from a sentence into a list a theorem can count.

`Cc.mnemonic` above returns the spelling this model PRINTS; these are all the
spellings that decode to it. -/
def Cc.suffixes : Cc → List String
  | .o  => ["o"]              | .no => ["no"]
  | .b  => ["b", "c", "nae"]  | .ae => ["ae", "nb", "nc"]
  | .e  => ["e", "z"]         | .ne => ["ne", "nz"]
  | .be => ["be", "na"]       | .a  => ["a", "nbe"]
  | .s  => ["s"]              | .ns => ["ns"]
  | .p  => ["p", "pe"]        | .np => ["np", "po"]
  | .l  => ["l", "nge"]       | .ge => ["ge", "nl"]
  | .le => ["le", "ng"]       | .g  => ["g", "nle"]

/-- ⭐ AND THE SAME SUFFIXES SPELL EVERY `Jcc`, `SETcc` AND `CMOVcc`, which is
why P1 batch 6 costs almost nothing: K files 30 branch mnemonics, 30 `set`
mnemonics and 30 `cmov` mnemonics, and they are ONE table of sixteen predicates
read three ways.  A model with a `Cc` type gets the second and third for free;
a model with one constructor per mnemonic would have written 90. -/
def Cc.synonyms (c : Cc) : List String := c.suffixes.map ("j" ++ ·)
def Cc.setSpellings (c : Cc) : List String := c.suffixes.map ("set" ++ ·)
def Cc.cmovSpellings (c : Cc) : List String := c.suffixes.map ("cmov" ++ ·)

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
  /-- P1 BATCH 5: JRCXZ / JECXZ (SDM Vol. 2A, JCC).  The one branch whose
  condition is a REGISTER rather than a flag, and the only conditional jump with
  no rel32 encoding at all — `E3 cb`, rel8 only.

  `addr32` selects the operand the address-size prefix `0x67` selects: with it
  the instruction tests **ECX**, the low 32 bits, and is spelled `jecxz`;
  without it it tests the whole of **RCX** and is spelled `jrcxz`.  One
  constructor rather than two because they are one instruction with a prefix —
  which is what every other form in this AST already assumes about prefixes
  (the header: "prefixes are resolved"). -/
  | jcxz  (addr32 : Bool) (d : Val)
  /-- P1 BATCH 6: SETcc (SDM Vol. 2A, SETcc).  Writes ONE BYTE — 1 or 0 — to an
  8-bit destination, register or memory.  "Flags Affected: None." -/
  | setcc (c : Cc) (dst : Operand)
  /-- P1 BATCH 6: CMOVcc (SDM Vol. 2A, CMOVcc).  The destination is always a
  REGISTER (`cmovcc r, r/m`); there is no memory-destination form.

  ⚠️ THE DESTINATION IS WRITTEN WHETHER OR NOT THE CONDITION HOLDS, and at width
  `d` that is observable rather than academic: a 32-bit write zero-extends (SDM
  Vol. 1 §3.4.1.1), so `cmovel %ecx, %eax` CLEARS the upper half of RAX even
  when ZF is clear and no data moves.  A model that skipped the write on a false
  condition is correct at w and q and wrong at d — this batch's planted hard
  half. -/
  | cmov  (c : Cc) (sz : Size) (dst : GPR) (src : Operand)
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
    | .adc => "adc" | .sbb => "sbb"
  | .un k .. => match k with
    | .inc => "inc" | .dec => "dec" | .neg => "neg" | .not => "not"
  | .shift k .. => match k with | .shl => "shl" | .shr => "shr" | .sar => "sar"
  | .lea .. => "lea"
  | .push .. => "push"
  | .pop .. => "pop"
  | .jmp .. => "jmp"
  | .jcc c _ => c.mnemonic
  | .jcxz a32 _ => if a32 then "jecxz" else "jrcxz"
  | .setcc c _ => "set" ++ (c.suffixes.headD "?")
  | .cmov c _ _ _ => "cmov" ++ (c.suffixes.headD "?")
  | .call .. => "call"

/-- The mnemonic NAMES this model implements, as data.  `Tests/Coverage.lean`
checks that this list and the set of `Op.mnemonic` values agree, so the coverage
table cannot drift from the AST.

The first twenty are P0's roster; `adc` and `sbb` are P1 batch 2.  The name is
still `rosterP0` because every downstream reference is to "the roster this model
implements" and renaming it would touch more than it clarifies — but the COUNT
is `rosterSize` below, so the three theorems that assert it cannot fall out of
step with each other. -/
def rosterP0 : List String :=
  ["mov", "add", "sub", "and", "or", "xor", "cmp", "test", "shl", "shr",
   "lea", "inc", "dec", "neg", "not", "push", "pop", "jmp", "jcc", "call",
   "adc", "sbb", "jrcxz", "jecxz", "setcc", "cmovcc", "sar"]

/-- The size of the implemented roster, named once.  Growing the roster changes
this and the three assertions in `Tests/Coverage.lean` follow — which is the
deliberate act that file's header asks for, rather than three separate numbers
drifting apart. -/
def rosterSize : Nat := rosterP0.length

end X86
