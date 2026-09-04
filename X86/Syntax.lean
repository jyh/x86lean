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
RIP-relative, plus the segment whose base a prefix selects.

⭐⭐ P2 ITEM 1 ADDED `seg`, AND IT IS THE ONLY FIELD HERE THAT IS NOT PART OF THE
OFFSET.  `base + index*scale + disp` is what the SDM calls the *effective
address*; the segment base turns it into a *linear address* (SDM Vol. 3A §3.4).
Two consumers want different ones of those, so `Ea` has two functions rather
than one — `Ea.offset` and `Ea.addr` — and `lea` is the reason: **LEA writes the
effective address, with no segment base added** (SDM Vol. 2A, LEA: "Computes the
effective address of the second operand"), so a segment prefix on a `lea` is
architecturally inert.  See the note on `Ea.addr` in `X86/Semantics.lean`. -/
structure Ea where
  base : Option GPR := none
  index : Option GPR := none
  scale : Scale := .s1
  /-- The displacement, ALREADY sign-extended to 64 bits by the decoder. -/
  disp : Val := 0
  /-- RIP-relative (ModR/M mod=00, r/m=101 in 64-bit mode). -/
  ripRel : Bool := false
  /-- The segment override, if the encoding carried one (prefix `64` = FS,
  `65` = GS).  `none` is every other case, including an explicit `%ds:`/`%ss:`
  override, whose base is zero in 64-bit mode and which therefore has nothing
  for this model to carry. -/
  seg : Option Seg := none
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

/-- P1 BATCH 7/8: the ROTATE mnemonics.  They are a separate kind from
`ShiftKind` and not an extension of it, because their flag rules are different
in kind: a rotate's CF is a COPY of a bit that stayed in the value (or, for
`rcl`/`rcr`, a bit that passed THROUGH CF), never a bit that fell off the end,
and CF is an INPUT to two of the four. -/
inductive RotKind where
  | rol | ror
  /-- Rotate THROUGH the carry: the operand and CF together form a `w+1`-bit
  ring (SDM Vol. 2A, RCL/RCR).  This is why their counts are taken modulo 9 and
  17 at widths b and w rather than modulo 8 and 16. -/
  | rcl | rcr
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

/-- P1 BATCH 9: the BIT-TEST group (SDM Vol. 2A, BT/BTC/BTR/BTS).  One kind per
what-happens-after-the-test, because the TEST is identical in all four: CF takes
the selected bit, and only then does the destination change (or not). -/
inductive BitKind where
  /-- Test only — the destination is READ and never written, like `cmp`. -/
  | bt
  | bts | btr | btc
  deriving DecidableEq, Repr, Inhabited, BEq

/-- P1 BATCH 14: the BIT-COUNTING group.  Six mnemonics that share one operand
shape — read one source at the operand width, write one GPR, set flags — and
agree on nothing else.

⭐ THEY ARE ONE CONSTRUCTOR FOR THE REASON `BinKind` IS: the shape is the same
and the RESULT and FLAG RULE are what vary, which is what a kind parameter is
for.  Compare `.shiftx`, which is a separate constructor from `.shift` because
its operand shape really is different (three operands, and a count register that
is not the destination).

⛔ AND THE SDM GIVES THREE DIFFERENT ANSWERS AT A ZERO SOURCE, which is the
whole content of the group and the reason these are not one function with a
flag:
* `popcnt` answers **0** — there are no set bits.
* `lzcnt`/`tzcnt` answer the **OPERAND WIDTH** — 64, 32 or 16, and set CF.
* `bsf`/`bsr` leave the **DESTINATION UNDEFINED** and set ZF.  This is the first
  form in this AST whose undefined region is a REGISTER rather than a flag; see
  the note on `step` and `X86.undefinedRegs`.
* `blsi` answers **0** and is not a count at all — it isolates the lowest set
  bit, `(-src) AND src`. -/
inductive BitCntKind where
  | popcnt | lzcnt | tzcnt | bsf | bsr | blsi
  deriving DecidableEq, Repr, Inhabited, BEq

/-- P1 BATCH 15: the STRING group (SDM Vol. 2A/2B: MOVS, STOS, LODS, CMPS, SCAS).

⭐ THE FIRST FORMS IN THIS AST WITH NO OPERAND FIELD AT ALL, and that is the
point of them rather than an economy.  Every other memory-touching form in this
model names its address in a `ModR/M` byte that the decoder handed us; these
five name theirs NOWHERE.  The addresses are RSI and RDI by opcode, the
accumulator is RAX by opcode, and the only thing the encoding varies is the
WIDTH.  `Operand` therefore has nothing to hold, and a constructor carrying one
would be inventing a field the machine does not have.

⭐ AND THEY ARE THE FIRST FORMS THAT WRITE A POINTER THEY ALSO READ.  Each one
advances RSI and/or RDI by the operand width — **forward or backward according
to DF** — so a single step both dereferences a register and updates it.  DF has
been in `Flags` since P0 and only `cld`/`std` (batch 11) could write it; these
are the first forms that READ it, and the first for which it changes an answer
rather than a bit of output.

⛔ `cmps` COMPUTES `[RSI] − [RDI]`, WHICH IS THE REVERSE OF HOW AT&T PRINTS IT.
clang disassembles the byte `A7` as `cmpsq %es:(%rdi), (%rsi)` — destination
first, as AT&T does everywhere — but the SUBTRACTION is source minus
destination, and the flags are of that difference.  A model written from the
printed operand order gets every `cmps` flag inverted.  ⚠️ `scas` is `RAX −
[RDI]` and would NOT be inverted by the same mistake, so the two do not fail
together and the differential would report `cmps` alone.  Measured against the
oracle before the semantics were written: `[rsi]=a0`, `[rdi]=b0` gives
`cf=1 sf=1 pf=1`, which is `0xa0 − 0xb0`, not `0xb0 − 0xa0`.

Every one of the five exists at all four widths — there is no `Encodable` table
here as there is for `.bitcnt`, because nothing in this group is missing. -/
inductive StringOp where
  | movs | stos | lods | cmps | scas
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The roster's base name for each string form.  The WIDTH is a suffix AT&T
adds (`movsb`/`movsw`/`movsl`/`movsq`), exactly as it does for `shl`, so the
base name is what `p1/roster.tsv` files them under.

⛔ `movs` IS NOT `movsb`/`movsw`/`movslq`.  Those three are `Op.movx` — the
SIGN-EXTENDING moves of batch 10 — and AT&T spells the byte-width string move
`movsb` too.  The two are distinguished here by the ROSTER BASE NAME (`movs`
against `movsw`), which is the only place the ambiguity is resolved; a coverage
claim keyed on the AT&T spelling alone would count one group twice and the
other never. -/
def StringOp.mnemonic : StringOp → String
  | .movs => "movs" | .stos => "stos" | .lods => "lods"
  | .cmps => "cmps" | .scas => "scas"

/-- P1 BATCH 16: THE REPEAT PREFIXES, which turn a string operation into a
loop.  Three constructors because the roster's `prefix` column has three base
names; TWO PREFIX BYTES, because `rep` and `repe` are both `F3`.

⭐ THE SPLIT BETWEEN `.rep` AND `.repe` IS A NAMING FACT, NOT AN ENCODING ONE,
and that is the one thing about this type a reader must not get wrong.  Measured
with clang: `rep cmpsq` and `repe cmpsq` assemble to the IDENTICAL bytes
`f3 48 a7`.  What differs is which string operation the byte prefixes — `F3` on
`movs`/`stos`/`lods` is spelled `rep` and repeats on the count alone, while `F3`
on `cmps`/`scas` is spelled `repe` and ALSO stops on `ZF = 0` — so the same byte
means two different loops depending on whether the instruction it prefixes sets
ZF.  Modelling that as one constructor with a context-dependent rule would hide
the branch inside `step`; modelling it as two makes `repApplies` below the place
where the partition is stated and checked.

⚠️ CONTRAST WITH `bitcntEncodable`, WHICH LOOKS LIKE THIS AND IS NOT.  That table
records which forms HAVE NO ENCODING — an architectural fact.  `repApplies` is a
ROSTER partition: every pair it rejects assembles perfectly well.  A comment
calling both "which forms exist" would be wrong about this one, and the
difference is exactly the sort a later reader would take on trust. -/
inductive RepPrefix where
  /-- `F3` on `movs`/`stos`/`lods`: repeat while RCX ≠ 0, and on nothing else. -/
  | rep
  /-- `F3` on `cmps`/`scas`: repeat while RCX ≠ 0 AND ZF = 1 (`repe`, `repz`). -/
  | repe
  /-- `F2` on `cmps`/`scas`: repeat while RCX ≠ 0 AND ZF = 0 (`repne`, `repnz`). -/
  | repn
  deriving DecidableEq, Repr, Inhabited, BEq

def RepPrefix.all : List RepPrefix := [.rep, .repe, .repn]

def RepPrefix.mnemonic : RepPrefix → String
  | .rep => "rep" | .repe => "repe" | .repn => "repne"

/-- ⭐ EVERY ASSEMBLER SPELLING OF EACH REPEAT PREFIX, for the same reason
`loopSpellings` and `movxSpellings` exist: the roster files FIVE prefix names and
this model has three constructors.  `repz` is `repe` and `repnz` is `repne`, and
clang assembles each pair to identical bytes, so the collapse is a fact about the
machine rather than a convenience. -/
def repSpellings : RepPrefix → List String
  | .rep => ["rep"]
  | .repe => ["repe", "repz"]
  | .repn => ["repne", "repnz"]

/-- WHICH (prefix, string op) PAIRS THIS MODEL CLAIMS — the roster's partition,
written as data beside the AST so that `Tests/Coverage.lean` can assert the exact
set rather than leaving it implicit in a chain of `halt` branches.

⛔ AND IT IS A CLAIM ABOUT THE ROSTER, NOT ABOUT THE MACHINE.  Both rejected
shapes assemble, and one of them was MEASURED against the oracle rather than
assumed:

* `F3` on `cmps`/`scas` spelled `rep` is the SAME INSTRUCTION as `repe` — same
  bytes — so `.rep` on a comparison would be a second name for a form `.repe`
  already covers, and the roster files it only under `repe`/`repz`.
* `F2` on `movs`/`stos`/`lods` (`repne movsq`, `f2 48 a5`) assembles, and
  x86isa EXECUTES IT AS AN UNPREFIXED STRING OP: one iteration, **RCX not
  decremented**, RIP advanced.  That is the oracle declining to treat `F2` as a
  repeat prefix there.  The roster does not file the form and this model does
  not claim it — copying an oracle's treatment of a shape nobody filed would be
  taking a quirk for a specification. -/
def repApplies : RepPrefix → StringOp → Bool
  | .rep, k => k == .movs || k == .stos || k == .lods
  | .repe, k => k == .cmps || k == .scas
  | .repn, k => k == .cmps || k == .scas

/-- ⭐⭐ WHETHER THE REPEAT ENDS IN *THIS* STEP — and it reads the flags the
iteration just wrote, not the incoming ones.

Measured, not assumed: `repe cmpsq` on operands that differ came back with
`ZF = 0` and RIP ADVANCED in the same step, from a pre-state whose incoming ZF
was 0 as well; `repne scasq` on operands that MATCH came back `ZF = 1` and RIP
advanced.  Both predicates therefore fire on the comparison's own result.

⛔ COUNT EXHAUSTION IS NOT IN THIS FUNCTION, AND THAT IS THE BATCH'S FINDING.
See the `.repstrop` case of `step`. -/
def RepPrefix.terminates : RepPrefix → Bool → Bool
  | .rep, _ => false
  | .repe, zf => !zf
  | .repn, zf => zf

/-- P1 BATCH 10: which way a WIDTH-CHANGING move fills the bits it invents.
Two constructors rather than a `Bool` because the two are one character apart in
the mnemonic (`movzbl` / `movsbl`) and opposite in effect, and a `Bool` named
`signed` reads the same at both call sites. -/
inductive MovxKind where
  | zero | sign
  deriving DecidableEq, Repr, Inhabited, BEq

/-- P1 BATCH 10: the IMPLICIT-ACCUMULATOR sign extensions (SDM Vol. 2A,
CBW/CWDE/CDQE and CWD/CDQ/CQO).  Six constructors and no operands at all: the
source and the destination are both fixed by the opcode.

⭐ THE TWO TRIOS DIFFER IN WHERE THE SIGN LANDS, and that is the whole content
of the group.  `cbw`/`cwde`/`cdqe` widen the accumulator IN PLACE — AL into AX,
AX into EAX, EAX into RAX.  `cwd`/`cdq`/`cqo` leave the accumulator alone and
fill **rDX** with copies of its sign bit, which is what makes a
double-width dividend for the `idiv` that always follows.  They are one bit
apart in the opcode (`98` vs `99`) and they write different registers.

The AT&T spellings are the names K's tree files them under, and are the names
this model prints: `cbtw cwtl cltq` and `cwtd cltd cqto`. -/
inductive CextKind where
  | cbw | cwde | cdqe
  | cwd | cdq | cqo
  deriving DecidableEq, Repr, Inhabited, BEq

def CextKind.mnemonic : CextKind → String
  | .cbw => "cbtw" | .cwde => "cwtl" | .cdqe => "cltq"
  | .cwd => "cwtd" | .cdq => "cltd"  | .cqo => "cqto"

/-- P1 BATCH 11: LOOP / LOOPE / LOOPNE (SDM Vol. 2A, LOOP/LOOPcc).  One
constructor per PREDICATE, exactly as `Cc` is: `loopz` is `loope` and `loopnz`
is `loopne` — clang assembles `loopz` and `loope` to the SAME BYTES (`E1 cb`),
and a model that distinguished them would be modelling the assembler.
`loopSpellings` below is the table that says which names each accounts for. -/
inductive LoopKind where
  | loop | loope | loopne
  deriving DecidableEq, Repr, Inhabited, BEq

/-- P1 BATCH 11: the FLAG-CONTROL singles (SDM Vol. 2A, CLC/STC/CMC/CLD/STD;
roster families 54-59).  No operands, one byte each, and each writes EXACTLY ONE
flag and leaves every other bit of the machine alone.

⭐ THEY ARE THE FIRST INSTRUCTIONS IN THIS MODEL THAT WRITE `df` AT ALL.  The
flag has been in `Flags` since P0 and in the differential comparator since P0 —
`Serialize.lean` prints it and diffs it — and until this batch nothing could
change it and no pre-state set it.  See docs/DECISIONS.md D27. -/
inductive FlagOp where
  | clc | stc | cmc | cld | std
  deriving DecidableEq, Repr, Inhabited, BEq

def FlagOp.mnemonic : FlagOp → String
  | .clc => "clc" | .stc => "stc" | .cmc => "cmc"
  | .cld => "cld" | .std => "std"

/-- P1 BATCH 17: the four one-operand members of opcode group `F6`/`F7`
(SDM Vol. 2A, MUL · IMUL · DIV · IDIV).  One operand is written in the
instruction; the other, and the destination, are `RDX:RAX` by opcode.

⭐ THEY ARE ONE KIND BECAUSE THEY ARE ONE ENCODING AND ONE REGISTER PAIR — `/4`,
`/5`, `/6`, `/7` of the same two opcodes — and because the thing that is hard
about them is shared: a result twice as wide as the operand, held in a pair
whose LOW half is the accumulator at every width but one.

⛔ AT `.b` THE PAIR IS `AH:AL`, NOT `DX:AX`.  "byte → AX", says the SDM's table,
and AX is one register.  A model that reached for RDX at every width would be
right at three widths out of four and would silently clobber RDX at the fourth. -/
inductive MulDivKind where
  | mul | imul | div | idiv
  deriving DecidableEq, Repr, Inhabited, BEq

def MulDivKind.mnemonic : MulDivKind → String
  | .mul => "mul" | .imul => "imul" | .div => "div" | .idiv => "idiv"

def MulDivKind.all : List MulDivKind := [.mul, .imul, .div, .idiv]

/-- Is this member of the group a DIVISION — the two whose meaning includes a
fault that depends on the operands?  Named rather than matched inline so the
distinction is one definition and the theorems can quantify over it. -/
def MulDivKind.isDiv : MulDivKind → Bool
  | .div | .idiv => true
  | _ => false

/-! ### P1 BATCH 18 — the DOUBLE-PRECISION SHIFTS

`shld` and `shrd` shift a destination by `n` and fill the vacated bits from a
SECOND operand instead of with zeros, the sign, or the carry.  They are one kind
for the reason `shl`/`shr`/`sar` are: one encoding family (`0F A4`/`A5` and
`0F AC`/`AD`), one count rule, one flag rule, and the only difference is the
DIRECTION — which decides which end of the destination the last bit leaves from
and which end of the source the incoming bits come from.

⛔ THEY ARE THE FIRST FORMS IN THIS MODEL WITH A "BAD PARAMETERS" BRANCH.  The
SDM (Vol. 2A, SHLD/SHRD) masks the count to 5 bits (6 at `.q`) and then says:
"If the count operand is 0, the flags are not affected.  If the count is greater
than the operand size, the result is undefined" — DEST *and* CF, OF, SF, ZF, AF
and PF, all six.  A 5-bit mask reaches 31 and a 16-bit operand is 16 wide, so
the branch is reachable at ONE width only, `.w`, and it is not a corner: over
this harness's own eighty-two pre-states a masked count lands above 16 in
THIRTY-FIVE of them.  Measured on the oracle before this constructor existed —
see docs/DECISIONS.md D52. -/
inductive DShiftKind where
  | shld | shrd
  deriving DecidableEq, Repr, Inhabited, BEq

def DShiftKind.mnemonic : DShiftKind → String
  | .shld => "shld" | .shrd => "shrd"

def DShiftKind.all : List DShiftKind := [.shld, .shrd]
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
  /-- P1 BATCH 8: ROL/ROR/RCL/RCR (SDM Vol. 2A). -/
  | rot   (k : RotKind) (sz : Size) (dst : Operand) (amt : ShiftAmt)
  /-- P1 BATCH 9: BT/BTS/BTR/BTC.  `off` is an immediate or a register; the
  MEMORY-destination-with-REGISTER-offset shape is NOT modelled — see the
  header note in `X86/Semantics.lean`. -/
  | bit   (k : BitKind) (sz : Size) (dst : Operand) (off : Operand)
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
  /-- P1 BATCH 10: MOVZX / MOVSX / MOVSXD (SDM Vol. 2A).  ⚠️ THE FIRST FORM IN
  THIS AST WITH TWO WIDTHS: the source is read at `ssz` and the destination is
  written at `dsz`, and `dsz` is what decides whether the write zero-extends
  (`.d`), preserves (`.w`), or replaces (`.q`) — SDM Vol. 1 §3.4.1.1.  Every
  other form here reads and writes at ONE width, and a model that kept one
  `Size` for both would be forced to guess which one this instruction means.

  The destination is always a REGISTER; there is no memory-destination form.
  `movslq` (Intel MOVSXD, opcode `63 /r`) is `.sign .q .d` — a different opcode
  from MOVSX but the same rule, so it is the same constructor. -/
  | movx  (k : MovxKind) (dsz ssz : Size) (dst : GPR) (src : Operand)
  /-- P1 BATCH 10: CBW/CWDE/CDQE and CWD/CDQ/CQO.  No operands: see
  `CextKind`. -/
  | cext  (k : CextKind)
  /-- P1 BATCH 10: XCHG (SDM Vol. 2A).  ⚠️ THE FIRST FORM THAT WRITES BOTH OF
  ITS OPERANDS, and at width `.d` that is observable in both of them at once:
  each write zero-extends, so `xchg %eax, %eax` — which the assembler must
  encode as `87 c0` because `90` is NOP — CLEARS the upper half of RAX while
  moving no data.

  ⛔ A MEMORY OPERAND IS DECLINED, not approximated: `xchg` with a memory
  operand asserts the LOCK signal whether or not `lock` is written (SDM Vol. 2A,
  XCHG), which is an atomicity claim this single-threaded model has no way to
  make.  Those forms are roster family 11.  See docs/DECISIONS.md D25. -/
  | xchg  (sz : Size) (a b : Operand)
  /-- P1 BATCH 10: BSWAP (SDM Vol. 2A).  ⛔ Widths `.b` and `.w` are DECLINED:
  "BSWAP ... with a 16-bit operand size ... is undefined" — the SDM does not say
  what the machine does, so neither does this model.  See D25. -/
  | bswap (sz : Size) (dst : GPR)
  /-- P1 BATCH 11: LOOP / LOOPE / LOOPNE (SDM Vol. 2A).  ⚠️ THE COUNTER IS
  DECREMENTED FIRST AND THE TEST IS ON THE DECREMENTED VALUE, and the write-back
  happens on BOTH paths — a `loop` that falls through has still decremented.
  A model that tested the OLD counter is wrong on exactly the pre-states where
  it holds 1 (fall through, not branch) and 0 (branch, not fall through).

  `addr32` selects the counter the address-size prefix `0x67` selects, exactly as
  it does for `jcxz`: with it the counter is **ECX** and the decrement is written
  back at 32 bits, which ZERO-EXTENDS and clears RCX's upper half (SDM Vol. 1
  §3.4.1.1); without it the counter is the whole of RCX.  "Flags Affected: None"
  — the counter moves, the flags do not, and ZF is an INPUT to two of the three.

  rel8 only: `E0`/`E1`/`E2 cb` have no rel32 encoding, the same gap `jcxz` has. -/
  | loop  (k : LoopKind) (addr32 : Bool) (d : Val)
  /-- P1 BATCH 11: CLC/STC/CMC/CLD/STD.  See `FlagOp`. -/
  | flagop (k : FlagOp)
  /-- P1 BATCH 12: NOP (SDM Vol. 2A).  The operand is `some` for the multi-byte
  form `0F 1F /0`, which carries a ModR/M byte purely to be long — and which the
  SDM says "does not alter the content of a register and does not issue a memory
  operation".  It is carried in the AST rather than discarded because the
  DECODER produced it and a model that threw it away could not round-trip an
  encoding; nothing in `step` reads it. -/
  | nop   (dst : Option Operand)
  /-- P1 BATCH 12: UD2 (SDM Vol. 2A): "Generates an invalid opcode exception."
  The one form in the roster so far whose whole meaning is a fault. -/
  | ud2
  /-- P1 BATCH 12: RET near, no immediate (`C3`).  Pops RIP.  The far return and
  the `RET imm16` form are NOT here — x86isa implements only the far return with
  immediate (`0xCA`), which is the complement of what this models. -/
  | ret
  /-- P1 BATCH 12: LEAVE (`C9`) — exactly `mov rsp, rbp` then `pop rbp`
  (SDM Vol. 2A, LEAVE). -/
  | leave
  /-- P1 BATCH 13: SARX / SHLX / SHRX (SDM Vol. 2A, "SARX/SHLX/SHRX — Shift
  Without Affecting Flags").  The SHIFT KIND is reused from `ShiftKind` because
  the value computed is the same function of the same three inputs; what is
  different is everything AROUND it.

  ⭐ THREE OPERANDS, AND NONE OF THEM IS THE OTHERS' — this is the first form in
  this AST that reads a source and writes a DIFFERENT destination while taking
  its count from a THIRD place.  `.shift` is a read-modify-write on one operand
  with the count in CL or an immediate; here `dst` is written, `src` is read,
  and `cnt` is any GPR.  A model that reused `.shift`'s shape would have had to
  pretend the destination and the source were the same register.

  ⛔ AND THE FLAGS ARE THE WHOLE POINT: "Flags Affected: None."  `.shift` at a
  non-zero masked count writes six flags and draws three oracle bits; this form
  writes none and draws none, at every count.  That is why it is a separate
  constructor and not a `Bool` on `.shift`: the two share a result and share
  nothing else.

  ⛔ Widths `.b` and `.w` HAVE NO ENCODING — VEX.W selects 32 or 64 bits and
  there is no 8- or 16-bit form — so `step` declines them rather than answering
  for bytes the machine cannot be asked about. -/
  | shiftx (k : ShiftKind) (sz : Size) (dst : GPR) (src : Operand) (cnt : GPR)
  /-- P1 BATCH 13: MOVBE (SDM Vol. 2A, MOVBE) — "Move Data After Swapping
  Bytes".  A load or a store that byte-reverses on the way through.

  ⛔ EXACTLY ONE OPERAND IS MEMORY, and that is an encoding fact rather than a
  convention: both encodings (`0F 38 F0 /r` and `0F 38 F1 /r`) take a ModR/M
  with a memory r/m, and `movbe r, r` does not exist.  `step` declines the
  register-to-register and immediate shapes instead of silently giving them the
  meaning of a byte-reversing `mov`.

  ⛔ Width `.b` has no encoding either — the byte form would be a no-op and
  Intel does not define one.  Widths w/l/q are the roster's `lqw`. -/
  | movbe (sz : Size) (dst src : Operand)
  /-- P1 BATCH 14: POPCNT / LZCNT / TZCNT / BSF / BSR / BLSI — see
  `BitCntKind`.  The destination is always a REGISTER (`r, r/m`); there is no
  memory-destination form for any of the six.

  ⛔ WIDTHS.  `.b` has no encoding for any of them.  `blsi` is VEX-encoded and
  VEX.W selects 32 or 64 only, so `.w` has no encoding for it either — the
  roster files it `lq` where the other five are `lqw`.  `step` declines what has
  no encoding rather than answering for it. -/
  | bitcnt (k : BitCntKind) (sz : Size) (dst : GPR) (src : Operand)
  /-- P1 BATCH 15: MOVS / STOS / LODS / CMPS / SCAS — see `StringOp`.  No
  operand field: the addresses are RSI and RDI and the accumulator is RAX, all
  by opcode.  All five exist at all four widths.

  ⚠️ THE POINTER UPDATE IS ALWAYS A FULL 64-BIT WRITE, whatever the operand
  width.  `movsb` advances the whole of RSI by one; it does not write RSI's low
  byte.  A model that routed the update through the ordinary width rule would
  be right at `.q`, right at `.d` by accident of zero-extension, and wrong at
  `.b` and `.w` — the two widths where `setReg` MERGES. -/
  | strop (k : StringOp) (sz : Size)
  /-- P1 BATCH 16: a string operation under a REPEAT PREFIX — see `RepPrefix`.

  ⭐ A SEPARATE CONSTRUCTOR RATHER THAN AN `Option RepPrefix` FIELD ON `.strop`.
  The field would have been the smaller diff and the worse one: it would have
  touched all twenty batch-15 vectors, every characterization lemma and both
  memory-destination gates, so a batch whose semantics reuse batch 15's
  UNCHANGED would have rewritten every line that mentions it.  Additive instead,
  for the reason batch 15 widened its window additively — nothing that already
  passed can be perturbed by a form that did not exist.

  The ITERATION is shared for real, not copied: `stringIter` is batch 15's body
  with the RIP write lifted out, and both constructors call it. -/
  | repstrop (r : RepPrefix) (k : StringOp) (sz : Size)
  /-- P1 BATCH 17: MUL / IMUL / DIV / IDIV in their ONE-OPERAND form — see
  `MulDivKind`.  All four exist at all four widths, and the destination is the
  `RDX:RAX` pair (`AH:AL` at `.b`) rather than anything the operand names.

  ⛔ THE TWO DIVISIONS FAULT ON THEIR OPERANDS.  `ud2` (batch 12) is the only
  other form in this model whose meaning is a fault, and its fault is a property
  of the OPCODE; these are the first whose refusal is a property of the VALUES,
  so the same instruction at the same width refuses in one pre-state and
  computes in the next.  Measured over the harness's own eighty-two pre-states
  before this constructor existed: `div` and `idiv` refuse in 51%–84% of them,
  depending on width and signedness, and both refusal causes — a zero divisor
  and a quotient too wide — are reached at every width. -/
  | muldiv (k : MulDivKind) (sz : Size) (src : Operand)
  /-- P1 BATCH 17: IMUL's TWO- and THREE-operand forms, which write a single
  register and no pair.

  ⭐ ONE CONSTRUCTOR, KEYED BY `imm`.  `imul r, r/m` is `dst := dst * src` and
  `imul $imm, r/m, r` is `dst := src * imm`: the destination, the width rule and
  the whole flag rule are identical, and the two differ in WHICH PAIR is
  multiplied — one expression.  `none` is the two-operand form.

  ⚠️ This is the opposite call from batch 16's, and deliberately so.  There a
  field on `.strop` would have touched twenty existing vectors and every lemma
  about them, so the batch added a constructor; here nothing exists yet to
  perturb, and a second constructor would have duplicated the CF/OF rule — the
  one part of IMUL a reader is likely to get wrong.

  ⛔ NO 8-BIT FORM EXISTS for either shape: `0F AF`, `6B` and `69` all take a
  16-, 32- or 64-bit operand, and the byte-wide multiply is the one-operand
  `F6 /5` above.  `imulrEncodable` is the table, and `step` declines `.b`. -/
  | imulr (sz : Size) (dst : GPR) (src : Operand) (imm : Option Val)
  /-- P1 BATCH 18: CMPXCHG — the first form in this model whose DESTINATION is
  decided by a comparison the instruction makes about its own operands.

  `cmpxchg dst, src` compares the ACCUMULATOR (AL/AX/EAX/RAX, by opcode, not by
  any operand) with `dst`.  Equal: `dst := src`.  Unequal: the accumulator takes
  `dst`, and `dst` is written back unchanged — the SDM's `DEST := DEST`, which
  is not a no-op at `.d`, where any register write zero-extends.

  ⚠️ THE ACCUMULATOR IS NOT AN OPERAND, so `dst` must not be RAX in a vector or
  the comparison is a tautology and the unequal branch is unreachable. -/
  | cmpxchg (sz : Size) (dst : Operand) (src : GPR)
  /-- P1 BATCH 18: XADD — the second form in this model that writes BOTH its
  operands (`xchg`, batch 10, was the first), and the first that writes both
  AND sets the flags.  `TEMP := SRC + DEST; SRC := DEST; DEST := TEMP`. -/
  | xadd (sz : Size) (dst : Operand) (src : GPR)
  /-- P1 BATCH 18: SHLD/SHRD.  `dst` is read and written, `src` is a REGISTER by
  the encoding (`0F A4 /r` is `r/m, r, imm8`), and the count is an immediate or
  CL exactly as the ordinary shifts' is — so `ShiftAmt` is reused rather than
  restated. -/
  | dshift (k : DShiftKind) (sz : Size) (dst : Operand) (src : GPR) (amt : ShiftAmt)
  /-- P1 BATCH 21: CMPXCHG8B — the only form in this model whose operands are a
  REGISTER PAIR, and the only one with no `Size` field at all.

  `cmpxchg8b m64` compares `EDX:EAX` with the eight bytes at `m64`.  Equal:
  `ZF := 1` and the memory takes `ECX:EBX`.  Unequal: `ZF := 0` and `EDX:EAX`
  takes the memory — two 32-bit register writes, which ZERO-EXTEND, so RDX's and
  RAX's upper halves are cleared on that branch.  D53's lesson arrives here as a
  RULE rather than as a surprise: every write in this instruction is 32 bits
  wide and none of them is a no-op.

  ⚠️ NO `Size` FIELD, because the width is not a choice: `0F C7 /1` is 64 bits
  of memory and 32-bit register halves, always.  Giving it a `Size` would invite
  `step` to branch on a width the encoding cannot express.

  ⛔ THE DESTINATION MUST BE MEMORY.  `0F C7 /1` with `mod = 11` is not
  `cmpxchg8b` on a register — it is #UD (the opcode's register form is
  `rdrand`/`rdseed` at other /r values).  `step` declines a non-memory operand
  rather than inventing a register-pair compare. -/
  | cmpxchg8b (dst : Operand)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- P1 BATCH 14: which (kind, width) pairs of the bit-counting group EXIST.

⭐ Written as DATA beside the AST rather than as a chain of `halt` branches
inside `step`, so that "which forms this model declines, and why" is a table a
theorem can read — `Tests/Coverage.lean` asserts the exact set, and the six
declined pairs are declined by an encoding fact rather than by an omission
nobody re-checks.

`blsi` is VEX-encoded and VEX.W selects 32 or 64, so it has no 16-bit form; none
of the six has an 8-bit form. -/
def bitcntEncodable : BitCntKind → Size → Bool
  | .blsi, sz => sz == .d || sz == .q
  | _,     sz => sz != .b


/-- P1 BATCH 17: which widths IMUL's two- and three-operand shapes EXIST at,
written as data beside the AST for the reason `bitcntEncodable` is.

⚠️ IT LOOKS LIKE `bitcntEncodable` AND IT SAYS THE SAME KIND OF THING — a form
with no encoding — which is the resemblance batch 16 had to disclaim about
`repApplies`, where it did NOT.  Here the resemblance is real: `imul %cl` is a
one-operand `.muldiv` and `imulb %cl, %al` does not assemble at all. -/
def imulrEncodable (sz : Size) : Bool := sz != .b

/-- P1 BATCH 18: the double shifts have no 8-bit encoding.  `0F A4`/`A5`/`AC`/
`AD` take a 16-, 32- or 64-bit operand and there is no byte form at all — the
same shape of fact as `imulrEncodable`, written the same way. -/
def dshiftEncodable (sz : Size) : Bool := sz != .b

/-- ⛔ P1 BATCH 18 — THE ONE PLACE THIS MODEL DECLINES TO ANSWER FOR A DOUBLE
SHIFT, AND WHY IT IS A REFUSAL RATHER THAN A GUESS OR AN OMISSION.

At `.w` a masked count above 16 leaves the DESTINATION undefined.  When that
destination is a REGISTER the model answers with the undefined-bit oracle, and
the machinery batch 14 built for `bsf`/`bsr` carries it: `declaredUndefGPRs`
names the register, `undefinedRegs` observes it move, and their EQUALITY is the
leak check.  There is no such channel for MEMORY.  `X86.undefinedLeaked` demands
that the two opposite oracle runs agree on every watched byte, and
`undefinableFields` in the comparator is a CLOSED list of flag and register
names whose own comment names the day a memory window reaches the undefined set
as the day it must be widened.

⇒ Rather than widen the model's strongest gate as a side effect of one batch,
this model REFUSES exactly the combination that would put an oracle bit into
memory: a memory destination, at `.w`, with a masked count above 16.  Every
other double shift — every width with a register destination, and `.w` in memory
with a count that is actually defined — is answered.  The refusal is a property
of (width, destination kind, count), so it is a theorem rather than a comment:
see `Tests/Coverage.lean`.  D52. -/
def dshiftMemUndefined (sz : Size) (dstIsMem : Bool) (n : Nat) : Bool :=
  dstIsMem && sz.bits < n

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
  | .rot k .. => match k with
    | .rol => "rol" | .ror => "ror" | .rcl => "rcl" | .rcr => "rcr"
  | .bit k .. => match k with
    | .bt => "bt" | .bts => "bts" | .btr => "btr" | .btc => "btc"
  | .setcc c _ => "set" ++ (c.suffixes.headD "?")
  | .cmov c _ _ _ => "cmov" ++ (c.suffixes.headD "?")
  | .call .. => "call"
  | .movx k .. => match k with | .zero => "movzx" | .sign => "movsx"
  | .cext k => k.mnemonic
  | .xchg .. => "xchg"
  | .bswap .. => "bswap"
  -- `addr32` does NOT change the mnemonic: AT&T spells the prefixed form
  -- `addr32 loop`, a prefix printed beside the same name — unlike `jrcxz`/
  -- `jecxz`, which really are two mnemonics for one instruction.
  | .loop k .. => match k with
    | .loop => "loop" | .loope => "loope" | .loopne => "loopne"
  | .flagop k => k.mnemonic
  -- AT&T prints the near return and LEAVE with the operand-size suffix even
  -- though neither has an operand; the roster files them under those names.
  | .nop _ => "nop"
  | .ud2 => "ud2"
  | .ret => "retq"
  | .leave => "leaveq"
  -- P1 BATCH 13.  The `x` suffix is the mnemonic, not a width: `shlx` is one
  -- instruction at two operand sizes, spelled `shlxl`/`shlxq` by AT&T exactly as
  -- `shl` is spelled `shll`/`shlq`.  The roster folds those widths, so these are
  -- the roster's own base names.
  | .shiftx k .. => match k with
    | .shl => "shlx" | .shr => "shrx" | .sar => "sarx"
  | .movbe .. => "movbe"
  | .bitcnt k .. => match k with
    | .popcnt => "popcnt" | .lzcnt => "lzcnt" | .tzcnt => "tzcnt"
    | .bsf => "bsf" | .bsr => "bsr" | .blsi => "blsi"
  | .strop k _ => k.mnemonic
  -- ⚠️ THE PREFIX IS THE MNEMONIC HERE, not the string op.  `p1/roster.tsv`
  -- files these eleven rows under their `prefix` column (`rep`, `repe`,
  -- `repne`, `repnz`, `repz`) with the string op in `base`, so a coverage claim
  -- keyed on `k.mnemonic` would name rows batch 15 already claims and leave
  -- these eleven unnamed.
  | .repstrop r _ _ => r.mnemonic
  | .muldiv k .. => k.mnemonic
  | .imulr .. => "imul"
  | .cmpxchg .. => "cmpxchg"
  | .xadd .. => "xadd"
  | .dshift k .. => k.mnemonic
  | .cmpxchg8b .. => "cmpxchg8b"

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
   "adc", "sbb", "jrcxz", "jecxz", "setcc", "cmovcc", "sar",
   "rol", "ror", "rcl", "rcr", "bt", "bts", "btr", "btc",
   -- P1 BATCH 10: the width-changing and two-destination moves.  `movzx` and
   -- `movsx` each stand for several AT&T spellings, as `setcc` and `cmovcc` do
   -- for thirty apiece; `movxSpellings` below is the table that says which, so
   -- the collapse is data a theorem can count rather than a claim in a comment.
   "movzx", "movsx", "cbtw", "cwtl", "cltq", "cwtd", "cltd", "cqto",
   "xchg", "bswap",
   -- P1 BATCH 11: the loop group and the flag-control singles.  `loope` and
   -- `loopne` each stand for two roster spellings (`loopz`, `loopnz`), as
   -- `setcc` stands for thirty; `loopSpellings` is the table that says which.
   "loop", "loope", "loopne",
   "clc", "stc", "cmc", "cld", "std",
   -- P1 BATCH 12: the near-free four of roster family 7.  `nop` covers all
   -- three of its roster shapes (bare `0x90` and the multi-byte `0F 1F /0` at a
   -- register and a memory operand) because they are one instruction.
   "nop", "ud2", "retq", "leaveq",
   -- P1 BATCH 13: the flagless shifts and the byte-swapping move.  `sarx`,
   -- `shlx` and `shrx` are three names for ONE constructor (`.shiftx`, keyed by
   -- `ShiftKind`), as `shl`/`shr`/`sar` are for `.shift`; `movbe` is its own.
   "sarx", "shlx", "shrx", "movbe",
   -- P1 BATCH 14: the bit-counting group.  Six names for ONE constructor
   -- (`.bitcnt`, keyed by `BitCntKind`), as `shl`/`shr`/`sar` are for `.shift`.
   -- ⚠️ `lzcnt` and `blsi` are on this list only because batch 13 MEASURED the
   -- oracle instead of reading its catalogue, which had struck both off; see
   -- docs/DECISIONS.md D36.
   "popcnt", "lzcnt", "tzcnt", "bsf", "bsr", "blsi",
   -- P1 BATCH 15: the string group.  Five names for ONE constructor
   -- (`.strop`, keyed by `StringOp`).  ⚠️ `movs` here is the STRING move, not
   -- the sign-extending `movsb`/`movsw`/`movslq` of batch 10 — see
   -- `StringOp.mnemonic` for why the roster base name is the only thing that
   -- tells them apart.  The `rep`-prefixed forms of these same opcodes are NOT
   -- claimed here; they are loop control over this data movement and are their
   -- own batch.
   "movs", "stos", "lods", "cmps", "scas",
   -- P1 BATCH 16: the repeat prefixes over that same data movement.  Three
   -- names for ONE constructor (`.repstrop`, keyed by `RepPrefix`), and `repe`
   -- and `repne` each stand for two roster spellings (`repz`, `repnz`) exactly
   -- as `loope` and `loopne` do; `repSpellings` is the table that says which.
   -- ⚠️ These are the PREFIX names, not the string ops — the five base names
   -- above are batch 15's rows and these eleven are separate rows of the same
   -- file, which is why the count moves by eleven and not by five.
   "rep", "repe", "repne",
   -- P1 BATCH 17: the multiply-divide group.  `mul`, `div` and `idiv` are one
   -- constructor apiece within `.muldiv`; `imul` is the only mnemonic in this
   -- model spread over TWO constructors — `.muldiv .imul` for the one-operand
   -- form that writes RDX:RAX, and `.imulr` for the two- and three-operand
   -- forms that write one register.  ⚠️ They are ONE roster row each way round:
   -- the roster files `imul` once as a base name at six shapes, and this list
   -- names mnemonics, so `imul` appears here once.
   "mul", "imul", "div", "idiv",
   -- P1 BATCH 18: the compare-exchange pair and the double-precision shifts.
   -- `shld` and `shrd` are two names for ONE constructor (`.dshift`, keyed by
   -- `DShiftKind`), as `shl`/`shr`/`sar` are for `.shift`; `cmpxchg` and `xadd`
   -- are a constructor apiece, because what is hard about each is different —
   -- one has a conditional destination, the other has two.
   "cmpxchg", "xadd", "shld", "shrd",
   -- P1 BATCH 21: the eight-byte compare-exchange.  ONE row, one constructor,
   -- one operand shape — and the last row of the roster that this model can
   -- claim at all: everything else outstanding either has no encoding
   -- (`jecxz rel32`, `jrcxz rel32`), is refused by the oracle at every
   -- pre-state (the nine BMI mnemonics and `movnti`), or was declined by a
   -- recorded decision (D23's bit-string `m,r`, D25's `xchg` at memory).
   "cmpxchg8b"]

/-- ⭐ EVERY ASSEMBLER SPELLING OF THE TWO WIDTH-CHANGING MOVES, for the same
reason `Cc.suffixes` exists: K's tree files `movzb`, `movzw`, `movsb`, `movsw`
and `movslq` as five separate base mnemonics, and this model has two
constructors.  A coverage claim over K's roster has to say which spellings a
constructor accounts for, and that is what this table is.

The width pair in the spelling reads SOURCE then DESTINATION (`movzbl` is
byte-to-long), which is the opposite order from the `Op.movx` argument list
(`dsz ssz`, destination first, as every other form in this AST writes its
destination first).  Both orders are conventional in their own place and this
sentence is the only thing that reconciles them. -/
def movxSpellings : MovxKind → List String
  | .zero => ["movzbw", "movzbl", "movzbq", "movzwl", "movzwq"]
  | .sign => ["movsbw", "movsbl", "movsbq", "movswl", "movswq", "movslq"]

/-- ⭐ EVERY ASSEMBLER SPELLING OF EACH LOOP PREDICATE, for the same reason
`Cc.suffixes` and `movxSpellings` exist: the roster files `loop`, `loope`,
`loopz`, `loopne` and `loopnz` as FIVE base mnemonics, and this model has three
constructors.  A coverage claim over that roster has to say which spellings a
constructor accounts for, and that is what this table is.

⚠️ AND THE COLLAPSE IS A FACT ABOUT THE MACHINE, NOT A CONVENIENCE: clang
assembles `loopz .+18` and `loope .+18` to the identical bytes `e1 10`, and
`loopnz`/`loopne` to `e0 10`.

⛔ THIS SENTENCE USED TO END BY NAMING A THEOREM — loop-synonyms-are-one-
encoding — AS LIVING IN Tests/Coverage.lean AND HOLDING THIS CLAIM "over the
vector table".  NO SUCH THEOREM WAS EVER WRITTEN.  It stood for five batches; P1 batch 16's
`scripts/check_citations.py` found it.  ⚠️ It could not have been written as
stated: there are no `loopz`/`loopnz` VECTORS and there must not be — a vector
per spelling is one instruction differentially tested twice — so a theorem
"over the vector table" had nothing to quantify over.  The claim is about an
ASSEMBLER, and it is now checked by one, in the `SYNONYMS` table of
`scripts/check_encodings.py`.  See docs/DECISIONS.md D48. -/
def loopSpellings : LoopKind → List String
  | .loop => ["loop"]
  | .loope => ["loope", "loopz"]
  | .loopne => ["loopne", "loopnz"]

def LoopKind.all : List LoopKind := [.loop, .loope, .loopne]

/-- The size of the implemented roster, named once.  Growing the roster changes
this and the three assertions in `Tests/Coverage.lean` follow — which is the
deliberate act that file's header asks for, rather than three separate numbers
drifting apart. -/
def rosterSize : Nat := rosterP0.length

end X86
