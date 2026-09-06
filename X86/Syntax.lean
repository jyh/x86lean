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
  /-- ⭐⭐ P2 ITEM 2: THE `LOCK` PREFIX (`F0`), CARRIED ON THE EFFECTIVE ADDRESS
  RATHER THAN ON THE INSTRUCTION, and the placement is the design.

  The SDM is explicit (Vol. 2A, "LOCK"): the prefix may be used *"only to those
  forms of the instruction where the destination operand is a MEMORY
  OPERAND"* — anything else is #UD.  So `lock` without a memory operand is not
  a state this AST should be able to describe, and putting the flag here makes
  that combination UNREPRESENTABLE instead of a runtime check somebody has to
  remember to write.

  ⚠️ THE ILLEGALITY IS A DECODE FACT, AND THIS AST IS POST-DECODE.  `f0 48 01
  c8` (`lock addq %rcx, %rax`) is rejected by the DECODER, and decode is trusted
  to XED and recorded as trusted (`TRUSTBASE.md`, and the coverage table's
  decode-trust column).  A model that could express it and then halted would be
  answering a question its own trust boundary says it does not answer.  What IS
  expressible, and therefore has to be checked here, is a lock on a memory
  destination of an instruction that is NOT on the SDM's lockable list — see
  `Op.lockable`.

  ⛔ AND IT DOES NOT CLAIM ATOMICITY.  A single-step, single-threaded semantics
  has no observation that distinguishes an atomic read-modify-write from a
  non-atomic one, and this field does not pretend otherwise: it RECORDS that the
  access is architecturally atomic, which is what D25 said the model lacked the
  vocabulary to say.  Having the vocabulary is what unblocks `xchg` at memory;
  it is not a claim that the model verifies anything about concurrency, and
  `TRUSTBASE.md` says so where a reader is looking. -/
  lock : Bool := false
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

/-- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 11 — WHICH 128-BIT MOVE THIS IS.

This field was `aligned : Bool` and it carried TWO facts at once: which mnemonic
a disassembler prints, and whether the form requires a 16-byte-aligned address.
That worked while there were exactly two mnemonics and the flag could stand for
both. `movaps`/`movups` are a THIRD and FOURTH spelling of the same 128-bit move
with the same alignment rule (SDM Vol. 2B, MOVAPS: "#GP(0) — if a memory operand
is not aligned on a 16-byte boundary"; MOVUPS states no such requirement), so a
Bool can no longer name the mnemonic.

⛔ THE ALIGNMENT RULE IS NOW DERIVED FROM THE MNEMONIC (`VMovKind.aligned`)
RATHER THAN CARRIED BESIDE IT. Two fields that must agree are two sources for
one fact and the second goes stale — the shape `vlanes` refuses for its lane
count and `vbinApply` for its widths. Here the mnemonic is the primitive datum
(it is what the encoding selects) and alignment is a function of it.

⚠️ FOUR MNEMONICS, FOUR OPCODES, ONE STATE TRANSITION BETWEEN REGISTERS —
`66 0f 6f`, `f3 0f 6f`, `0f 28`, `0f 10`. That they agree between registers is a
claim about the architecture and not an accident of this encoding, so it is a
theorem over ALL FOUR kinds (`vmov_kind_irrelevant`, Tests/Coverage.lean) rather
than the comment that first stated it for two.

⚠️ `aps`/`ups` are the SINGLE-PRECISION spellings and this model does not
distinguish them from the integer ones. That is deliberate and it is an
ARCHITECTURAL claim, not an oversight: the SDM gives MOVAPS and MOVDQA the same
data movement and the same fault, and the difference between them — a
domain-crossing forwarding penalty — is a MICROARCHITECTURAL property that no
architectural state in this model, or in the SDM, can observe. A model that
distinguished them would be modelling the pipeline. -/
inductive VMovKind where
  /-- `movdqa` — `66 0f 6f` / `66 0f 7f`. Aligned. -/
  | dqa
  /-- `movdqu` — `f3 0f 6f` / `f3 0f 7f`. Unaligned permitted. -/
  | dqu
  /-- `movaps` — `0f 28` / `0f 29`. Aligned. -/
  | aps
  /-- `movups` — `0f 10` / `0f 11`. Unaligned permitted. -/
  | ups
  /-- ⭐ P2 BATCH 35 — `movapd` — `66 0f 28` / `66 0f 29`. Aligned.

  ⚠️ THE `66` IS A MANDATORY PREFIX, NOT AN OPERAND-SIZE OVERRIDE. `0f 28` with
  no prefix is `movaps` and with `66` it is `movapd`; the prefix SELECTS THE
  MNEMONIC and changes nothing this model can observe about the transfer. Both
  move all 128 bits and both fault on a misaligned memory operand, so the pair
  stands to `movaps` exactly as `movdqa` does — a spelling a disassembler
  prints, held apart by the encoding gate and not by the differential. -/
  | apd
  /-- ⭐ P2 BATCH 35 — `movupd` — `66 0f 10` / `66 0f 11`. Unaligned permitted. -/
  | upd
  deriving DecidableEq, Repr, Inhabited, BEq

/-- ⭐⭐ P2 BATCH 22 — the PREFETCH locality hint (SDM Vol. 2B, PREFETCHh).

⛔ **THE HINT IS ARCHITECTURALLY INVISIBLE**, and that is the whole difficulty of
the form rather than a detail of it. All four spellings share opcode `0f 18` and
differ only in the ModRM `/reg` field; the SDM says the hint influences cache
state and *"does not affect program behavior"*. So the four are FOUR ROWS — a
disassembler prints four names — carrying ONE semantics, and no differential
vector can tell them apart. See `Op.prefetch`. -/
inductive PrefetchHint where
  /-- `prefetchnta` — `0f 18 /0`. Non-temporal. -/
  | nta
  /-- `prefetcht0` — `0f 18 /1`. All cache levels. -/
  | t0
  -- ⛔ `/2` AND `/3` (`prefetcht1`, `prefetcht2`) ARE NOT HERE, and their absence
  -- is demand, not oversight.  The census measures 315 instructions of
  -- `prefetchnta` and 151 of `prefetcht0` and **none at all** of the other two,
  -- and this roster is demand-driven — `pshufw` is declined on the same rule.
  -- ⭐ THE KERNEL-COST GATE IS WHAT NAMED THIS: with four hints the batch put
  -- `Tests.Coverage`'s residue 700 ms over its ceiling, because four roster rows
  -- cost several `decide` theorems that are quadratic in the row count.  The
  -- gate refused, the cheaper build was the demand-honest one, and it weakens
  -- nothing ([[feedback-a-gate-that-refuses-names-a-cheaper-build]]).
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The mnemonic a disassembler prints for this hint. -/
def PrefetchHint.mnemonic : PrefetchHint → String
  | .nta => "prefetchnta" | .t0 => "prefetcht0"

/-- Whether this mnemonic requires a 16-byte-aligned memory operand (SDM Vol. 2B,
MOVDQA / MOVAPS: #GP(0) otherwise). ⚠️ DERIVED, never stored beside the kind. -/
def VMovKind.aligned : VMovKind → Bool
  | .dqa | .aps | .apd => true
  | .dqu | .ups | .upd => false

/-- The mnemonic a disassembler prints for this kind. -/
def VMovKind.mnemonic : VMovKind → String
  | .dqa => "movdqa" | .dqu => "movdqu" | .aps => "movaps" | .ups => "movups"
  | .apd => "movapd" | .upd => "movupd"

/-- ⭐⭐ P2 BATCH 35 — EVERY KIND, so a claim about the alignment rule can be made
about the TYPE rather than about a list of literals someone remembered to update.

⛔ THIS EXISTS BECAUSE THE CLAIM THAT MOTIVATED IT WAS FALSE WHEN I ARRIVED.
`Tests.vmov_alignment_is_by_kind` asserted the partition over `dqa`/`aps`/`dqu`/
`ups` and its docstring said *"written as a claim about the derived flag rather
than as four separate cases, so a fifth mnemonic cannot be added without
answering the question."*  It is four separate cases. Adding `.apd` and `.upd`
left the theorem TRUE, GREEN and SILENT about both — the prose described the
theorem the author meant to write.  Paired with `vmov_kinds_are_all_listed`
below, whose `cases` is exhaustive by construction, the enumeration now cannot
fall behind the type: a seventh kind fails to compile rather than passing
unmentioned.  [[feedback-a-declared-list-inherits-its-default]]
[[feedback-a-citation-is-an-ungated-claim]] -/
def VMovKind.all : List VMovKind := [.dqa, .dqu, .aps, .ups, .apd, .upd]

/-- ⭐⭐ P2 BATCH 36 — WHICH QUADWORD OF THE DESTINATION A HALF-MOVE WRITES.

The four half-moves (`movlps` `movlpd` `movhps` `movhpd`) differ from one another
in exactly two independent ways, and this is the one with SEMANTIC content: the
half that is written, and therefore the half that is PRESERVED. -/
inductive VHalf where
  /-- The LOW quadword is written; `dst[127:64]` is preserved. `0f 12` / `0f 13`. -/
  | lo
  /-- The HIGH quadword is written; `dst[63:0]` is preserved. `0f 16` / `0f 17`. -/
  | hi
  deriving DecidableEq, Repr

/-- ⭐⭐ P2 BATCH 36 — THE MANDATORY PREFIX OF A HALF-MOVE, i.e. ITS SPELLING.

⚠️ THIS IS A DIFFERENT FIELD FROM `VMovKind` AND THE DIFFERENCE IS THE ARGUMENT
FOR IT. `VMovKind`'s entire content is `VMovKind.aligned` — the 16-byte #GP rule —
and `vloadq`'s docstring is right that a half-move has no such rule to carry (an
8-byte operand is Exception Type 5, MEASURED on the oracle at three alignments
with a two-sided control, D119). `VQuadKind`'s content is the PREFIX BYTE, and
the prefix selects the MNEMONIC: `0f 12` is `movlps` and `66 0f 12` is `movlpd`.
That is meaningful where an `aligned` answer would not have been, which is why
this is a kind and not a fifth and sixth constructor. -/
inductive VQuadKind where
  /-- No prefix — the `ps` spelling. -/
  | ps
  /-- `66` — the `pd` spelling. -/
  | pd
  deriving DecidableEq, Repr

/-- Every half, so a claim can be made about the TYPE rather than about a list of
literals someone remembered to update — `VMovKind.all`'s reason, and batch 35's. -/
def VHalf.all : List VHalf := [.lo, .hi]

/-- Every spelling, for the same reason. -/
def VQuadKind.all : List VQuadKind := [.ps, .pd]

/-- The mnemonic a disassembler prints for a half-move.

⚠️ FOUR LITERALS AND NOT A CONCATENATION. This string is walked character by
character inside a kernel `decide`, and building it with `++` would put that
work on the hot path — the cost this repository has already paid twice.
[[feedback-prose-in-a-kernel-reduced-string-is-a-cost]] -/
def quadMnemonic : VHalf → VQuadKind → String
  | .lo, .ps => "movlps" | .lo, .pd => "movlpd"
  | .hi, .ps => "movhps" | .hi, .pd => "movhpd"

/-- ⭐⭐⭐ P2 VECTOR WAVE — THE PACKED-INTEGER BINARY OPERATIONS, and the LANE
WIDTH is part of the kind rather than a `Size`.

`Size` in this model means the width of ONE value (SDM Vol. 1 §3.4.1.1's rule
about what a write does to the rest of the register).  A packed operation has
two widths that are both essential and neither of which is that one: the
register is always 128 bits, and the LANE is 8, 16, 32 or 64.  Reusing `Size`
here would have made `paddd` and `paddw` differ in a field that every other
`Op` uses to mean something else — so the lane lives in the kind, exactly as
`BinKind` carries the difference between `add` and `adc` rather than a flag.

⚠️ The lane WIDTH is not repeated in a table beside this type. It is written
once per case in `vbinApply` (X86/Semantics.lean) and the lane COUNT is derived
from it there, never written down — a width and a count side by side is two
sources for one fact and the second one goes stale (D41/D74's shape).

⚠️ The bitwise three (`pxor`, `pand`, `por`) have NO lane width: they are the
same function at every lane, which is why the SDM gives them one entry and no
`b/w/d/q` suffix. They are here rather than in `BinKind` because their operands
are XMM registers, and that is a different register FILE, not a different
width. -/
inductive VBinKind where
  /-- Packed add, 16 lanes of 8 / 8 of 16 / 4 of 32 / 2 of 64 (SDM Vol. 2B,
  PADDB/PADDW/PADDD/PADDQ).  Each lane wraps independently — there is no carry
  between lanes and no flag is written. -/
  | addb | addw | addd | addq
  /-- Packed subtract (SDM Vol. 2B, PSUBB/PSUBW/PSUBD/PSUBQ). -/
  | subb | subw | subd | subq
  /-- The bitwise trio (SDM Vol. 2B, PXOR/PAND/POR): lane-independent. -/
  | xor | and | or
  /-- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 7 — THE UNPACK (INTERLEAVE) GROUP, SDM Vol. 2B
  PUNPCKL*/PUNPCKH*.  These are the first vector operations here that are not
  lane-wise ARITHMETIC but a PERMUTATION: they take half the lanes of each
  operand and interleave them, destination lane first.

  ⚠️ `l`/`h` selects WHICH half is consumed — the low half of each operand or the
  high half — and it is not a variant of the same function: `punpckl` and
  `punpckh` read disjoint halves of their inputs, so no pre-state in which the
  two halves agree can tell them apart.  That is worth knowing before trusting a
  green run on them. -/
  | unpcklb | unpcklw | unpckld | unpcklq
  | unpckhb | unpckhw | unpckhd | unpckhq
  /-- ⭐⭐ P2 BATCH 37 — THE `ps`/`pd` SPELLINGS OF FOUR UNPACKS.  Batch 34's
  shape exactly: the SAME function at another opcode, so they join `vbinApply`'s
  arm rather than copying it, and they are separate KINDS because the BYTES
  differ (`0f 14` against `66 0f 62`).

  ⛔⛔ THE IDENTITY WAS DECIDED ON K'S LEAF SEQUENCE, NOT ON ITS TEXT, AND THE
  TEXT WOULD HAVE SAID SOMETHING ELSE.  Whitespace-normalised, the two `pd` pairs
  are byte-identical and the two `ps` pairs DIFFER at char 122 of 345 — the
  difference being pure RE-ASSOCIATION of `concatenateMInt`, which is associative
  on bit strings.  Under the leaf-sequence normal form all four pairs are
  identical and three controls (`unpcklps`/`unpckhps`, `unpcklpd`/`unpcklps`,
  `punpckldq`/`punpcklqdq`) DIFFER.
  ⇒ 🔑 a byte comparison over the four would have reported *two spellings, two new
  semantics* — a self-consistent WRONG design with a ready-made `ps`/`pd`
  explanation attached.  A comparison that fails on HALF a set invites a theory of
  the half.  ⭐ A THIRD SOURCE agrees independently of K: LLVM's disassembler
  prints the same operand comment for each pair (`unpcklps` and `punpckldq` both
  `xmm0[0],xmm1[0],xmm0[1],xmm1[1]`).
  [[feedback-a-generated-files-text-is-not-its-meaning]]
  [[feedback-the-third-source-turns-a-disagreement-into-a-finding]] -/
  | unpcklps | unpckhps | unpcklpd | unpckhpd
  /-- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 17 — THE PACKED COMPARES (SDM Vol. 2B,
  PCMPEQB/W/D and PCMPGTB/W/D).  They join `VBinKind` rather than taking a kind of
  their own, and the reason is that they ARE packed binary operations: two XMM
  operands, lane-wise, no flag written, and — the part that decides it — BOTH
  OPERAND SHAPES COME FREE, because `Op.vbin` and `Op.vbinm` already carry them.
  A separate inductive would have needed its own memory constructor, its own step
  arm and its own alignment branch, all identical to these.

  ⚠️ THE RESULT IS A MASK, NOT A FLAG: a lane is set to ALL ONES or all zeros,
  never to 1.  That is the model a reader coming from `Flags` writes, and it is
  bit-identical to this one in the low bit of every lane — which is why the
  planted `boolean` arm exists and why it is caught weakly at `pcmpeqd` (12 of 88
  pre-states agree with it) and strongly at the memory forms (0 of 88).

  ⛔ `pcmpgt` IS A **SIGNED** COMPARISON, and `pcmpeq` is neither signed nor
  unsigned — equality is the same relation either way, so an `eq` vector prices
  NOTHING about signedness and the two must not be pooled when counting what the
  group tests. -/
  | cmpeqb | cmpeqw | cmpeqd
  | cmpgtb | cmpgtw | cmpgtd
  /-- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 18 — `packuswb` (SDM Vol. 2B, PACKUSWB): eight
  SIGNED words from the destination and eight from the source, each SATURATED to
  an UNSIGNED byte, destination's low.

  ⛔⛔ **THE SIGNEDNESS IS ASYMMETRIC AND THAT IS THE WHOLE INSTRUCTION**: the
  SOURCE lanes are read as SIGNED and the RESULT lanes are UNSIGNED, so a negative
  word saturates to **0** and a word above 255 to **255**. A model that read the
  source as unsigned would send every negative word to 255 — the opposite end of
  the range — and it agrees with this one at 32 of 88 pre-states at the register
  shape and 0 of 88 at the memory shape (measured before this was written).

  ⚠️ AND TRUNCATION IS THE OTHER MODEL: keeping the low byte is bit-identical at
  every in-range value, which is every value a casual vector table contains. It
  agrees at 0 of 88 here only because the pre-states reach out of range.

  ⛔ ITS TWO SIGNED SIBLINGS ARE NOT HERE AND CANNOT BE: `packsswb` and `packssdw`
  REFUSE on the oracle at every pre-state (D115), and `packssdw` is roster rank 15
  at 5,613 instructions. A batch sampled at `packuswb` — its own sibling — would
  have been written against an oracle that cannot run two thirds of the group. -/
  | packuswb
  /-- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 34 — THE BITWISE COMPLEMENT, and the group is
  named by what it does NOT need rather than by an extension.

  Nine mnemonics that operate on XMM registers and are **pure bit manipulation**:
  no rounding, no MXCSR, no lane width, no new state.  They are the part of the
  SSE-legacy residue that the soft-float commission's forty pairs do not cover —
  measured, 24 pairs / 11,040 instructions, of which these nine are the bitwise
  half (D157).  Being FP-TYPED is not the same as being FP-VALUED: `xorps` reads
  no exponent and writes no rounded result, and neither does any member here.

  ⛔⛔ **`ANDN` IS ASYMMETRIC AND THAT IS THE WHOLE OPERATION.** SDM Vol. 2B
  (PANDN/ANDNPS/ANDNPD): `DEST ← (NOT DEST) AND SRC`.  The destination is
  complemented, **not** the source.  The model a reader writes from the mnemonic
  is `DEST AND (NOT SRC)`, which is a different function everywhere the two
  operands differ, and `wrongAndnComplementsSource` is that model planted.
  ⭐ CONFIRMED ON A SECOND, INDEPENDENT SOURCE before this was written: K's
  `pandn_xmm_xmm.k` reads `andMInt(negMInt(DEST), SRC)`, and `negMInt` is bitwise
  NOT rather than arithmetic negation — read off `sbbb_rh_imm8.k`, where
  `a + negMInt(b)` is the CF=1 arm of `a - b - CF` and so can only be one's
  complement.  A rule this easy to get backwards is not taken from one reading
  ([[feedback-two-readings-are-not-two-witnesses]]).

  ⚠️ **SIX OF THE NINE ARE NEW ENCODINGS OF AN OPERATION ALREADY HERE**, and they
  are separate KINDS rather than a field because the bytes differ — `pand` is
  `66 0f db`, `andps` is `0f 54`, `andpd` is `66 0f 54`, all three measured on the
  assembler.  That is the `movdqa`/`movaps` rule (`VMovKind`), not the
  `pmovmskb` r32/r64 one: batch 18 refused a width field because the two
  spellings emitted IDENTICAL bytes, so no encoding could set it.  Here every
  spelling is distinguishable, and the `synonym collapse` gate is what would say
  otherwise.

  ⚠️ Their SEMANTICS is shared by NOT branching on the kind — `vbinApply` gives
  `.and`, `.andps` and `.andpd` one arm — so nine kinds add three arms and one new
  function.  A second copy of `a &&& b` under another name is a duplicate born in
  agreement ([[feedback-a-duplicate-born-in-agreement]]). -/
  | andn | andnps | andnpd
  | andps | andpd | orps | orpd | xorps | xorpd
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The assembler spelling of each packed binary operation.  ⭐ ONE TABLE FOR
BOTH OPERAND SHAPES (`Op.vbin` and `Op.vbinm`): the memory form prints exactly
what the register form does, and a second copy would be a duplicate that diverges
the day one of them is corrected. -/
def VBinKind.mnemonic : VBinKind → String
  | .addb => "paddb" | .addw => "paddw" | .addd => "paddd" | .addq => "paddq"
  | .subb => "psubb" | .subw => "psubw" | .subd => "psubd" | .subq => "psubq"
  | .xor => "pxor"   | .and => "pand"   | .or => "por"
  | .unpcklb => "punpcklbw" | .unpcklw => "punpcklwd"
  | .unpckld => "punpckldq" | .unpcklq => "punpcklqdq"
  | .unpckhb => "punpckhbw" | .unpckhw => "punpckhwd"
  | .unpckhd => "punpckhdq" | .unpckhq => "punpckhqdq"
  -- P2 BATCH 37: four spellings of operations two lines above.  The BYTES differ,
  -- so they are four roster rows; the semantics is shared by not branching.
  | .unpcklps => "unpcklps" | .unpckhps => "unpckhps"
  | .unpcklpd => "unpcklpd" | .unpckhpd => "unpckhpd"
  | .cmpeqb => "pcmpeqb" | .cmpeqw => "pcmpeqw" | .cmpeqd => "pcmpeqd"
  | .cmpgtb => "pcmpgtb" | .cmpgtw => "pcmpgtw" | .cmpgtd => "pcmpgtd"
  | .packuswb => "packuswb"
  -- P2 BATCH 34: one spelling per kind.  ⚠️ `pandn`, `andnps` and `andnpd` are
  -- ONE function at three opcodes, so they share `vbinApply`'s arm and differ
  -- only here and in the bytes a vector carries.
  | .andn => "pandn"   | .andnps => "andnps" | .andnpd => "andnpd"
  | .andps => "andps"  | .andpd => "andpd"
  | .orps => "orps"    | .orpd => "orpd"
  | .xorps => "xorps"  | .xorpd => "xorpd"

/-- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 13 — THE PACKED SHIFTS' OPERATION, HELD APART
FROM THEIR LANE WIDTH.

⚠️ **THIS IS A DEPARTURE FROM `VBinKind`, WHICH PUTS THE LANE IN THE KIND**
(`addb`/`addw`/`addd`/`addq`), and the burden is on the departure.  What let
`VBinKind` do that is that it has NO HOLE: add and sub both exist at all four
lane widths, so there was never an absent pair to represent.  The shifts have
TWO holes, and each is an ENCODING FACT rather than a decision of this model:

  * there is **no packed BYTE shift at all** — `psllb` does not assemble, at any
    of the three operations;
  * there is **no `psraq`** in this model's encoding space.  `psllq` and `psrlq`
    exist, and the ARITHMETIC right shift stops at the doubleword (SDM Vol. 2B,
    PSRAW/PSRAD list W and D and no Q).  `psraq` is real but EVEX-only, i.e. in
    the AVX-512 batch this model has measured its oracle cannot answer at all.

A hole is exactly what `bitcntEncodable` exists for, and this repository's rule
is that a form the model declines is DATA A THEOREM CAN READ rather than a
constructor nobody wrote.  A flat eight-constructor kind list would have made
"there is no `psraq`" an ABSENCE, and an absence in a declared list falls the way
the default points ([[feedback-a-declared-list-inherits-its-default]]). -/
inductive VShiftOp where
  /-- Packed shift left LOGICAL (SDM Vol. 2B, PSLLW/PSLLD/PSLLQ). -/
  | sll
  /-- Packed shift right LOGICAL (PSRLW/PSRLD/PSRLQ): zeroes shift in. -/
  | srl
  /-- Packed shift right ARITHMETIC (PSRAW/PSRAD): the lane's own SIGN BIT
  shifts in, which is the whole difference from `srl` and is invisible at any
  pre-state whose lanes are all non-negative. -/
  | sra
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The lane width a packed shift operates at.

⚠️ `w8` IS HERE ON PURPOSE, so that "there is no packed byte shift" is a ROW OF
`vshiftEncodable` rather than a constructor nobody wrote — the same choice
`vmovsEncodable` makes by ranging over all four `Size`s and admitting two.  It is
NOT `Size`, for the reason `VBinKind`'s note gives: `Size` in this model means
the width of ONE value, and a packed operation's register is always 128 bits
while its LANE is 8, 16, 32 or 64. -/
inductive VShiftW where
  | w8 | w16 | w32 | w64
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The lane width in bits.  ⚠️ The LANE COUNT is never written beside it —
`vshiftApply` derives `128 / bits`, for the reason `vlanes` does. -/
def VShiftW.bits : VShiftW → Nat
  | .w8 => 8 | .w16 => 16 | .w32 => 32 | .w64 => 64

/-- Which (operation, lane width) pairs EXIST, written as data beside the AST for
the reason `bitcntEncodable` is: `Tests/Coverage.lean` asserts the exact declined
set, so the two holes are re-checked by the kernel rather than by a reader. -/
def vshiftEncodable : VShiftOp → VShiftW → Bool
  | _,    .w8  => false        -- no packed byte shift exists, at any operation
  | .sra, .w64 => false        -- and no PSRAQ outside AVX-512
  | _,    _    => true

/-- The assembler spelling.  ⚠️ THE SUFFIX NAMES THE LANE, NOT THE OPERAND SIZE:
`psrad` shifts four 32-bit lanes of a 128-bit register, and every other `w/d/q`
suffix in this AST names the width of the whole value.

⚠️ The two UNENCODABLE pairs are given their real architectural names rather than
a placeholder — `psraq` is a genuine AVX-512 mnemonic and `psllb` is what a byte
shift would be called — because a `mnemonic` that lied about an unreachable case
would be a worse thing to read than one that is simply out of this model's
encoding space.  `vshiftEncodable` is what says which are reachable. -/
def VShiftOp.mnemonic : VShiftOp → VShiftW → String
  | .sll, .w8 => "psllb" | .sll, .w16 => "psllw"
  | .sll, .w32 => "pslld" | .sll, .w64 => "psllq"
  | .srl, .w8 => "psrlb" | .srl, .w16 => "psrlw"
  | .srl, .w32 => "psrld" | .srl, .w64 => "psrlq"
  | .sra, .w8 => "psrab" | .sra, .w16 => "psraw"
  | .sra, .w32 => "psrad" | .sra, .w64 => "psraq"

/-- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 14 — THE PERMUTE (SHUFFLE) GROUP'S KIND.

`pshufd`, `pshuflw` and `pshufhw` are ONE opcode (`0F 70 /r ib`) under three
mandatory prefixes (`66`, `F2`, `F3`), and they are the first operations in this
model that **read a source and write a destination without combining them**: no
lane of the result is a function of the destination's old value, and no lane is a
function of more than one source lane.  A permutation, not an operation.

⚠️ **THERE IS NO LANE-WIDTH FIELD, AND ITS ABSENCE IS THE POINT.**  The reflex
from `VShiftW` is to carry `w16`/`w32` beside the kind, and it would be wrong
twice: `lw` and `hw` are not one function at two widths (they consume DISJOINT
halves of the source, exactly as `punpckl`/`punpckh` do), and `d` is not a third
width of the same function (it replaces the whole register, where both word forms
COPY the untouched quadword through).  The width is a consequence of the kind,
so it is derived in `vshufApply` and written nowhere else.

⛔ **`pshufw` IS NOT HERE, AND IT IS DECLINED BY REGISTER FILE, NOT BY OVERSIGHT.**
`0F 70 /r ib` with no prefix takes MMX operands, and this model has no MMX
register file (the same decline the packed shifts made for 2,822 of their
instructions, D107).  Measured on the census's `asm` class: **642 of 642 of this
corpus's `pshufw` are MMX-register forms**, so the decline costs the model nothing
it could otherwise have claimed — but it is stated here because a mnemonic absent
from a kind is an ABSENCE, and an absence falls the way the default points. -/
inductive VShufKind where
  /-- `pshufd` (`66 0F 70 /r ib`): four 32-bit lanes selected from the source by
  the four 2-bit fields of the immediate.  The WHOLE register is written. -/
  | d
  /-- `pshuflw` (`F2 0F 70 /r ib`): the source's four LOW words are selected into
  the destination's four low words; **the high quadword is COPIED FROM THE
  SOURCE**, not preserved from the destination — the destination's old value is
  not read at all. -/
  | lw
  /-- `pshufhw` (`F3 0F 70 /r ib`): the source's four HIGH words, selected into
  the destination's four high words, with the source's low quadword copied
  through.  ⚠️ `lw` and `hw` consume DISJOINT halves, so no pre-state whose two
  halves agree can tell them apart. -/
  | hw
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The assembler spelling.  One mnemonic per kind and no suffix table: unlike
the shifts, the letter in the name (`d`/`lw`/`hw`) is the KIND and not a lane
width, so there is nothing here for a width to disagree with. -/
def VShufKind.mnemonic : VShufKind → String
  | .d => "pshufd" | .lw => "pshuflw" | .hw => "pshufhw"

/-- ⭐⭐⭐ P2 BATCH 37 — THE TWO-SOURCE SHUFFLE, AND WHY IT IS NOT A `VShufKind`.

`shufps` and `shufpd` are 88% of this batch's demand (1,545 + 70 of 1,833) and the
only new SEMANTICS in it.  ⛔⛔ **`VShufKind` IS THE WRONG HOME AND THE REASON IS
STRUCTURAL, NOT STYLISTIC**: every member of that kind selects lanes from ONE
source (`pshufd` permutes its source; `pshuflw`/`pshufhw` permute half of it and
copy the other half THROUGH from the same source).  These read BOTH operands —
the low half of the result comes from the DESTINATION and the high half from the
SOURCE — so `vshufApply`, whose signature takes a single `src`, could not express
them at any kind.  A new constructor, not a new member.

⭐ K DECIDES BOTH, and the bit order is K's big-endian read against the SDM's
`Select4`:
```
   shufps   lane0 ← DEST[imm[1:0]]   lane1 ← DEST[imm[3:2]]
            lane2 ← SRC [imm[5:4]]   lane3 ← SRC [imm[7:6]]
   shufpd   qword0 ← DEST[imm[0]]    qword1 ← SRC[imm[1]]
```
⭐ CONFIRMED BY A THIRD SOURCE before a line was written: LLVM disassembles
`shufps $0x1b,%xmm1,%xmm0` as `xmm0 = xmm0[3,2],xmm1[1,0]` and
`shufpd $0x1,%xmm1,%xmm0` as `xmm0 = xmm0[1],xmm1[0]` — both exactly this rule.

⚠️ BOTH PRESERVE THE YMM UPPER 128 (legacy SSE), which K writes explicitly as
`extractMInt(R3, 0, 128)`.  This model's `XmmReg` is 128 bits wide, so that half
of the rule is carried by the TYPE and there is nothing here to state it. -/
inductive VShufpKind where
  /-- `shufps` (`0F C6 /r ib`): four 32-bit lanes, two from each operand. -/
  | ps
  /-- `shufpd` (`66 0F C6 /r ib`): two 64-bit lanes, one from each operand.
  ⚠️ Only the low TWO bits of the immediate are read; the SDM's `imm8[7:2]` are
  ignored, so a vector varying them cannot witness anything. -/
  | pd
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Every two-source shuffle spelling, so a claim can be made about the TYPE. -/
def VShufpKind.all : List VShufpKind := [.ps, .pd]

/-- The assembler spelling.  Two literals, not a concatenation (`quadMnemonic`'s
reason: this is walked character by character inside a kernel `decide`). -/
def VShufpKind.mnemonic : VShufpKind → String
  | .ps => "shufps" | .pd => "shufpd"

/-- ⭐⭐ P2 BATCH 37 — WHICH LANE WIDTH A SIGN-MASK REDUCES, i.e. WHICH
MNEMONIC.  `Op.vmovmsk` carried no field at all until this batch: it was built for
`pmovmskb` alone (batch 23) and its lane count was the literal sixteen.

`movmskps` is the SAME REDUCTION at a different lane width — one sign bit per
32-bit lane instead of one per byte — so it is a KIND on the existing constructor
and not a new one.  The two are held apart by their BYTES (`66 0f d7` against
`0f 50`), which `scripts/check_encodings.py` is the instrument for.

⚠️ **THE LANE COUNT IS DERIVED FROM `laneBits`, NOT WRITTEN.**  `Op.vmovmsk`'s
semantics folded over a literal `List.range 16`, and the comment beside it already
said why that was a hazard — *"a literal sixteen repeated in the body is a place
for a typo no type can catch"*.  A second kind is exactly the change that would
have paid that price, so the count is `128 / laneBits` and appears once.

⛔ **AND THERE IS STILL NO WIDTH FIELD, MEASURED ON THIS MNEMONIC RATHER THAN
INHERITED FROM `pmovmskb`'s.**  The `r32`/`r64` question has to be asked again for
every mnemonic that has both rows, because the answer is a fact about the
ASSEMBLER and not about the family: `movmskps %xmm1,%eax` and `movmskps %xmm1,%rax`
both assemble to `0f50c1` (measured with `clang -target x86_64-unknown-linux-gnu`,
the assembler `check_encodings.py` uses), exactly as `pmovmskb`'s two rows both give
`660fd7c1`.  K agrees on the other side — `movmskps_r32_xmm.k` and
`movmskps_r64_xmm.k` are the identical `concatenateMInt(mi(60,0), …)` — so the two
SDM rows are one semantics AND one encoding here too.
[[feedback-inherited-diagnosis-is-a-hypothesis]] [[feedback-a-batch-cannot-be-sampled]] -/
inductive VMovMskKind where
  /-- `pmovmskb` (`66 0F D7 /r`): one sign bit per BYTE, sixteen lanes. -/
  | b
  /-- `movmskps` (`0F 50 /r`): one sign bit per 32-bit lane, four lanes.
  ⚠️ `movmskpd` (`66 0F 50 /r`) is a third member this type does not have: it
  has ZERO measured demand in the census, and an absence falls the way the default
  points, so it is declined HERE in writing rather than left unmentioned. -/
  | ps
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Every kind, so a claim can be made about the TYPE rather than about a list of
literals someone remembered to update — `VMovKind.all`'s reason, and batch 35's. -/
def VMovMskKind.all : List VMovMskKind := [.b, .ps]

/-- The assembler spelling.

⚠️ TWO LITERALS AND NOT A CONCATENATION, for `quadMnemonic`'s reason: this string
is walked character by character inside a kernel `decide`.
[[feedback-prose-in-a-kernel-reduced-string-is-a-cost]] -/
def VMovMskKind.mnemonic : VMovMskKind → String
  | .b => "pmovmskb" | .ps => "movmskps"

/-- The WIDTH OF ONE LANE in bits, which is the whole semantic content of the
kind: the lane COUNT is `128 / laneBits` and the sign bit of lane `i` sits at
`laneBits * i + (laneBits - 1)`.  Both are derived in `X86.Semantics` and written
nowhere else. -/
def VMovMskKind.laneBits : VMovMskKind → Nat
  | .b => 8 | .ps => 32

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

/-- P1 BATCH 10: LOOP / LOOPE / LOOPNE (SDM Vol. 2A, LOOP/LOOPcc).  One
constructor per PREDICATE, exactly as `Cc` is: `loopz` is `loope` and `loopnz`
is `loopne` — clang assembles `loopz` and `loope` to the SAME BYTES (`E1 cb`),
and a model that distinguished them would be modelling the assembler.
`loopSpellings` below is the table that says which names each accounts for. -/
inductive LoopKind where
  | loop | loope | loopne
  deriving DecidableEq, Repr, Inhabited, BEq

/-- P1 BATCH 10: the FLAG-CONTROL singles (SDM Vol. 2A, CLC/STC/CMC/CLD/STD;
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
  /-- P1 BATCH 10: LOOP / LOOPE / LOOPNE (SDM Vol. 2A).  ⚠️ THE COUNTER IS
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
  /-- P1 BATCH 10: CLC/STC/CMC/CLD/STD.  See `FlagOp`. -/
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
  /-- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 2 — THE FIRST INSTRUCTION IN THIS MODEL THAT
  WRITES AN XMM REGISTER.

  `movdqa` and `movdqu` between two REGISTERS are one instruction here, and that
  is a modelling statement, not a shortcut: the alignment rule that separates
  them applies to a MEMORY operand ("when the source or destination operand is a
  memory operand, the operand must be aligned on a 16-byte boundary" — SDM
  Vol. 2B, MOVDQA), and between registers there is no address to be aligned. The
  same reasoning already collapses `sal` into `shl`.

  ⛔ THE MEMORY FORMS ARE NOT HERE, and their absence is deliberate rather than
  pending. They need a 128-bit memory path (`readMem`/`writeMem` are defined at
  `Size`, which stops at 64) AND they are where `movdqa` and `movdqu` STOP being
  the same instruction — an unaligned `movdqa` is #GP. That is a semantic
  question of its own and it gets its own batch rather than riding in on this
  one.

  ⚠️ `aligned` RECORDS WHICH OF THE TWO IT WAS, and it is deliberately inert
  here. `movdqa` is `66 0f 6f` and `movdqu` is `f3 0f 6f` — DIFFERENT OPCODES, so
  unlike `sal`/`shl` these are not one encoding under two spellings and the model
  must not print one name for the other. Between registers the flag changes
  nothing, and that is the SDM's own claim rather than an accident of this
  encoding — so it is stated as a theorem (`vmov_aligned_irrelevant`,
  Tests/Coverage.lean) instead of a comment. It becomes load-bearing on the day
  the memory forms arrive, which is the day the two stop agreeing. -/
  | vmov  (k : VMovKind) (dst src : XmmReg)
  /-- P2 VECTOR WAVE, BATCH 2 — the packed-integer binary operations between two
  XMM registers (SDM Vol. 2B). "Flags Affected: None" for every one of them: a
  packed operation writes no flag, which is the single most important thing to
  get right about them and the easiest to get wrong by analogy with `BinKind`. -/
  | vbin  (k : VBinKind) (dst src : XmmReg)
  /-- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 3 — THE MEMORY FORMS, and the point at which
  `movdqa` and `movdqu` STOP BEING THE SAME INSTRUCTION.

  `aligned` was inert in `vmov` because between two registers there is no address
  to align.  Here there is: `movdqa` requires the effective address to be a
  multiple of 16 and raises **#GP(0)** otherwise (SDM Vol. 2B, MOVDQA), while
  `movdqu` has no such requirement.  Same operands, same width, same data
  movement — and one of them faults.

  ⚠️ TWO CONSTRUCTORS RATHER THAN ONE WITH A `VOperand` PAIR, and the reason is
  the same one that made `wellFormed2` necessary for the GPR forms: an operand
  type admitting both `xmm` and `mem` on both sides can represent
  `movdqa (%rax), (%rbx)`, which no encoding produces, and the model would then
  need a well-formedness CHECK where it could instead have a type that cannot
  say it.  Splitting load from store makes the illegal state unrepresentable —
  strictly better than the shape `Op.mov` is stuck with. -/
  | vload  (k : VMovKind) (dst : XmmReg) (ea : Ea)
  | vstore (k : VMovKind) (ea : Ea) (src : XmmReg)
  /-- ⭐⭐ P2 BATCH 20 — `movhps`, THE HIGH-QUADWORD MOVE (SDM Vol. 2B, MOVHPS).
  `0f 16` loads, `0f 17` stores; 3,672 instructions of the assembly class.

  THE FORM IN ONE LINE: the memory operand is 64 bits and it is the register's
  HIGH quadword that moves. On a load `dst[127:64] ← m64` and **`dst[63:0] is
  PRESERVED`**; on a store `m64 ← src[127:64]`.

  ⭐⭐ P2 BATCH 36 WIDENED THIS PAIR FROM `movhps` TO ALL FOUR HALF-MOVES, and the
  two new fields are the two independent ways they differ: `VHalf` (which
  quadword is written, and therefore which is PRESERVED) and `VQuadKind` (the
  mandatory prefix, i.e. the spelling). `mod` selects the MNEMONIC here and not
  merely the operand shape — `0f 12` is four different mnemonics — which is why
  these are not the pure spelling change `movapd` was.

  ⛔ IT IS STILL DELIBERATELY NOT A `VMovKind`, and that is not a naming choice.
  That kind's entire content is `VMovKind.aligned` — the 16-byte #GP rule — and
  this form HAS no such rule: its memory operand is eight bytes, so SDM Exception
  Type 5 applies and no alignment is required. Giving it a `VMovKind` would force
  a fifth constructor whose `aligned` answer is meaningless, and a field whose
  value means nothing is read by someone eventually. ⚠️ MEASURED, not read off
  the manual: the oracle executes both directions at 16-, 8- AND 4-byte
  alignment, in a run where `pand 0x8(%rbx),%xmm0` REFUSES and
  `pand (%rbx),%xmm0` EXECUTES — so the harness demonstrably CAN see an
  alignment refusal, and its silence here is a reading rather than a blind spot.

  ⚠️ TWO CONSTRUCTORS, for exactly the reason `vload`/`vstore` are two: an
  operand pair admitting `mem` on both sides could spell `movhps (%rax),(%rbx)`,
  which no encoding produces. ⭐ AND THE ENCODING RETROACTIVELY JUSTIFIES IT:
  these four mnemonics have NO register-to-register form at all — at `mod=11`
  the same opcode is a DIFFERENT mnemonic (`movhlps`, `movlhps`) — so the absence
  of an `x,x` shape here is the encoding rather than a convenience.

  ⭐ THE PRESERVED HALF IS THE CONTENT. A model that CLEARS `dst[63:0]` instead of
  preserving it is bit-identical to this one wherever the low half is already
  zero — the mirror of the `movd`-into-XMM defect (D93), where the oracle merged
  what the SDM clears. Here the SDM preserves, so the wrong model is the one that
  zeroes, and it is caught only by a pre-state whose low quadword is non-zero. -/
  | vloadq  (h : VHalf) (k : VQuadKind) (dst : XmmReg) (ea : Ea)
  | vstoreq (h : VHalf) (k : VQuadKind) (ea : Ea) (src : XmmReg)
  /-- ⭐⭐ P2 BATCH 36 — `movhlps` / `movlhps`, THE TWO CROSS HALF-MOVES.
  `0f 12` and `0f 16` at **mod=11**; 1,341 and 340 instructions.

  ⛔⛔ THESE ARE NOT THE REGISTER FORMS OF `vloadq`, AND THAT IS THE WHOLE POINT.
  The ModRM `mod` field selects the MNEMONIC here, not merely the operand shape:
  `0f 12` is `movlps` at memory and `movhlps` at a register, which are different
  instructions moving different halves. That is why `vloadq`/`vstoreq` have no
  `x,x` shape — its absence is the ENCODING and not a convenience.

  ⭐ ONE FIELD AND ONE RULE FOR BOTH, because they are duals: `d` is the half of
  the DESTINATION that is written, and the half READ is always the OPPOSITE one.
  `d = .lo` is `movhlps` (dst[63:0] ← src[127:64]); `d = .hi` is `movlhps`
  (dst[127:64] ← src[63:0]). Writing them as two constructors would be two copies
  of one rule that must agree.

  ⭐ THE PRESERVED HALF IS THE CONTENT, as it is for `vloadq`: each writes one
  half and leaves the other alone, so the plausible wrong model is the one that
  reads the destination's OWN half rather than the opposite one. -/
  | vmovhl (d : VHalf) (dst src : XmmReg)
  /-- ⭐⭐ P2 BATCH 36 — `movddup`, register source (`f2 0f 12`, mod=11). 506
  instructions.

  ⛔ IT IS THE ONE FORM OF THIS BATCH THAT PRESERVES NOTHING: both halves of the
  destination are written, and both get the SOURCE'S LOW quadword. So the
  plausible wrong model inverts for it — for every other form in the batch the
  mistake is ZEROING the half that should be preserved, and here it is
  PRESERVING a half that should be written. -/
  | vddupR (dst src : XmmReg)
  /-- ⭐⭐ P2 BATCH 36 — `movddup`, memory source (`f2 0f 12`, mod≠11).

  ⚠️ TWO CONSTRUCTORS AND NOT AN OPERAND, for `vload`/`vstore`'s reason: an
  operand type admitting either would let the model spell shapes no encoding
  produces. `movddup` is the only member of this batch with BOTH forms. -/
  | vddupM (dst : XmmReg) (ea : Ea)
  /-- ⭐⭐ P2 BATCH 22 — `PREFETCHh` (SDM Vol. 2B). 466 instructions across
  `prefetchnta` (315) and `prefetcht0` (151).

  ⛔⛔ **THE FORM CHANGES NO ARCHITECTURAL STATE AT ALL**, and this constructor
  exists to say exactly that and nothing more: `step` advances RIP and touches
  nothing else. It does not read the memory it names, and PREFETCHh **does not
  fault** — not on an unmapped address, not on a misaligned one (SDM: it is a
  hint, and "prefetches from an illegal address are ignored").

  ⚠️⚠️ **SO THE HINT FIELD IS UNDISTINGUISHABLE BY ANY VECTOR THAT CAN EXIST**, and
  a wrong-model arm for it would be a FALSE ENTRY in the gate's own inventory —
  D91's rule, which cost this repository an arm that could never fire. The four
  spellings are held apart by the ENCODING gate (`scripts/check_encodings.py`
  assembles each `asm` and compares bytes), which is the instrument that can
  actually see a `/reg` field, not by the differential.

  ⚠️ The `Ea` is still carried and still reported by `Op.eas`, so the segment and
  lock walks see it: `lock prefetchnta` must be #UD, and `lockable` refusing it is
  what makes it so — the address is named by the instruction even though nothing
  reads it. -/
  | prefetch (hint : PrefetchHint) (ea : Ea)
  /-- ⭐⭐ P2 BATCH 23 — `PMOVMSKB` (SDM Vol. 2B). 453 instructions, and the LAST
  form in the measured residue that needs no new vocabulary.

  `dst[i] ← MSB(src.byte i)` for i in 0..15, and everything above bit 15 is zero.
  It is the first operation here that reads a vector register and writes a
  GENERAL-PURPOSE one while computing something — `vmovg` moves bits across the
  files, this one REDUCES them.

  ⭐⭐ **THERE IS NO `Size` FIELD, AND TWO INDEPENDENT SOURCES SAY THERE MUST NOT
  BE.** The SDM lists `PMOVMSKB r32, xmm` and `PMOVMSKB r64, xmm` as separate
  rows, which invites a width parameter:
  * **K** gives both `pmovmskb_r32_xmm.k` and `pmovmskb_r64_xmm.k` the SAME value —
    `concatenateMInt(mi(48,0), <16 bits>)` — so the two rows are one semantics;
  * **the assembler** goes further: `pmovmskb %xmm1,%eax` and `pmovmskb %xmm1,%rax`
    both assemble to `660fd7c1`, the identical bytes, because the result is
    zero-extended and REX.W buys nothing.
  ⇒ 🔑 A width field here would be a field no encoding can set and no semantics can
  read. The 32-bit write already zero-extends to 64 by SDM Vol. 1 §3.4.1.1, which
  `Cpu.setReg .d` implements — so the rule is INHERITED rather than restated. -/
  | vmovmsk (k : VMovMskKind) (dst : GPR) (src : XmmReg)
  /-- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 5 — MOVD / MOVQ ACROSS THE REGISTER FILES.
  Rank 4 and rank 8 of the measured demand list (3.05% and 2.05%), and the first
  instructions in this model whose two operands live in DIFFERENT REGISTER FILES.

  `toXmm` is the direction and `sz` is the width — `.d` spells `movd`, `.q`
  spells `movq`.  Both directions ZERO what they do not write, and at two
  different granularities, which is the whole content of the form:

  * **into XMM**: the destination's upper bits are ZEROED, not preserved — a
    32-bit `movd` clears bits 127:32 (SDM Vol. 2B, MOVD);
  * **out of XMM**: an ordinary GPR write, so `.d` zero-extends to 64 by the rule
    every other form in this model already obeys (SDM Vol. 1 §3.4.1.1).

  ⚠️ A model that PRESERVED the upper bits of the XMM destination is the obvious
  wrong one and is bit-identical to this one whenever the destination happened to
  be zero — which is why the pre-state XMM pattern being non-zero (batch 0) is
  what makes this form testable at all. -/
  | vmovg (toXmm : Bool) (sz : Size) (x : XmmReg) (r : GPR)
  /-- P2 VECTOR WAVE, BATCH 5 — `movq %xmm1, %xmm0` (`f3 0f 7e`), which is NOT
  `movdqa` at 64 bits: it moves the low quadword and **ZEROES the upper one**.
  objdump says so in its own disassembly comment (`xmm0 = xmm1[0],zero`).

  ⛔ It is a separate constructor from `vmov` rather than a width field on it,
  because `vmov` PRESERVES nothing and copies everything while this ZEROES half
  the destination — they are different functions, and one constructor with a
  width would invite the reading that `vmov` at 64 bits is this. -/
  | vmovq (dst src : XmmReg)
  /-- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 11 — MOVSS / MOVSD, AND THE FIRST FORM IN THIS
  MODEL WHOSE DESTINATION RULE DEPENDS ON WHERE ITS SOURCE LIVES.

  `movss`/`movsd` move ONE scalar — 32 or 64 bits — into the low lane of an XMM
  register. What happens to the REST of that register is not one rule (SDM
  Vol. 2B, MOVSS/MOVSD):

  * from a REGISTER, the upper bits are **PRESERVED** — `movss %xmm1,%xmm0`
    leaves 127:32 as they were, and objdump prints the merge in its own
    disassembly comment (`xmm0 = xmm1[0],xmm0[1,2,3]`);
  * from MEMORY, the upper bits are **ZEROED**.

  ⛔ THE SAME MNEMONIC, THE SAME WIDTH, THE SAME DESTINATION — AND TWO DIFFERENT
  FUNCTIONS, SELECTED BY THE SOURCE OPERAND'S KIND. Every other form in this
  model treats its source as a value; these read the *provenance* of the value.
  That is why they are three constructors and not one over a source operand
  type: a single constructor would have to branch on which case it was given,
  which is the branch this type removes (the `vload`/`vstore` argument, one step
  further — there the split made an illegal state unrepresentable, here it also
  makes two different SEMANTICS impossible to confuse).

  ⚠️ A MODEL THAT ALWAYS MERGED AND A MODEL THAT ALWAYS ZEROED ARE EACH
  BIT-IDENTICAL TO THIS ONE ON HALF THE FORMS, and both are indistinguishable
  from it at any pre-state whose destination XMM register is already zero. The
  vectors must therefore carry BOTH shapes at a NON-ZERO destination, and the
  arms in Main.lean plant exactly those two wrong models. -/
  | vmovs   (sz : Size) (dst src : XmmReg)
  /-- P2 VECTOR WAVE, BATCH 11 — `movss`/`movsd` from MEMORY: the low lane is
  loaded and the upper bits are ZEROED. See `Op.vmovs` for why this is a separate
  constructor rather than a source operand.

  ⚠️ NO ALIGNMENT REQUIREMENT. `movss`/`movsd` are SCALAR and the SDM states no
  alignment rule for them — unlike `movaps`/`movdqa`, whose #GP is the whole
  content of `VMovKind.aligned`. A reader who expects an `aligned` field here
  should expect its absence: there is nothing for it to say. -/
  | vmovsld (sz : Size) (dst : XmmReg) (ea : Ea)
  /-- P2 VECTOR WAVE, BATCH 11 — `movss`/`movsd` TO MEMORY: `sz` bytes of the low
  lane are stored and nothing is zeroed, because nothing else is written. The
  merge/zero question does not arise in this direction at all, which is why the
  store is one function rather than two. -/
  | vmovsst (sz : Size) (ea : Ea) (src : XmmReg)
  /-- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 13 — THE PACKED SHIFTS AT AN IMMEDIATE COUNT
  (`66 0F 71/72/73 /r ib`), and the first operation in this model whose RESULT
  IS NOT A FUNCTION OF ITS OPERANDS LANE BY LANE: one count is applied to every
  lane, so the combinator `vlanes` — which pairs lane `i` of `a` with lane `i` of
  `b` — cannot express it and a unary one is introduced beside it.

  ⛔⛔ **THE COUNT SATURATES, IT DOES NOT WRAP** (SDM Vol. 2B, PSLLW: "if the
  value specified by the count operand is greater than 15 (for words), 31 (for
  doublewords), or 63 (for a quadword), then the destination operand is set to
  all 0s"; PSRAW/PSRAD: "each destination data element is filled with the initial
  value of the sign bit").  A model taking the count MODULO the lane width is the
  obvious wrong one and is bit-identical to this one on every in-range count —
  which is every count a casual vector table would contain.  Measured on the
  oracle before a line of this was written: 20 rows where the two models differ,
  and ACL2 x86isa agrees with the SDM on all 20. -/
  | vshifti (op : VShiftOp) (w : VShiftW) (dst : XmmReg) (cnt : BitVec 8)
  /-- P2 VECTOR WAVE, BATCH 13 — the packed shifts with the count in the LOW
  QUADWORD OF AN XMM REGISTER (`66 0F F1/D1/E1/F2/D2/E2/F3/D3 /r`).

  ⛔⛔ **THE COUNT IS ALL SIXTY-FOUR BITS, AND THAT IS THE WHOLE CONTENT OF THIS
  CONSTRUCTOR.**  It is a separate constructor from `vshifti` rather than a count
  OPERAND on one, for the reason `vload`/`vstore` are two: the shapes are two
  different opcodes and an operand type admitting both would represent forms no
  encoding produces.  But the semantic difference is real as well — an immediate
  count cannot exceed 255, and a register count reaching 2^32 is a case the
  immediate form CANNOT CONSTRUCT.

  ⚠️ A model reading only the count's low BYTE agrees with this one on every
  count below 256, and the corpus's own pre-state sweep produces counts far above
  that.  Measured on the oracle: at a count of 2^32 + 3 the low-byte model and
  this one differ on all eight encodable forms, and x86isa answers with this
  one. -/
  | vshiftx (op : VShiftOp) (w : VShiftW) (dst src : XmmReg)
  /-- P2 VECTOR WAVE, BATCH 13 — the packed shifts with the count loaded from
  MEMORY.  128 bits are addressed and the low quadword is the count, so this
  reuses `readMem128` exactly as `vload` does.

  ⛔⛔ **THIS DOCSTRING SAID "NO ALIGNMENT REQUIREMENT … its absence is the rule
  rather than an omission", AND IT WAS AN OMISSION** (P2 batch 14, D110).
  `psrlw xmm,m128` is SDM `Table 2-21, "Type 4 Class Exception Conditions"` — the
  same table as `pand` and as `movdqu` — and it is MOVDQU's entry that decides it:
  its operand *"may be unaligned to any alignment without causing a
  general-protection exception (#GP) to be generated"*. **An exemption is proof of
  the rule it exempts from**, and the shifts are not exempted. THE ADDRESS MUST BE
  16-BYTE ALIGNED, ELSE `#GP(0)`.

  ⛔⛔ **AND IT SURVIVED A GREEN RUN OF 78,584 CASES WITH A VECTOR POINTED
  STRAIGHT AT IT.** `psraw_m_disp` addressed `0x8(%rbx)` = 0x2008, unaligned, and
  was added in the same commit as this constructor. It passed at all 88
  pre-states — because x86isa implements the 16-byte rule in exactly one file of
  its tree and not in `pshift.lisp`, so **the model's missing check and the
  oracle's missing check are the same omission**. ⇒ 🔑 TWO DEFECTS THAT CANCEL
  SURVIVE EVERY GREEN RUN THAT COMPARES THEM TO EACH OTHER; a differential is
  blind to exactly the errors its two sides share, and nothing inside it can
  report that.

  ⚠️ AND THE SENTENCE IT CITED IS STILL TRUE WHERE IT WAS WRITTEN. `vmovsld` does
  state no alignment requirement: `movss`/`movsd` are SCALAR, a 4- or 8-byte
  operand in exception Type 5, with no 16-byte rule to break. What was wrong was
  carrying that sentence ACROSS a class boundary — from a scalar form to a
  128-bit one — because the two arms look alike.

  ⭐ IT IS BUILT RATHER THAN DECLINED, and the reason is measured: this shape is
  **305 of the group's 35,704 corpus instructions (0.85%)**, which is small — but
  the census counts by MNEMONIC and would have counted all 35,704 as covered
  either way, so declining it would have been an over-claim of exactly 0.85% that
  no gate in this repository could see. -/
  | vshiftm (op : VShiftOp) (w : VShiftW) (dst : XmmReg) (ea : Ea)
  /-- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 13 — `pslldq` / `psrldq` (`66 0F 73 /7 ib`,
  `/3 ib`), WHICH ARE NOT PACKED AT ALL.

  ⛔ THEY SHIFT THE WHOLE 128-BIT REGISTER BY WHOLE BYTES, crossing every lane
  boundary — the one thing the word "packed" promises does not happen.  They wear
  a `p` prefix and sit at the same opcode byte as `psllq`/`psrlq`, distinguished
  only by the ModRM `/r` field, which is exactly why they are the two forms most
  likely to be modelled by analogy with their neighbours and be wrong.

  ⚠️ THE COUNT IS IN BYTES AND SATURATES AT 16, not at 128: `pslldq $0x14` zeroes
  the register (measured on the oracle, and objdump prints the all-`zero` shuffle
  comment itself).  There is no register or memory count shape — the SDM gives
  the immediate alone — and the corpus agrees: 0 of the 4,786 `pslldq`/`psrldq`
  instructions in it use anything but an immediate. -/
  | vshiftdq (left : Bool) (dst : XmmReg) (cnt : BitVec 8)
  /-- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 14 — THE PERMUTE GROUP, REGISTER SOURCE
  (`66/F2/F3 0F 70 /r ib`).

  ⚠️ **`dst` AND `src` ARE TWO REGISTERS AND THE DESTINATION IS NEVER READ**,
  which is a departure from every packed constructor before it: `vbin` and
  `vshifti`/`vshiftx` are read-modify-writes on `dst`.  A model that reused that
  shape — one register, permuted in place — is bit-identical to this one on every
  vector whose destination is its own source, and this repository has already
  paid for the register-field version of that mistake once (batch 5's
  `movdqa`, where every vector read xmm1 into xmm0 and a model ignoring the
  fields agreed on all of them).  `pshufd_x2x3` below is what forbids it. -/
  | vshuf  (k : VShufKind) (dst src : XmmReg) (sel : BitVec 8)
  /-- ⭐⭐ P2 VECTOR WAVE, BATCH 14 — THE PERMUTE GROUP, MEMORY SOURCE
  (`66/F2/F3 0F 70 /r ib` with a memory ModRM).

  ⛔⛔ **THE ADDRESS MUST BE 16-BYTE ALIGNED, ELSE `#GP(0)`** — and this is the
  rule `Op.vshiftm` was written WITHOUT, which was a defect and is repaired in
  this batch (D110).  The chain is the SDM's own, not a reading of one page:
  PSHUFD, PAND and MOVDQU are all `Table 2-21, "Type 4 Class Exception
  Conditions"`, and MOVDQU's entry states that its operand *"may be unaligned to
  any alignment without causing a general-protection exception (#GP) to be
  generated"*.  **An exemption is proof of the rule it exempts from**: Type 4
  carries a 16-byte `#GP` for every member not so exempted, and `pshufd` is not.

  ⚠️ **NO VECTOR CAN VALIDATE THIS, AND THAT IS MEASURED RATHER THAN ASSUMED.**
  ACL2 x86isa implements the check in exactly one file of its whole tree
  (`logical.lisp`, the legacy `pand`/`por`/`pxor`), so it REFUSES `pand
  8(%rbx),%xmm0` at all 88 pre-states and EXECUTES `pshufd 8(%rbx),%xmm0` at all
  88 — one exception class, two answers.  A vector here would be a one-sided
  refusal in every pre-state, which `classify` rightly calls `refusal` and counts
  UNEXPLAINED.  So the rule is a THEOREM (`vshufm_unaligned_faults`,
  `vshiftm_unaligned_faults`), exactly as D91 made `vload`'s, and the route by
  which it becomes differentially validatable is named and priced: the `vbin`
  memory shape, where the oracle DOES check. -/
  | vshufm (k : VShufKind) (dst : XmmReg) (ea : Ea) (sel : BitVec 8)
  /-- ⭐⭐⭐ P2 BATCH 37 — `SHUFPS`/`SHUFPD` between registers (`0F C6 /r ib`,
  `66 0F C6 /r ib`).  See `VShufpKind` for why this is not `Op.vshuf` at a new
  kind: these read BOTH operands, and `vshufApply` takes one source.

  ⚠️ THE DESTINATION IS READ AS WELL AS WRITTEN, which no other shuffle here does
  — `Op.vshuf`'s destination is overwritten without being consulted.  So a frame
  lemma or a wrong model that treats the destination as write-only is wrong for
  this constructor and right for that one. -/
  | vshufp  (k : VShufpKind) (dst src : XmmReg) (sel : BitVec 8)
  /-- ⭐⭐ P2 BATCH 37 — the same at a 128-bit MEMORY source, with the Type-4
  16-byte `#GP` every other 128-bit memory operand in this model carries (D110).
  ⚠️ The DESTINATION register is still read; only the SOURCE moves to memory. -/
  | vshufpm (k : VShufpKind) (dst : XmmReg) (ea : Ea) (sel : BitVec 8)
  /-- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 15 — THE PACKED BINARY GROUP AT A MEMORY SOURCE
  (`66 0F ..` with a memory ModRM), the second operand shape of the nineteen
  operations `Op.vbin` has carried since batches 5 and 7.

  ⛔⛔ **THIS BATCH ADDS NO CENSUS COVERAGE AND THAT IS THE POINT: IT REMOVES AN
  OVER-CLAIM.**  The census counts by MNEMONIC, so all 182,286 instructions of
  these nineteen are ALREADY counted as covered — including the **7,705** whose
  source is memory, which this model could not execute at all.  A gain of zero in
  the published number and a removal of 4.63% of a silent lie is exactly the
  trade `Op.vshiftm` made at 0.85% (D107), one order of magnitude up.

  ⭐⭐ **AND IT MAKES THE 16-BYTE `#GP` DIFFERENTIALLY VALIDATABLE FOR THE FIRST
  TIME IN THIS REPOSITORY.**  D91 recorded that no vector could test the rule
  because the oracle executes where this model faults; D110 found why — x86isa
  implements the check in exactly ONE file of its tree.  That file is
  `logical.lisp`, and it implements `pand`/`por`/`pxor`.  So at those three
  mnemonics an unaligned m128 is refused by BOTH models, `bothRefused` reports
  agreement, and the rule is finally carried by a RUN and not only by a theorem.
  ⚠️ At the other sixteen it is still theorem-only, and the split is not a
  judgement call: it is which x86isa source file implements the instruction.

  ⭐ THE SPLIT WAS PREDICTED BEFORE IT WAS MEASURED, from reading x86isa's files
  rather than from running it — `por 8(%rbx)` refuses at all 88 pre-states,
  `paddd`, `psubw` and `punpcklbw` at the same address execute at all 88. -/
  | vbinm (k : VBinKind) (dst : XmmReg) (ea : Ea)
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

/-- P2 VECTOR WAVE, BATCH 11: the scalar moves exist at 32 and 64 bits ONLY.
`movss` is `f3 0f 10` and `movsd` is `f2 0f 10`; there is no byte or word form —
the prefix selects the width and only two prefixes are defined for this opcode.
Written as data beside the AST for the reason `bitcntEncodable` is: "which forms
this model declines, and why" is then a table a theorem can read
(`Tests/Coverage.lean`) rather than an omission nobody re-checks. -/
def vmovsEncodable (sz : Size) : Bool := sz == .d || sz == .q

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

/-- ⭐⭐ EVERY OPERAND AN `Op` NAMES, WITH NO WILDCARD ARM.

⛔ THE ABSENCE OF `| _ => []` IS THE WHOLE POINT, AND IT REPLACES A THEOREM.
The first version of this function had a wildcard and a companion theorem
comparing its answer against the ENCODED BYTES (`64`/`65` prefixes) over all
784 vectors — a real second source, and it worked.  It also cost **4 200 ms of
kernel time**, the second most expensive declaration in this module, measured:
the byte half alone is 7.9 s standalone against 0.4 s for the AST half, because
`String.toList` on 784 literals is what the kernel actually spends its time on.

⇒ THE CEILING REFUSED IT AND NAMED A CHEAPER BUILD, which is the recurring shape
in this repository ([[a-gate-that-refuses-names-a-cheaper-build]]).  Exhaustive,
the completeness question is answered by the COMPILER on every build rather than
by a sweep: a thirty-seventh `Op` constructor is a compile error here and forces
whoever adds it to say whether it can carry a segment.  That is strictly stronger
than the theorem it replaces — which could only have caught a constructor some
VECTOR already used — and it costs nothing.

⚠️ The byte-side check is not lost: `seg_findings` in `scripts/check_encodings.py`
gates it, where a `%fs:` in the AT&T text, a `64`/`65` prefix in the bytes, and
the `seg` field of the AST must agree — per vector and per SEGMENT — and where
reading a string costs microseconds. -/
def opOperands : Op → List Operand
  -- ⭐ THE VECTOR FORMS NAME NO `Operand`, and that is a statement rather than a
  -- gap: `Operand` is the GPR/memory/immediate vocabulary, and an XMM register
  -- is a different register FILE, not another value in this one. A register-only
  -- vector form has no effective address, so every consumer that walks operands
  -- — the segment gate, the lock gate — correctly sees nothing to check. The day
  -- the memory forms land, THIS is the line that has to grow, and the compiler
  -- will say so.
  | .vmov .. | .vbin .. => []
  -- ⭐ AND THE MEMORY FORMS DO NAME ONE.  `Operand.mem` is how every consumer of
  -- this walk — the segment gate, the lock gate — finds an effective address, so
  -- a vector load's address is reported here exactly as a scalar one is. That is
  -- what makes `lock movdqa` #UD for free: `lockable` does not list it.
  | .vload _ _ ea | .vstore _ ea _ => [.mem ea]
  -- `movhps` names an address exactly as `vload`/`vstore` do, so the segment and
  -- lock gates see it with no new rule.
  | .vloadq _ _ _ ea | .vstoreq _ _ ea _ => [.mem ea]
  -- ⚠️ Two register files and no address: the cross moves name no `Ea` at all.
  | .vmovhl .. | .vddupR .. => []
  | .vddupM _ ea => [.mem ea]
  -- ⚠️ NAMED even though nothing reads it — see `Op.prefetch`.
  | .prefetch _ ea => [.mem ea]
  -- No memory operand at all: two register files, no address.
  | .vmovmsk .. => []
  | .vmovsld _ _ ea | .vmovsst _ ea _ => [.mem ea]
  -- ⭐ The GPR half IS an `Operand`; the XMM half is not. Reporting what can be
  -- reported keeps the lock and segment walks exact.
  | .vmovg _ _ _ r => [.reg r]
  | .vmovq .. => []
  | .vmovs .. => []
  -- ⭐ P2 BATCH 13.  The immediate and register count shapes name no `Operand`
  -- (the count is an `imm8` inside the opcode's ModRM, or an XMM register, and
  -- neither is in this vocabulary); the MEMORY shape names its address, so the
  -- lock and segment walks see it exactly as `vload`'s.
  | .vshifti .. | .vshiftx .. | .vshiftdq .. => []
  | .vshiftm _ _ _ ea => [.mem ea]
  -- P2 BATCH 14: the permute group, exactly as the shifts — the register source
  -- names no `Operand` (an XMM register is a different file), the memory source
  -- names its address so the lock and segment walks see it.
  | .vshuf .. => []
  | .vshufm _ _ ea _ => [.mem ea]
  | .vshufp .. => []
  | .vshufpm _ _ ea _ => [.mem ea]
  -- P2 BATCH 15: the packed binary group's memory SOURCE names its address.
  | .vbinm _ _ ea => [.mem ea]
  | .mov _ dst src => [dst, src]
  | .bin _ _ dst src => [dst, src]
  | .un _ _ dst => [dst]
  | .shift _ _ dst _ => [dst]
  | .lea _ _ _ => []          -- its `Ea` is collected below, not as an operand
  | .push _ src => [src]
  | .pop _ dst => [dst]
  | .jmp t => (match t with | .rel _ => [] | .indirect o => [o])
  | .jcc _ _ => []
  | .jcxz _ _ => []
  | .rot _ _ dst _ => [dst]
  | .bit _ _ dst off => [dst, off]
  | .setcc _ dst => [dst]
  | .cmov _ _ _ src => [src]
  | .call t => (match t with | .rel _ => [] | .indirect o => [o])
  | .movx _ _ _ _ src => [src]
  | .cext _ => []
  | .xchg _ a b => [a, b]
  | .bswap _ _ => []
  | .loop _ _ _ => []
  | .flagop _ => []
  | .nop dst => dst.toList
  | .ud2 => []
  | .ret => []
  | .leave => []
  | .shiftx _ _ _ src _ => [src]
  | .movbe _ dst src => [dst, src]
  | .bitcnt _ _ _ src => [src]
  -- the string group addresses RSI/RDI by opcode: no operand field at all, and
  -- therefore no place a segment override could be recorded in this AST.
  | .strop _ _ => []
  | .repstrop _ _ _ => []
  | .muldiv _ _ src => [src]
  | .imulr _ _ src _ => [src]
  | .cmpxchg _ dst _ => [dst]
  | .xadd _ dst _ => [dst]
  | .dshift _ _ dst _ _ => [dst]
  | .cmpxchg8b dst => [dst]

/-- The effective addresses an instruction names — every memory operand's, plus
`lea`'s, which is not an operand.  ONE walk, shared by the segment theorems in
`Tests/Coverage.lean` and by the LOCK well-formedness rule below, so a
constructor added to `opOperands` reaches both. -/
def Op.eas (o : Op) : List Ea :=
  (opOperands o).filterMap (fun x => match x with | .mem e => some e | _ => none)
    ++ (match o with | .lea _ _ e => [e] | _ => [])

/-- ⭐⭐ P2 ITEM 2: THE SDM'S LOCKABLE LIST, AS DATA.

SDM Vol. 2A, "LOCK — Assert LOCK# Signal Prefix": *"The LOCK prefix can be
prepended only to the following instructions and only to those forms of the
instructions where the destination operand is a memory operand: ADD, ADC, AND,
BTC, BTR, BTS, CMPXCHG, CMPXCHG8B, CMPXCHG16B, DEC, INC, NEG, NOT, OR, SBB, SUB,
XOR, XADD, and XCHG."*  Anything else raises #UD.

⛔ THE LIST IS TRANSCRIBED FROM THE MANUAL AND NOT INFERRED FROM WHAT THIS MODEL
HAPPENS TO IMPLEMENT.  `CMPXCHG16B` is on it and is not in this roster; `MOV` is
NOT on it and is in this roster and is the form a reader would most expect to be
lockable, because `lock movq %rax, (%rbx)` looks exactly like the atomic store
somebody wants.  A list derived from "the memory-destination forms we have"
would have quietly admitted `mov`, `shl`, `sar`, the whole shift group and every
`cmp`/`test` — every one of them a #UD on real silicon.

⚠️ `XCHG` IS ON THE LIST AND IS ALSO IMPLICITLY LOCKED: with a memory operand it
asserts LOCK whether or not the prefix is written (SDM Vol. 2A, XCHG).  So an
`xchg` at memory is lock-legal with the flag set OR clear, and both spellings
are the same instruction — which is why `Op.lockable` answers about the FORM and
`Instr` carries no separate "was the prefix written" bit for it. -/
def Op.lockable : Op → Bool
  -- The arithmetic and logic group, at a memory DESTINATION.  `cmp` and `test`
  -- are deliberately NOT here: they write no destination, so there is nothing
  -- to make atomic and the manual does not list them.
  | .bin k _ dst _ => dst.isMem && (match k with
      | .add | .adc | .and | .or | .sbb | .sub | .xor => true
      | .cmp | .test => false)
  | .un k _ dst => dst.isMem && (match k with
      | .inc | .dec | .neg | .not => true)
  -- BTC/BTR/BTS are lockable; plain BT is NOT — it writes nothing.
  | .bit k _ dst _ => dst.isMem && (match k with
      | .bts | .btr | .btc => true
      | .bt => false)
  | .cmpxchg _ dst _ => dst.isMem
  | .cmpxchg8b dst => dst.isMem
  | .xadd _ dst _ => dst.isMem
  | .xchg _ a b => a.isMem || b.isMem
  | _ => false

/-- Does this operand carry a `lock`?  ⭐ It exists so a characterization theorem
over a GENERAL operand can state P2 item 2's side condition without restating the
whole instruction — `(hl : o.locked = false)` rather than a copy of the `Op` the
theorem is already about, which would be a duplicate born in agreement. -/
def Operand.locked : Operand → Bool
  | .mem e => e.lock
  | _ => false

/-- Does any operand of this form carry a `lock`?

⭐⭐ THIS IS A SECOND TRAVERSAL AND NOT A CONVENIENCE, and the measurement is
why.  `lockIllegal` was first written as `o.eas.any Ea.lock` — three list passes
(`filterMap`, `++`, `any`) that `simp` unfolds symbolically at EVERY call site,
and `step`'s guard puts one at the head of every characterization theorem in
`X86/Theorems.lean`.  Measured: **733 ms against a 540 ms ceiling**, a module
that had never been near it.  One pass over `opOperands` costs what the `simp`
set can afford; `Op.eas` stays, unmarked, for the segment theorems that want the
addresses themselves. -/
def Op.anyLocked : Op → Bool
  -- No memory operand, so no `lock` prefix can be attached; `lock movdqa` is not
  -- a form the SDM lists and `lockable` refusing it is what makes it #UD.
  | .vmov .. | .vbin .. => false
  | .vload _ _ ea | .vstore _ ea _ => ea.lock
  | .vloadq _ _ _ ea | .vstoreq _ _ ea _ => ea.lock
  | .vmovhl .. | .vddupR .. => false
  | .vddupM _ ea => ea.lock
  | .prefetch _ ea => ea.lock
  | .vmovmsk .. => false
  | .vmovsld _ _ ea | .vmovsst _ ea _ => ea.lock
  | .vmovg .. | .vmovq .. | .vmovs .. => false
  -- P2 BATCH 13: `lock psrad` is not a form the SDM lists, so `lockable`
  -- refusing it is what makes it #UD — the memory shape reports its `Ea` here
  -- for the same reason `vload` does.
  | .vshifti .. | .vshiftx .. | .vshiftdq .. => false
  | .vshiftm _ _ _ ea => ea.lock
  -- P2 BATCH 14: `lock pshufd` is not a form the SDM lists.
  | .vshuf .. => false
  | .vshufm _ _ ea _ => ea.lock
  -- P2 BATCH 37: `lock shufps` is not a form the SDM lists, as for `pshufd`.
  | .vshufp .. => false
  | .vshufpm _ _ ea _ => ea.lock
  -- P2 BATCH 15: `lock paddd` is not a form the SDM lists.
  | .vbinm _ _ ea => ea.lock
  | .mov _ dst src => dst.locked || src.locked
  | .bin _ _ dst src => dst.locked || src.locked
  | .un _ _ dst => dst.locked
  | .shift _ _ dst _ => dst.locked
  | .lea _ _ e => e.lock
  | .push _ src => src.locked
  | .pop _ dst => dst.locked
  | .jmp t => (match t with | .rel _ => false | .indirect o => o.locked)
  | .jcc _ _ => false
  | .jcxz _ _ => false
  | .rot _ _ dst _ => dst.locked
  | .bit _ _ dst off => dst.locked || off.locked
  | .setcc _ dst => dst.locked
  | .cmov _ _ _ src => src.locked
  | .call t => (match t with | .rel _ => false | .indirect o => o.locked)
  | .movx _ _ _ _ src => src.locked
  | .cext _ => false
  | .xchg _ a b => a.locked || b.locked
  | .bswap _ _ => false
  | .loop _ _ _ => false
  | .flagop _ => false
  | .nop dst => (dst.map Operand.locked).getD false
  | .ud2 => false
  | .ret => false
  | .leave => false
  | .shiftx _ _ _ src _ => src.locked
  | .movbe _ dst src => dst.locked || src.locked
  | .bitcnt _ _ _ src => src.locked
  | .strop _ _ => false
  | .repstrop _ _ _ => false
  | .muldiv _ _ src => src.locked
  | .imulr _ _ src _ => src.locked
  | .cmpxchg _ dst _ => dst.locked
  | .xadd _ dst _ => dst.locked
  | .dshift _ _ dst _ _ => dst.locked
  | .cmpxchg8b dst => dst.locked

/-- ⛔⛔ AND THE DUPLICATE IS GATED BY THE COMPILER.  `anyLocked` above is a
SECOND walk over the same operand structure `opOperands` describes, written out
per constructor because that is what `simp` can reduce cheaply — and a second
copy of a 36-arm match is a duplicate born in agreement, which diverges on the
next constructor somebody adds to one and not the other.

This equation is the gate: it holds by `rfl` in every arm, so a divergence is a
BUILD FAILURE and not a drift.  ⚠️ `lea` is the one arm where the two genuinely
differ, and deliberately: its `Ea` is not an operand, so `opOperands` does not
carry it and `Op.eas` adds it separately. -/
theorem Op.anyLocked_eq (o : Op) :
    o.anyLocked = (match o with
                   | .lea _ _ e => e.lock
                   | _ => (opOperands o).any Operand.locked) := by
  cases o
  case jmp t | call t => cases t <;> simp [Op.anyLocked, opOperands, Operand.locked]
  case nop d => cases d <;> simp [Op.anyLocked, opOperands, Operand.locked]
  all_goals simp [Op.anyLocked, opOperands, Operand.locked]

/-- ⭐⭐ IS A `lock` FLAG SET ON A FORM THE SDM DOES NOT ALLOW IT ON?

This is the ONE thing about LOCK a post-decode model still has to decide, and it
is decidable here rather than at decode: `lock movq %rax, (%rbx)` is a
well-formed ENCODING that the decoder will hand over — the prefix is legal
bytes, the operands are legal operands — and it is #UD because MOV is not on the
manual's list.  `lock addq %rcx, %rax`, by contrast, cannot reach this AST at
all: the flag lives on an `Ea`, and there is no `Ea` in it.

⛔ SO THIS PREDICATE'S SUBJECT IS EXACTLY THE CASE THE TYPE CANNOT RULE OUT, and
the differential run compares it through the `refused` channel against x86isa's
own #UD. -/
def Op.lockIllegal (o : Op) : Bool := o.anyLocked && !o.lockable

@[simp] theorem Operand.locked_reg (r : GPR) (h8 : Bool) :
    (Operand.reg r h8).locked = false := rfl
@[simp] theorem Operand.locked_imm (v : Val) : (Operand.imm v).locked = false := rfl
@[simp] theorem Operand.locked_mem (e : Ea) : (Operand.mem e).locked = e.lock := rfl


/- ⭐ THE THREE DEFINITIONS ABOVE ARE `simp` DEFINITIONS, and that is what keeps
P2 item 2's guard from costing sixty-one theorems a hypothesis.

`step` now tests `lockIllegal` BEFORE its match, so every characterization
theorem acquires a side condition.  For the register-only forms — most of the
sixty-one — the condition is decidably FALSE by structure: no `Ea`, therefore no
`lock`, therefore no violation.  With the equation lemmas in the simp set,
`simp [step, h]` discharges it exactly as it discharged `wellFormed2` before,
and those theorems keep their statements unchanged.

⛔ THE MEMORY-OPERAND THEOREMS ARE A DIFFERENT CASE AND MUST NOT BE PAPERED OVER.
For `mov m,r` the condition is `ea.lock`, which is a real hypothesis: the
theorem was making a claim that is now FALSE for a locked operand, because a
locked `mov` is #UD.  Those theorems gain `(hl : ea.lock = false)` and say so —
narrowing a claim that had become too wide is the honest repair, and hiding it
behind a simp lemma would be the dishonest one. -/
attribute [simp] Op.anyLocked Op.lockable Op.lockIllegal

/-! ### The lock-guard's side condition, discharged per family

⭐ P2 ITEM 2.  `step` tests `lockIllegal` before its match, so a characterization
theorem written with `simp only` and a hand-listed lemma set — which is how the
oracle-drawing families are written, because their bodies do not survive a full
`simp` — cannot see that the condition is false.  These lemmas are the bridge:
one per family whose operand is a VARIABLE, stating the obvious fact in the form
`simp only` can use. -/

@[simp] theorem lockIllegal_bitcnt (k : BitCntKind) (sz : Size) (dst : GPR) (src : Operand)
    (h : src.locked = false) : (Op.bitcnt k sz dst src).lockIllegal = false := by
  cases src <;> simp_all [Operand.locked, opOperands]

@[simp] theorem lockIllegal_muldiv (k : MulDivKind) (sz : Size) (src : Operand)
    (h : src.locked = false) : (Op.muldiv k sz src).lockIllegal = false := by
  cases src <;> simp_all [Operand.locked, opOperands]

@[simp] theorem lockIllegal_imulr (sz : Size) (dst : GPR) (src : Operand) (imm : Option Val)
    (h : src.locked = false) : (Op.imulr sz dst src imm).lockIllegal = false := by
  cases src <;> simp_all [Operand.locked, opOperands]

@[simp] theorem lockIllegal_dshift (k : DShiftKind) (sz : Size) (dst : Operand) (src : GPR)
    (amt : ShiftAmt) (h : dst.locked = false) :
    (Op.dshift k sz dst src amt).lockIllegal = false := by
  cases dst <;> simp_all [Operand.locked, opOperands]

/-- The mnemonic a disassembler prints, used by the coverage table and by the
differential harness's disagreement reports. -/
def Op.mnemonic : Op → String
  -- ⚠️ ALL FOUR SPELLINGS, because all four opcodes exist, and the kind is what
  -- names them. See `VMovKind`.
  | .vmov k .. => k.mnemonic
  | .vload k .. | .vstore k .. => k.mnemonic
  -- ⚠️ THE SPELLING IS THE (half, prefix) PAIR, and both directions of a given
  -- pair print the same name: `0f 16` and `0f 17` are both `movhps`.
  | .vloadq h k _ _ | .vstoreq h k _ _ => quadMnemonic h k
  -- ⚠️ THE HALF NAMES THE MNEMONIC, and the two names are crossed relative to
  -- it: writing the LOW half is `movhlps`, because the SOURCE half is the high
  -- one and the mnemonic is named for the move, not for the destination.
  | .vmovhl d _ _ => match d with | .lo => "movhlps" | .hi => "movlhps"
  | .vddupR .. | .vddupM .. => "movddup"
  | .prefetch h _ => h.mnemonic
  | .vmovmsk k .. => k.mnemonic
  -- ⚠️ `movsd` COLLIDES WITH THE STRING INSTRUCTION `movsd` (MOVS m32, `a5`) in
  -- AT&T spelling, and they are unrelated: this one is `f2 0f 10`. The model
  -- does not carry the string form, so nothing here is ambiguous — but the day
  -- it does, these are two rows and not one, unlike `shl`/`sal`.
  | .vmovs sz .. | .vmovsld sz .. | .vmovsst sz .. =>
      match sz with | .q => "movsd" | _ => "movss"
  | .vmovg _ sz .. => match sz with | .q => "movq" | _ => "movd"
  -- ⭐ P2 BATCH 13.  All three count shapes print the SAME mnemonic — `psrad`
  -- names the operation and the lane, and the count's provenance is in the
  -- operands, not in the name.  That is the opposite of `movss`/`movsd`, where
  -- the shapes differ in SEMANTICS and share a name; here they share a name and
  -- share the semantics, differing only in where the count is read from.
  | .vshifti op w .. | .vshiftx op w .. | .vshiftm op w .. => op.mnemonic w
  | .vshiftdq left .. => if left then "pslldq" else "psrldq"
  -- ⭐ P2 BATCH 14.  Both operand shapes print the same mnemonic, for the reason
  -- the three shift shapes do: the mandatory prefix names the operation and the
  -- source's provenance is in the operands.
  | .vshuf k .. | .vshufm k .. => k.mnemonic
  | .vshufp k .. | .vshufpm k .. => k.mnemonic
  | .vmovq .. => "movq"
  -- ⭐ P2 BATCH 15: BOTH operand shapes read the SAME table, which is now a
  -- function beside the kind rather than a `match` inside this one.  A copy here
  -- for `vbinm` would be a duplicate that diverges the day a spelling is fixed
  -- in one of them and not the other (D106's shape, and it is not re-learned).
  | .vbin k .. | .vbinm k .. => k.mnemonic
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
   -- P1 BATCH 10: the loop group and the flag-control singles.  `loope` and
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
   "cmpxchg8b",
   -- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 2 — the first roster rows whose register file is
   -- not the general-purpose one.  `movdqa` and `movdqu` are TWO rows for ONE
   -- constructor (`Op.vmov`, distinguished by `aligned`) because they are two
   -- OPCODES — unlike `shl`/`sal`, which are one opcode under two spellings and
   -- are therefore one row.  The eleven packed operations are one row each.
   "movdqa", "movdqu",
   "paddb", "paddw", "paddd", "paddq",
   "psubb", "psubw", "psubd", "psubq",
   "pxor", "pand", "por",
   -- P2 VECTOR WAVE, BATCH 5: the cross-register-file moves.  `movq` is a roster
   -- name here in its SSE sense; the GPR `movq %rcx,%rax` is a spelling of `mov`
   -- and always has been, which is why the two do not collide.
   "movd", "movq",
   -- P2 VECTOR WAVE, BATCH 7: the unpack group, one roster row per mnemonic.
   "punpcklbw", "punpcklwd", "punpckldq", "punpcklqdq",
   "punpckhbw", "punpckhwd", "punpckhdq", "punpckhqdq",
   -- ⭐ P2 VECTOR WAVE, BATCH 11: the move family completed.  `movaps`/`movups`
   -- are two more ROWS for the SAME constructor (`Op.vmov`, now distinguished by
   -- `VMovKind`) for the reason `movdqa`/`movdqu` are two — they are distinct
   -- OPCODES, and a model that printed one name for the other would be wrong
   -- about what it decoded.  `movss`/`movsd` are one row each.
   "movaps", "movups", "movss", "movsd",
   -- ⭐⭐ P2 BATCH 35: the `pd` spellings of the two 128-bit moves.  `movapd` is
   -- `66 0f 28`/`66 0f 29` and `movupd` is `66 0f 10`/`66 0f 11`, so the `66` is
   -- a MANDATORY PREFIX selecting the mnemonic rather than an operand-size
   -- override.  Two more ROWS for the same constructor, on the `movdqa`/`movaps`
   -- rule: distinct opcodes, distinct printed names, and nothing this model can
   -- observe distinguishes the transfers.
   "movapd", "movupd",
   -- ⭐⭐ P2 BATCH 20: `movhps`, ONE row for BOTH directions — unlike
   -- `movdqa`/`movdqu` these are one mnemonic at two opcodes (`0f 16`/`0f 17`),
   -- so a disassembler prints the same name for each and the roster has one row.
   "movhps",
   -- ⭐⭐ P2 BATCH 36: the rest of the half-move family.  SIX rows, because the
   -- roster counts what a disassembler PRINTS and the ModRM `mod` field selects
   -- the MNEMONIC here — `0f 12` prints `movlps` at memory and `movhlps` at a
   -- register, which is a different instruction and not a different shape.
   "movhpd", "movlps", "movlpd", "movhlps", "movlhps", "movddup",
   -- ⭐⭐ P2 BATCH 22: TWO rows for one semantics — the roster counts what a
   -- disassembler PRINTS, and `0f 18` prints a name per `/reg` value.  Only the
   -- two with measured demand are modelled; see `PrefetchHint`.
   "prefetchnta", "prefetcht0",
   -- ⭐⭐ P2 BATCH 23: ONE row — the r32 and r64 spellings share an ENCODING, so a
   -- disassembler prints one name.  See `Op.vmovmsk`.
   "pmovmskb",
   -- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 13: the packed SHIFT group.  EIGHT rows for the
   -- eight encodable (operation, lane) pairs — `vshiftEncodable` is what says
   -- there are eight and not twelve, and `Tests/Coverage.lean` asserts that this
   -- list and that table name the same set, so a row added here without an
   -- encoding, or an encoding added without a row, is a kernel failure.
   --
   -- ⚠️ ONE ROW PER MNEMONIC, NOT PER COUNT SHAPE.  `psrad $3,%xmm0`,
   -- `psrad %xmm1,%xmm0` and `psrad (%rbx),%xmm0` are three ENCODINGS of one
   -- mnemonic — the roster counts what a disassembler prints, and it prints
   -- `psrad` for all three.  The shapes are backed by vectors and asserted per
   -- shape in the coverage theorems instead.
   "psllw", "pslld", "psllq",
   "psrlw", "psrld", "psrlq",
   "psraw", "psrad",
   -- and the two WHOLE-REGISTER byte shifts, which are not packed (`Op.vshiftdq`)
   "pslldq", "psrldq",
   -- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 14: the permute group.  THREE rows for one
   -- opcode — `0F 70 /r ib` under three mandatory prefixes — because the roster
   -- counts what a disassembler PRINTS, and it prints three names.  That is the
   -- `movdqa`/`movdqu` rule, not the `shl`/`sal` one.
   --
   -- ⛔ `pshufw` IS ABSENT AND IS THE FOURTH PREFIX (none) OF THE SAME OPCODE.
   -- It is MMX-only and this model has no MMX register file; measured, 642 of
   -- 642 of the census's `asm` class are MMX-register forms.  A row here without
   -- a constructor would claim a form the model cannot execute.
   "pshufd", "pshuflw", "pshufhw",
   -- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 17: the packed compares, six rows.  They are
   -- `VBinKind` members, so both operand shapes are covered by the constructors
   -- that already existed — but the ROSTER counts mnemonics a disassembler
   -- prints, and it prints six.
   --
   -- ⛔ THE GROUP WAS PICKED FROM A MEASUREMENT, NOT A RANK (D115): every other
   -- candidate in the residue at this size REFUSES on the oracle, including the
   -- whole saturating add/subtract family and both signed packs.
   "pcmpeqb", "pcmpeqw", "pcmpeqd", "pcmpgtb", "pcmpgtw", "pcmpgtd",
   -- ⭐ P2 VECTOR WAVE, BATCH 18: `packuswb`, the ONE member of the pack group the
   -- oracle can execute.  `packsswb` and `packssdw` refuse at every pre-state.
   "packuswb",
   -- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 34: the bitwise complement, NINE rows.  They are
   -- `VBinKind` members, so both operand shapes come from the constructors that
   -- already existed — but the roster counts mnemonics a disassembler PRINTS, and
   -- these are nine distinct opcodes printing nine distinct names.
   --
   -- ⭐ THE GROUP WAS DERIVED, NOT RANKED (D157).  It is exactly the bitwise half
   -- of the SSE-legacy residue the soft-float commission does NOT cover: the 64
   -- unclaimed pairs the oracle EXECUTES, minus the commission's 40, leaves 24
   -- pairs / 11,040 instructions that need no rounding at all, and these nine are
   -- its bitwise members.  The partition is checked by reproducing the
   -- commission's own published 12/6,619, 2/898 and 26/29,408 from the census.
   "pandn", "andnps", "andnpd",
   "andps", "andpd", "orps", "orpd", "xorps", "xorpd",
   -- ⭐⭐ P2 BATCH 37 — the `ps`/`pd` unpack spellings and the dword sign-mask.
   -- The four unpacks are spellings of operations already here (held together by
   -- `unpack_aliases_are_their_integer_siblings`, held apart by their bytes);
   -- `movmskps` is a new KIND on `Op.vmovmsk`, the same reduction at 32-bit lanes.
   -- ⛔ ONE row for `movmskps` and not two: its r32 and r64 spellings assemble to
   -- the IDENTICAL bytes (`0f50c1`), measured on this mnemonic rather than
   -- inherited from `pmovmskb`'s.
   "unpcklps", "unpckhps", "unpcklpd", "unpckhpd",
   -- ⭐⭐⭐ P2 BATCH 37 — the two-source shuffles, 88% of the batch's demand and
   -- the only NEW SEMANTICS in it.  One row each, both operand shapes.
   "shufps", "shufpd"]

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
