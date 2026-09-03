/-
# X86.Coverage — the coverage table as DATA, never as prose

Plan v1 §3.2: "Every form's tier is machine-listed; 'coverage' is a generated
table, never prose."  Plan v1 §3.4 and the helm's ruling: DECODE TRUST is a
named item in TRUSTBASE.md and a COLUMN here.

The table below is the single source of truth for what this model claims.  It is
checked against the AST by `Tests/Coverage.lean` (every mnemonic the `Op` type
can produce appears exactly once; every row's mnemonic is one the AST can
produce), so the table cannot drift from the semantics in either direction — the
usual failure of a hand-written coverage claim is a row for a form that was
removed, and the second half of that check is what catches it.

LANE. Personal lane, public sources only.
-/
import X86.Syntax

namespace X86

/-- The FIDELITY TIER of a form (plan v1 §3.2).  The names are this project's
coinage; the concept is ACL2 x86isa's app-view/catalogue split and Sail's
`Unspecified`, and the over-approximative-lifting literature's distinction
between an exact and a sound-but-imprecise model. -/
inductive Tier where
  /-- Every architected bit of the result and of the flags is computed. -/
  | exact
  /-- The frame is exact — which state components change is exact — but one or
  more result bits come from the undefined-bit oracle, because the SDM declines
  to define them. -/
  | frame
  /-- Refused: the model stops rather than guess. -/
  | absent
  deriving DecidableEq, Repr, Inhabited, BEq

def Tier.toString : Tier → String
  | .exact => "T-exact"
  | .frame => "T-frame"
  | .absent => "T-absent"

/-- How this model came to trust the DECODING of a form.  At P0 every row is
`xed`: the AST is built from Intel XED's structured output and NOTHING in this
repository proves that XED decoded the bytes correctly.  That is a real trust
assumption, it is named in TRUSTBASE.md, and it is a column here so that a reader
of the coverage table cannot miss it.  P4's Lean decoder is what moves rows to
`proved`. -/
inductive DecodeTrust where
  /-- Decoded by Intel XED (Apache-2.0); trusted, not proved. -/
  | xed
  /-- Decoded by this project's Lean decoder, with a proof (P4). -/
  | proved
  deriving DecidableEq, Repr, Inhabited, BEq

def DecodeTrust.toString : DecodeTrust → String
  | .xed => "XED (trusted)"
  | .proved => "Lean (proved)"

/-- One row of the coverage table. -/
structure Row where
  mnemonic : String
  /-- Operand shapes covered, in AT&T-free Intel-ish notation. -/
  shapes : String
  tier : Tier
  decode : DecodeTrust
  /-- The flags this model draws from the undefined-bit oracle, per the SDM.
  EMPTY means the form commits to every flag it writes. -/
  undefined : List String
  /-- The SDM section read for this form. -/
  sdm : String
  deriving Repr, Inhabited

/-- THE P0 TABLE.  Twenty rows, one per mnemonic in the plan v1 §5 roster. -/
def tableP0 : List Row :=
  let rm := "r/m, r/imm"
  -- P1 BATCH 1 (`p1/roster.tsv` family `0xuxx0-|-|reg`): the register-destination
  -- shapes at every width, plus the accumulator short encodings and the high-8
  -- register views.  The memory-DESTINATION forms are batch 4 of the roster and
  -- are NOT claimed here.
  --
  -- ⛔ THIS COMMENT USED TO END "`m,r` below is P0's row, at width q only", and
  -- that sentence is why the false claim under it survived a batch: it read as
  -- a deliberate, already-considered decision.  There is no P0 `m,r` row for
  -- these three mnemonics — P0's `and_q`/`or_q`/`xor_q` were register-to-
  -- register — so the sentence explained something that was not there.
  -- ⇒ A WRONG CLAIM WITH A REASSURING COMMENT BESIDE IT IS HARDER TO SEE THAN A
  -- BARE ONE, because the comment answers the question a reader was about to
  -- ask.  The gate, not the comment, is what now holds this.
  let carryShapes := "r,r · r,imm · r,m — all of b/w/l/q · acc,imm · rh"
  -- ⛔ THIS STRING ENDED `· m,r (q)` UNTIL P1 BATCH 3 AND THAT WAS FALSE.  Batch
  -- 1 shipped `and_rm_*` — a memory SOURCE with a register destination — and the
  -- shapes column, which writes shapes DESTINATION-FIRST, transposed it into a
  -- memory destination the repository has never had a vector for.  The
  -- memory-destination logic forms are roster family 4 and have not been run.
  -- `Tests/Coverage.lean`'s `mem_dest_claims_are_backed` is the gate that now
  -- refuses this claim without a vector behind it; it was driven RED against
  -- exactly this string before the string was corrected.
  -- ⭐ AND `m,r · m,imm` IS BACK, EARNED THIS TIME.  P1 batch 4 covers the
  -- memory-DESTINATION forms (roster family 4) at all four widths — more than
  -- the claim batch 3 deleted ever asserted — and
  -- `Tests/Coverage.lean`'s `mem_dest_claims_are_backed` is what holds it now.
  let logicShapes := "r,r · r,imm · r,m · m,r · m,imm — all of b/w/l/q · \
acc,imm · rh"
  [ { mnemonic := "mov",  shapes := "r,r · r,imm · r,m · m,r", tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A MOV" }
  , { mnemonic := "add",  shapes := rm, tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A ADD" }
  , { mnemonic := "sub",  shapes := rm, tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A SUB" }
  , { mnemonic := "and",  shapes := logicShapes, tier := .frame, decode := .xed,
      undefined := ["AF"], sdm := "Vol. 2A AND" }
  , { mnemonic := "or",   shapes := logicShapes, tier := .frame, decode := .xed,
      undefined := ["AF"], sdm := "Vol. 2A OR" }
  , { mnemonic := "xor",  shapes := logicShapes, tier := .frame, decode := .xed,
      undefined := ["AF"], sdm := "Vol. 2A XOR" }
  -- P1 BATCH 3 (`p1/roster.tsv` families `xxxxxx-|-|flags/ctl` and
  -- `0xuxx0-|-|flags/ctl`): the two mnemonics whose destination is the FLAGS.
  -- `m,r` and `m,imm` are real here in a way they are nowhere else in this
  -- table — the memory operand is ADDRESSED and READ, and never written, which
  -- is the claim `cmp_mem_dest_writes_no_memory` anchors and the harness's
  -- seventh planted bug is pointed at.  TEST has no `r,m` form: Intel encodes
  -- one direction only (SDM Vol. 2A, TEST).
  , { mnemonic := "cmp",  shapes := "r,r · r,imm · r,m · m,r · m,imm — all of \
b/w/l/q · acc,imm · rh · rip-rel (q)", tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A CMP" }
  -- P1 BATCH 2 (`p1/roster.tsv` family `xxxxxx-|cf|reg`): the first forms whose
  -- RESULT reads a flag.  Register destination only; the memory-destination
  -- forms are a different family.
  , { mnemonic := "adc",  shapes := carryShapes, tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A ADC" }
  , { mnemonic := "sbb",  shapes := carryShapes, tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A SBB" }
  , { mnemonic := "test", shapes := "r,r · r,imm · m,r · m,imm — all of b/w/l/q \
· acc,imm · rh", tier := .frame, decode := .xed,
      undefined := ["AF"], sdm := "Vol. 2A TEST" }
  -- P1 BATCH 7: the SHIFT group (roster families 8, 9, 12, 13, 60, 61) — a
  -- memory destination and the `,one` encoding (`D1 /r`, the count in the
  -- opcode) for all three, plus SAR.  `sal` is an ALIAS of `shl` (same opcode
  -- `/4`) and is covered by identity, not by a row.
  , { mnemonic := "shl",  shapes := "r · m(rmw) — one/imm8/cl, b/w/l/q (sal: alias)",
      tier := .frame, decode := .xed,
      undefined := ["CF (count ≥ width)", "OF (count ≠ 1)", "AF (count ≠ 0)"],
      sdm := "Vol. 2A SAL/SAR/SHL/SHR" }
  , { mnemonic := "shr",  shapes := "r · m(rmw) — one/imm8/cl, b/w/l/q",
      tier := .frame, decode := .xed,
      undefined := ["CF (count ≥ width)", "OF (count ≠ 1)", "AF (count ≠ 0)"],
      sdm := "Vol. 2A SAL/SAR/SHL/SHR" }
  -- ⭐ SAR's UNDEFINED SET IS SMALLER THAN SHL's AND SHR's BY ONE ENTRY, and
  -- that is the SDM's own wording rather than a simplification: the undefined
  -- clause names "SHL and SHR instructions where the count is greater than or
  -- equal to the size of the destination operand".  SAR has no such clause —
  -- shifting right past the width still has an answer, and it is the sign.
  , { mnemonic := "sar",  shapes := "r · m(rmw) — one/imm8/cl, b/w/l/q",
      tier := .frame, decode := .xed,
      undefined := ["OF (count ≠ 1)", "AF (count ≠ 0)"], sdm := "Vol. 2A SAL/SAR/SHL/SHR" }
  -- P1 BATCH 8: the ROTATE group (roster families 25, 26, 49-52).  Same opcode
  -- block as the shifts, different `/r`, and entirely different flags: a rotate
  -- touches ONLY CF and OF (SDM Vol. 2A), leaving SF/ZF/PF/AF exactly as they
  -- were — which is why AF is absent from these undefined lists and present in
  -- the shifts'.  `rcl`/`rcr` also READ CF, because they rotate through it.
  -- P1 BATCH 9: the BIT-TEST group (roster families 31, 32, 41).  ⚠️ ZF is the
  -- only arithmetic flag that SURVIVES — "the ZF flag is unaffected... the OF,
  -- SF, AF, and PF flags are undefined" — which is the widest undefined set in
  -- this model and the reason all four rows are T-frame despite computing
  -- almost nothing.  `bt` writes no destination, exactly as `cmp` does.
  -- ⛔ The `m,r` shape (memory base with a REGISTER offset) is a signed BIT
  -- STRING index that reaches outside the operand; it is NOT modelled and is
  -- named as absent here rather than quietly folded in.  See D23.
  , { mnemonic := "bt",   shapes := "r,imm · r,r · m,imm — w/l/q (m,r: bit-string, not modelled)",
      tier := .frame, decode := .xed,
      undefined := ["PF", "AF", "SF", "OF"], sdm := "Vol. 2A BT" }
  , { mnemonic := "bts",  shapes := "r,imm · r,r · m(rmw),imm — w/l/q (m,r: not modelled)",
      tier := .frame, decode := .xed,
      undefined := ["PF", "AF", "SF", "OF"], sdm := "Vol. 2A BTS" }
  , { mnemonic := "btr",  shapes := "r,imm · r,r · m(rmw),imm — w/l/q (m,r: not modelled)",
      tier := .frame, decode := .xed,
      undefined := ["PF", "AF", "SF", "OF"], sdm := "Vol. 2A BTR" }
  , { mnemonic := "btc",  shapes := "r,imm · r,r · m(rmw),imm — w/l/q (m,r: not modelled)",
      tier := .frame, decode := .xed,
      undefined := ["PF", "AF", "SF", "OF"], sdm := "Vol. 2A BTC" }
  , { mnemonic := "rol",  shapes := "r · m(rmw) — one/imm8/cl, b/w/l/q",
      tier := .frame, decode := .xed,
      undefined := ["OF (count ≠ 1)"], sdm := "Vol. 2A RCL/RCR/ROL/ROR" }
  , { mnemonic := "ror",  shapes := "r · m(rmw) — one/imm8/cl, b/w/l/q",
      tier := .frame, decode := .xed,
      undefined := ["OF (count ≠ 1)"], sdm := "Vol. 2A RCL/RCR/ROL/ROR" }
  , { mnemonic := "rcl",  shapes := "r · m(rmw) — one/imm8/cl, b/w/l/q",
      tier := .frame, decode := .xed,
      undefined := ["OF (count ≠ 1)"], sdm := "Vol. 2A RCL/RCR/ROL/ROR" }
  , { mnemonic := "rcr",  shapes := "r · m(rmw) — one/imm8/cl, b/w/l/q",
      tier := .frame, decode := .xed,
      undefined := ["OF (count ≠ 1)"], sdm := "Vol. 2A RCL/RCR/ROL/ROR" }
  , { mnemonic := "lea",  shapes := "r, m", tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A LEA" }
  -- P1 BATCH 4 (`p1/roster.tsv` families `-xxxxx-|-|mem` and `-xxxxx-|-|reg`):
  -- INC and DEC at BOTH destinations and all four widths.  The memory forms are
  -- read-modify-writes, and CF is untouched at either destination.
  , { mnemonic := "inc",  shapes := "r · m(rmw) — all of b/w/l/q", tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A INC" }
  , { mnemonic := "dec",  shapes := "r · m(rmw) — all of b/w/l/q", tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A DEC" }
  -- ⛔ THESE FOUR ROWS CLAIMED SHAPES NO VECTOR HAS, and P1 batch 4's gate is
  -- what found them.  `neg`/`not` said `r/m` with only register vectors;
  -- `push` said `r · m · imm` and `pop` said `r · m` with only `push_r`/`pop_r`.
  -- Each is now narrowed to what is actually executed, and the missing halves
  -- are named as the roster families that will earn them (10 and 11) — the same
  -- correction `and`/`or`/`xor` took in batch 3 and earned back in batch 4.
  , { mnemonic := "neg",  shapes := "r — b/q (m: roster family 10)", tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A NEG" }
  , { mnemonic := "not",  shapes := "r — q (m: roster family 11)", tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A NOT" }
  , { mnemonic := "push", shapes := "r — q (m, imm: roster family 11)", tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A PUSH" }
  , { mnemonic := "pop",  shapes := "r — q (m: roster family 11)", tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A POP" }
  -- P1 BATCH 5 (`p1/roster.tsv` family `-------|-|flags/ctl`, its BRANCH
  -- subset): every condition at BOTH relative encodings, plus JRCXZ/JECXZ.
  --
  -- ⛔ TWO MORE OVER-CLAIMS DIED HERE, both from P0 and both found by reading
  -- the column rather than by a failure.  `jmp` said `rel32` and its only
  -- relative vector was `eb 09` — a rel8.  `jcc` said "all 16 conditions" and
  -- had vectors for TWO of them, both rel8.  Batch 5 is what makes both true,
  -- and `vectors_cover_every_condition` in Tests/Coverage.lean is what now
  -- holds the second rather than the sentence holding itself.
  , { mnemonic := "jmp",  shapes := "rel8 · rel32 · r/m64", tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A JMP" }
  , { mnemonic := "jcc",  shapes := "rel8 · rel32 — all 16 conditions, 30 spellings",
      tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A Jcc" }
  -- JRCXZ and JECXZ are ONE instruction with an address-size prefix, and are two
  -- rows because K files them as two mnemonics and the coverage table is read
  -- against K's roster.  ⚠️ NEITHER HAS A rel32 ENCODING — `E3 cb` is rel8 only
  -- (SDM Vol. 2A, JCC) — and the roster claims one for each because K's tree
  -- carries an autogenerated `jecxz_rel32.k`.  Those two roster forms cannot be
  -- assembled at all; see docs/DECISIONS.md D17.
  , { mnemonic := "jrcxz", shapes := "rel8 (no rel32 encoding exists)", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A JCC" }
  , { mnemonic := "jecxz", shapes := "rel8 (no rel32 encoding exists)", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A JCC" }
  -- P1 BATCH 6: the CONDITION-CODE families (16, 18-22, 28-30, 34-38, 44, 45),
  -- 120 roster forms over TWO `step` cases.  `Cc` keys on the PREDICATE, so
  -- K's 30 `set` and 30 `cmov` spellings are the same sixteen predicates the
  -- branches use; `Cc.setSpellings`/`Cc.cmovSpellings` derive the names and
  -- Tests/Coverage.lean counts them.
  --
  -- ⚠️ `cmovcc` has NO memory destination (`cmovcc r, r/m` only), which is why
  -- its shapes read `r,m` and not `m,r`.  `setcc`'s memory form is a WRITE that
  -- never reads, hence `m8(w)` rather than the `m(rmw)` inc/dec take.
  , { mnemonic := "setcc", shapes := "r8 · rh8 · m8(w) — 30 spellings",
      tier := .exact, decode := .xed, undefined := [], sdm := "Vol. 2A SETcc" }
  , { mnemonic := "cmovcc", shapes := "r,r · r,m — w/l/q, 30 spellings",
      tier := .exact, decode := .xed, undefined := [], sdm := "Vol. 2A CMOVcc" }
  , { mnemonic := "call", shapes := "rel32 · r/m64", tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A CALL" }
  -- P1 BATCH 10 (`p1/roster.tsv` family `-------|-|reg`, its NO-FLAG core): the
  -- width-changing and two-destination moves.  ⭐ EVERY ROW BELOW IS T-exact
  -- WITH AN EMPTY UNDEFINED COLUMN, and that is the batch's shape rather than a
  -- coincidence: not one of these instructions writes a flag, so there is no
  -- undefined flag for the comparator to absorb and every disagreement they can
  -- produce is a DATA-path disagreement.  Batch 9 was the opposite extreme —
  -- four undefined flags leaving ZF to carry the whole test.
  , { mnemonic := "movzx", shapes := "r,r · r,m · rh,r — b→w/l/q, w→l/q (5 spellings)",
      tier := .exact, decode := .xed, undefined := [], sdm := "Vol. 2A MOVZX" }
  , { mnemonic := "movsx", shapes := "r,r · r,m — b→w/l/q, w→l/q, l→q (6 spellings, movslq = MOVSXD)",
      tier := .exact, decode := .xed, undefined := [], sdm := "Vol. 2A MOVSX/MOVSXD" }
  -- The two trios differ in WHERE the sign lands, and each row says which
  -- register it writes, because that is the only thing that distinguishes them.
  , { mnemonic := "cbtw", shapes := "no operands — ax := sext(al)", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A CBW/CWDE/CDQE" }
  , { mnemonic := "cwtl", shapes := "no operands — eax := sext(ax), zero-extending into rax",
      tier := .exact, decode := .xed, undefined := [], sdm := "Vol. 2A CBW/CWDE/CDQE" }
  , { mnemonic := "cltq", shapes := "no operands — rax := sext(eax)", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A CBW/CWDE/CDQE" }
  , { mnemonic := "cwtd", shapes := "no operands — dx := sign(ax), rax untouched", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A CWD/CDQ/CQO" }
  , { mnemonic := "cltd", shapes := "no operands — edx := sign(eax), zero-extending into rdx",
      tier := .exact, decode := .xed, undefined := [], sdm := "Vol. 2A CWD/CDQ/CQO" }
  , { mnemonic := "cqto", shapes := "no operands — rdx := sign(rax)", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A CWD/CDQ/CQO" }
  -- ⚠️ `ax,r` AND `r,ax` ARE THE SAME BYTES.  The assembler emits `66 91` for
  -- both `xchg %ax, %cx` and `xchg %cx, %ax`, so the roster's two forms are one
  -- encoding and the differential cannot tell them apart — said here rather
  -- than left for a reader to assume they were separately tested.  The memory
  -- shape is REFUSED, not missing (D25).
  , { mnemonic := "xchg", shapes := "r,r · acc,r · r,acc — b/w/l/q (m: refused, implicit LOCK)",
      tier := .exact, decode := .xed, undefined := [], sdm := "Vol. 2A XCHG" }
  , { mnemonic := "bswap", shapes := "r — l/q only (b/w: SDM undefined, refused)", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A BSWAP" }
  -- P1 BATCH 11 (roster family 15's loop group, and families 54-59): the three
  -- loop predicates and the five flag-control singles.  ⭐ EVERY ROW IS T-exact
  -- WITH AN EMPTY UNDEFINED COLUMN, as batch 10's were — but for the opposite
  -- reason.  Batch 10 wrote no flag at all; these eight write flags and the
  -- counter with COMPLETE definiteness: the SDM leaves nothing undefined in
  -- either group, so there is again nothing for the comparator to absorb.
  --
  -- ⚠️ NO LOOP FORM HAS A rel32 ENCODING — `E0`/`E1`/`E2 cb` is rel8 only (SDM
  -- Vol. 2A, LOOP) — the same gap `jrcxz` has, and the roster's `label` shapes
  -- are the assembler's name for the same rel8 byte, not a second encoding.
  , { mnemonic := "loop", shapes := "rel8 (no rel32 encoding exists) · addr32 → ecx counter",
      tier := .exact, decode := .xed, undefined := [], sdm := "Vol. 2A LOOP/LOOPcc" }
  , { mnemonic := "loope", shapes := "rel8 — 2 spellings (loope, loopz)", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A LOOP/LOOPcc" }
  , { mnemonic := "loopne", shapes := "rel8 — 2 spellings (loopne, loopnz)", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A LOOP/LOOPcc" }
  -- Each of these five names the ONE flag it writes, because that is the whole
  -- instruction and the coverage table should say so.
  , { mnemonic := "clc", shapes := "no operands — cf := 0", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A CLC" }
  , { mnemonic := "stc", shapes := "no operands — cf := 1", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A STC" }
  , { mnemonic := "cmc", shapes := "no operands — cf := ¬cf", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A CMC" }
  , { mnemonic := "cld", shapes := "no operands — df := 0", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A CLD" }
  , { mnemonic := "std", shapes := "no operands — df := 1", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A STD" }
  -- P1 BATCH 12: the near-free four of roster family 7.  None writes a flag and
  -- none draws an oracle bit, so all four are `T-exact` with no undefined
  -- column — the batch's difficulty was never in the flags.
  , { mnemonic := "nop", shapes := "no operands (0x90) · r · m — all inert",
      tier := .exact, decode := .xed, undefined := [], sdm := "Vol. 2A NOP" }
  -- ⭐ `ud2` IS `T-exact` AND NOT `T-absent`, AND THE DISTINCTION IS THE POINT.
  -- `T-absent` means the model REFUSED to give a form a meaning.  `ud2` has a
  -- meaning and the model computes it: the meaning is #UD.  Filing a fully
  -- modelled instruction under the tier reserved for gaps would understate the
  -- coverage AND corrupt the one column a reader consults to find them — which
  -- is why the refusal carries `MsErr.byDesign` rather than `.unimplemented`.
  , { mnemonic := "ud2", shapes := "no operands — #UD by definition",
      tier := .exact, decode := .xed, undefined := [], sdm := "Vol. 2A UD2" }
  , { mnemonic := "retq", shapes := "no operands — near return, pops rip",
      tier := .exact, decode := .xed, undefined := [], sdm := "Vol. 2A RET" }
  , { mnemonic := "leaveq", shapes := "no operands — rsp := rbp; pop rbp",
      tier := .exact, decode := .xed, undefined := [], sdm := "Vol. 2A LEAVE" }
  -- P1 BATCH 13: the flagless shifts and the byte-swapping move.  All four are
  -- `T-exact` with an EMPTY undefined column, and for these three that column is
  -- the whole instruction: `shl`/`shr`/`sar` draw three oracle bits at every
  -- non-zero count, and their `x`-suffixed cousins compute the same result and
  -- draw none, because "Flags Affected: None".
  --
  -- ⚠️ THE SHAPES ARE WRITTEN DESTINATION-FIRST like every other row, so `r,r,r`
  -- is `dst, src, count` and `r,m,r` has the memory operand as the SOURCE.
  -- Neither is a memory-destination claim and `claimsMemDest` must not read one:
  -- these forms cannot write memory at all.
  , { mnemonic := "sarx", shapes := "r,r,r · r,m,r — l/q only", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A SARX/SHLX/SHRX" }
  , { mnemonic := "shlx", shapes := "r,r,r · r,m,r — l/q only", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A SARX/SHLX/SHRX" }
  , { mnemonic := "shrx", shapes := "r,r,r · r,m,r — l/q only", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A SARX/SHLX/SHRX" }
  -- ⭐ `movbe` IS THE BATCH'S MEMORY-DESTINATION CLAIM, spelled `m(w)` — a WRITE
  -- that never reads its destination, the same kind of write `setcc` makes, and
  -- the notation's rule (`m`, an optional width, a parenthesised kind) is what
  -- `claimsMemDest` reads.  `isMemDestVector` gains its `.movbe` case in the
  -- same commit; D32 is what that pairing costs when it is not done.
  , { mnemonic := "movbe", shapes := "r,m · m(w),r — w/l/q", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A MOVBE" }
  -- P1 BATCH 14 (`p1/roster.tsv` families 33, 39, 42, 46): the BIT-COUNTING
  -- group.  One operand shape — `r,r · r,m`, destination always a register —
  -- and six different answers about what the flags mean.
  --
  -- ⭐ THE `undefined` COLUMN IS NOW GATED, and this batch is why.  Until now it
  -- was checked only against the TIER (`frame_tier_iff_undefined_bits`: frame
  -- iff non-empty), so a row naming the wrong flags, or too few, read exactly
  -- like a right one.  `undefined_column_matches_the_model` in `Main.lean`
  -- compares its flag TOKENS against the set the model actually draws over
  -- every emitted case.  See docs/DECISIONS.md D39.
  --
  -- ⛔ AND `bsf`/`bsr` CARRY A TOKEN NO ROW HAS EVER CARRIED: `DEST`.  Their
  -- undefined region includes the DESTINATION REGISTER at a zero source, not
  -- only flags, and a column that could only name flags would have been unable
  -- to state the most unusual claim in the table.
  , { mnemonic := "popcnt", shapes := "r,r · r,m — w/l/q", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2B POPCNT" }
  , { mnemonic := "lzcnt", shapes := "r,r · r,m — w/l/q", tier := .frame,
      decode := .xed, undefined := ["PF", "AF", "SF", "OF"],
      sdm := "Vol. 2A LZCNT" }
  , { mnemonic := "tzcnt", shapes := "r,r · r,m — w/l/q", tier := .frame,
      decode := .xed, undefined := ["PF", "AF", "SF", "OF"],
      sdm := "Vol. 2A TZCNT" }
  , { mnemonic := "bsf", shapes := "r,r · r,m — w/l/q", tier := .frame,
      decode := .xed, undefined := ["CF", "PF", "AF", "SF", "OF", "DEST (src=0)"],
      sdm := "Vol. 2A BSF" }
  , { mnemonic := "bsr", shapes := "r,r · r,m — w/l/q", tier := .frame,
      decode := .xed, undefined := ["CF", "PF", "AF", "SF", "OF", "DEST (src=0)"],
      sdm := "Vol. 2A BSR" }
  , { mnemonic := "blsi", shapes := "r,r · r,m — l/q only", tier := .frame,
      decode := .xed, undefined := ["PF", "AF"], sdm := "Vol. 2A BLSI" }
  ]

/-- Render the table as GitHub-flavoured Markdown.  `Main` writes it to
`docs/COVERAGE.md` so the file in the repository is GENERATED and a stale table
is a diff, not a discovery. -/
def renderTable (rows : List Row) : String :=
  let hdr := "| mnemonic | operand shapes | tier | decode trust | undefined bits | SDM |\n"
  let sep := "|---|---|---|---|---|---|\n"
  let line (r : Row) : String :=
    let u := if r.undefined.isEmpty then "—" else String.intercalate ", " r.undefined
    s!"| `{r.mnemonic}` | {r.shapes} | {r.tier.toString} | {r.decode.toString} | {u} | {r.sdm} |\n"
  hdr ++ sep ++ String.join (rows.map line)

/-- Summary counts, for the harness's report line. -/
def tierCounts (rows : List Row) : Nat × Nat × Nat :=
  ( (rows.filter (fun r => r.tier == .exact)).length
  , (rows.filter (fun r => r.tier == .frame)).length
  , (rows.filter (fun r => r.tier == .absent)).length )

end X86
