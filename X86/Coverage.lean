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
  , { mnemonic := "shl",  shapes := "r/m, imm8 · r/m, cl", tier := .frame, decode := .xed,
      undefined := ["CF (count ≥ width)", "OF (count ≠ 1)", "AF (count ≠ 0)"],
      sdm := "Vol. 2A SAL/SAR/SHL/SHR" }
  , { mnemonic := "shr",  shapes := "r/m, imm8 · r/m, cl", tier := .frame, decode := .xed,
      undefined := ["CF (count ≥ width)", "OF (count ≠ 1)", "AF (count ≠ 0)"],
      sdm := "Vol. 2A SAL/SAR/SHL/SHR" }
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
  , { mnemonic := "jmp",  shapes := "rel32 · r/m64", tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A JMP" }
  , { mnemonic := "jcc",  shapes := "rel8/rel32, all 16 conditions", tier := .exact,
      decode := .xed, undefined := [], sdm := "Vol. 2A Jcc" }
  , { mnemonic := "call", shapes := "rel32 · r/m64", tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A CALL" }
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
