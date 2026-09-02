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
  -- are NOT claimed here; `m,r` below is P0's row, at width q only.
  let logicShapes := "r,r · r,imm · r,m — all of b/w/l/q · acc,imm · rh · m,r (q)"
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
  , { mnemonic := "cmp",  shapes := rm, tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A CMP" }
  , { mnemonic := "test", shapes := rm, tier := .frame, decode := .xed,
      undefined := ["AF"], sdm := "Vol. 2A TEST" }
  , { mnemonic := "shl",  shapes := "r/m, imm8 · r/m, cl", tier := .frame, decode := .xed,
      undefined := ["CF (count ≥ width)", "OF (count ≠ 1)", "AF (count ≠ 0)"],
      sdm := "Vol. 2A SAL/SAR/SHL/SHR" }
  , { mnemonic := "shr",  shapes := "r/m, imm8 · r/m, cl", tier := .frame, decode := .xed,
      undefined := ["CF (count ≥ width)", "OF (count ≠ 1)", "AF (count ≠ 0)"],
      sdm := "Vol. 2A SAL/SAR/SHL/SHR" }
  , { mnemonic := "lea",  shapes := "r, m", tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A LEA" }
  , { mnemonic := "inc",  shapes := "r/m", tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A INC" }
  , { mnemonic := "dec",  shapes := "r/m", tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A DEC" }
  , { mnemonic := "neg",  shapes := "r/m", tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A NEG" }
  , { mnemonic := "not",  shapes := "r/m", tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A NOT" }
  , { mnemonic := "push", shapes := "r · m · imm", tier := .exact, decode := .xed,
      undefined := [], sdm := "Vol. 2A PUSH" }
  , { mnemonic := "pop",  shapes := "r · m", tier := .exact, decode := .xed,
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
