/-
# x86lean-diff — the differential harness driver

Plan v1 §4.3 and the P0 EXIT CRITERION: one differential run of the twenty
scalar forms against ACL2 x86isa with ZERO UNEXPLAINED disagreements, every
disagreement filed with its class.

WHAT "EXPLAINED" MEANS HERE, since the exit criterion turns on it.  A
disagreement is EXPLAINED exactly when it lies entirely inside the set of flags
this model marks undefined for that (instruction, state) — and that set is not
declared in the harness, it is DERIVED by running the same step under two
opposite oracles (`X86.undefinedFlags`).  There is therefore one notion of
"undefined" in the system, the semantics', and the harness cannot drift from it.
Everything else is UNEXPLAINED and is a finding.

MODES
  emit <out>            run the Lean model over every vector × pre-state
  emit-asm <out>        the assembly source, for the encoder cross-check
  compare <a> <b>       classify the disagreements between two record files
  selftest              drive the comparator with DELIBERATELY WRONG models
  coverage <out>        regenerate the coverage table
  runs <out>            regenerate the vector run-index certificate (D105)
  stats                 vector and case counts

⭐ ON `selftest`.  Plan v1 §7 lists "the harness's own bugs" as a risk and names
the mitigation: a selftest with a deliberately wrong model.  A comparator that
has only ever been run on two agreeing models is not known to detect anything.
`selftest` injects one deliberately wrong model per entry of `selftestArms`
(twenty-seven at P1 batch 11; the count is READ FROM THE TABLE and never typed,
because both stale literals this file used to carry — "nineteen" here and
"twenty-three" in the banner — outlived the lists they described).  Among them:
an `inc` that clobbers CF, a
`movl` that fails to zero-extend, a shift that forgets to mask its count, an `adc`
that drops the carry-in, an `adc` whose carry-OUT forgets the carry-in, a `cmp`
that writes its result back, and a `cmp` that writes back ONLY to a memory
destination, a memory read-modify-write that drops its store, and one that
stores the right value at the wrong WIDTH, a `jcxz` with an inverted test, and a
`jecxz` that ignores the address-size prefix, an inverted `setcc`, and a `cmov`
that skips its write on a false condition, a `sar` that brings in zeros, and a
`sar` given SHL/SHR's undefined-CF rule, a backwards `rol`, and a rotate whose CF
write keys on the reduced count, an off-by-one `bts`, and a bit-test that
recomputes ZF, a `movsx` that zero-extends, an `xchg` that copies instead of
swapping, a `cltd` that merges where it must zero-extend, and a width-changing
move that bounds its VALUE instead of its WRITE — and REQUIRES the comparator to
catch each one.

⭐ THE PATTERN THE LAST FOUR MAKE, since it is now deliberate rather than
accidental: each batch plants a PAIR, an easy half that almost any pre-state
catches and a hard half that only the batch's own new coverage can see.  Batch
2's pair turns on the carry boundary in the PRE-STATES; batch 3's turns on a
memory operand in the DESTINATION, which no vector had before it.  The hard half
is the arm that says the batch's new coverage is load-bearing, and it is the one
to run when asking whether some of that coverage could be dropped.

LANE. Personal lane, public sources only.
-/
import X86
import Tests.Vectors

open X86
open X86.Tests

/-! ## Record emission -/

/-- One emitted case. -/
def caseLines (v : Vec) (idx : Nat) (pre : Cpu) (stepFn : Instr → Cpu → Cpu) : List String :=
  let post := stepFn v.instr pre
  -- ⛔ P1 BATCH 14: the undefined SET, not the undefined FLAGS.  `bsf`/`bsr` at
  -- a zero source leave the destination REGISTER undefined, and a record that
  -- named only flags would have made every such case an unexplained
  -- disagreement in `rax` — the differential's gate failing on the model being
  -- RIGHT.  `undefinedRegs` is cross-checked against the AST-level declaration
  -- by `undefinedLeaked`, so widening the record here does not widen what can
  -- be explained away; see the note in `X86/Serialize.lean`.
  let und := undefinedFlags v.instr pre ++ undefinedRegs v.instr pre
  let leak := undefinedLeaked v.instr pre windows
  [ s!"CASE id={v.id}/{idx} mnemonic={v.mnemonic} bytes={v.bytes} len={v.instr.len}"
  , s!"PRE {pre.render windows}"
  , s!"POST {post.render windows}"
  , s!"UNDEF {if und.isEmpty then "-" else String.intercalate "," und}"
  , s!"LEAK {if leak then "1" else "0"}" ]

def emitAll (stepFn : Instr → Cpu → Cpu) (nRandom : Nat) : List String :=
  (vectors.flatMap fun v =>
    (preStates 0x9E3779B97F4A7C15 nRandom).zipIdx.flatMap fun (pre, i) =>
      caseLines v i pre stepFn)

/-! ## Emission for the ACL2 side

⭐ THE LISP SIDE PARSES NOTHING.  Rather than teach ACL2 to read the record
format, the harness EMITS ACL2 SOURCE: a `defconst` holding the cases as
ordinary Lisp data.  A parser on the oracle side would be a second
implementation of the format, in a language chosen for theorem proving rather
than for string handling, and every bug in it would look exactly like a
disagreement — which is the one thing this harness must never confuse. -/

/-- Split a hex string into its byte pairs. -/
def hexPairs : List Char → List String
  | a :: b :: rest => s!"{a}{b}" :: hexPairs rest
  | _ => []

/-- The instruction's bytes, as a list of Lisp hex literals. -/
def bytesToLisp (hexStr : String) : String :=
  "(" ++ String.intercalate " " ((hexPairs hexStr.toList).map (fun p => s!"#x{p}")) ++ ")"

/-- ⭐⭐⭐ THE XMM ALIST, by register index (P2 vector wave, batch 0).

The oracle's XMM registers are not an argument of `init-x86-state-64`, so the
driver writes them after initialising — the same shape the segment bases take,
and for the same reason: the VALUES travel from here and the x86isa API
(`wx128`) stays on the Lisp side.  Each value is one 128-bit natural, which
ACL2 reads as an ordinary integer literal. -/
def xmmsToLisp (s : Cpu) : String :=
  "(" ++ String.intercalate " "
    (XmmReg.all.map (fun r =>
      let v := s.xmm.get r
      let hi : BitVec 64 := (v >>> 64).setWidth 64
      let lo : BitVec 64 := v.setWidth 64
      s!"({r.index.val} . #x{hex64 hi}{hex64 lo})")) ++ ")"

/-- The GPR alist, by x86isa register index. -/
def gprsToLisp (s : Cpu) : String :=
  "(" ++ String.intercalate " "
    (GPR.all.map (fun r => s!"({r.index.val} . #x{hex64 (s.regs.get r)})")) ++ ")"

/-- RFLAGS as a 32-bit word.  Bit 1 is the architecturally reserved one
(SDM Vol. 1 Figure 3-8); x86isa initialises through `!rflags`, so the value has
to be a real RFLAGS image rather than seven loose booleans. -/
def rflagsToLisp (f : Flags) : String :=
  -- The positions come from `flagFields` (D30), so this emitter and the record
  -- format cannot disagree about which flags exist.  Bit 1 is added on its own
  -- because it is not a flag we model — it is the architecturally reserved bit,
  -- always 1, and it belongs to the IMAGE rather than to the field list.
  let v := flagFields.foldl
    (fun acc r => acc + (if r.get f then Nat.shiftLeft 1 r.bit else 0)) 2
  s!"#x{hexPad (BitVec.ofNat 64 v) 8}"

/-- The memory alist: the instruction's own bytes at RIP, then every byte the
watch windows cover.  The windows are written explicitly (rather than only the
non-zero bytes of our representation) so that the two models start from
BYTE-IDENTICAL memory over the whole compared region — a zero we did not write
and a zero x86isa did not write are the same value but not the same evidence. -/
def memToLisp (v : Vec) (s : Cpu) (ws : List Window) : String :=
  let insn := (hexPairs v.bytes.toList).zipIdx.map (fun (b, i) =>
    s!"(#x{hex64 (s.rip + BitVec.ofNat 64 i)} . #x{b})")
  let win := ws.flatMap fun w =>
    (List.range w.len).map fun i =>
      let a := w.base + BitVec.ofNat 64 i
      s!"(#x{hex64 a} . #x{hex8 (s.mem.read a)})"
  "(" ++ String.intercalate " " (insn ++ win) ++ ")"

/-- ⭐⭐ P2 ITEM 1: THE SEGMENT BASES TRAVEL AS VALUES AND THE *INDICES* STAY IN
THE LISP.  x86isa keeps FS's and GS's 64-bit bases in the IA32_FS_BASE and
IA32_GS_BASE MSRs, addressed by ITS OWN internal indices
(`*ia32_fs_base-idx*`) — numbers that mean nothing outside that model.  Emitting
them from here would put an x86isa implementation detail in a Lean source file
and would be a second place to keep it right; emitting the VALUES and letting
`scripts/x86isa_driver.lisp` name the registers keeps each side saying what it
alone knows.  The same reasoning `gprsToLisp` uses for `r.index`, one level up:
there the encoding is architectural and shared, here it is not. -/
def acl2Case (v : Vec) (idx : Nat) (pre : Cpu) (ws : List Window) : String :=
  s!"  (:id \"{v.id}/{idx}\" :rip #x{hex64 pre.rip} :len {v.instr.len}\n\
   :bytes {bytesToLisp v.bytes}\n\
   :gprs {gprsToLisp pre}\n\
   :fsbase #x{hex64 pre.fsBase} :gsbase #x{hex64 pre.gsBase}\n\
   :xmms {xmmsToLisp pre}\n\
   :rflags {rflagsToLisp pre.flags}\n\
   :mem {memToLisp v pre ws})"

/-! ## The comparator -/

structure Rec where
  id : String
  mnemonic : String
  post : List (String × String)
  undef : List String
  leak : Bool
  deriving Inhabited

def parseKV (s : String) : List (String × String) :=
  (s.splitOn " ").filterMap fun tok =>
    match tok.splitOn "=" with
    | [k, v] => some (k, v)
    | _ => none

def parseRecords (lines : List String) : List Rec := Id.run do
  let mut out : List Rec := []
  let mut cur : Option (String × String) := none
  let mut post : List (String × String) := []
  let mut und : List String := []
  let mut leak := false
  for l in lines do
    if l.startsWith "CASE " then
      match cur with
      | some (id, mn) => out := out ++ [{ id, mnemonic := mn, post, undef := und, leak }]
      | none => pure ()
      let kv := parseKV (l.drop 5).toString
      cur := some ((kv.lookup "id").getD "?", (kv.lookup "mnemonic").getD "?")
      post := []; und := []; leak := false
    else if l.startsWith "POST " then
      post := parseKV (l.drop 5).toString
    else if l.startsWith "UNDEF " then
      let t := (l.drop 6).trimAscii.toString
      und := if t == "-" then [] else t.splitOn ","
    else if l.startsWith "LEAK " then
      leak := (l.drop 5).trimAscii.toString == "1"
  match cur with
  | some (id, mn) => out := out ++ [{ id, mnemonic := mn, post, undef := und, leak }]
  | none => pure ()
  return out

/-- A disagreement, with its class. -/
structure Disagreement where
  id : String
  mnemonic : String
  field : String
  lhs : String
  rhs : String
  /-- `undefined-region` (EXPLAINED) · `spec` · `halt` · `harness`. -/
  cls : String

/-- The seven flag names. -/
def flagNames : List String := flagFields.map (·.name)

/-- ⛔ THE FIELDS THAT MAY BE EXPLAINED AS UNDEFINED AT ALL.

This list used to be `flagNames`, and the comment beside it read "so a
disagreement in a flag can be tested against the undefined set while a
disagreement in a register never is".  P1 BATCH 14 made that false: `bsf`/`bsr`
at a zero source leave the DESTINATION REGISTER undefined (SDM Vol. 2A), so a
register disagreement can be legitimate.

⚠️ IT IS STILL A CLOSED LIST, and deliberately.  Dropping the guard entirely and
testing only `a.undef.contains k` would give the same answer today — the record
carries nothing but flag and register names — and would silently start
explaining away `rip`, `refused`, or a memory window the day one of those
reached the undefined set.  RIP and memory are exactly what `undefinedLeaked`
refuses to let the oracle touch, and this list is the second place that refusal
is written down. -/
def undefinableFields : List String := flagNames ++ GPR.all.map (·.name .q)

/-- ⭐ WHEN BOTH MODELS REFUSE, THEY AGREE.

A refused instruction has no post-state either model is claiming, so comparing
the registers, RIP and memory after a refusal compares two pieces of debris.
The claim being made is "this faults", and on that the two agree. Anything else
would make the fix for the non-canonical-branch gap look like eighty new
disagreements instead of eighty resolved ones.

A refusal on ONE side only is the real finding and gets its own class. -/
def bothRefused (a b : Rec) : Bool :=
  (a.post.lookup "refused" == some "1") && (b.post.lookup "refused" == some "1")

/-- ⭐⭐⭐ THE KNOWN-ORACLE-DIVERGENCE LIST (P2 vector wave, batch 6).

⛔ WHY THIS EXISTS, AND WHY IT IS THE MOST DANGEROUS LIST IN THE REPOSITORY.

Twice now the differential has been RIGHT and the ORACLE wrong: `movdqa` at an
unaligned address, which x86isa does not fault on (D91, oracle INCOMPLETE), and
`movd`/`movq` into an XMM register, which x86isa MERGES where the SDM and K both
say CLEAR (D93, oracle WRONG). Both times the remedy was to DELETE the vector,
and deleting a vector stops that test **permanently and silently**: if x86isa is
fixed tomorrow, nothing notices, and the model's own rule goes back to being
carried by a theorem alone.

⇒ A declared divergence keeps the case RUNNING. It is compared on every run, it
is reported in its own class and counted, and — the half that makes it safe —
**it is gated in BOTH directions**: an entry that stops diverging is a FAILURE,
not a quiet success, because it means either the oracle was fixed (delete the
entry) or this model drifted into agreeing with a known-wrong answer (find out
why, urgently).

⚠️ EVERY ENTRY CARRIES ITS THIRD SOURCE, and that is the admission price. A
two-model disagreement names no culprit (D93); an entry here asserts that some
*independent* public authority — K's semantics, the SDM by section — agrees with
THIS model against the oracle. Without that, this list is just a place to hide
red.

⚠️ AND IT IS DELIBERATELY NARROW: an entry names a vector-id PREFIX and ONE
FIELD. It cannot excuse a whole vector, and it cannot excuse a field the entry
did not name. `undefinableFields` is the only comparable mechanism here and its
own comment warns what a broad explaining-away list costs. -/
structure KnownDivergence where
  /-- The vector id, without the `/n` pre-state suffix. -/
  vec : String
  /-- The single field this model and the oracle are known to differ in. -/
  field : String
  /-- The INDEPENDENT authority that agrees with this model. Not optional. -/
  source : String
  /-- The decision note recording the measurement. -/
  note : String
  deriving Repr, Inhabited

def knownDivergences : List KnownDivergence :=
  [ { vec := "movd_to_x", field := "xmm0"
    , source := "K `movd_xmm_r32.k`: concatenateMInt(mi(96,0), …); SDM Vol. 2B MOVD: DEST[127:32] <- 0"
    , note := "D93" }
  , { vec := "movq_to_x", field := "xmm0"
    , source := "K `movq_xmm_r64.k`: concatenateMInt(mi(64,0), …); SDM Vol. 2B MOVQ: DEST[127:64] <- 0"
    , note := "D93" }
  -- ⛔⛔⛔ P2 BATCH 13 (D108) — ACL2 x86isa READS THE PACKED-SHIFT COUNT FROM ALL
  -- 128 BITS OF THE COUNT REGISTER, where the SDM and K both read SRC[63:0].
  --
  -- Found by the differential, not by reading: 8 unexplained disagreements, all
  -- at the ONE pre-state whose `xmm1` has a small low quadword and a NON-ZERO
  -- upper one. Isolated to a single bit: flipping one bit of the count
  -- register's upper quadword — a bit the SDM says is not part of the count —
  -- flips the oracle's answer from `shift by 3` to `all zeros`.
  --
  -- ⭐⭐ AND THE ORACLE CONTRADICTS ITSELF, which is what makes this a finding
  -- rather than an interpretation. The MEMORY-count shape of the SAME mnemonic,
  -- given the SAME 128-bit count value, returns the SDM's answer:
  --     psllw %xmm1,%xmm0   count 0xbfbe…b9b8_0000000000000003  ⇒  0  (wrong)
  --     psllw (%rbx),%xmm0  the same 128 bits in memory         ⇒  shift by 3
  -- so x86isa's own memory path already implements the 64-bit rule that its
  -- register path does not. `vshiftm` is therefore NOT declared here: it agrees,
  -- and declaring it would be an entry that never diverges — which this channel
  -- fails, by design.
  --
  -- ⚠️ EIGHT ENTRIES AND NOT ONE WILDCARD. The channel names a vector prefix and
  -- ONE field; a single broad entry would excuse the whole group, including any
  -- future disagreement about a lane width or a sign fill that has nothing to do
  -- with the count's width.
  , { vec := "psllw_x", field := "xmm0"
    , source := "K `psllw_xmm_xmm.k`: the saturation test is `ugtMInt(extractMInt(getParentValue(R1),192,256), mi(64,15))` — bits 192..256 of the 256-bit parent are SRC[63:0], and the upper quadword is not read; SDM Vol. 2B PSLLW: COUNT <- COUNT_SOURCE[63:0]"
    , note := "D108" }
  , { vec := "pslld_x", field := "xmm0"
    , source := "K `pslld_xmm_xmm.k`: the saturation test is `ugtMInt(extractMInt(getParentValue(R1),192,256), mi(64,31))` — bits 192..256 of the 256-bit parent are SRC[63:0], and the upper quadword is not read; SDM Vol. 2B PSLLD: COUNT <- COUNT_SOURCE[63:0]"
    , note := "D108" }
  , { vec := "psllq_x", field := "xmm0"
    , source := "K `psllq_xmm_xmm.k`: the saturation test is `ugtMInt(extractMInt(getParentValue(R1),192,256), mi(64,63))` — bits 192..256 of the 256-bit parent are SRC[63:0], and the upper quadword is not read; SDM Vol. 2B PSLLQ: COUNT <- COUNT_SOURCE[63:0]"
    , note := "D108" }
  , { vec := "psrlw_x", field := "xmm0"
    , source := "K `psrlw_xmm_xmm.k`: the saturation test is `ugtMInt(extractMInt(getParentValue(R1),192,256), mi(64,15))` — bits 192..256 of the 256-bit parent are SRC[63:0], and the upper quadword is not read; SDM Vol. 2B PSRLW: COUNT <- COUNT_SOURCE[63:0]"
    , note := "D108" }
  , { vec := "psrld_x", field := "xmm0"
    , source := "K `psrld_xmm_xmm.k`: the saturation test is `ugtMInt(extractMInt(getParentValue(R1),192,256), mi(64,31))` — bits 192..256 of the 256-bit parent are SRC[63:0], and the upper quadword is not read; SDM Vol. 2B PSRLD: COUNT <- COUNT_SOURCE[63:0]"
    , note := "D108" }
  , { vec := "psrlq_x", field := "xmm0"
    , source := "K `psrlq_xmm_xmm.k`: the saturation test is `ugtMInt(extractMInt(getParentValue(R1),192,256), mi(64,63))` — bits 192..256 of the 256-bit parent are SRC[63:0], and the upper quadword is not read; SDM Vol. 2B PSRLQ: COUNT <- COUNT_SOURCE[63:0]"
    , note := "D108" }
  , { vec := "psraw_x", field := "xmm0"
    , source := "K `psraw_xmm_xmm.k`: the saturation test is `ugtMInt(extractMInt(getParentValue(R1),192,256), mi(64,15))` — bits 192..256 of the 256-bit parent are SRC[63:0], and the upper quadword is not read; SDM Vol. 2B PSRAW: COUNT <- COUNT_SOURCE[63:0]"
    , note := "D108" }
  , { vec := "psrad_x", field := "xmm0"
    , source := "K `psrad_xmm_xmm.k`: the saturation test is `ugtMInt(extractMInt(getParentValue(R1),192,256), mi(64,31))` — bits 192..256 of the 256-bit parent are SRC[63:0], and the upper quadword is not read; SDM Vol. 2B PSRAD: COUNT <- COUNT_SOURCE[63:0]"
    , note := "D108" } ]

def divergenceFor (id field : String) : Option KnownDivergence :=
  knownDivergences.find? (fun d => d.vec == id.takeWhile (· != '/') && d.field == field)

/-- ⚠️ `divs` IS A PARAMETER, NOT A GLOBAL, AND THE SCOPING IS THE POINT.  A
declared divergence is a statement about **this model against the ORACLE**. The
selftest's `driveWrong` compares this model against a deliberately WRONG COPY OF
ITSELF, where an oracle's defect is irrelevant — so it passes `[]` and an arm
that lands on a divergent field still counts as a catch. Passing the same list to
both would have let a declared oracle divergence quietly excuse a planted bug. -/
def classify (divs : List KnownDivergence) (a b : Rec) : List Disagreement :=
  if bothRefused a b then [] else
  let keys := (a.post.map Prod.fst) ++ (b.post.map Prod.fst).filter
    (fun k => !(a.post.map Prod.fst).contains k)
  keys.filterMap fun k =>
    let x := (a.post.lookup k).getD "<missing>"
    let y := (b.post.lookup k).getD "<missing>"
    if x == y then none
    else
      let cls :=
        if x == "<missing>" || y == "<missing>" then "harness"
        else if k == "refused" then "refusal"
        else if undefinableFields.contains k && a.undef.contains k then "undefined-region"
        -- ⭐ A DECLARED DIVERGENCE IS ITS OWN CLASS. It is NOT "matched" and NOT
        -- "explained": it is a disagreement this repository has measured, named
        -- and attributed to the oracle, and it is counted and reported on every
        -- run so it can never become invisible.
        else if (divs.find? (fun d =>
                   d.vec == a.id.takeWhile (· != '/') && d.field == k)).isSome then
          "oracle-divergence"
        else "spec"
      some { id := a.id, mnemonic := a.mnemonic, field := k, lhs := x, rhs := y, cls }

structure Report where
  cases : Nat := 0
  matched : Nat := 0
  explained : Nat := 0
  unexplained : Nat := 0
  /-- Disagreements matching a declared `knownDivergences` entry. -/
  diverged : Nat := 0
  leaks : Nat := 0
  missing : Nat := 0
  details : List Disagreement := []

def compareRecs (divs : List KnownDivergence) (as bs : List Rec) : Report := Id.run do
  let mut r : Report := {}
  for a in as do
    r := { r with cases := r.cases + 1 }
    if a.leak then r := { r with leaks := r.leaks + 1 }
    match bs.find? (fun b => b.id == a.id) with
    | none => r := { r with missing := r.missing + 1 }
    | some b =>
      let ds := classify divs a b
      if ds.isEmpty then r := { r with matched := r.matched + 1 }
      else
        let expl := ds.filter (fun d => d.cls == "undefined-region")
        let dvg := ds.filter (fun d => d.cls == "oracle-divergence")
        let unex := ds.filter (fun d => d.cls != "undefined-region"
                                        && d.cls != "oracle-divergence")
        r := { r with
          explained := r.explained + expl.length
          diverged := r.diverged + dvg.length
          unexplained := r.unexplained + unex.length
          details := r.details ++ ds }
  return r

def renderReport (r : Report) : String :=
  let head := s!"cases={r.cases} matched={r.matched} explained={r.explained} \
unexplained={r.unexplained} oracle-divergence={r.diverged} \
oracle-leaks={r.leaks} missing={r.missing}"
  let byClass := ["spec", "refusal", "harness", "undefined-region",
                  "oracle-divergence"].map fun c =>
    s!"  {c}: {(r.details.filter (fun d => d.cls == c)).length}"
  let sample := (r.details.filter (fun d => d.cls != "undefined-region"
                                              && d.cls != "oracle-divergence")).take 20
  let lines := sample.map fun d =>
    s!"  [{d.cls}] {d.id} ({d.mnemonic}) {d.field}: lean={d.lhs} oracle={d.rhs}"
  String.intercalate "\n" ([head] ++ byClass ++
    (if lines.isEmpty then [] else ["first unexplained disagreements:"] ++ lines))

/-! ## The deliberately wrong models (plan v1 §7)

Each is a REAL x86 modelling bug, not a random perturbation:
* `wrongInc` clobbers CF, which is the single most-cited `inc`-vs-`add` error;
* `wrongMovD` preserves the upper 32 bits on a 32-bit write, i.e. models the
  32-bit rule as if it were the 16-bit one;
* `wrongShiftMask` shifts by the unmasked count, so `shlq $64` zeroes the
  register instead of being a no-op.
If the comparator misses any of these it is not a comparator. -/

def wrongInc (i : Instr) (s : Cpu) : Cpu :=
  let out := step i s
  match i.op with
  | .un .inc _ _ => { out with flags := { out.flags with cf := !s.flags.cf } }
  | _ => out

def wrongMovD (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .mov .d (.reg r _) src =>
      let nr := s.rip + BitVec.ofNat 64 i.len
      let v := s.readOperand .d nr src
      -- the BUG: merge instead of zero-extend
      let old := s.regs.get r
      { s with regs := s.regs.set r ((old &&& ~~~(Size.mask .d)) ||| Value.trunc .d v),
               rip := nr }
  | _ => step i s

/-- SURGICAL: everything as the correct model does it, except that the shift
count is not masked.  The first draft of this function also dropped the flag
computation, which made it a DIFFERENT bug — and it still produced hundreds of
disagreements, so it looked like a pass.  A wrong model that is wrong in more
ways than the one being tested cannot tell you the comparator found the one you
planted; that is why this one recomputes the flags exactly. -/
def wrongShiftMask (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .shift k sz dst amt =>
      let nr := s.rip + BitVec.ofNat 64 i.len
      let cnt : BitVec 8 := match amt with
        | .imm8 v => v
        | .cl => (s.getReg .b .rcx).setWidth 8
      let n := cnt.toNat            -- the BUG: no masking to 5 or 6 bits
      let a := s.readOperand sz nr dst
      let res := match k with
        | .shl => Value.trunc sz (a <<< n)
        | .shr => (Value.trunc sz a) >>> n
        | .sar => Value.sar sz a n
      if n = 0 then (s.writeOperand sz nr dst res).setRip nr
      else
        let (cfU, s) := s.undefBit
        let (ofU, s) := s.undefBit
        let (afU, s) := s.undefBit
        let s := s.setFlags (Flags.shiftFlags k sz a res n cfU ofU afU s.flags)
        (s.writeOperand sz nr dst res).setRip nr
  | _ => step i s

/-- ⭐ P1 BATCH 2's PLANTED BUG, and the reason it is here rather than in a
comment.  This model is `adc` with the carry-in DROPPED — i.e. `adc` implemented
as `add`, which is the single most likely way to get a carry-propagating form
wrong and the one a reviewer is least likely to see, because the two agree on
every operand pair that does not sit on the carry boundary.

It is SURGICAL in the sense P0's `wrongShiftMask` had to be taught: the flags are
recomputed by the same route, so the only difference is the carry.

⚠️ THIS ONE IS THE EASY HALF, AND SAYING SO IS THE POINT.  Any pre-state with CF
set catches it, because dropping the carry moves the RESULT by one on almost
every operand pair — 630 disagreements, from three sweeps that were already
there.  `wrongAdcCarryOutCF` below is the hard half, and it is the one that says
whether `carryBoundary` earns its place. -/
def wrongAdcNoCarry (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .bin .adc sz dst src =>
      if !wellFormed2 dst src then s.halt (.illegalOperands "two memory operands")
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let a := s.readOperand sz nr dst
        let b := s.readOperand sz nr src
        -- the BUG: `false` where the model reads `s.flags.cf`
        let res := Flags.adcResult sz a b false
        let s := s.setFlags (Flags.adc sz a b false s.flags)
        (s.writeOperand sz nr dst res).setRip nr
  | _ => step i s

/-- ⭐ THE HARD HALF, AND THE ONE THE CARRY BOUNDARY EXISTS FOR.  This model
computes the RESULT correctly — carry-in and all — and gets only the CARRY-OUT
wrong, by asking `adcCF` for the carry of `a + b` instead of `a + b + CF`.

Every operand pair on which `a + b` already carries, or already does not, gives
the same CF either way. The two models differ ONLY where the incoming carry is
what pushes the sum over the top: `0xFF + 0x00 + 1` at width b, and its siblings
at the other three widths. That is one point in the state space, and P0's three
sweeps do not contain it — the diagonal has every flag clear, and the two
rotated sweeps pair each adversarial value with something far from zero.

⛔ AND THE PARAGRAPH THAT STOOD HERE CLAIMED SOMETHING THE PROBE REFUTED.  It
said that deleting `carryBoundary` from `Tests/Vectors.lean` would make this arm
catch nothing.  Deleting it was tried, and this arm still caught the bug — 62
disagreements instead of 76.  P0's three sweeps DO cross the carry boundary,
twice over and both times by accident: `0xAAAA…` and `0x5555…` sit next to each
other in the adversarial list and are exact complements, so `a + b + 1` wraps at
width q; and truncating `0x100000000` to a byte gives zero, so several pairs
become `0xFF + 0x00` at width b.

Which leaves the honest reason `carryBoundary` stays, stated as what it is:
⇒ **COVERAGE THAT ARISES INCIDENTALLY FROM A LIST WRITTEN FOR ANOTHER PURPOSE IS
COVERAGE NOBODY IS MAINTAINING.**  Reordering `adversarial`, or dropping one of
those two constants, would silently remove the only states that exercise this
rule, and no gate would say so.  `Tests/Coverage.lean`'s
`pre_states_cross_the_carry_boundary` is what turns the accident into an
assertion; `carryBoundary` is what makes the assertion cheap to keep true. -/
def wrongAdcCarryOutCF (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .bin .adc sz dst src =>
      if !wellFormed2 dst src then s.halt (.illegalOperands "two memory operands")
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let a := s.readOperand sz nr dst
        let b := s.readOperand sz nr src
        let cin := s.flags.cf
        let res := Flags.adcResult sz a b cin            -- correct
        let f := Flags.adc sz a b cin s.flags
        -- the BUG, and nothing else: the carry OUT forgets the carry IN
        let s := s.setFlags { f with cf := Flags.adcCF sz a b false }
        (s.writeOperand sz nr dst res).setRip nr
  | _ => step i s

/-- ⭐ P1 BATCH 3's PLANTED BUG, EASY HALF: a `cmp` that WRITES ITS RESULT BACK.

This is the single most likely way to get `cmp` wrong — it is `sub` with the
result discarded, and the discarding is one line that is easy not to write.  At
a REGISTER destination any pre-state whose operands differ catches it, which is
why this arm expects `rax` and is labelled the easy half. -/
def wrongCmpWritesBack (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .bin .cmp sz dst src =>
      if !wellFormed2 dst src then s.halt (.illegalOperands "two memory operands")
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let a := s.readOperand sz nr dst
        let b := s.readOperand sz nr src
        let s := s.setFlags (Flags.sub sz a b s.flags)
        -- the BUG: `cmp` is `sub` with the result DISCARDED, and here it is not
        (s.writeOperand sz nr dst (Flags.subResult sz a b)).setRip nr
  | _ => step i s

/-- ⭐ THE HARD HALF, AND THE ARM THAT SAYS WHETHER THIS BATCH'S NEW VECTORS
EARN THEIR PLACE.  This model discards the result exactly as the correct one
does at every REGISTER destination, and writes it back only when the destination
is MEMORY.

Before P1 batch 3 there was no vector in this repository with a memory operand in
a `cmp` or `test` destination, so this model was IDENTICAL to the correct one on
every case the harness ran — a whole class of wrongness with nothing pointed at
it.  The arm expects the data window rather than a register, because a register
is precisely where this bug is invisible. -/
def wrongCmpMemWriteBack (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .bin .cmp sz dst src =>
      if !wellFormed2 dst src then s.halt (.illegalOperands "two memory operands")
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let a := s.readOperand sz nr dst
        let b := s.readOperand sz nr src
        let s := s.setFlags (Flags.sub sz a b s.flags)
        -- the BUG, and only here: a memory destination is written back
        if dst.isMem then (s.writeOperand sz nr dst (Flags.subResult sz a b)).setRip nr
        else s.setRip nr
  | _ => step i s

/-- ⭐ P1 BATCH 4's PLANTED BUG, EASY HALF: a read-modify-write to MEMORY that
sets its flags correctly and never performs the STORE.

`andq %rax, (%rbx)` is the first shape in this repository that reads a memory
location, computes, and writes it back.  A model that computed the flags and
forgot the store would look completely correct in every register and every flag
— which is most of what the record carries. -/
def wrongMemStoreDropped (i : Instr) (s : Cpu) : Cpu :=
  let out := step i s
  match i.op with
  | .bin k _ (.mem _) _ =>
      -- `cmp`/`test` legitimately write nothing, so leaving them alone keeps the
      -- bug surgical: exactly one thing is wrong with this model.
      if k == .cmp || k == .test then out else { out with mem := s.mem }
  | .un _ _ (.mem _) => { out with mem := s.mem }
  | _ => out

/-- ⭐ THE HARD HALF, AND THE ONE ALL FOUR WIDTHS EXIST FOR.  This model stores
the RIGHT VALUE at the RIGHT ADDRESS and gets the WIDTH of the store wrong: it
writes eight bytes where the operand is one, two or four.

At width q it is IDENTICAL to the correct model.  At a REGISTER destination it
is identical too, because the register path truncates in `setReg` and never
touches a neighbour.  It differs only in the bytes ABOVE the operand inside the
data window — which is exactly what `memory_window_margin_is_fixed` keeps
patterned, and exactly what no batch before this one had a vector to look at.

The claim that `and_mr_b`/`_w`/`_l` and their siblings are load-bearing is
tested by deleting them and re-running this arm, not asserted
(docs/DIFFERENTIAL-P1-BATCH4.md). -/
def wrongMemStoreWidth (i : Instr) (s : Cpu) : Cpu :=
  let out := step i s
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .bin k sz (.mem ea) _ =>
      if k == .cmp || k == .test then out
      else
        let a := ea.addr s nr
        -- the BUG: the value the model stored, re-stored eight bytes wide
        { out with mem := out.mem.writeSize .q a (out.mem.readSize sz a) }
  | .un _ sz (.mem ea) =>
      let a := ea.addr s nr
      { out with mem := out.mem.writeSize .q a (out.mem.readSize sz a) }
  | _ => out

/-- ⭐ P1 BATCH 5's PLANTED BUG, EASY HALF: a `jcxz` whose test is INVERTED.
Any pre-state at all catches it, in `rip`. -/
def wrongJcxzInverted (i : Instr) (s : Cpu) : Cpu :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .jcxz addr32 d =>
      let c := if addr32 then Value.trunc .d (s.regs.get .rcx) else s.regs.get .rcx
      -- the BUG: the sense of the test
      if c != 0 then s.setRipChecked (nr + d) else s.setRip nr
  | _ => step i s

/-- ⭐ THE HARD HALF, AND THE ONE THE ADDRESS-SIZE PREFIX EXISTS FOR.  This model
implements `jecxz` by reading ALL 64 BITS of RCX — that is, it writes the
instruction ONCE and lets `jrcxz`'s width stand for both, which is the obvious
way to get this pair wrong and the way a reviewer is least likely to see.

The two agree on every state except one shape: RCX non-zero with its low 32 bits
zero.

⛔ AND THE FIRST VERSION OF THIS COMMENT NAMED `0x1_00000000` AS THE VALUE THAT
REACHES IT, WHICH WAS TOO SPECIFIC AND WAS REFUTED THE SAME WAY BATCH 2's CLAIM
WAS.  Deleting that constant from `adversarial` left this arm still catching the
bug — 3 disagreements instead of 6 — because `0x8000000000000000` is also
non-zero with a zero low half, and is also in the list. TWO constants reach the
point and either alone suffices.

⭐ SO THE THING TO SAY IS ABOUT THE GATE, NOT THE CONSTANT.  With BOTH removed
this arm catches ZERO — and `pre_states_separate_rcx_from_ecx` in
Tests/Coverage.lean FIRES.  That assertion was written before the probe, against
D13's and D14's law, and this is the first time in this repository that such an
assertion has caught a coverage loss PROSPECTIVELY rather than being written
after one was found. It does not care which constant supplies the point, which
is exactly why it is the right thing to have. -/
def wrongJecxzWidth (i : Instr) (s : Cpu) : Cpu :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .jcxz _ d =>
      -- the BUG, and only here: the address-size prefix is ignored
      if s.regs.get .rcx == 0 then s.setRipChecked (nr + d) else s.setRip nr
  | _ => step i s

/-- ⭐ P1 BATCH 6's PLANTED BUG, EASY HALF: a `setcc` that writes 1 and 0 the
wrong way round.  Any pre-state catches it. -/
def wrongSetccInverted (i : Instr) (s : Cpu) : Cpu :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .setcc c dst =>
      -- the BUG: the sense of the condition
      (s.writeOperand .b nr dst (if c.eval s.flags then 0 else 1)).setRip nr
  | _ => step i s

/-- ⭐ THE HARD HALF, AND THE REASON EVERY `cmov` VECTOR IS AT WIDTH `l`.  This
model implements CMOVcc the way the mnemonic reads — *if the condition holds,
move; otherwise do nothing* — which is correct at widths w and q and WRONG at
width d.

A 32-bit write zero-extends (SDM Vol. 1 §3.4.1.1), and CMOVcc writes its
destination unconditionally: only the VALUE is conditional.  So `cmovel %ecx,
%eax` with ZF clear moves nothing and still clears the upper half of RAX, and a
model that skipped the write leaves it intact.  The two differ only at width d,
and only when the destination's upper 32 bits are non-zero. -/
def wrongCmovSkipsWrite (i : Instr) (s : Cpu) : Cpu :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .cmov c sz dst src =>
      -- the BUG: no write at all on a false condition
      if c.eval s.flags then ((s.setReg sz dst (s.readOperand sz nr src)).setRip nr)
      else s.setRip nr
  | _ => step i s

/-- ⭐ P1 BATCH 7's PLANTED BUG, EASY HALF: a SAR that brings in ZEROS — i.e.
`sar` implemented as `shr`, which is what happens when the arithmetic shift is
written as the logical one.  Any negative operand catches it. -/
def wrongSarLogical (i : Instr) (s : Cpu) : Cpu :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .shift .sar sz dst amt =>
      let cnt : BitVec 8 := match amt with
        | .imm8 v => v
        | .cl => (s.getReg .b .rcx).setWidth 8
      let n := Flags.shiftCount sz cnt
      let a := s.readOperand sz nr dst
      -- the BUG: a logical shift where an arithmetic one belongs
      let res := (Value.trunc sz a) >>> n
      if n = 0 then (s.writeOperand sz nr dst res).setRip nr
      else
        let (cfU, s) := s.undefBit
        let (ofU, s) := s.undefBit
        let (afU, s) := s.undefBit
        let s := s.setFlags (Flags.shiftFlags .sar sz a res n cfU ofU afU s.flags)
        (s.writeOperand sz nr dst res).setRip nr
  | _ => step i s

/-- ⭐ THE HARD HALF, AND IT IS A MISREADING OF THE SDM RATHER THAN A TYPO.  This
model gives SAR the CF rule that SHL and SHR have — *undefined when the count is
at or above the operand width*, so it DRAWS AN ORACLE BIT there — which is what
a reader who saw one sentence about three mnemonics would write.

The SDM's undefined clause names only "SHL and SHR instructions"; SAR has no
such clause, because shifting right past the width still has an answer and it is
the sign.  The two models therefore agree everywhere except at a count ≥ the
width, which in this vector table is `sar_b9` and nothing else, and only when
the operand is negative.  `sar_covered_at_count_ge_width` is the assertion that
keeps such a vector present. -/
def wrongSarCfUndefinedAtLargeCount (i : Instr) (s : Cpu) : Cpu :=
  let out := step i s
  match i.op with
  | .shift .sar sz dst amt =>
      let cnt : BitVec 8 := match amt with
        | .imm8 v => v
        | .cl => (s.getReg .b .rcx).setWidth 8
      let n := Flags.shiftCount sz cnt
      if n = 0 || n < sz.bits then out
      else
        -- the BUG, and only here: SHL/SHR's undefined rule applied to SAR
        { out with flags := { out.flags with cf := s.oracle.bits s.oracle.cursor } }
  | _ => step i s

/-- ⭐ P1 BATCH 8's PLANTED BUG, EASY HALF: a `rol` that rotates RIGHT.  Any
non-symmetric operand catches it. -/
def wrongRolDirection (i : Instr) (s : Cpu) : Cpu :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .rot .rol sz dst amt =>
      let cnt : BitVec 8 := match amt with
        | .imm8 v => v
        | .cl => (s.getReg .b .rcx).setWidth 8
      let n := Flags.rotMasked sz cnt
      let t := Flags.rotReduced .rol sz n
      let a := s.readOperand sz nr dst
      -- the BUG: the other direction
      let res := Flags.rotResult .ror sz a s.flags.cf t
      if n = 0 then (s.writeOperand sz nr dst res).setRip nr
      else
        let (ofU, s) := s.undefBit
        let s := s.setFlags (Flags.rotFlags .rol sz a res n t ofU s.flags)
        (s.writeOperand sz nr dst res).setRip nr
  | _ => step i s

/-- ⭐ THE HARD HALF, AND IT IS THE MOST NATURAL WAY TO WRITE THIS INSTRUCTION
WRONG.  This model asks "did the data move?" — the REDUCED count — where the SDM
asks "was the count non-zero?" — the MASKED one.  So it skips `rol`'s and
`ror`'s CF write whenever the masked count is a non-zero multiple of the width.

Everywhere else the two counts are both zero or both non-zero and the models are
identical.  `rol_b8` is the one vector in this table where they differ, and
`rotates_reach_a_full_turn` in Tests/Coverage.lean is what keeps such a case
present. -/
def wrongRotCfKeyedOnReducedCount (i : Instr) (s : Cpu) : Cpu :=
  let out := step i s
  match i.op with
  | .rot k sz _ amt =>
      let cnt : BitVec 8 := match amt with
        | .imm8 v => v
        | .cl => (s.getReg .b .rcx).setWidth 8
      let n := Flags.rotMasked sz cnt
      let t := Flags.rotReduced k sz n
      match k with
      | .rol | .ror =>
          -- the BUG: CF left alone when the data did not move, though n ≠ 0
          if n ≠ 0 && t = 0 then { out with flags := { out.flags with cf := s.flags.cf } }
          else out
      | _ => out
  | _ => step i s

/-- ⭐ P1 BATCH 9's PLANTED BUG, EASY HALF: a `bts` that sets the bit ABOVE the
one it tested.  CF is right and the destination is wrong. -/
def wrongBtsOffByOne (i : Instr) (s : Cpu) : Cpu :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .bit .bts sz dst off =>
      let a := s.readOperand sz nr dst
      let n := (s.readOperand sz nr off).toNat % sz.bits
      let bit := a.getLsbD n
      -- the BUG: n + 1
      let res := Value.trunc sz (a ||| (BitVec.ofNat 64 1 <<< (n + 1)))
      let (pfU, s) := s.undefBit
      let (afU, s) := s.undefBit
      let (sfU, s) := s.undefBit
      let (ofU, s) := s.undefBit
      let s := s.setFlags { s.flags with
        cf := bit, pf := pfU, af := afU, sf := sfU, of := ofU }
      (s.writeOperand sz nr dst res).setRip nr
  | _ => step i s

/-- ⭐ THE HARD HALF, AND IT IS THE ONE FLAG THE HARNESS CAN STILL SEE.

The bit-test group leaves ZF ALONE (SDM Vol. 2A: "the ZF flag is unaffected")
and leaves OF, SF, AF and PF UNDEFINED.  A model that recomputed ZF from the
result — which is what every other read-modify-write in this model does, so it
is the natural thing to write — differs from the correct one only in ZF.

⚠️ AND THAT IS EXACTLY WHY THIS ARM IS SHARP RATHER THAN LUCKY.  A disagreement
in PF, AF, SF or OF would be classified EXPLAINED, because those flags are in
the undefined set for these forms and the comparator absorbs them by design.
ZF is the only flag of the six whose disagreement can be unexplained here, so
this bug is visible through a very narrow window — and a model that got several
of these flags wrong at once would still be caught only by the ZF one. -/
def wrongBitRecomputesZf (i : Instr) (s : Cpu) : Cpu :=
  let out := step i s
  match i.op with
  | .bit _ sz dst _ =>
      -- the BUG: ZF from the post-state destination, as an ALU op would
      { out with flags := { out.flags with
          zf := (out.readOperand sz (s.rip + BitVec.ofNat 64 i.len) dst) == 0 } }
  | _ => step i s

/-- ⭐ P1 BATCH 10's PLANTED BUG, EASY HALF: a `movsx` that ZERO-extends — that
is, `movsx` implemented as `movzx`, which is what happens when the two are
written from one template and the extension is the parameter someone forgot to
thread.  Any pre-state whose source has its sign bit set catches it, which is
most of the adversarial list.

The two extensions agree exactly when the source is non-negative, so this arm is
also what says `movx_reaches_a_negative_source` in Tests/Coverage.lean is about
something real: without a negative source in the pre-states, `movsx` and `movzx`
are the same function under test and this bug is invisible. -/
def wrongMovsxZeroExtends (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .movx .sign dsz ssz dst src =>
      let nr := s.rip + BitVec.ofNat 64 i.len
      let v := s.readOperand ssz nr src
      -- the BUG: zero where the sign belongs
      ((s.setReg dsz dst (Value.zext ssz v)).setRip nr)
  | _ => step i s

/-- ⭐ P1 BATCH 10's SECOND EASY HALF: an `xchg` that COPIES instead of swapping
— it writes the second operand into the first and leaves the second alone.  This
is what a half-written swap looks like, and no other form in this repository
could catch it because no other form writes two destinations.

Surgical in the sense P0's `wrongShiftMask` had to be taught: the first write is
exactly the correct one, at the correct width, so the only difference is the
write that is missing. -/
def wrongXchgCopies (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .xchg sz a b =>
      if a.isMem || b.isMem || a.isImm || b.isImm then step i s
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let vb := s.readOperand sz nr b
        -- the BUG: the second write never happens
        ((s.writeOperand sz nr a vb).setRip nr)
  | _ => step i s

/-- ⭐ THE HARD HALF, AND THE ONE THE NEW PRE-STATE EXISTS FOR.  This model gives
the `99` trio — `cwtd`/`cltd`/`cqto` — ONE write rule: merge the computed value
into the register the way a 16-bit write does.  That is correct for `cwtd`
(whose write really is 16 bits) and correct for `cqto` (where the merge mask is
empty), and WRONG for `cltd`, whose write is 32 bits and therefore CLEARS RDX's
upper half (SDM Vol. 1 §3.4.1.1).

⚠️ It is the same shape as batch 7's SAR bug: one rule read off one sentence and
applied to three mnemonics, right for two of them.  And it is invisible unless
RDX starts with something in its upper half — which it never did before this
batch, in any of the seventy-four pre-states.  `mkPre` now gives RDX the
complement of RAX; deleting that line makes this arm catch ZERO and makes
`pre_states_give_rdx_a_nonzero_upper_half` fail. -/
def wrongCdqMerges (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .cext k =>
      let nr := s.rip + BitVec.ofNat 64 i.len
      let a := s.regs.get .rax
      let merge (sz : Size) (v : Val) : Cpu :=
        -- the BUG: the 16-bit merge rule, applied at every width of the trio
        let old := s.regs.get .rdx
        let nv := (old &&& ~~~sz.mask) ||| Value.trunc sz v
        { s with regs := s.regs.set .rdx nv }
      match k with
      | .cwd => ((merge .w (if Value.msb .w a then Size.mask .w else 0)).setRip nr)
      | .cdq => ((merge .d (if Value.msb .d a then Size.mask .d else 0)).setRip nr)
      | .cqo => ((merge .q (if Value.msb .q a then Size.mask .q else 0)).setRip nr)
      | _ => step i s
  | _ => step i s

/-- ⭐ THE SECOND HARD HALF, AND THE ONE THE `bw` VECTORS EXIST FOR.  This model
applies the destination width to the VALUE and not to the WRITE: it truncates
the extension to `dsz` and then writes all sixty-four bits.

At `.d` that is exactly right, because a 32-bit write zero-extends and this
zero-fills.  At `.q` it is right because the write is the whole register.  At
`.w` it is WRONG, because a 16-bit write PRESERVES what is above it and this
clears it — and `movzbw`/`movsbw` are the only two vectors in the table with a
16-bit destination.  Two rows of thirty-three, and without them a whole rule of
the SDM's three-way write asymmetry goes untested. -/
def wrongMovxFullWidthWrite (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .movx k dsz ssz dst src =>
      let nr := s.rip + BitVec.ofNat 64 i.len
      let v := s.readOperand ssz nr src
      let e := match k with
        | .zero => Value.zext ssz v
        | .sign => Value.sext ssz v
      -- the BUG: the width bounds the VALUE and not the WRITE
      ({ s with regs := s.regs.set dst (Value.trunc dsz e) }).setRip nr
  | _ => step i s

/-- ⭐ P1 BATCH 11's PLANTED BUG, EASY HALF: a `loop` that tests the counter
BEFORE decrementing it rather than after.  This is the reading the mnemonic
invites — "loop while the counter is non-zero" — and it is wrong at exactly two
counter values: 1, which must fall through after decrementing to zero, and 0,
which must branch after wrapping to all-ones.  Everywhere else the two readings
agree, which is why it needs those two values in the pre-state set and gets them
from `adversarial`.

The counter write-back is left CORRECT, so the only difference is the test. -/
def wrongLoopTestsOldCounter (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .loop k addr32 d =>
      let nr := s.rip + BitVec.ofNat 64 i.len
      let sz : Size := if addr32 then .d else .q
      let zf := s.flags.zf
      let cnt := s.getReg sz .rcx
      let cnt' := Value.trunc sz (cnt - 1)
      let s := s.setReg sz .rcx cnt'
      -- the BUG: the test reads the counter as it was BEFORE the decrement
      let taken :=
        match k with
        | .loop   => cnt != 0
        | .loope  => cnt != 0 && zf
        | .loopne => cnt != 0 && !zf
      if taken then s.setRipChecked (nr + d) else s.setRip nr
  | _ => step i s

/-- ⭐ THE HARD HALF, AND THE ONE THE CONDITIONAL LOOPS EXIST FOR.  This model
decrements and writes the counter back ONLY when it branches — "if the condition
holds, decrement and jump" — which is how the instruction reads if you take the
branch to be the instruction and the counter to be its bookkeeping.

⚠️ WHAT MAKES IT HARD IS WHICH VECTOR CATCHES IT.  Plain `loop` falls through at
exactly ONE counter value (1), so a table of `loop` alone would rest the whole
bug on whether `adversarial` happens to contain 1.  `loope`/`loopne` fall
through whenever ZF has the wrong polarity — half the pre-states — so the bug is
caught broadly, but only because the conditional predicates are in the table.
⇒ A form's coverage can depend on a SIBLING form's presence rather than on its
own vectors. -/
def wrongLoopNoWritebackOnFallthrough (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .loop k addr32 d =>
      let nr := s.rip + BitVec.ofNat 64 i.len
      let sz : Size := if addr32 then .d else .q
      let zf := s.flags.zf
      let cnt := s.getReg sz .rcx
      let cnt' := Value.trunc sz (cnt - 1)
      let taken :=
        match k with
        | .loop   => cnt' != 0
        | .loope  => cnt' != 0 && zf
        | .loopne => cnt' != 0 && !zf
      -- the BUG: the counter is written back only on the taken path
      if taken then (s.setReg sz .rcx cnt').setRipChecked (nr + d) else s.setRip nr
  | _ => step i s

/-- ⭐ THE SECOND HARD HALF, AND THE ONE `loopCounterStates` EXISTS FOR.  This
model writes the counter back at the RIGHT width — 32 bits under `addr32`,
zero-extending — and TESTS the full 64-bit RCX.  Splitting the width across the
read/write and the test is the natural slip when a single `addr32` flag has to
reach three places.

⚠️ It is invisible unless the low 32 bits of RCX are 1 while the upper half is
not zero, which is the ONLY state where `ECX - 1` is zero and `RCX - 1` is not.
Not one of the seventy-four pre-states was such a state; `loopCounterStates` is.
Deleting it makes this arm catch ZERO and makes
`pre_states_reach_ecx_one_over_a_nonzero_upper_half` fail. -/
def wrongLoopAddr32TestsFullWidth (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .loop k addr32 d =>
      let nr := s.rip + BitVec.ofNat 64 i.len
      let sz : Size := if addr32 then .d else .q
      let zf := s.flags.zf
      let cnt := s.getReg sz .rcx
      let cnt' := Value.trunc sz (cnt - 1)
      let s' := s.setReg sz .rcx cnt'
      -- the BUG: the TEST always reads the full register, whatever the prefix said
      let test := s.regs.get .rcx - 1
      let taken :=
        match k with
        | .loop   => test != 0
        | .loope  => test != 0 && zf
        | .loopne => test != 0 && !zf
      if taken then s'.setRipChecked (nr + d) else s'.setRip nr
  | _ => step i s

/-- ⭐ P1 BATCH 11's SECOND EASY HALF, AND THE ONE THAT WAS NOT CATCHABLE AT ALL
UNTIL THIS BATCH TOUCHED THE PRE-STATES.  This model implements `cld` as a
no-op — which is what an unwritten case in a five-way `match` amounts to.

⛔ AGAINST THE PRE-STATE SET AS IT STOOD, THIS BUG IS INVISIBLE.  DF was `false`
in all seventy-four states and nothing could write it, so "clear DF" and "do
nothing" are the same function and the comparator — which has diffed `df` since
P0 — would have reported agreement.  `dfStates` is what makes the arm catch;
deleting it makes it catch ZERO and makes `pre_states_set_df` fail. -/
def wrongCldIsNoOp (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .flagop .cld =>
      -- the BUG: the flag is never written
      s.setRip (s.rip + BitVec.ofNat 64 i.len)
  | _ => step i s

/-! ### P1 BATCH 12's four arms -/

/-- ⭐ THE HARD HALF OF THE NOP PAIR: every `nop` advances RIP by ONE.

That is what a model written against the bare `0x90` looks like when the
multi-byte `0F 1F /0` forms arrive — the semantics are genuinely "do nothing", so
the length is the ONLY thing left to get wrong, and a `step` that ignored
`i.len` would be right on the one-byte form and wrong on the other four.  It is
caught only by the multi-byte vectors, which is what says they are not
redundant spellings of `nop`. -/
def wrongNopFixedLength (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .nop _ => s.setRip (s.rip + 1)
  | _ => step i s

/-- The easy half: `ud2` treated as a no-op rather than a fault.  Caught by
`refused` in every state — which is the point of an easy half, and of `ud2`
being in the table at all: a form whose entire content is that it REFUSES is the
only kind of vector that tests the refusal channel itself. -/
def wrongUd2Executes (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .ud2 => s.setRip (s.rip + BitVec.ofNat 64 i.len)
  | _ => step i s

/-- ⭐⭐ THE HARD HALF OF THE BATCH, AND THE ARM THAT PRICES `frameStates`.

This `retq` jumps to the return address WITHOUT POPPING IT — RSP is left where it
was.  ⛔ Against the seventy-eight pre-states that existed before this batch the
bug is INVISIBLE, and not because the states are weak: the stack window's
background pattern makes the eight bytes at RSP read as `0x3736353433323130`,
which is not canonical, so `retq` REFUSES in every one of them and never reaches
the line the bug is on.  Only the two `frameStates` put a returnable address on
the stack.  Deleting them makes this arm catch ZERO.

It is D27's shape a third time — after a constant FLAG and an unreached
COMBINATION, a constant WINDOW CONTENT — and the first time the batch that would
have been fooled looked for it in advance. -/
def wrongRetNoPop (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .ret =>
      let tgt := s.readMem .q (s.regs.get .rsp)
      if canonical tgt then { s with rip := tgt }   -- the BUG: RSP never moves
      else s.halt (.unimplemented "non-canonical return address (#GP(0) in hardware)")
  | _ => step i s

/-- `leaveq` with its two steps in the wrong order: the pop happens first, from
the OLD RSP, and only then is RSP set from RBP.  This is the single most likely
way to write LEAVE wrongly, because "set RSP to RBP, then POP RBP" reads as two
independent assignments and it is only the ORDER that makes the pop read the
frame rather than the caller's stack. -/
def wrongLeaveWrongOrder (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .leave =>
      let (v, s') := s.popValue .q
      ((s'.setReg .q .rsp (s.regs.get .rbp)).setReg .q .rbp v).setRip
        (s.rip + BitVec.ofNat 64 i.len)
  | _ => step i s

/-! ### P1 BATCH 13 — the flagless shifts and the byte-swapping move

Three arms.  The first is the DEFINING property of `sarx`/`shlx`/`shrx` — they
compute a shift and write no flag — and it is the arm that would be missing if
the batch had been priced as "the shifts again with a different encoding".

⚠️ THE OTHER TWO ARE BOTH ABOUT WIDTH, because that is where `movbe` can be
wrong while looking right: a model that byte-reverses 64 bits and truncates is
CORRECT at `.q`, and a store that writes the wrong number of bytes is invisible
unless the margin around it is watched. -/

/-- `shlx`/`shrx`/`sarx` writing the flags an ordinary shift writes — the exact
bug a model gets by routing the new mnemonics through the old `.shift` case.
"Flags Affected: None" (SDM Vol. 2A, SARX/SHLX/SHRX). -/
def wrongShiftxWritesFlags (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .shiftx k sz dst src cnt =>
      match sz with
      | .d | .q =>
          let n := Flags.shiftCount sz ((s.getReg .b cnt).setWidth 8)
          let a := s.readOperand sz (s.rip + BitVec.ofNat 64 i.len) src
          let res : Val :=
            match k with
            | .shl => Value.trunc sz (a <<< n)
            | .shr => (Value.trunc sz a) >>> n
            | .sar => Value.sar sz a n
          if n = 0 then (s.setReg sz dst res).setRip (s.rip + BitVec.ofNat 64 i.len)
          else
            let (cfU, s) := s.undefBit
            let (ofU, s) := s.undefBit
            let (afU, s) := s.undefBit
            let s := s.setFlags (Flags.shiftFlags k sz a res n cfU ofU afU s.flags)
            (s.setReg sz dst res).setRip (s.rip + BitVec.ofNat 64 i.len)
      | _ => step i s
  | _ => step i s

/-- ⭐ `movbe` REVERSING AT 64 BITS AND TRUNCATING AFTERWARDS — the model that is
RIGHT AT `.q` and wrong at `.w` and `.d`.  It is the most likely wrong `movbe`
because `Value.bswap` reads as a whole-register operation and the width looks
like a detail of the write rather than of the reversal. -/
def wrongMovbeFullWidth (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .movbe sz dst src =>
      if !(dst.isMem != src.isMem) || dst.isImm || src.isImm then step i s
      else match sz with
      | .w | .d | .q =>
          let nr := s.rip + BitVec.ofNat 64 i.len
          let a := s.readOperand sz nr src
          (s.writeOperand sz nr dst (Value.byteRev 8 a)).setRip nr
      | .b => step i s
  | _ => step i s

/-- `movbe` moving the bytes without reversing them — a byte-swapping move that
forgot the swap, i.e. an ordinary `mov`.  Invisible on a palindrome and loud
everywhere else, which is what the sweeping data window provides. -/
def wrongMovbeNoReversal (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .movbe sz dst src =>
      if !(dst.isMem != src.isMem) || dst.isImm || src.isImm then step i s
      else match sz with
      | .w | .d | .q =>
          let nr := s.rip + BitVec.ofNat 64 i.len
          (s.writeOperand sz nr dst (s.readOperand sz nr src)).setRip nr
      | .b => step i s
  | _ => step i s

/-! ### P1 BATCH 14 — the bit-counting group

⭐ THERE IS NO ARM FOR THE UNDEFINED DESTINATION, AND THAT IS CORRECT.  A model
that writes a different value into `bsf`'s destination at a zero source is not
WRONG — the SDM leaves it undefined, `classify` files the disagreement as
`undefined-region`, and `driveWrong` excludes that class from its hits by
design.  The undefined destination is held up by `Tests/Nonvacuity.lean` (two
oracles must differ there, and must AGREE at a non-zero source) and by
`X86.undefinedLeaked`, which requires the DERIVED undefined registers to equal
the AST-level DECLARATION on every case.  Probing a claim in the place that can
actually see it is the point; an arm here would have been a probe that could
only ever report a pass. -/

/-- ⭐⭐ BSR REPORTING THE COUNT OF LEADING ZEROS INSTEAD OF THE INDEX OF THE
TOP SET BIT — the confusion the encoding invites, because `lzcnt` IS `bsr` with
an F3 prefix and a CPU without the feature runs one as the other.  The two sum
to the width minus one, so they agree only where that sum is symmetric and
differ on almost every source; batch 13's ACL2 probe measured the witness
(`0x123456789ABCDEF0`: `lzcnt` 3, `bsr` 60). -/
def wrongBsrIsLzcnt (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .bitcnt .bsr sz dst src =>
      if !(bitcntEncodable .bsr sz) then step i s
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let a := s.readOperand sz nr src
        let (cfU, s) := s.undefBit
        let (pfU, s) := s.undefBit
        let (afU, s) := s.undefBit
        let (sfU, s) := s.undefBit
        let (ofU, s) := s.undefBit
        let s := s.setFlags (Flags.bitScan sz a cfU pfU afU sfU ofU s.flags)
        if Value.isZero sz a then
          let (u, s) := s.undefVal sz.bits
          (s.setReg sz dst u).setRip nr
        else
          -- the BUG, and only here
          (s.setReg sz dst (BitVec.ofNat 64 (Value.clz sz a))).setRip nr
  | _ => step i s

/-- ⭐ LZCNT SETTING ZF FROM THE SOURCE — `bsf`/`bsr`'s rule, applied to the
instruction one prefix byte away.  "ZF ← (DEST = 0)" and "ZF ← (SRC = 0)" have
the same answer for every source EXCEPT those whose top bit is set, where the
count is zero and the source is not.  `adversarial` is full of them. -/
def wrongLzcntZfFromSource (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .bitcnt .lzcnt sz dst src =>
      if !(bitcntEncodable .lzcnt sz) then step i s
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let a := s.readOperand sz nr src
        let res : Val := BitVec.ofNat 64 (Value.clz sz a)
        let (pfU, s) := s.undefBit
        let (afU, s) := s.undefBit
        let (sfU, s) := s.undefBit
        let (ofU, s) := s.undefBit
        ((s.setFlags { Flags.bitCount sz a res pfU afU sfU ofU s.flags with
            zf := Value.isZero sz a }).setReg sz dst res).setRip nr
  | _ => step i s

/-- BLSI's CF the usual way up — set when the source IS zero.  The SDM has it
the other way (`IF SRC = 0 THEN CF ← 0 ELSE CF ← 1`), which makes `blsi` the one
instruction in this batch whose CF disagrees with `lzcnt`/`tzcnt`'s on every
state rather than on some of them. -/
def wrongBlsiCfSense (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .bitcnt .blsi sz dst src =>
      if !(bitcntEncodable .blsi sz) then step i s
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let a := s.readOperand sz nr src
        let res := Value.blsi sz a
        let (pfU, s) := s.undefBit
        let (afU, s) := s.undefBit
        ((s.setFlags { Flags.blsi sz a res pfU afU s.flags with
            zf := Value.isZero sz res, cf := Value.isZero sz a }).setReg sz dst res).setRip nr
  | _ => step i s

/-- ⚠️ POPCNT COUNTING THE WHOLE REGISTER RATHER THAN THE OPERAND.  Correct at
`.q` and wrong at `.w` and `.d` whenever the bits above the operand are set —
the same shape as `wrongMovbeFullWidth` in batch 13, and the reason the narrow
widths are in the vector table at all. -/
def wrongPopcntFullWidthSource (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .bitcnt .popcnt sz dst src =>
      if !(bitcntEncodable .popcnt sz) then step i s
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let a := s.readOperand sz nr src
        let full := match src with
          | .reg r _ => s.regs.get r
          | _ => s.readOperand .q nr src
        let res : Val := BitVec.ofNat 64 (Value.popCount .q full)
        ((s.setFlags (Flags.popcnt sz a s.flags)).setReg sz dst res).setRip nr
  | _ => step i s

/-! ## Main -/

def writeLines (path : String) (ls : List String) : IO Unit :=
  IO.FS.writeFile path (String.intercalate "\n" ls ++ "\n")

def readLines (path : String) : IO (List String) := do
  let s ← IO.FS.readFile path
  return (s.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)

/-! ### ⭐⭐ P1 BATCH 14 — THE `undefined` COLUMN, GATED AT LAST

⛔ UNTIL THIS BATCH THE COLUMN WAS CHECKED ONLY AGAINST THE TIER.
`frame_tier_iff_undefined_bits` says a row is `T-frame` exactly when its
`undefined` list is non-empty — so a row naming the WRONG flags, or four of the
five it should, read exactly like a correct one.  It is the published statement
of where this model declines to commit, it is what a reader checks a proof's
strength against, and nothing compared it to the model.

⇒ **A COLUMN NO GATE READS IS WRONG WHEREVER NOBODY LOOKED.**  This is the same
defect as D15 (a shapes column asserting coverage nothing checked) in the column
next to it, found while adding the first row whose undefined region is not a
flag.

⚠️ THE COMPARISON IS ON TOKENS, NOT ON THE STRINGS.  Existing rows write real
conditions — `CF (count ≥ width)`, `OF (count ≠ 1)` — and those conditions are
worth keeping in the published table.  So the gate extracts the flag NAMES a row
mentions and compares that SET against the set the model actually draws, over
every emitted case.  It does not police the prose; it polices the claim inside
it.  A row could still carry a wrong CONDITION, which is named here as the
limit of this gate rather than left for a reader to discover. -/

/-- The flag (and `DEST`) tokens a coverage row's `undefined` column mentions. -/
def undefinedColumnTokens (r : Row) : List String :=
  ["CF", "PF", "AF", "ZF", "SF", "OF", "DEST"].filter
    (fun t => r.undefined.any (fun e => (e.splitOn t).length > 1))

/-- The tokens the MODEL actually draws, per mnemonic, over every vector and
pre-state.  A register in the undefined set is reported as `DEST`: the only
register any form declares undefined is its own destination, which
`X86.undefinedLeaked` enforces case by case. -/
def measuredUndefinedTokens (n : Nat) : List (String × List String) := Id.run do
  let mut acc : List (String × List String) := []
  for v in vectors do
    for pre in preStates 0x9E3779B97F4A7C15 n do
      let fs := (undefinedFlags v.instr pre).map String.toUpper
      let rs := if (undefinedRegs v.instr pre).isEmpty then [] else ["DEST"]
      let cur := (acc.lookup v.mnemonic).getD []
      acc := acc.filter (fun kv => kv.1 != v.mnemonic)
             ++ [(v.mnemonic, (cur ++ fs ++ rs).eraseDups)]
  return acc

/-- ⭐ AND IT IS CHECKED IN BOTH DIRECTIONS.  A row naming a flag the model never
draws OVER-claims — it advertises a weaker model than the one shipped.  A row
missing a flag the model does draw UNDER-claims, which is worse: a reader takes
a bit for committed that the oracle chooses. -/
def checkUndefinedColumn (n : Nat) : IO Bool := do
  let measured := measuredUndefinedTokens n
  let mut ok := true
  for r in tableP0 do
    let claimed := undefinedColumnTokens r
    let got := (measured.lookup r.mnemonic).getD []
    let over := claimed.filter (fun t => !got.contains t)
    let under := got.filter (fun t => !claimed.contains t)
    if !over.isEmpty || !under.isEmpty then
      ok := false
      IO.println s!"  ⛔ {r.mnemonic}: column says {claimed}, model draws {got} \
(over-claims {over}, under-claims {under})"
  if ok then
    IO.println s!"  ✔ undefined column: all {tableP0.length} rows match what the model draws"
  return ok

/-- Run one wrong model against the correct one and REQUIRE a catch. -/
def driveWrong (name : String) (wrong : Instr → Cpu → Cpu) (expectField : String) :
    IO Bool := do
  let good := parseRecords (emitAll step 4)
  let bad := parseRecords (emitAll wrong 4)
  let r := compareRecs [] good bad
  -- ⭐ D33: THE FILTER USED TO READ `d.cls == "spec"`, AND THAT MADE ONE CHANNEL
  -- OF THE COMPARATOR UNTESTABLE BY CONSTRUCTION.  `classify` gives a
  -- disagreement in `refused` the class **"refusal"**, not "spec" — so an arm
  -- whose bug shows in the refusal channel could never register a hit, however
  -- loudly the comparator caught it.  `ud2` is the first form whose whole
  -- content is that it refuses, and its arm is what walked into it: the
  -- comparator found all seventy-six disagreements and the SELFTEST reported
  -- "fires on the wrong thing".
  --
  -- ⛔ The gap survived because nothing had asked.  Thirty arms, none of them on
  -- `refused` — the same shape as DF (D27), one level up: not a constant in the
  -- STATE this time but an unexercised branch in the INSTRUMENT.  `bothRefused`
  -- was written for this channel and the selftest could not plant a bug in it.
  --
  -- What is excluded is exact rather than convenient: `undefined-region` is an
  -- EXPLAINED disagreement and must never count as catching a bug, and
  -- `harness` means a field went missing from a record, which is an instrument
  -- failure rather than a caught model bug.  Everything else — `spec` and
  -- `refusal` — is the comparator doing its job.
  let hits := r.details.filter
    (fun d => d.field == expectField && d.cls != "undefined-region" && d.cls != "harness")
  -- ⭐ FLUSHED AFTER EVERY ARM, and the reason is a three-hour silence.
  --
  -- This binary's stdout is BLOCK-BUFFERED when it is not a tty, so the full
  -- 73-arm selftest — 3 h 44 m at the P1 seal — wrote NOTHING until it exited.
  -- A watcher could see the process was alive (CPU advancing) but not where it
  -- was, so a stuck run and a slow one looked identical from outside, which is
  -- the defect bench reported on the fleet bus at 13:41 (*"a watch built on
  -- END-OF-UNIT events cannot tell a long unit from a dead one"*) arriving in
  -- this repository's own longest-running gate.
  -- ⇒ 🔑 LIVENESS IS NOT PROGRESS.  One flush per arm turns a three-hour
  -- silence into 73 events, and costs one syscall against ~161 seconds of work.
  let say (msg : String) : IO Unit := do
    IO.println msg
    (← IO.getStdout).flush
  if r.unexplained == 0 then
    say s!"  ⛔ {name}: comparator reported ZERO unexplained disagreements against a \
KNOWN-WRONG model. The comparator does not work."
    return false
  else if hits.isEmpty then
    say s!"  ⛔ {name}: {r.unexplained} unexplained disagreements, but NONE in the \
field the bug is in ({expectField}). The comparator fires on the wrong thing."
    return false
  else
    say s!"  ✔ {name}: caught — {hits.length} disagreement(s) in `{expectField}` \
(total unexplained {r.unexplained}, explained {r.explained})"
    return true

/-! ### P1 BATCH 15 — the string group's planted defects

Each of these is a mistake the group actually invites, and each is written so it
is RIGHT somewhere: an arm that is wrong on every case would be caught by any
vector and says nothing about the sweep. -/

/-- ⭐ DF IGNORED — the pointer always advances forward.  ⚠️ THIS IS CORRECT ON
78 OF THE 80 PRE-STATES: only `dfStates` sets DF, so this arm is a direct
measurement of whether batch 11's two DF states are still doing work.  Before
those states existed, this defect was invisible. -/
def wrongStringNoDF (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .strop k sz =>
      let d : BitVec 64 := BitVec.ofNat 64 sz.bytes   -- DF never consulted
      let nr := s.rip + BitVec.ofNat 64 i.len
      let si := s.regs.get .rsi
      let di := s.regs.get .rdi
      match k with
      | .movs =>
          let v := s.readMem sz si
          let s := s.writeMem sz di v
          (((s.setReg .q .rsi (si + d)).setReg .q .rdi (di + d))).setRip nr
      | .stos => ((s.writeMem sz di (s.getReg sz .rax)).setReg .q .rdi (di + d)).setRip nr
      | .lods => ((s.setReg sz .rax (s.readMem sz si)).setReg .q .rsi (si + d)).setRip nr
      | .cmps =>
          let s := s.setFlags (Flags.sub sz (s.readMem sz si) (s.readMem sz di) s.flags)
          (((s.setReg .q .rsi (si + d)).setReg .q .rdi (di + d))).setRip nr
      | .scas =>
          let s := s.setFlags (Flags.sub sz (s.getReg sz .rax) (s.readMem sz di) s.flags)
          (s.setReg .q .rdi (di + d)).setRip nr
  | _ => step i s

/-- ⭐ THE POINTER UPDATE ROUTED THROUGH THE OPERAND-WIDTH RULE.  `setReg sz`
instead of `setReg .q`, which is the natural mistake because every OTHER write
in this model goes through the width rule.  ⚠️ It is RIGHT at `.q` (a 64-bit
write) and RIGHT at `.d` (a 32-bit write zero-extends, and the pointers here are
below 2^32), and WRONG only at `.b` and `.w`, the two widths where `setReg`
MERGES — so it is caught by a quarter of the group's vectors and by no other. -/
def wrongStringPointerWidth (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .strop k sz =>
      let step' : BitVec 64 := BitVec.ofNat 64 sz.bytes
      let d : BitVec 64 := if s.flags.df then 0 - step' else step'
      let nr := s.rip + BitVec.ofNat 64 i.len
      let si := s.regs.get .rsi
      let di := s.regs.get .rdi
      match k with
      | .movs =>
          let v := s.readMem sz si
          let s := s.writeMem sz di v
          (((s.setReg sz .rsi (si + d)).setReg sz .rdi (di + d))).setRip nr
      | .stos => ((s.writeMem sz di (s.getReg sz .rax)).setReg sz .rdi (di + d)).setRip nr
      | .lods => ((s.setReg sz .rax (s.readMem sz si)).setReg sz .rsi (si + d)).setRip nr
      | .cmps =>
          let s := s.setFlags (Flags.sub sz (s.readMem sz si) (s.readMem sz di) s.flags)
          (((s.setReg sz .rsi (si + d)).setReg sz .rdi (di + d))).setRip nr
      | .scas =>
          let s := s.setFlags (Flags.sub sz (s.getReg sz .rax) (s.readMem sz di) s.flags)
          (s.setReg sz .rdi (di + d)).setRip nr
  | _ => step i s

/-- ⭐ THE COPY HAPPENS AT THE ALREADY-ADVANCED POINTERS.  ⚠️ Its REGISTER
results are identical to the correct model's — the pointers end in the same
place — so this arm can only ever be caught in the MEMORY window, which is why
it names one.  It is the arm that says the widened window is load-bearing: with
DF set it writes eight bytes BELOW `rdi`, at 0x2008, and before batch 15 that
address was still inside the old window but the SOURCE it reads with DF clear
(0x1ff0) and the address it writes forward (0x2018) were not both watched. -/
def wrongMovsPreIncrement (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .strop .movs sz =>
      let step' : BitVec 64 := BitVec.ofNat 64 sz.bytes
      let d : BitVec 64 := if s.flags.df then 0 - step' else step'
      let nr := s.rip + BitVec.ofNat 64 i.len
      let si := (s.regs.get .rsi) + d
      let di := (s.regs.get .rdi) + d
      let v := s.readMem sz si
      let s := s.writeMem sz di v
      (((s.setReg .q .rsi si).setReg .q .rdi di)).setRip nr
  | _ => step i s

/-- ⭐⭐ THE OPERAND-ORDER TRAP, WRITTEN OUT.  `[rdi] − [rsi]`, which is exactly
what AT&T prints (`cmpsq %es:(%rdi), (%rsi)`) and exactly the reverse of what
the instruction computes.  ⚠️ It agrees with the correct model whenever the two
operands are EQUAL, and this batch's pre-states make that reachable on purpose,
so the arm is not vacuously distinguished either. -/
def wrongCmpsOperandOrder (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .strop .cmps sz =>
      let step' : BitVec 64 := BitVec.ofNat 64 sz.bytes
      let d : BitVec 64 := if s.flags.df then 0 - step' else step'
      let nr := s.rip + BitVec.ofNat 64 i.len
      let si := s.regs.get .rsi
      let di := s.regs.get .rdi
      let s := s.setFlags (Flags.sub sz (s.readMem sz di) (s.readMem sz si) s.flags)
      (((s.setReg .q .rsi (si + d)).setReg .q .rdi (di + d))).setRip nr
  | _ => step i s

/-- ⭐ THE POINTER SWAP.  `scas` reads `[rsi]`, not `[rdi]` — the confusion the
whole group invites, since three of the five use RSI and two use RDI and the
names differ by one letter.  ⚠️ It still advances RDI correctly, so only the
FLAGS give it away. -/
def wrongScasUsesRsi (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .strop .scas sz =>
      let step' : BitVec 64 := BitVec.ofNat 64 sz.bytes
      let d : BitVec 64 := if s.flags.df then 0 - step' else step'
      let nr := s.rip + BitVec.ofNat 64 i.len
      let di := s.regs.get .rdi
      let s := s.setFlags
        (Flags.sub sz (s.getReg sz .rax) (s.readMem sz (s.regs.get .rsi)) s.flags)
      (s.setReg .q .rdi (di + d)).setRip nr
  | _ => step i s

/-- ⭐ `lods` MERGING AT 32 BITS.  The accumulator write is the one place in the
group where the ordinary width rule is WANTED, and this arm bypasses it in the
direction that looks harmless: it preserves RAX's upper half at `.d` instead of
clearing it (SDM Vol. 1 §3.4.1.1).  ⚠️ Correct at `.b`, `.w` and `.q`; wrong at
`.d` alone, and only when RAX's upper half is non-zero — which `adversarial`
supplies. -/
def wrongLodsNoZeroExtend (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .strop .lods sz =>
      let step' : BitVec 64 := BitVec.ofNat 64 sz.bytes
      let d : BitVec 64 := if s.flags.df then 0 - step' else step'
      let nr := s.rip + BitVec.ofNat 64 i.len
      let si := s.regs.get .rsi
      let v := s.readMem sz si
      let old := s.regs.get .rax
      let merged : Val := match sz with
        | .d => (old &&& 0xFFFFFFFF00000000) ||| (Value.trunc .d v)
        | _  => Value.writeView sz old v
      let s := s.setReg .q .rax merged
      (s.setReg .q .rsi (si + d)).setRip nr
  | _ => step i s

/-- ⭐⭐ P1 BATCH 16'S CENTRAL ARM: THE MODEL A CAREFUL READER WOULD WRITE.
Decrement RCX, notice it has reached zero, fall through — which is the SDM's
loop read as a single step, and it is wrong about x86isa.  ⚠️ IT IS RIGHT
EVERYWHERE EXCEPT RCX = 1: at RCX = 0 no iteration happens in either model, and
at RCX ≥ 2 the count does not reach zero.  One value of one register separates
it from the truth, `adversarial` contains that value, and the arm is caught. -/
def wrongRepAdvanceOnCountZero (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .repstrop r k sz =>
      if !repApplies r k then s.halt (.unimplemented "declined") else
      let nr := s.rip + BitVec.ofNat 64 i.len
      let cx := s.regs.get .rcx
      if cx == 0 then s.setRip nr
      else
        let s' := (stringIter k sz s).setReg .q .rcx (cx - 1)
        -- the extra disjunct is the whole defect
        s'.setRip (if r.terminates s'.flags.zf || cx - 1 == 0 then nr else s.rip)
  | _ => step i s

/-- The count consulted AFTER its own decrement, so a repeat with RCX = 1 does
nothing at all.  ⚠️ Distinct from the arm above: that one performs the right
work and stops too early, this one performs no work at RCX = 1. -/
def wrongRepDecrementFirst (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .repstrop r k sz =>
      if !repApplies r k then s.halt (.unimplemented "declined") else
      let nr := s.rip + BitVec.ofNat 64 i.len
      let cx := s.regs.get .rcx - 1
      if s.regs.get .rcx == 0 then s.setRip nr
      else if cx == 0 then (s.setReg .q .rcx cx).setRip nr
      else
        let s' := (stringIter k sz s).setReg .q .rcx cx
        s'.setRip (if r.terminates s'.flags.zf then nr else s.rip)
  | _ => step i s

/-- The count decremented through the OPERAND-width rule, exactly as batch 15's
POINTERS were in `wrongStringPointerWidth`.  ⚠️ The same defect in the one
register batch 15 did not write — and the same blind spot applies: it is
invisible unless RCX's decrement CARRIES across the operand width, which is why
`adversarial`'s `0x100000000` and `0x10` matter here. -/
def wrongRepCountWidth (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .repstrop r k sz =>
      if !repApplies r k then s.halt (.unimplemented "declined") else
      let nr := s.rip + BitVec.ofNat 64 i.len
      let cx := s.regs.get .rcx
      if cx == 0 then s.setRip nr
      else
        let s' := (stringIter k sz s).setReg sz .rcx (cx - 1)
        s'.setRip (if r.terminates s'.flags.zf then nr else s.rip)
  | _ => step i s

/-- The exit predicate reading the flags the instruction STARTED with.  A repeat
whose termination lags one iteration behind its own comparison. -/
def wrongRepZfIncoming (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .repstrop r k sz =>
      if !repApplies r k then s.halt (.unimplemented "declined") else
      let nr := s.rip + BitVec.ofNat 64 i.len
      let cx := s.regs.get .rcx
      if cx == 0 then s.setRip nr
      else
        let s' := (stringIter k sz s).setReg .q .rcx (cx - 1)
        s'.setRip (if r.terminates s.flags.zf then nr else s.rip)
  | _ => step i s

/-- The decrement applied on the RCX = 0 path too, so a zero count WRAPS to
all-ones.  ⚠️ The one arm here whose damage is invisible in RIP — both models
fall through — and visible only in RCX, which is why its watched field is
`rcx` and not `rip`. -/
def wrongRepDecrementAtZero (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .repstrop r k sz =>
      if !repApplies r k then s.halt (.unimplemented "declined") else
      let nr := s.rip + BitVec.ofNat 64 i.len
      let cx := s.regs.get .rcx
      if cx == 0 then (s.setReg .q .rcx (cx - 1)).setRip nr
      else
        let s' := (stringIter k sz s).setReg .q .rcx (cx - 1)
        s'.setRip (if r.terminates s'.flags.zf then nr else s.rip)
  | _ => step i s


/-! ### P1 BATCH 17 — the multiply-divide arms

⭐ SEVEN ARMS, AND THE SHAPE OF THE BATCH DICTATES THEM.  Measured before any of
this existed: `div` and `idiv` REFUSE in 51%–84% of the eighty-two pre-states.
A refusal is agreement that says nothing about the quotient, so this group's
danger is not a wrong answer — it is a model that is never asked.  Three of the
seven attack the fault predicate directly, one from each side and one from the
middle, and the rest attack the arithmetic that only runs when the fault does
not fire. -/

/-- ⭐ IMUL TAKING MUL's OVERFLOW RULE — the single most plausible wrong model in
this batch, and it is CORRECT on every non-negative product.  MUL sets CF when
the high half is non-zero; IMUL sets it when the full product differs from the
sign-extension of the low half.  `-1 * 1` at `.b` has high half `0xFF` and no
overflow, and this model claims one. -/
def wrongImulUsesMulOverflow (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .muldiv .imul sz src =>
      let nr := s.rip + BitVec.ofNat 64 i.len
      let a := s.readOperand sz nr src
      let lo := s.getReg sz .rax
      let (l, h) := Value.imulPair sz lo a
      let ovf := (Value.imulPair sz lo a).2 != 0
      let (sfU, s) := s.undefBit
      let (zfU, s) := s.undefBit
      let (afU, s) := s.undefBit
      let (pfU, s) := s.undefBit
      ((s.setFlags (Flags.mulFlags ovf sfU zfU afU pfU s.flags)).setMdPair sz l h).setRip nr
  | _ => step i s

/-- ⭐⭐ IDIV ROUNDING THE WRONG WAY — `Int`'s `/` and `%`, which in Lean are the
EUCLIDEAN pair, in place of `tdiv`/`tmod`.  The machine truncates toward zero;
this rounds toward negative infinity, so `-7 / 2` is `-4` here and `-3` on the
machine.  ⚠️ INVISIBLE ON EVERY NON-NEGATIVE DIVIDEND, which is most of
`adversarial` at `.b`, and invisible whenever the division is exact at any
width. -/
def wrongIdivFloorDivision (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .muldiv .idiv sz src =>
      let nr := s.rip + BitVec.ofNat 64 i.len
      let a := s.readOperand sz nr src
      let lo := s.getReg sz .rax
      let dv := Value.sval sz a
      if dv == 0 then s.halt (.byDesign "idiv: #DE") else
      let n := Value.dividendS sz (s.mdHi sz) lo
      let q := n / dv
      let lim : Int := 2 ^ (sz.bits - 1)
      if q < -lim || q > lim - 1 then s.halt (.byDesign "idiv: #DE") else
      let qv : Val := BitVec.ofNat 64 ((q % (2 ^ sz.bits : Int)).toNat)
      let rv : Val := BitVec.ofNat 64 (((n % dv) % (2 ^ sz.bits : Int)).toNat)
      let (cfU, s) := s.undefBit
      let (pfU, s) := s.undefBit
      let (afU, s) := s.undefBit
      let (zfU, s) := s.undefBit
      let (sfU, s) := s.undefBit
      let (ofU, s) := s.undefBit
      ((s.setFlags (Flags.divFlags cfU pfU afU zfU sfU ofU s.flags)).setMdPair
        sz qv rv).setRip nr
  | _ => step i s

/-- ⛔ DIV THAT FAULTS ONLY ON A ZERO DIVISOR, truncating an over-wide quotient
instead of refusing.  Half the fault predicate, deleted.  ⚠️ It is the half a
reader is likeliest to forget: "#DE if the source operand is 0" is the sentence
everybody knows, and "if the quotient is too large for the designated register"
is the one beside it. -/
def wrongDivNoQuotientOverflow (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .muldiv .div sz src =>
      let nr := s.rip + BitVec.ofNat 64 i.len
      let a := s.readOperand sz nr src
      let lo := s.getReg sz .rax
      let dv := Value.uval sz a
      if dv == 0 then s.halt (.byDesign "div: #DE") else
      let n := Value.dividendU sz (s.mdHi sz) lo
      let (cfU, s) := s.undefBit
      let (pfU, s) := s.undefBit
      let (afU, s) := s.undefBit
      let (zfU, s) := s.undefBit
      let (sfU, s) := s.undefBit
      let (ofU, s) := s.undefBit
      ((s.setFlags (Flags.divFlags cfU pfU afU zfU sfU ofU s.flags)).setMdPair
        sz (BitVec.ofNat 64 (n / dv)) (BitVec.ofNat 64 (n % dv))).setRip nr
  | _ => step i s

/-- ⭐⭐ THE ARM THAT PROVES THE QUOTIENT IS OBSERVED AT ALL: a `div` that
refuses on EVERY divisor.  It agrees with the oracle on the 51%–84% of
pre-states that genuinely fault and must be caught by the rest.

⚠️ WITHOUT THIS ARM THE BATCH WOULD HAVE NO EVIDENCE THAT THE NON-FAULTING PATH
IS TESTED.  A group whose forms mostly refuse is the mirror of batch 12's
`retq`, where the model was unobserved because every pre-state refused — and
there the refusal was the MODEL's, here it is the ORACLE's too, so the two agree
and the agreement means nothing. -/
def wrongDivAlwaysRefuses (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .muldiv .div _ _ => s.halt (.byDesign "div: #DE")
  | _ => step i s

/-- ⛔ THE BYTE MULTIPLY WRITING `DX:AX` INSTEAD OF `AH:AL`.  Correct at `.w`,
`.d` and `.q` — it is the same function there — and at `.b` it clobbers RDX and
leaves AH holding whatever it held.  ⚠️ This is the arm `Cpu.setMdPair` exists
to make hard: with the pair addressed inline at four call sites, the `.b`
special case is four chances to forget it. -/
def wrongMulBytePairInRdx (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .muldiv .mul sz src =>
      let nr := s.rip + BitVec.ofNat 64 i.len
      let a := s.readOperand sz nr src
      let lo := s.getReg sz .rax
      let (l, h) := Value.mulPair sz lo a
      let ovf := Value.mulOverflow sz lo a
      let (sfU, s) := s.undefBit
      let (zfU, s) := s.undefBit
      let (afU, s) := s.undefBit
      let (pfU, s) := s.undefBit
      (((s.setFlags (Flags.mulFlags ovf sfU zfU afU pfU s.flags)).setReg sz .rax l).setReg
        sz .rdx h).setRip nr
  | _ => step i s

/-- ⛔ IMUL's THREE-OPERAND FORM MULTIPLYING ITS DESTINATION.  `imul $7, %rcx,
%rax` is `rax := rcx * 7`; this model computes `rax := rax * 7` and ignores the
source entirely.  ⚠️ It agrees wherever RAX and the source happen to be equal —
which is the whole `diag` sweep, twenty of the eighty-two pre-states. -/
def wrongImul3ReadsDest (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .imulr sz dst src (some im) =>
      if !(imulrEncodable sz) then step i s else
      let nr := s.rip + BitVec.ofNat 64 i.len
      let _ := s.readOperand sz nr src
      let x := s.getReg sz dst
      let y := Value.trunc sz im
      let (l, _) := Value.imulPair sz x y
      let ovf := Value.imulOverflow sz x y
      let (sfU, s) := s.undefBit
      let (zfU, s) := s.undefBit
      let (afU, s) := s.undefBit
      let (pfU, s) := s.undefBit
      ((s.setFlags (Flags.mulFlags ovf sfU zfU afU pfU s.flags)).setReg sz dst l).setRip nr
  | _ => step i s

/-- ⛔ IDIV's REMAINDER TAKING THE DIVISOR's SIGN rather than the dividend's.
`Int.emod` in place of `Int.tmod` on the remainder ALONE — the quotient is left
correct, so this is the half of the rounding rule that `wrongIdivFloorDivision`
gets for free and this one gets on its own.  Invisible whenever the division is
exact, and whenever dividend and divisor share a sign. -/
def wrongIdivRemainderSign (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .muldiv .idiv sz src =>
      let nr := s.rip + BitVec.ofNat 64 i.len
      let a := s.readOperand sz nr src
      let lo := s.getReg sz .rax
      match Value.divPairS sz (s.mdHi sz) lo a with
      | none => s.halt (.byDesign "idiv: #DE")
      | some (q, _) =>
          let n := Value.dividendS sz (s.mdHi sz) lo
          let dv := Value.sval sz a
          let rv : Val := BitVec.ofNat 64 (((n % dv) % (2 ^ sz.bits : Int)).toNat)
          let (cfU, s) := s.undefBit
          let (pfU, s) := s.undefBit
          let (afU, s) := s.undefBit
          let (zfU, s) := s.undefBit
          let (sfU, s) := s.undefBit
          let (ofU, s) := s.undefBit
          ((s.setFlags (Flags.divFlags cfU pfU afU zfU sfU ofU s.flags)).setMdPair
            sz q rv).setRip nr
  | _ => step i s

/-! ### P1 BATCH 18 — the compare-exchange pair and the double shifts

⭐⭐ TWO OF THESE EIGHT ARMS ARE THE MODEL THIS BATCH ACTUALLY SHIPPED FIRST.
`wrongCmpxchgSdmWriteBack` and `wrongDshiftZeroCountWritesNothing` are the SDM
read literally — the first writes `DEST := TEMP` on the unequal branch, the
second performs the manual's "no operation" — and the differential run rejected
both, 80 disagreements and 51.  Planting them here turns two one-off findings
into a standing probe: if either rule is ever "corrected" back to what the
manual says, the selftest goes red instead of the differential going red two
hundred vectors later.  See docs/DECISIONS.md D53 and D54.

⭐ AND TWO OF THEM EXIST TO PRICE THE OBSERVATION, not to be plausible.
`cmpxchg`'s answer is a CHOICE, so an arm that always takes one branch agrees
with the model on every case of that branch — whatever catches it is exactly the
evidence that the OTHER branch is reached.  Both directions are here, because one
alone would leave half the instruction unmeasured while reporting agreement. -/

/-- ⭐ THE EQUAL BRANCH, ALWAYS — never writes the accumulator.  Correct on every
case where the values match, so what catches it measures the UNEQUAL branch. -/
def wrongCmpxchgAlwaysStores (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .cmpxchg sz dst src =>
      if dst.isImm then step i s
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let acc := s.getReg sz .rax
        let tmp := s.readOperand sz nr dst
        let s := s.setFlags (Flags.sub sz acc tmp s.flags)
        (s.writeOperand sz nr dst (s.getReg sz src)).setRip nr
  | _ => step i s

/-- ⭐ THE UNEQUAL BRANCH, ALWAYS — never stores the source.  Correct on every
case where the values differ, so what catches it measures the EQUAL branch, and
the pair of arms together says both are reached. -/
def wrongCmpxchgNeverStores (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .cmpxchg sz dst src =>
      if dst.isImm then step i s
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let acc := s.getReg sz .rax
        let tmp := s.readOperand sz nr dst
        let s := s.setFlags (Flags.sub sz acc tmp s.flags)
        ((s.setReg sz .rax tmp)).setRip nr
  | _ => step i s

/-- ⛔⛔ THE SDM, READ LITERALLY: `DEST := TEMP` on the unequal branch.  It looks
like a no-op and is not one at `.d`, where a 32-bit register write zero-extends —
so this arm clears the destination's upper half on every unequal 32-bit case and
agrees with the shipped model at every other width.  D53. -/
def wrongCmpxchgSdmWriteBack (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .cmpxchg sz dst src =>
      if dst.isImm then step i s
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let acc := s.getReg sz .rax
        let tmp := s.readOperand sz nr dst
        let s := s.setFlags (Flags.sub sz acc tmp s.flags)
        if Value.trunc sz acc == Value.trunc sz tmp then
          (s.writeOperand sz nr dst (s.getReg sz src)).setRip nr
        else
          ((s.setReg sz .rax tmp).writeOperand sz nr dst tmp).setRip nr
  | _ => step i s

/-- XADD AS AN ORDINARY ADD — the sum reaches the destination and the source is
left alone.  Invisible wherever the destination already held what the source is
about to get, and loud everywhere else. -/
def wrongXaddNoSourceWrite (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .xadd sz dst src =>
      if dst.isImm then step i s
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let a := s.readOperand sz nr dst
        let b := s.getReg sz src
        let res := Flags.addResult sz a b
        let s := s.setFlags (Flags.add sz a b s.flags)
        (s.writeOperand sz nr dst res).setRip nr
  | _ => step i s

/-- ⛔⛔ THE SDM, READ LITERALLY, A SECOND TIME: "IF COUNT = 0 THEN no
operation".  Both public executable models write the destination anyway, and K's
rule for this case carries the comment `// Intel Bug`.  Observable at `.d` alone.
D54. -/
def wrongDshiftZeroCountWritesNothing (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .dshift _ sz dst _ amt =>
      if !(dshiftEncodable sz) || dst.isImm then step i s
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let cnt : BitVec 8 :=
          match amt with
          | .imm8 v => v
          | .cl => (s.getReg .b .rcx).setWidth 8
        if Flags.shiftCount sz cnt = 0 then s.setRip nr else step i s
  | _ => step i s

/-- ⭐ THE BOUNDARY OFF BY ONE: "the count is GREATER than the operand size" read
as "greater than or equal".  A count EQUAL to the width is legal and its answer
is the source; this arm calls it undefined and draws.  It is wrong at exactly one
count, reachable only at `.w`, and `adversarial` contains `0x10` — so the five
pre-states whose CL masks to 16 are the whole of its evidence. -/
def wrongDshiftBadAtWidth (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .dshift _ sz dst _ amt =>
      if !(dshiftEncodable sz) || dst.isImm then step i s
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let cnt : BitVec 8 :=
          match amt with
          | .imm8 v => v
          | .cl => (s.getReg .b .rcx).setWidth 8
        let n := Flags.shiftCount sz cnt
        if dshiftMemUndefined sz dst.isMem n || n != sz.bits then step i s
        else
          let (cfU, s) := s.undefBit
          let (pfU, s) := s.undefBit
          let (afU, s) := s.undefBit
          let (zfU, s) := s.undefBit
          let (sfU, s) := s.undefBit
          let (ofU, s) := s.undefBit
          let (u, s) := s.undefVal sz.bits
          ((s.setFlags (Flags.dshiftBadFlags cfU pfU afU zfU sfU ofU s.flags)).writeOperand
            sz nr dst u).setRip nr
  | _ => step i s

/-- SHRD FILLING FROM THE SOURCE'S TOP BITS — `shld`'s fill, applied to the
other direction.  The two agree only where the source's top `n` bits equal its
bottom `n`, which `adversarial`'s alternating patterns make rare and its
all-ones entries make certain, so the arm is right somewhere and wrong mostly. -/
def wrongShrdFillsFromSourceTop (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .dshift .shrd sz dst src amt =>
      if !(dshiftEncodable sz) || dst.isImm then step i s
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let cnt : BitVec 8 :=
          match amt with
          | .imm8 v => v
          | .cl => (s.getReg .b .rcx).setWidth 8
        let n := Flags.shiftCount sz cnt
        let a := s.readOperand sz nr dst
        if dshiftMemUndefined sz dst.isMem n || n = 0 || sz.bits < n then step i s
        else
          let b := s.getReg sz src
          let res := Value.trunc sz
            (((Value.trunc sz a) >>> n) ||| ((Value.trunc sz b) >>> (sz.bits - n)))
          let (ofU, s) := s.undefBit
          let (afU, s) := s.undefBit
          let s := s.setFlags (Flags.dshiftFlags .shrd sz a res n ofU afU s.flags)
          (s.writeOperand sz nr dst res).setRip nr
  | _ => step i s

/-- ⭐ CF READ OFF THE RESULT INSTEAD OF THE ORIGINAL DESTINATION — one
substitution, and it is the mistake the definition invites, because in the result
the bit at that position holds an incoming SOURCE bit.  The two agree exactly
where the two operands happen to match at one bit, so roughly half the cases. -/
def wrongDshiftCfFromResult (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .dshift k sz dst src amt =>
      if !(dshiftEncodable sz) || dst.isImm then step i s
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let cnt : BitVec 8 :=
          match amt with
          | .imm8 v => v
          | .cl => (s.getReg .b .rcx).setWidth 8
        let n := Flags.shiftCount sz cnt
        let a := s.readOperand sz nr dst
        if dshiftMemUndefined sz dst.isMem n || n = 0 || sz.bits < n then step i s
        else
          let b := s.getReg sz src
          let res := Flags.dshiftRes k sz a b n
          let (ofU, s) := s.undefBit
          let (afU, s) := s.undefBit
          -- the BUG: `res` where the rule says the ORIGINAL destination
          let s := s.setFlags (Flags.dshiftFlags k sz res res n ofU afU s.flags)
          (s.writeOperand sz nr dst res).setRip nr
  | _ => step i s

/-! ### P1 BATCH 20 — the four arms pointed at claims nothing was pointed at

⭐ THE 71 SHAPE VECTORS OF THIS BATCH PASSED THE DIFFERENTIAL ON THE FIRST RUN,
and that is exactly the result that has to be distrusted rather than enjoyed.
No line of `X86/Semantics.lean` changed for them, so a green run is what the
design predicted — but "the code is already validated" is a claim about code the
new vectors mostly do not reach on any path the old ones did not.

⛔ AND LOOKING FOUND TWO CLAIMS IN `step` THAT NOTHING COULD SEE.  `.push` reads
its source BEFORE RSP moves; `.pop` computes its destination address AFTER RSP
moves.  Both sentences are in the semantics, both have been since P0, and
against every push/pop vector that existed — including this batch's own, which
address memory through RBX — a model with either order reversed is BIT-IDENTICAL.
⇒ **A CLAIM THE VECTORS CANNOT DISTINGUISH IS NOT TESTED BY THEM**, however many
of them there are.  The four vectors `push_rsp`, `pop_rsp`, `push_m_rsp` and
`pop_m_rsp` exist to give these three arms something to bite on, and the arms
exist so that the vectors' load-bearingness is CHECKED and not asserted. -/

/-- P1 BATCH 20: `push` reads its source AFTER the stack pointer has moved.

Caught only by a source that MOVES with RSP: `pushq %rsp` pushes 0x7ff8 instead
of 0x8000, and `pushq (%rsp)` reads the wrong quadword.  Against `push_r`
(RAX), `push_i_q` (an immediate) and `push_m_q` (RBX) this model is exactly the
right one, which is what keeps the bug surgical. -/
def wrongPushValueAfterDecrement (i : Instr) (s : Cpu) : Cpu :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .push sz src =>
      -- the state the SDM says the source is NOT read in
      let moved := s.setReg .q .rsp (s.regs.get .rsp - BitVec.ofNat 64 sz.bytes)
      (s.push sz (moved.readOperand sz nr src)).setRip nr
  | _ => step i s

/-- P1 BATCH 20: `pop` computes its destination's effective address BEFORE the
stack pointer is incremented (SDM Vol. 2A, POP: the address is computed after).

Caught only by a destination whose address moves with RSP: `popq (%rsp)` stores
at 0x8000 instead of 0x8008.  Both addresses are inside the watched stack window,
which is what makes the difference observable rather than merely real. -/
def wrongPopAddressBeforeIncrement (i : Instr) (s : Cpu) : Cpu :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .pop sz (.mem ea) =>
      let (v, s') := s.popValue sz
      -- the BUG: the address comes from the PRE-increment state
      { s' with mem := s'.mem.writeSize sz (ea.addr s nr) v }.setRip nr
  | _ => step i s

/-- P1 BATCH 20: `pop` into a REGISTER writes the loaded value first and the
stack-pointer increment second, so `popq %rsp` ends holding RSP+8 rather than
the value it loaded.

⚠️ THIS IS A SEPARATE ARM FROM THE ONE ABOVE AND NOT A GENERALISATION OF IT.
The memory arm is about an ADDRESS and shows in the stack window; this one is
about WHICH WRITE WINS and shows in `rsp`.  A single arm covering both would have
been caught by either vector and would not have said which claim was tested. -/
def wrongPopRegisterOrder (i : Instr) (s : Cpu) : Cpu :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .pop sz (.reg r h) =>
      let sp := s.regs.get .rsp
      let v := s.readMem sz sp
      -- the BUG: the destination write happens first, so the RSP update
      -- overwrites it when the destination IS RSP
      let s := s.writeOperand sz nr (.reg r h) v
      (s.setReg .q .rsp (sp + BitVec.ofNat 64 sz.bytes)).setRip nr
  | _ => step i s

/-- P1 BATCH 20: an INDIRECT branch jumps to the address of its memory operand
instead of to the value stored there — `jmp *(%rbx)` going to 0x2000 rather than
to `[0x2000]`.

⭐ It is the classic indirect-branch confusion, and until this batch there was no
vector with an indirect memory target for it to be wrong about.  ⚠️ It is
DELIBERATELY VISIBLE IN THE REFUSAL CHANNEL TOO: `[0x2000]` is non-canonical in
26 of the 82 pre-states and 0x2000 never is, so the wrong model BRANCHES where
this one refuses — which is the half of the disagreement a comparator that only
diffed committed states would miss. -/
def wrongIndirectBranchUsesAddress (i : Instr) (s : Cpu) : Cpu :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .jmp (.indirect (.mem ea)) => s.setRipChecked (ea.addr s nr)
  | .call (.indirect (.mem ea)) =>
      let tgt := ea.addr s nr
      if canonical tgt then (s.push .q nr).setRip tgt
      else s.halt (.unimplemented "non-canonical branch target (#GP(0) in hardware)")
  | _ => step i s

/-! ### P1 BATCH 21 — CMPXCHG8B

⭐ FIVE ARMS, AND TWO OF THEM PRICE THE OBSERVATION RATHER THAN BEING PLAUSIBLE.
This instruction chooses a branch, and — measured on the oracle before the
constructor existed — the EQUAL branch is reached in ONE of the 82 inherited
pre-states.  So an arm that always takes one branch agrees with the model on
every case of that branch, and whatever catches it is exactly the evidence that
the OTHER branch is reached.  `cmpxchg8bStates` is what makes the second of the
two catchable at all; deleting those four states and re-running the arm is the
check that they are load-bearing (D64).
-/

/-- ⭐ THE EQUAL BRANCH, ALWAYS.  Correct wherever the values match, so what
catches it measures how often they do NOT. -/
def wrongCmpxchg8bAlwaysStores (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .cmpxchg8b dst =>
      if !dst.isMem then step i s
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let src := (s.getReg .d .rcx) <<< 32 ||| s.getReg .d .rbx
        ((s.writeOperand .q nr dst src).setFlags { s.flags with zf := true }).setRip nr
  | _ => step i s

/-- ⭐ THE UNEQUAL BRANCH, ALWAYS.  Correct wherever the values differ, so what
catches it is the evidence that the equal branch is REACHED — and before this
batch's four purpose-built pre-states, exactly one case in the whole run could
have caught it. -/
def wrongCmpxchg8bNeverStores (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .cmpxchg8b dst =>
      if !dst.isMem then step i s
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let tmp := s.readOperand .q nr dst
        let s := s.setReg .d .rdx (tmp >>> 32)
        let s := s.setReg .d .rax tmp
        (s.setFlags { s.flags with zf := false }).setRip nr
  | _ => step i s

/-- ⛔ THE COMPARISON, THIRTY-TWO BITS WIDE — EAX against `[m][31:0]`, ignoring
EDX.  It differs from this model exactly where the two operands agree in their
low half and differ in their high half.  ⚠️ MEASURED: 21 of the 82 INHERITED
pre-states are already such a state — `mkPre` puts RCX in the memory operand and
`~RAX` in RDX, so the whole diagonal matches in the low half by construction — so
this arm is caught with or without batch 21's `delta` states, and the comment
that first stood here claimed otherwise.  See `cmpxchg8bStates`. -/
def wrongCmpxchg8bCompares32 (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .cmpxchg8b dst =>
      if !dst.isMem then step i s
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let tmp := s.readOperand .q nr dst
        if Value.trunc .d tmp == s.getReg .d .rax then
          let src := (s.getReg .d .rcx) <<< 32 ||| s.getReg .d .rbx
          ((s.writeOperand .q nr dst src).setFlags { s.flags with zf := true }).setRip nr
        else
          let s := s.setReg .d .rdx (tmp >>> 32)
          let s := s.setReg .d .rax tmp
          (s.setFlags { s.flags with zf := false }).setRip nr
  | _ => step i s

/-- ⛔⛔ `EDX:EAX := DEST` AS A MERGE INSTEAD OF A ZERO-EXTENSION — D53's defect,
in the form this instruction invites.  Every register write here is 32 bits
wide, so both writes clear bits 63:32; a model that preserved them is correct on
every state whose RAX and RDX already had zero up there, and this harness has
plenty. -/
def wrongCmpxchg8bMergesRegisters (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .cmpxchg8b dst =>
      if !dst.isMem then step i s
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let tmp := s.readOperand .q nr dst
        let acc := (s.getReg .d .rdx) <<< 32 ||| s.getReg .d .rax
        if tmp == acc then
          let src := (s.getReg .d .rcx) <<< 32 ||| s.getReg .d .rbx
          ((s.writeOperand .q nr dst src).setFlags { s.flags with zf := true }).setRip nr
        else
          let keep (old v : Val) : Val := (old &&& 0xFFFFFFFF00000000) ||| (v &&& 0xFFFFFFFF)
          let s := { s with regs := (s.regs.set .rdx (keep (s.regs.get .rdx) (tmp >>> 32))) }
          let s := { s with regs := (s.regs.set .rax (keep (s.regs.get .rax) tmp)) }
          (s.setFlags { s.flags with zf := false }).setRip nr
  | _ => step i s

/-- ⛔ THE STORED PAIR, SWAPPED — `EBX:ECX` instead of `ECX:EBX`.  ⚠️ RBX is this
harness's fixed data-window pointer, so EBX is 0x2000 in every pre-state and
only ECX sweeps; this arm is caught by the half that DOES move, and the case
that no state here can catch is named beside `cmpxchg8bStates`. -/
def wrongCmpxchg8bStoresSwapped (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .cmpxchg8b dst =>
      if !dst.isMem then step i s
      else
        let nr := s.rip + BitVec.ofNat 64 i.len
        let acc := (s.getReg .d .rdx) <<< 32 ||| s.getReg .d .rax
        let tmp := s.readOperand .q nr dst
        if tmp == acc then
          let src := (s.getReg .d .rbx) <<< 32 ||| s.getReg .d .rcx
          ((s.writeOperand .q nr dst src).setFlags { s.flags with zf := true }).setRip nr
        else
          let s := s.setReg .d .rdx (tmp >>> 32)
          let s := s.setReg .d .rax tmp
          (s.setFlags { s.flags with zf := false }).setRip nr
  | _ => step i s

/-! ### ⭐⭐ P2 ITEM 1 (BATCH 22) — the segment base's four planted defects

Four arms, and they are four DIFFERENT claims rather than four spellings of one.
Dropping the base, swapping the two bases, adding the base where the SDM says
not to, and adding it to the load but not the store are each a model somebody
would plausibly write, and each leaves the other three claims correct — so no
one of them is caught by another's vector.

⛔ THE FIRST ARM IS THE ONE THIS BATCH WAS MOST LIKELY TO HAVE SHIPPED, and it
is also what says the pre-states earn their keep.  `%fs:0x28` with the base
dropped is address 0x28, outside both watched windows — so if the vectors'
displacements had been chosen for realism alone and not for where they LAND,
this arm would have been an unobserved difference on the load side and an
invisible store on the write side, and would have registered as agreement.

⚠️ THE FIRST TWO ARMS PERTURB THE PRE-STATE RATHER THAN THE SEMANTICS, which is
a different technique from every other arm in this file and is the honest one
here: "the base is ignored" IS "the base is zero", and writing a second
`Ea.addr` to say so would have planted a defect in a copy of the code rather
than in the model under test. -/

/-- ⛔ A SEGMENT OVERRIDE IS IGNORED — the effective address is used as the
linear address, which is correct for CS/DS/ES/SS in 64-bit mode and wrong for
exactly the two registers this batch added. -/
def wrongSegBaseIgnored (i : Instr) (s : Cpu) : Cpu :=
  step i { s with fsBase := 0, gsBase := 0 }

/-- ⛔ FS AND GS READ EACH OTHER'S BASE.  Caught only because the two bases
DIFFER in every pre-state (`mkPre`); with one base for both, this arm would be
silent and the batch would have shipped an untested half. -/
def wrongSegFsGsSwapped (i : Instr) (s : Cpu) : Cpu :=
  step i { s with fsBase := s.gsBase, gsBase := s.fsBase }

/-- ⛔⛔ `lea` ADDS THE SEGMENT BASE.  The one arm about the SPLIT rather than
about the base: it plants the model in which `Ea.offset` and `Ea.addr` are the
same function — which is what this repository had before this batch — and
`leaq %fs:0x28, %rax` is the only vector that can see it. -/
def wrongLeaAddsSegBase (i : Instr) (s : Cpu) : Cpu :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .lea sz dst ea =>
      if s.stopped then s
      else (s.setReg sz dst (ea.addr s nr)).setRip nr
  | _ => step i s

/-- ⛔ THE BASE REACHES THE LOAD BUT NOT THE STORE.  A `mov` to a segmented
memory destination writes at the effective address — the shape a model takes
when the base is added in `readOperand` alone, which is the natural place to put
it first. -/
def wrongSegStoreUnsegmented (i : Instr) (s : Cpu) : Cpu :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .mov sz (.mem ea) src =>
      if s.stopped then s
      else
        let v := s.readOperand sz nr src
        (s.writeMem sz (ea.offset s nr) v).setRip nr
  | _ => step i s

/-! ### ⭐⭐ P2 ITEM 2 (BATCH 23) — the LOCK vocabulary's four planted defects

⛔ THE HARD PART OF THIS BATCH IS THAT LOCK HAS NO ARITHMETIC.  A single-step,
single-threaded semantics computes exactly the same result locked or unlocked,
so `lock addq %rcx, (%rbx)` and `addq %rcx, (%rbx)` are the same function and no
arm can distinguish a model that "implements LOCK" from one that ignores it in
the value channel.  What IS observable is the two edges: the forms the prefix
makes ILLEGAL, and the form the vocabulary UN-DECLINED.  All four arms live on
those edges, and each leaves the other three claims correct.

⚠️ AND TWO OF THEM MOVE THE LOCKABLE LIST IN OPPOSITE DIRECTIONS, deliberately.
A widened list and a narrowed one are caught by DIFFERENT vectors — the widened
one by `lock_mov_m_q_ud`, the narrowed one by `lock_xadd_m_q` and its siblings —
so neither can stand in for the other. -/

/-- ⛔ THE PREFIX IS IGNORED ENTIRELY: no form is #UD, so `lock movq %rax,(%rbx)`
stores instead of faulting.  The model this batch was most likely to have
shipped, because the value channel gives no reason to write the rule at all. -/
def wrongLockIgnored (i : Instr) (s : Cpu) : Cpu :=
  let strip (e : Ea) : Ea := { e with lock := false }
  let stripOp (o : Operand) : Operand :=
    match o with | .mem e => .mem (strip e) | x => x
  match i.op with
  | .mov sz d src => step ⟨.mov sz (stripOp d) (stripOp src), i.len⟩ s
  | .bin k sz d src => step ⟨.bin k sz (stripOp d) (stripOp src), i.len⟩ s
  | .un k sz d => step ⟨.un k sz (stripOp d), i.len⟩ s
  | .bit k sz d off => step ⟨.bit k sz (stripOp d) (stripOp off), i.len⟩ s
  | .lea sz d ea => step ⟨.lea sz d (strip ea), i.len⟩ s
  | _ => step i s

/-- ⛔ THE LOCKABLE LIST IS WIDENED to "anything with a memory destination" —
the derivation `Op.lockable`'s note says a reader would reach for, and which
quietly admits `mov`, the shifts and `cmp`.  Caught by the #UD vector. -/
def wrongLockableIsAnyMemDest (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .mov sz d src =>
      if d.isMem then
        let strip (o : Operand) : Operand :=
          match o with | .mem e => .mem { e with lock := false } | x => x
        step ⟨.mov sz (strip d) (strip src), i.len⟩ s
      else step i s
  | _ => step i s

/-- ⛔ THE LOCKABLE LIST IS NARROWED: the read-modify-write pair `xadd` and
`cmpxchg8b` fall off it, so their LEGAL locked forms fault.  The opposite
direction from the arm above, and caught by different vectors. -/
def wrongLockableOmitsRmw (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .xadd _ dst _ =>
      if dst.isMem && (X86.Op.eas i.op).any Ea.lock then
        s.halt (.byDesign "lock prefix on a form the SDM does not permit it on (#UD)")
      else step i s
  | .cmpxchg8b dst =>
      if dst.isMem && (X86.Op.eas i.op).any Ea.lock then
        s.halt (.byDesign "lock prefix on a form the SDM does not permit it on (#UD)")
      else step i s
  | _ => step i s

/-- ⛔ `xchg` AT MEMORY STILL REFUSES — the model as it stood before this batch.
It is the arm that proves the un-decline is OBSERVED rather than merely written:
without a vector at that shape, deleting D25's decline would have changed
nothing any gate could see. -/
def wrongXchgMemStillRefuses (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .xchg _ a b =>
      if a.isMem || b.isMem then
        s.halt (.unimplemented "xchg with a memory operand (implicit LOCK)")
      else step i s
  | _ => step i s

/-- ⭐⭐ P2 ITEM 3 (BATCH 24) — `movabs` TAKES THE `imm32` PATH.

⛔ THIS IS THE ONLY THING ABOUT `movabs` THAT CAN BE WRONG IN THIS MODEL, and
saying so is the batch's honesty.  `Operand.imm` has carried a full `BitVec 64`
since P0 and the decoder is trusted to have done any extension, so `movabsq
$imm64` and `movq $imm32` reach `step` as the same shape and no semantics
distinguishes them.  What a wrong DECODER would do is re-derive the value
through the 32-bit immediate path — truncate and sign-extend — and that is what
this plants.

⚠️ IT IS KEYED ON THE VALUE, NOT ON THE LENGTH.  Keying on `i.len == 10` would
plant a defect in the decoder's output rather than in a model of it, and would
be indistinguishable from a typo.  Truncate-and-sign-extend is IDENTITY on every
immediate that fits in a signed 32 bits — which is every other `mov r,imm`
vector in the table — so the arm fires on exactly the three vectors whose values
cannot be reached by extending anything. -/
def wrongMovabsImm32Path (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .mov sz dst (.imm v) =>
      let v32 : Val := BitVec.signExtend 64 (v.truncate 32)
      step ⟨.mov sz dst (.imm v32), i.len⟩ s
  | _ => step i s

/-! ### ⭐⭐⭐ P2 VECTOR WAVE, BATCH 2 — the wrong models for the PACKED forms.

Batch 0's arm could only clobber a register, because no instruction wrote one.
These are the first arms that can be WRONG RULES about vector arithmetic, and
they are chosen to be the mistakes a model would actually make. -/

/-- ⛔⛔ THE LANE WIDTH, WHICH IS THE WHOLE OF "PACKED".  This model computes
every packed add and subtract at 64-bit lanes, whatever the mnemonic says — so
`paddd` carries out of bit 31 into bit 32 instead of wrapping inside its lane.

⚠️ THIS IS THE ARM THAT COULD SILENTLY PASS, and it is the reason the batch is
not sealed on `unexplained=0` alone. A wrong lane width is invisible unless some
lane actually CARRIES across its boundary in some pre-state: if every xmm lane
in the pre-state pattern were small, `paddd` and `paddq` would agree on every
case and the differential would report agreement about a rule it never tested.
Running this arm is how the batch learns which it is. -/
def wrongVbinLaneWidth (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vbin k d s' =>
      let k' : VBinKind := match k with
        | .addb | .addw | .addd => .addq
        | .subb | .subw | .subd => .subq
        | other => other
      step ⟨.vbin k' d s', i.len⟩ s
  | _ => step i s

/-- ⛔ THE OPERAND ORDER OF A NON-COMMUTATIVE PACKED OP: `SRC - DEST` instead of
`DEST - SRC`. The adds and the bitwise trio are commutative and cannot see this,
so it is a claim about `psub*` alone — which is why it is a separate arm from
the lane width rather than folded into it. -/
def wrongVbinSubReversed (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vbin k d s' =>
      match k with
      | .subb | .subw | .subd | .subq =>
          (s.setXmm d (vbinApply k (s.getXmm s') (s.getXmm d))).setRip
            (s.rip + BitVec.ofNat 64 i.len)
      | _ => step i s
  | _ => step i s

/-- ⛔ THE REGISTER FIELDS, IGNORED: every `movdqa`/`movdqu` moves xmm1 into
xmm0 regardless of what it encodes. Thirteen of the fourteen new vectors DO
write xmm0 from xmm1, so this arm is caught by exactly one of them —
`paddd_x2x3`'s sibling reasoning, and the reason that row exists. -/
def wrongVmovFixedRegisters (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vmov a _ _ => step ⟨.vmov a .x0 .x1, i.len⟩ s
  | _ => step i s

/-- ⛔⛔⛔ P2 BATCH 13, ARM 1 — THE COUNT TAKEN **MODULO** THE LANE WIDTH.

This is the wrong model a reader would actually write, and it is BIT-IDENTICAL
to the right one at every count below the lane width.  `psrlw $3` cannot tell
them apart; `psrlw $0x10` can, and the difference is maximal — the SDM says all
zeros, this says the operand unchanged.

⚠️ IT IS SPELLED AS A REAL SHIFT, not as a `halt`: an arm that refuses is caught
by the frame and says nothing about the RULE. -/
def wrongVshiftModuloCount (i : Instr) (s : Cpu) : Cpu :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .vshifti op w dst cnt =>
      if !(vshiftEncodable op w) then step i s
      else (s.setXmm dst (vshiftApply op w (s.getXmm dst) (cnt.toNat % w.bits))).setRip nr
  | .vshiftx op w dst src =>
      if !(vshiftEncodable op w) then step i s
      else
        let c := ((s.getXmm src).setWidth 64).toNat
        (s.setXmm dst (vshiftApply op w (s.getXmm dst) (c % w.bits))).setRip nr
  | _ => step i s

/-- ⛔⛔ P2 BATCH 13, ARM 2 — THE COUNT READ AS **EIGHT BITS**, not sixty-four.

`psrad %xmm1,%xmm0` takes SRC[63:0] as its count.  A model that truncated to a
byte agrees with this one on every count below 256 — and the immediate forms
CANNOT distinguish it at all, because an `imm8` never exceeds 255.  Only the
`_x` and `_m` vectors can catch this, which is why the batch has them and why
`shift_count_reaches_both_regimes` insists the sweep reaches large counts.

⚠️ Deliberately NOT applied to `vshifti`: an arm that is wrong on a shape the
vectors cannot distinguish would be caught by the OTHER shape and read as
covering both. -/
def wrongVshiftLowByteCount (i : Instr) (s : Cpu) : Cpu :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .vshiftx op w dst src =>
      if !(vshiftEncodable op w) then step i s
      else
        let c := ((s.getXmm src).setWidth 8).toNat
        (s.setXmm dst (vshiftApply op w (s.getXmm dst) c)).setRip nr
  | .vshiftm op w dst ea =>
      if !(vshiftEncodable op w) then step i s
      else
        let a := ea.addr s nr
        let c := ((s.readMem128 a).setWidth 8).toNat
        (s.setXmm dst (vshiftApply op w (s.getXmm dst) c)).setRip nr
  | _ => step i s

/-- ⛔⛔ P2 BATCH 13, ARM 3 — `pslldq`/`psrldq` MODELLED AS THEIR OPCODE
NEIGHBOURS.  They share opcode byte `73` with `psllq`/`psrlq` and differ only in
the ModRM `/r` field, so treating them as a 64-bit-lane shift is the confusion
the encoding invites — and it also shifts by BITS where the real form shifts by
BYTES, so the arm is wrong twice in the same direction a careless reading is. -/
def wrongVshiftdqIsLaneWise (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vshiftdq left dst cnt =>
      (s.setXmm dst (vshiftApply (if left then .sll else .srl) .w64
        (s.getXmm dst) cnt.toNat)).setRip (s.rip + BitVec.ofNat 64 i.len)
  | _ => step i s

/-- ⛔ P2 BATCH 13, ARM 4 — THE ARITHMETIC SHIFT MADE LOGICAL.  `psraw`/`psrad`
shift the lane's own SIGN BIT in; this shifts zeros.  Invisible at any pre-state
whose lanes are all non-negative, which is why `xmmPattern`'s high half carries
`a` and the adversarial sweep reaches negative lanes. -/
def wrongVshiftAritheticIsLogical (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vshifti .sra w dst cnt =>
      if !(vshiftEncodable .sra w) then step i s
      else (s.setXmm dst (vshiftApply .srl w (s.getXmm dst) cnt.toNat)).setRip
             (s.rip + BitVec.ofNat 64 i.len)
  | _ => step i s

/-- ⛔ A PACKED OPERATION THAT WRITES A FLAG — the mistake of reaching for
`BinKind`'s machinery by analogy. "Flags Affected: None" on every SDM entry in
the group, so ZF moving at all is a disagreement. -/
def wrongVbinWritesFlags (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vbin .. => let t := step i s; t.setFlags { t.flags with zf := true }
  | _ => step i s

/-! ### ⭐⭐⭐ P2 VECTOR WAVE, BATCH 3 — the wrong models for the MEMORY forms.

⛔ AND ONE ARM IS DELIBERATELY ABSENT, WHICH IS WORTH MORE THAN ITS PRESENCE.
The obvious arm — "`movdqa` ignores its alignment requirement" — CANNOT BE
CAUGHT by this table, because there is no unaligned `movdqa` vector and there
cannot be one: ACL2 x86isa does not implement the check, so such a vector would
be a one-sided refusal in every pre-state. Adding the arm anyway would put a
permanently-silent entry in a list whose whole value is that every entry fires.
The rule is carried by `vload_unaligned_faults` instead, and D91 records that it
has no second source. ⇒ **AN ARM THAT NO VECTOR CAN DISTINGUISH IS NOT A WEAK
TEST, IT IS A FALSE ENTRY IN THE GATE'S OWN INVENTORY.** -/

/-- ⛔ A vector load that reads only EIGHT bytes and zeroes the top half — the
mistake of reusing the 64-bit path. The high eight bytes at `(%rbx)` are
baseMem's 0xB8…0xBF, non-zero and all distinct, so this differs in every
pre-state. -/
def wrongVload8Bytes (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vload _ d ea =>
      let a := ea.addr s (s.rip + BitVec.ofNat 64 i.len)
      (s.setXmm d ((s.readMem .q a).setWidth 128)).setRip (s.rip + BitVec.ofNat 64 i.len)
  | _ => step i s

/-- ⛔ A vector store that writes only the low eight bytes, leaving the rest of
the window as it was. -/
def wrongVstore8Bytes (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vstore _ ea r =>
      let a := ea.addr s (s.rip + BitVec.ofNat 64 i.len)
      (s.writeMem .q a ((s.getXmm r).setWidth 64)).setRip (s.rip + BitVec.ofNat 64 i.len)
  | _ => step i s

/-! ### ⭐⭐ P2 BATCH 20 — the wrong models for MOVHPS.

All three are about WHICH HALF, because that is the whole content of the form.
⚠️ They share the substring `movhps`, so ONE filter selects all three — D117's
rule, written after a filter ran half a batch's arms and printed PASS. -/

/-- ⛔ THE LOAD WRITES THE **LOW** QUADWORD instead of the high one. The plain
misreading of "MOVHPS moves 64 bits", and it is caught wherever the loaded value
and the destination's own halves differ. -/
def wrongMovhpsLoadsLow (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vloadh d ea =>
      let nr := s.rip + BitVec.ofNat 64 i.len
      let a := ea.addr s nr
      let hi := (((s.getXmm d) >>> 64).setWidth 64).setWidth 128 <<< 64
      (s.setXmm d (hi ||| ((s.readMem .q a).setWidth 128))).setRip nr
  | _ => step i s

/-- ⛔⛔ THE ARM THIS BATCH EXISTS FOR: the load CLEARS `dst[63:0]` instead of
PRESERVING it. It writes the right bits into the right half and is bit-identical
to the real model at every pre-state whose low quadword is already zero — so what
refutes it is not the instruction but `xmmPattern`'s non-zero low half, and its
score is a joint fact about the model and the pre-states (D117).

⭐ It is the MIRROR of D93: there ACL2 x86isa MERGED where the SDM clears; here
the SDM PRESERVES, so the plausible wrong model is the one that zeroes. -/
def wrongMovhpsClearsLow (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vloadh d ea =>
      let nr := s.rip + BitVec.ofNat 64 i.len
      let a := ea.addr s nr
      (s.setXmm d (((s.readMem .q a).setWidth 128) <<< 64)).setRip nr
  | _ => step i s

/-- ⛔ THE STORE WRITES THE **LOW** QUADWORD. The store-side twin of
`wrongMovhpsLoadsLow`, and it needs its own arm because the load arms cannot
reach `vstoreh` at all. -/
def wrongMovhpsStoresLow (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vstoreh ea r =>
      let nr := s.rip + BitVec.ofNat 64 i.len
      let a := ea.addr s nr
      (s.writeMem .q a ((s.getXmm r).setWidth 64)).setRip nr
  | _ => step i s

/-! ### ⭐⭐ P2 BATCH 22 — the wrong models for PREFETCHh.

⛔⛔ **THERE ARE TWO, AND THERE IS DELIBERATELY NO THIRD.** The obvious candidate —
*"prefetch ignores its locality hint"* — is architecturally INVISIBLE, so no vector
that can exist would distinguish it, and an arm no vector can distinguish is a
FALSE ENTRY in this list rather than a weak test (D91, which cost this repository
exactly that). The hint is held apart by `check_encodings.py` instead: it assembles
each `asm` and compares bytes, which is the instrument that can see a `/reg` field.

⚠️ What remains is everything a "do nothing" model can still get WRONG, and both
are real mistakes a reader might make from the SDM's word "hint". -/

/-- ⛔ PREFETCH FAULTS on an address it may not touch. The plainest misreading:
treating a named memory operand as an ACCESS. PREFETCHh never faults — not on an
unmapped address, not on a misaligned one — so this halts where the real model
runs. -/
def wrongPrefetchFaults (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .prefetch _ _ => s.halt (.byDesign "prefetch treated as a faulting access")
  | _ => step i s

/-- ⛔ PREFETCH READS ITS OPERAND INTO A REGISTER — the "it's a load" model. It
changes `rax`, which the differential watches, so it is caught wherever the
prefetched window is non-zero. ⚠️ This is the arm that gives the batch its only
positive content: without it, "both sides changed nothing" would be a claim no
wrong model was ever tested against. -/
def wrongPrefetchLoads (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .prefetch _ ea =>
      let nr := s.rip + BitVec.ofNat 64 i.len
      ((s.setReg .q .rax (s.readMem .q (ea.addr s nr))).setRip nr)
  | _ => step i s

/-- ⛔ `movdqu` APPLIES THE ALIGNMENT CHECK TOO — i.e. a model that made both
mnemonics fault. This is the arm `movdqu_load_unal` exists for: it is the only
vector in the table at an address that is not 16-byte aligned, so without it this
wrong model would be indistinguishable from the right one. -/
def wrongVmovduAlsoAligns (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vload _ d ea => step ⟨.vload .dqa d ea, i.len⟩ s
  | .vstore _ ea r => step ⟨.vstore .dqa ea r, i.len⟩ s
  | _ => step i s

/-! ### ⭐⭐⭐ P2 VECTOR WAVE, BATCH 5 — the wrong models for MOVD/MOVQ.

All three are about ZEROING, because that is all these forms do beyond moving
bits, and each one is bit-identical to the right model whenever the bits it fails
to clear were already zero — which is exactly why batch 0's XMM pre-state pattern
is deliberately non-zero and non-constant. -/

/-- ⛔ `movd`/`movq` INTO an XMM register MERGE instead of clearing: the bits
above the written width keep whatever the destination held. ⚠️ THIS IS EXACTLY
THE DEFECT ACL2 x86isa HAS (D93) — which is why it is planted against the Lean
model rather than the oracle, and why `driveWrong` passes an EMPTY divergence
list: a declared oracle divergence must never excuse a planted bug. -/
def wrongVmovgPreservesUpper (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vmovg true sz x r =>
      let old := s.getXmm x
      let v := (s.getReg sz r).setWidth 128
      let keep : BitVec 128 := old &&& (BitVec.allOnes 128 <<< (sz.bits))
      (s.setXmm x (v ||| keep)).setRip (s.rip + BitVec.ofNat 64 i.len)
  | _ => step i s

/-- ⛔ `movq %xmm1,%xmm0` behaves like `movdqa` — it copies all 128 bits instead
of moving the low quadword and ZEROING the upper one. -/
def wrongVmovqCopiesAll (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vmovq dst src => (s.setXmm dst (s.getXmm src)).setRip (s.rip + BitVec.ofNat 64 i.len)
  | _ => step i s

/-- ⛔ `movd %xmm0,%ecx` writes 32 bits WITHOUT zero-extending, preserving the
GPR's upper half — the `.d`-width mistake this model has caught before in the
scalar forms, now on the other side of the register-file boundary. -/
def wrongVmovgFromXNoZeroExtend (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vmovg false sz x r =>
      if sz == .d then
        let old := s.getReg .q r
        let lo := (s.getXmm x).setWidth 64 &&& 0xFFFFFFFF
        (s.setReg .q r ((old &&& 0xFFFFFFFF00000000) ||| lo)).setRip
          (s.rip + BitVec.ofNat 64 i.len)
      else step i s
  | _ => step i s

/-! ### ⭐⭐⭐ P2 VECTOR WAVE, BATCH 11 — the wrong models for the MOVE FAMILY.

⛔⛔ THE FIRST TWO ARE THE BATCH, AND THEY POINT IN OPPOSITE DIRECTIONS.
`movss`/`movsd` PRESERVE the destination's upper bits from a register and CLEAR
them from memory, so there are exactly two ways to be wrong by being consistent —
always merge, or always zero — and each is bit-identical to this model on HALF
the vectors.  A gate that planted only one of them would report a green that
means "this model is not the other one", which is not the claim.

⚠️ AND BOTH ARE ALSO INDISTINGUISHABLE FROM THE RIGHT MODEL AT ANY PRE-STATE
WHOSE DESTINATION XMM REGISTER IS ZERO.  That is a property of the PRE-STATES,
not of the model, and the caught-counts below are what measure it — batch 0's
deliberately non-zero pattern is the reason there is anything to count. -/

/-- ⛔ THE SCALAR MOVE ZEROES WHAT IT SHOULD PRESERVE: `movss %xmm1,%xmm0` clears
bits 127:32 instead of leaving them.  This is `vmovq`'s rule applied to a form
that does not have it — the mistake five previous batches of "XMM writes clear
the rest" make natural. -/
def wrongVmovsZeroesUpper (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vmovs sz d s' =>
      (s.setXmm d (((s.getXmm s').setWidth sz.bits).setWidth 128)).setRip
        (s.rip + BitVec.ofNat 64 i.len)
  | _ => step i s

/-- ⛔ AND THE OPPOSITE: the scalar LOAD merges into the destination instead of
clearing it — the SDM's register clause applied to its memory clause.  ⚠️ This is
the direction a reader is LESS likely to plant, because "a load overwrites the
register" feels obviously true; what it overwrites is the whole point. -/
def wrongVmovsldMergesUpper (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vmovsld sz d ea =>
      let a := ea.addr s (s.rip + BitVec.ofNat 64 i.len)
      let keep := ((s.getXmm d) >>> sz.bits) <<< sz.bits
      let low  := ((s.readMem sz a).setWidth sz.bits).setWidth 128
      (s.setXmm d (keep ||| low)).setRip (s.rip + BitVec.ofNat 64 i.len)
  | _ => step i s

/-- ⛔ THE SCALAR MOVE IGNORES ITS REGISTER FIELDS — every `movss`/`movsd`
between registers moves xmm1 into xmm0.  ⚠️ `movss_x4x5` and `movsd_x4x5` exist
FOR this arm, and batch 5 is why they exist BEFORE the run rather than after it:
with only x0←x1 vectors this wrong model is bit-identical to the right one and
the arm would report a green about operands nothing decoded. -/
def wrongVmovsFixedRegisters (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vmovs sz _ _ => step ⟨.vmovs sz .x0 .x1, i.len⟩ s
  | _ => step i s

/-- ⛔ THE SCALAR MOVE USES THE WRONG WIDTH — `movss` moves 64 bits and `movsd`
32.  ⚠️ Without this arm the two mnemonics are distinguished only by a `Size`
field nothing reads back: a model that collapsed them would agree with this one
wherever the source's bits 63:32 happened to match the destination's. -/
def wrongVmovsWidthSwapped (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vmovs sz d s' => step ⟨.vmovs (if sz == .d then .q else .d) d s', i.len⟩ s
  | .vmovsld sz d ea => step ⟨.vmovsld (if sz == .d then .q else .d) d ea, i.len⟩ s
  | .vmovsst sz ea r => step ⟨.vmovsst (if sz == .d then .q else .d) ea r, i.len⟩ s
  | _ => step i s

/-- ⛔ THE SCALAR STORE WRITES THE WHOLE REGISTER — 16 bytes where the SDM says 4
or 8.  The bytes above the lane in the memory window are `baseMem`'s, non-zero
and all distinct, so an over-wide store differs in every pre-state. -/
def wrongVmovsstStoresAll (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vmovsst _ ea r =>
      let a := ea.addr s (s.rip + BitVec.ofNat 64 i.len)
      (s.writeMem128 a (s.getXmm r)).setRip (s.rip + BitVec.ofNat 64 i.len)
  | _ => step i s

/-! ⛔ `movaps` APPLIES NO ALIGNMENT CHECK — i.e. a model that read `VMovKind`'s
new members as unaligned by default.  ⚠️ THIS ARM CANNOT FIRE, AND IT IS NOT IN
THE LIST BELOW FOR EXACTLY THAT REASON: there is no unaligned `movaps` vector,
because the oracle does not implement the check (D91), so the arm would be a
permanently-silent entry in an inventory whose whole value is that every entry
fires.  The rule is carried by `vload_unaligned_faults`, which is now stated over
`k.aligned` and therefore covers `movaps` as well as `movdqa`.  ⇒ The comment
above `wrongVmovduAlsoAligns` said this once for two mnemonics; it says it for
four now, and the theorem that replaced the arm grew with them. -/

/-! ### ⭐⭐⭐ P2 VECTOR WAVE, BATCH 7 — the wrong models for the UNPACK group.

Both are about WHICH BITS, not about arithmetic — an unpack computes nothing, it
only chooses. -/

/-- ⛔ `punpckl` reads the HIGH half of each operand and `punpckh` the LOW one.
⚠️ THIS ARM MEASURES SOMETHING ABOUT THE PRE-STATES, not only about the model:
`punpckl` and `punpckh` read DISJOINT halves, so any pre-state whose two halves
happened to agree could not tell them apart. If this arm fires in far fewer cases
than the others, that is a fact about the XMM pattern and not about the rule. -/
def wrongUnpackHalf (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vbin k d s' =>
      let k' : VBinKind := match k with
        | .unpcklb => .unpckhb | .unpcklw => .unpckhw
        | .unpckld => .unpckhd | .unpcklq => .unpckhq
        | .unpckhb => .unpcklb | .unpckhw => .unpcklw
        | .unpckhd => .unpckld | .unpckhq => .unpcklq
        | other => other
      step ⟨.vbin k' d s', i.len⟩ s
  | _ => step i s

/-- ⛔ THE ORDER WITHIN EACH PAIR IS REVERSED — source lane low, destination lane
high. The SDM and objdump both give destination first
(`xmm0 = xmm0[0],xmm1[0],…`), and this is the mistake a reader makes by reading
the AT&T operand order instead of the operation's. -/
def wrongUnpackOrder (i : Instr) (s : Cpu) : Cpu :=
  match i.op with
  | .vbin k d s' =>
      match k with
      | .unpcklb | .unpcklw | .unpckld | .unpcklq
      | .unpckhb | .unpckhw | .unpckhd | .unpckhq =>
          -- swap the two operands: `vunpack` puts its FIRST argument low
          (s.setXmm d (vbinApply k (s.getXmm s') (s.getXmm d))).setRip
            (s.rip + BitVec.ofNat 64 i.len)
      | _ => step i s
  | _ => step i s

/-! ### ⭐⭐⭐ P2 VECTOR WAVE, BATCH 0 — the harness's own red arm

⛔ THIS BATCH ADDS NO SEMANTICS, SO ITS ARM CANNOT BE A WRONG RULE.  Nothing in
the roster writes a vector register; what the batch claims is that the CHANNEL
exists and is compared, and the only way to test a channel with nothing flowing
through it is to push something through it deliberately.

⇒ The arm CLOBBERS one XMM register on every step.  If it is caught, the sixteen
new fields are genuinely being read, rendered, transported to the oracle,
rendered again on the far side and diffed.  If it were not caught — and before
this batch it could not have been, because the field did not exist — then a P2
vector run would have reported `unexplained=0` about a region nobody looked at.

⚠️ IT PICKS xmm3 AND NOT xmm0, deliberately: `xmm0` is the register a
half-initialised file is most likely to have right by accident, and the first
element of a walk is the one an off-by-one still reaches. -/
def wrongXmmClobbered (i : Instr) (s : Cpu) : Cpu :=
  (step i s).setXmm .x3 0

/-- ⛔⛔ P2 BATCH 14, ARM 1 — THE PERMUTE'S FIELD ORDER REVERSED.  Destination
lane `j` takes the immediate's field `3-j` instead of field `j`.

⚠️ THIS IS THE ONE MISTAKE THE GROUP INVITES, because the SDM prints the fields
most-significant-first (`ORDER[7:6]`, `ORDER[5:4]`, `ORDER[3:2]`, `ORDER[1:0]`)
while the LANES it assigns them to run least-significant-first.  A reader
transcribing the pseudocode top to bottom writes exactly this.
⚠️ AND IT IS INVISIBLE AT A PALINDROMIC SELECTOR — `$0x1b` is a reversal, so the
wrong model returns the IDENTITY there rather than a scrambled register, which
looks like a plausible answer.  `$0x93` is in the table for that reason. -/
def wrongVshufReversedFields (i : Instr) (s : Cpu) : Cpu :=
  let rev (sel : BitVec 8) : BitVec 8 :=
    ((sel &&& 3) <<< 6) ||| (((sel >>> 2) &&& 3) <<< 4)
      ||| (((sel >>> 4) &&& 3) <<< 2) ||| ((sel >>> 6) &&& 3)
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .vshuf k dst src sel =>
      (s.setXmm dst (vshufApply k (s.getXmm src) (rev sel))).setRip nr
  | .vshufm k dst ea sel =>
      let a := ea.addr s nr
      if !aligned16 a then step i s
      else (s.setXmm dst (vshufApply k (s.readMem128 a) (rev sel))).setRip nr
  | _ => step i s

/-- ⛔⛔ P2 BATCH 14, ARM 2 — THE PERMUTE AS A READ-MODIFY-WRITE.  It permutes the
DESTINATION instead of the source, which is the shape every packed constructor
before this batch has (`vbin`, `vshifti`, `vshiftx` all read `dst`).

⚠️ BIT-IDENTICAL TO THE RIGHT MODEL ON ANY VECTOR WHOSE DESTINATION ALREADY HOLDS
ITS SOURCE — and every register vector in this repository before batch 5 was
`x0 ← x1`, which is not that, but is one small step from it.  `pshufd_x2x3` and
the memory forms are what separate them. -/
def wrongVshufPermutesInPlace (i : Instr) (s : Cpu) : Cpu :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .vshuf k dst _ sel =>
      (s.setXmm dst (vshufApply k (s.getXmm dst) sel)).setRip nr
  | _ => step i s

/-- ⛔⛔⛔ P2 BATCH 14, ARM 3 — `pshuflw`/`pshufhw` PERMUTING ALL EIGHT WORDS.
This is the `vlanes` reflex written out: derive the lane count from the WIDTH
(`128 / 16 = 8`) rather than from the SELECTOR (`8 / 2 = 4`), and apply the same
four 2-bit fields twice, once to each half.

⛔ It destroys exactly the half the SDM says to copy through, and it leaves
`pshufd` — where `128 / 32` and `8 / 2` are both 4 — COMPLETELY UNTOUCHED.  So an
arm that only ran `pshufd` vectors would pass this model, which is the reason the
word forms carry vectors of their own rather than riding on the doubleword's. -/
def wrongVshufWholeRegisterWords (i : Instr) (s : Cpu) : Cpu :=
  let both (src : BitVec 128) (sel : BitVec 8) : BitVec 128 :=
    vselect 16 src sel.toNat 0 ||| vselect 16 src sel.toNat 4
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .vshuf k dst src sel =>
      match k with
      | .d => step i s
      | _ => (s.setXmm dst (both (s.getXmm src) sel)).setRip nr
  | .vshufm k dst ea sel =>
      match k with
      | .d => step i s
      | _ =>
        let a := ea.addr s nr
        if !aligned16 a then step i s
        else (s.setXmm dst (both (s.readMem128 a) sel)).setRip nr
  | _ => step i s

/-- ⭐⭐⭐ P2 BATCH 15, THE ARM D91 RECORDED AS IMPOSSIBLE — a packed binary
operation that IGNORES its 16-byte alignment requirement.

⛔ D91 wrote: *"`movdqa` ignores its alignment requirement` cannot be caught by
any vector that can exist, and an arm no vector can distinguish is not a weak
test but a FALSE ENTRY in the gate's own inventory."* That was true, and it was
true of every alignment rule in this repository for nine batches.

⭐ It stops being true here for three of the nineteen. `pand_m_unal`,
`por_m_unal` and `pxor_m_unal` are addresses at which BOTH models refuse — and a
model that executes instead disagrees in `refused`, which `classify` reports in
the `refusal` class (D33's channel). ⚠️ THIS ARM IS WHAT PRICES THOSE THREE
VECTORS: two sides refusing looks exactly like two sides broken, and without a
planted model that does NOT refuse, their agreement would be silence
([[a-refusing-form-needs-a-refuse-always-control]]).

⚠️ It reports in `refused` and not in `xmm0`, because at an unaligned address the
wrong model WRITES where the right one halts — and it is the halt, not the value,
that the vectors are testing. -/
def wrongVbinmIgnoresAlignment (i : Instr) (s : Cpu) : Cpu :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .vbinm k dst ea =>
      let a := ea.addr s nr
      (s.setXmm dst (vbinApply k (s.getXmm dst) (s.readMem128 a))).setRip nr
  | _ => step i s

/-- ⛔⛔ P2 BATCH 15, ARM 2 — THE OPERANDS SWAPPED. `vbinApply k dst mem` becomes
`vbinApply k mem dst`.

⚠️ INVISIBLE AT ELEVEN OF THE NINETEEN. `pand`/`por`/`pxor` and the eight
add/subtract... no: the ELEVEN that commute are the three bitwise and the four
adds, four of them — `psub*` does not commute and neither does an unpack, whose
`a` argument is the DESTINATION and takes the low lane of every pair. So the arm
is caught only by `psub*` and `punpck*`, which is twelve of the nineteen vectors,
and that is the number to read: an arm caught by a MINORITY of a group's vectors
is one whose group needed those vectors. -/
def wrongVbinmOperandsSwapped (i : Instr) (s : Cpu) : Cpu :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .vbinm k dst ea =>
      let a := ea.addr s nr
      if !aligned16 a then step i s
      else (s.setXmm dst (vbinApply k (s.readMem128 a) (s.getXmm dst))).setRip nr
  | _ => step i s

/-- ⛔⛔⛔ P2 BATCH 17, ARM 1 — `pcmpgt` COMPARED AS UNSIGNED. Lean's `<` on
`BitVec` IS unsigned, so this is not a strawman: it is what a model written
without noticing the SDM's word "signed" compiles to, and it type-checks.

⚠️ IT AGREES WITH THE RIGHT MODEL WHEREVER BOTH LANES ARE NON-NEGATIVE — 61 of 88
pre-states for `pcmpgtb %xmm1,%xmm0`, and **88 of 88 for `pcmpgtb %xmm3,%xmm2`**,
which is why the register-field control cannot stand in for the signedness one.
⛔ And it is invisible at every `pcmpeq` vector, because equality is the same
relation signed or unsigned. -/
def wrongVcmpUnsigned (i : Instr) (s : Cpu) : Cpu :=
  let un (k : VBinKind) (a b : BitVec 128) : BitVec 128 :=
    match k with
    | .cmpgtb => vlanes 8  (fun x y => if y < x then -1 else 0) a b
    | .cmpgtw => vlanes 16 (fun x y => if y < x then -1 else 0) a b
    | .cmpgtd => vlanes 32 (fun x y => if y < x then -1 else 0) a b
    | _ => vbinApply k a b
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .vbin k dst src => (s.setXmm dst (un k (s.getXmm dst) (s.getXmm src))).setRip nr
  | .vbinm k dst ea =>
      let a := ea.addr s nr
      if !aligned16 a then step i s
      else (s.setXmm dst (un k (s.getXmm dst) (s.readMem128 a))).setRip nr
  | _ => step i s

/-- ⛔⛔ P2 BATCH 17, ARM 2 — THE COMPARE RESULT AS A FLAG RATHER THAN A MASK: a
lane becomes `1` instead of all ones.

⚠️ BIT-IDENTICAL IN THE LOW BIT OF EVERY LANE, which is the bit a reader coming
from `Flags` is thinking about. Measured: it agrees at 34-53 of 88 pre-states at
the register shape and at 0-8 at the memory shape, so the memory vectors are
carrying this arm and the register ones are barely carrying it at all. -/
def wrongVcmpBooleanNotMask (i : Instr) (s : Cpu) : Cpu :=
  let bl (k : VBinKind) (a b : BitVec 128) : BitVec 128 :=
    match k with
    | .cmpeqb => vlanes 8  (fun x y => if x == y then 1 else 0) a b
    | .cmpeqw => vlanes 16 (fun x y => if x == y then 1 else 0) a b
    | .cmpeqd => vlanes 32 (fun x y => if x == y then 1 else 0) a b
    | .cmpgtb => vlanes 8  (fun x y => if y.slt x then 1 else 0) a b
    | .cmpgtw => vlanes 16 (fun x y => if y.slt x then 1 else 0) a b
    | .cmpgtd => vlanes 32 (fun x y => if y.slt x then 1 else 0) a b
    | _ => vbinApply k a b
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .vbin k dst src => (s.setXmm dst (bl k (s.getXmm dst) (s.getXmm src))).setRip nr
  | .vbinm k dst ea =>
      let a := ea.addr s nr
      if !aligned16 a then step i s
      else (s.setXmm dst (bl k (s.getXmm dst) (s.readMem128 a))).setRip nr
  | _ => step i s

/-- ⛔⛔⛔ P2 BATCH 18, ARM 1 — `packuswb` TRUNCATING INSTEAD OF SATURATING.
Keeping the low byte of each word is BIT-IDENTICAL at every in-range value, which
is every value a vector table written without adversarial constants contains. It
is the model this group exists to refute. -/
def wrongPackuswbTruncates (i : Instr) (s : Cpu) : Cpu :=
  let tr (dst src : BitVec 128) : BitVec 128 :=
    let byteOf (v : BitVec 128) (k : Nat) : BitVec 128 :=
      ((v.extractLsb' (k * 16) 16).setWidth 8).setWidth 128
    (List.range 8).foldl (fun acc k =>
      acc ||| (byteOf dst k <<< (k * 8)) ||| (byteOf src k <<< ((8 + k) * 8))) 0
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .vbin .packuswb dst src => (s.setXmm dst (tr (s.getXmm dst) (s.getXmm src))).setRip nr
  | .vbinm .packuswb dst ea =>
      let a := ea.addr s nr
      if !aligned16 a then step i s
      else (s.setXmm dst (tr (s.getXmm dst) (s.readMem128 a))).setRip nr
  | _ => step i s

/-- ⛔⛔ P2 BATCH 18, ARM 2 — `packuswb` READING ITS SOURCE AS UNSIGNED, so a
negative word clamps to 255 instead of to 0 — the OPPOSITE END of the range.

⚠️ It agrees with the right model at 32 of 88 pre-states at the register shape and
0 of 88 at the memory shape, so the memory vector is what carries this arm. -/
def wrongPackuswbUnsignedSource (i : Instr) (s : Cpu) : Cpu :=
  let un (dst src : BitVec 128) : BitVec 128 :=
    let byteOf (v : BitVec 128) (k : Nat) : BitVec 128 :=
      let w := v.extractLsb' (k * 16) 16
      (((if 255 < w.toNat then (255 : BitVec 8) else w.setWidth 8)).setWidth 128)
    (List.range 8).foldl (fun acc k =>
      acc ||| (byteOf dst k <<< (k * 8)) ||| (byteOf src k <<< ((8 + k) * 8))) 0
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .vbin .packuswb dst src => (s.setXmm dst (un (s.getXmm dst) (s.getXmm src))).setRip nr
  | .vbinm .packuswb dst ea =>
      let a := ea.addr s nr
      if !aligned16 a then step i s
      else (s.setXmm dst (un (s.getXmm dst) (s.readMem128 a))).setRip nr
  | _ => step i s

/-- THE ARMS, AS DATA: name, wrong model, and the field the bug must show in.
Named once so the filtered probe mode and the full selftest cannot drift apart —
a probe that ran a different set from the gate would be the exact defect the
coverage table kept making (D15).

⛔ AND FOR ONE BATCH THAT SENTENCE WAS FALSE, WHICH IS WHY IT IS STILL HERE WITH
THIS NOTE UNDER IT.  Batch 10 added this table and wired only the FILTERED mode
to it; the no-argument `selftest` — the form CI runs — kept its own hand-written
sequence of twenty-three `driveWrong` calls. The two lists drifted immediately
and silently, and the comment above is what made the drift invisible: it
described the intended design as though it were the built one.

Both readers now fold over THIS list, so the claim is structural rather than
aspirational — there is no second list to disagree with. D29. -/
def selftestArms : List (String × (Instr → Cpu → Cpu) × String) :=
  [ ("inc clobbers CF", wrongInc, "cf")
  , ("movl fails to zero-extend", wrongMovD, "rax")
  , ("shift forgets to mask its count", wrongShiftMask, "rax")
  , ("adc drops the carry-in", wrongAdcNoCarry, "rax")
  , ("adc's carry-OUT forgets the carry-in", wrongAdcCarryOutCF, "cf")
  , ("cmp writes its result back", wrongCmpWritesBack, "rax")
  , ("cmp writes back ONLY to a memory destination", wrongCmpMemWriteBack,
     "mem@0000000000001fe0")
  , ("a memory read-modify-write drops its STORE", wrongMemStoreDropped,
     "mem@0000000000001fe0")
  , ("a memory store ignores its operand WIDTH", wrongMemStoreWidth,
     "mem@0000000000001fe0")
  -- P1 BATCH 20.  The first three catch in the STACK window and in `rsp`, not
  -- in the data window: they are about the order of two writes, not about a
  -- value.
  , ("push reads its source AFTER the stack pointer moves",
     wrongPushValueAfterDecrement, "mem@0000000000007fe0")
  , ("pop computes its destination address BEFORE the increment",
     wrongPopAddressBeforeIncrement, "mem@0000000000007fe0")
  , ("pop into a register lets the RSP update overwrite the loaded value",
     wrongPopRegisterOrder, "rsp")
  , ("an indirect branch uses the ADDRESS of its operand, not the value",
     wrongIndirectBranchUsesAddress, "rip")
  , ("jcxz inverts its test", wrongJcxzInverted, "rip")
  , ("jecxz ignores the address-size prefix and reads all 64 bits", wrongJecxzWidth, "rip")
  , ("setcc inverts its condition", wrongSetccInverted, "rax")
  , ("cmov skips the write when the condition is false", wrongCmovSkipsWrite, "rax")
  , ("sar brings in zeros instead of the sign", wrongSarLogical, "rax")
  , ("sar takes SHL/SHR's undefined-CF rule at a large count",
     wrongSarCfUndefinedAtLargeCount, "cf")
  , ("rol rotates the wrong way", wrongRolDirection, "rax")
  , ("a rotate keys its CF write on the REDUCED count", wrongRotCfKeyedOnReducedCount, "cf")
  , ("bts sets the bit above the one it tested", wrongBtsOffByOne, "rax")
  , ("a bit-test recomputes ZF instead of leaving it alone", wrongBitRecomputesZf, "zf")
  , ("movsx zero-extends (movsx written as movzx)", wrongMovsxZeroExtends, "rax")
  , ("xchg copies instead of swapping", wrongXchgCopies, "rcx")
  , ("the cwtd/cltd/cqto trio merges where cltd must zero-extend", wrongCdqMerges, "rdx")
  , ("a width-changing move bounds the VALUE and not the WRITE",
     wrongMovxFullWidthWrite, "rax")
  , ("loop tests the counter before decrementing it", wrongLoopTestsOldCounter, "rip")
  , ("loop writes the counter back only when it branches",
     wrongLoopNoWritebackOnFallthrough, "rcx")
  , ("addr32 loop tests the full 64-bit counter", wrongLoopAddr32TestsFullWidth, "rip")
  , ("cld is a no-op (the flag nothing could write)", wrongCldIsNoOp, "df")
  , ("every nop advances RIP by one byte", wrongNopFixedLength, "rip")
  , ("ud2 executes instead of faulting", wrongUd2Executes, "refused")
  , ("retq jumps without popping (the state nothing could reach)", wrongRetNoPop, "rsp")
  , ("leaveq pops before it moves RSP", wrongLeaveWrongOrder, "rbp")
  -- P1 BATCH 13.  ⚠️ `wrongMovbeNoReversal`'s field is the DATA WINDOW and not
  -- `rax`, deliberately: the store direction is the half a register field
  -- cannot see, and the load direction is caught by the other two arms.
  , ("shlx/shrx/sarx write the flags a shift writes", wrongShiftxWritesFlags, "cf")
  , ("movbe reverses 64 bits at every width", wrongMovbeFullWidth, "rax")
  , ("movbe moves without reversing", wrongMovbeNoReversal,
     "mem@0000000000001fe0")
  -- P1 BATCH 14.  The two opcode-pair confusions, the inverted CF, and the
  -- width the narrow vectors exist to defend.
  , ("bsr reports leading zeros instead of the top bit's index",
     wrongBsrIsLzcnt, "rax")
  , ("lzcnt takes ZF from the source, as bsf does", wrongLzcntZfFromSource, "zf")
  , ("blsi sets CF when the source IS zero", wrongBlsiCfSense, "cf")
  , ("popcnt counts the whole register, not the operand",
     wrongPopcntFullWidthSource, "rax")
  -- P1 BATCH 15 — the string group.  Six arms, and every one of them is a
  -- defect that would leave some other width or some other flag correct, so
  -- none of them can be caught by a single case.
  , ("a string op ignores DF and always moves forward", wrongStringNoDF, "rdi")
  , ("a string pointer is updated at the OPERAND width, not 64 bits",
     wrongStringPointerWidth, "rdi")
  , ("movs advances its pointers BEFORE the copy", wrongMovsPreIncrement,
     "mem@0000000000001fe0")
  , ("cmps subtracts destination from source, as AT&T prints it",
     wrongCmpsOperandOrder, "cf")
  , ("scas compares against rsi instead of rdi", wrongScasUsesRsi, "cf")
  , ("lods merges into the accumulator instead of zero-extending at 32 bits",
     wrongLodsNoZeroExtend, "rax")
  -- P1 BATCH 16 — the repeat prefixes.  Five arms, and the FIRST of them is the
  -- model this batch was most likely to have written.
  , ("rep advances rip when the decrement drives rcx to zero",
     wrongRepAdvanceOnCountZero, "rip")
  , ("rep decrements rcx before the string operation reads it",
     wrongRepDecrementFirst, "rip")
  , ("the repeat count is decremented at the OPERAND width",
     wrongRepCountWidth, "rcx")
  , ("repe/repne test the INCOMING zf instead of the comparison's own",
     wrongRepZfIncoming, "rip")
  , ("rep decrements rcx even when it is already zero",
     wrongRepDecrementAtZero, "rcx")
  -- P1 BATCH 17 — the multiply-divide group.  Seven arms; three of them are
  -- about the FAULT rather than the arithmetic, because a group that refuses in
  -- most pre-states is a group whose agreement is mostly silence.
  , ("imul takes MUL's overflow rule", wrongImulUsesMulOverflow, "cf")
  , ("idiv rounds toward negative infinity instead of toward zero",
     wrongIdivFloorDivision, "rax")
  , ("div forgets that an over-wide quotient is also #DE",
     wrongDivNoQuotientOverflow, "refused")
  , ("div refuses on every divisor (the arm that proves the quotient is observed)",
     wrongDivAlwaysRefuses, "refused")
  , ("the byte multiply writes DX:AX instead of AH:AL", wrongMulBytePairInRdx, "rdx")
  , ("imul's three-operand form multiplies its destination", wrongImul3ReadsDest, "rax")
  , ("idiv's remainder takes the divisor's sign", wrongIdivRemainderSign, "rdx")
  -- P1 BATCH 18 — the compare-exchange pair and the double shifts.  Eight arms.
  -- ⭐ TWO OF THEM ARE THE SDM READ LITERALLY, and both were this batch's own
  -- first model: the differential rejected them with 80 and 51 disagreements
  -- before either became an arm.
  -- ⭐ AND TWO ARE THE OBSERVATION CONTROLS for `cmpxchg`'s two branches: each
  -- agrees with the model on every case of one branch, so what catches it is
  -- exactly the evidence that the other branch is reached.
  , ("cmpxchg always stores (the arm that proves the unequal branch is reached)",
     wrongCmpxchgAlwaysStores, "rax")
  , ("cmpxchg never stores (the arm that proves the equal branch is reached)",
     wrongCmpxchgNeverStores, "rcx")
  , ("cmpxchg writes DEST := TEMP on the unequal branch, as the SDM's pseudo-code says",
     wrongCmpxchgSdmWriteBack, "rcx")
  , ("xadd forgets to write its source", wrongXaddNoSourceWrite, "rcx")
  , ("shld/shrd perform the SDM's \"no operation\" at a count of zero",
     wrongDshiftZeroCountWritesNothing, "rax")
  , ("shld/shrd call a count EQUAL to the operand size bad parameters",
     wrongDshiftBadAtWidth, "rax")
  , ("shrd fills from the source's top bits, as shld does", wrongShrdFillsFromSourceTop, "rax")
  , ("shld/shrd take CF from the result instead of the original destination",
     wrongDshiftCfFromResult, "cf")
  -- P1 BATCH 21 — the eight-byte compare-exchange.  Five arms; the first two are
  -- the branch-observation pair, and the second of them is the reason
  -- `cmpxchg8bStates` exists.
  , ("cmpxchg8b always stores (the arm that proves the unequal branch is reached)",
     wrongCmpxchg8bAlwaysStores, "mem@0000000000001fe0")
  , ("cmpxchg8b never stores (the arm that proves the equal branch is reached)",
     wrongCmpxchg8bNeverStores, "mem@0000000000001fe0")
  , ("cmpxchg8b compares EAX alone against the low half of the memory operand",
     wrongCmpxchg8bCompares32, "zf")
  , ("cmpxchg8b merges EDX:EAX into RDX:RAX instead of zero-extending",
     wrongCmpxchg8bMergesRegisters, "rdx")
  , ("cmpxchg8b stores EBX:ECX instead of ECX:EBX",
     wrongCmpxchg8bStoresSwapped, "mem@0000000000001fe0")
  -- ⭐⭐ P2 ITEM 1 (BATCH 22) — the segment base.  Four arms; the note above
  -- their definitions says why they are four claims and not four spellings.
  , ("a segment override is ignored", wrongSegBaseIgnored, "rax")
  , ("fs and gs read each other's base", wrongSegFsGsSwapped, "rax")
  , ("lea adds the segment base (the split that is the whole item)",
     wrongLeaAddsSegBase, "rax")
  , ("a segmented STORE lands at the effective address", wrongSegStoreUnsegmented,
     "mem@0000000000001fe0")
  -- ⭐⭐ P2 ITEM 2 (BATCH 23) — the LOCK vocabulary.  Four arms on the two
  -- OBSERVABLE edges (which forms are #UD, and the un-declined `xchg`), because
  -- the value channel cannot distinguish locked from unlocked at all.
  , ("the lock prefix is ignored, so an illegal lock executes", wrongLockIgnored,
     "mem@0000000000001fe0")
  , ("the lockable list is widened to any memory destination",
     wrongLockableIsAnyMemDest, "mem@0000000000001fe0")
  , ("the lockable list drops xadd and cmpxchg8b", wrongLockableOmitsRmw, "refused")
  , ("xchg at memory still refuses (the model before this batch)",
     wrongXchgMemStillRefuses, "refused")
  -- ⭐⭐ P2 ITEM 3 (BATCH 24) — the 64-bit immediate.  ONE arm, because there is
  -- exactly one thing about this form the model could get wrong.
  , ("movabs re-derives its immediate through the imm32 path",
     wrongMovabsImm32Path, "rax")
  -- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 2 — the first arms that are wrong RULES about
  -- vector arithmetic rather than a clobbered channel.
  , ("a packed add/subtract uses 64-bit lanes whatever the mnemonic says",
     wrongVbinLaneWidth, "xmm0")
  , ("psub computes SRC - DEST", wrongVbinSubReversed, "xmm0")
  , ("movdqa/movdqu ignore their register fields", wrongVmovFixedRegisters, "xmm4")
  , ("a packed operation writes ZF", wrongVbinWritesFlags, "zf")
  -- ⭐⭐ P2 VECTOR WAVE, BATCH 3 — the memory forms.
  , ("a vector load reads only eight bytes", wrongVload8Bytes, "xmm0")
  , ("a vector store writes only eight bytes", wrongVstore8Bytes,
     "mem@0000000000001fe0")
  , ("movdqu applies movdqa's alignment check", wrongVmovduAlsoAligns, "refused")
  -- ⭐⭐ P2 BATCH 20 — MOVHPS. All three share the substring `movhps` (D117).
  , ("movhps loads into the LOW quadword", wrongMovhpsLoadsLow, "xmm0")
  , ("movhps CLEARS the low half instead of preserving it", wrongMovhpsClearsLow,
     "xmm0")
  , ("movhps stores the LOW quadword", wrongMovhpsStoresLow,
     "mem@0000000000001fe0")
  -- ⭐⭐ P2 BATCH 22 — PREFETCHh. Two arms, and no third: see the comment above
  -- `wrongPrefetchFaults` for why the hint field gets none.
  , ("prefetch faults on its operand", wrongPrefetchFaults, "refused")
  , ("prefetch loads its operand into rax", wrongPrefetchLoads, "rax")
  -- ⭐⭐ P2 VECTOR WAVE, BATCH 5 — the cross-file moves, all three about ZEROING.
  -- ⭐ RESTORED WITH ITS VECTORS (D95).  It was removed at batch 5 when the two
  -- into-XMM vectors went, because an arm no vector can distinguish is a false
  -- entry in this list. `knownDivergences` brought the vectors back, so the arm
  -- has a subject again — and note that it plants EXACTLY the mistake x86isa
  -- makes, which is why it must be compared against the Lean model and not the
  -- oracle: `driveWrong` passes `[]` for the divergence list.
  , ("movd/movq into XMM merge instead of clearing the upper bits",
     wrongVmovgPreservesUpper, "xmm0")
  , ("movq xmm,xmm copies all 128 bits instead of zeroing the upper quadword",
     wrongVmovqCopiesAll, "xmm0")
  , ("movd out of XMM does not zero-extend its 32-bit GPR write",
     wrongVmovgFromXNoZeroExtend, "rcx")
  -- ⭐⭐ P2 VECTOR WAVE, BATCH 7 — the unpack group: which bits, not what value.
  , ("punpckl and punpckh read each other's half", wrongUnpackHalf, "xmm0")
  , ("an unpack interleaves source-first instead of destination-first",
     wrongUnpackOrder, "xmm0")
  -- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 11 — the move family.  The first two are the
  -- batch's claim in its two directions; neither alone would say it.
  , ("movss/movsd from a register ZERO the upper bits instead of preserving them",
     wrongVmovsZeroesUpper, "xmm0")
  , ("movss/movsd from memory MERGE into the upper bits instead of clearing them",
     wrongVmovsldMergesUpper, "xmm0")
  , ("movss/movsd ignore their register fields", wrongVmovsFixedRegisters, "xmm4")
  , ("movss and movsd swap widths", wrongVmovsWidthSwapped, "xmm0")
  , ("a scalar store writes all sixteen bytes", wrongVmovsstStoresAll,
     "mem@0000000000001fe0")
  -- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 0 — the harness.  One arm, and it is the whole
  -- claim: a planted XMM difference must be CAUGHT before one line of vector
  -- semantics is written.
  , ("an XMM register is clobbered (the harness's own red arm)",
     wrongXmmClobbered, "xmm3")
  -- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 13 — THE PACKED SHIFTS.  Four arms, and the
  -- first two are the batch: each is a model a careful reader would write, and
  -- each is bit-identical to the right one over a whole regime of counts.
  , ("a packed shift takes its count MODULO the lane width",
     wrongVshiftModuloCount, "xmm0")
  , ("a packed shift reads only the low BYTE of a register/memory count",
     wrongVshiftLowByteCount, "xmm0")
  , ("pslldq/psrldq are modelled as 64-bit-lane bit shifts",
     wrongVshiftdqIsLaneWise, "xmm0")
  , ("psraw/psrad shift in zeros instead of the sign bit",
     wrongVshiftAritheticIsLogical, "xmm0")
  -- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 14 — THE PERMUTE GROUP.  Three arms, one per way
  -- the group can be got wrong that a green run would otherwise hide.
  --
  -- ⛔ THERE IS NO FOURTH ARM FOR THE ALIGNMENT RULE, AND ITS ABSENCE IS STATED
  -- RATHER THAN LEFT AS A GAP: every memory vector in this table is at a
  -- 16-byte-aligned address, so a model with the `#GP` branch deleted agrees
  -- with this one on all of them.  That rule is gated by the kernel
  -- (`vshufm_unaligned_faults`, `vshiftm_unaligned_faults`) and its red
  -- direction was demonstrated by deleting each branch in turn — each took its
  -- OWN theorem down and no other.
  , ("the permute's immediate fields are read in reverse order",
     wrongVshufReversedFields, "xmm0")
  , ("the permute reads its DESTINATION instead of its source",
     wrongVshufPermutesInPlace, "xmm2")
  , ("pshuflw/pshufhw permute all eight words instead of four",
     wrongVshufWholeRegisterWords, "xmm0")
  -- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 15 — and the FIRST of these two is the arm D91
  -- recorded as impossible to write.  It reports in `refused`, not in a value.
  , ("a packed binary operation ignores its 16-byte alignment requirement",
     wrongVbinmIgnoresAlignment, "refused")
  , ("the packed binary memory form has its operands swapped",
     wrongVbinmOperandsSwapped, "xmm0")
  -- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 17 — the packed compares.
  , ("pcmpgt compares its lanes as UNSIGNED",
     wrongVcmpUnsigned, "xmm0")
  , ("a packed compare writes 1 instead of an all-ones MASK",
     wrongVcmpBooleanNotMask, "xmm0")
  -- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 18 — `packuswb`.  ⚠️ BOTH ARM NAMES CONTAIN
  -- `packuswb`, so one filter selects both — the defect batch 17 hit, where two
  -- arms of one batch shared no substring and `selftest` ran half of them and
  -- said PASS (D116 §5).
  , ("packuswb truncates instead of saturating",
     wrongPackuswbTruncates, "xmm0")
  , ("packuswb reads its source as UNSIGNED, clamping negatives to 255",
     wrongPackuswbUnsignedSource, "xmm0") ]

/-- ⭐⭐ THE SHARD SELECTION, DEFINED ONCE.  `selftest-shard` runs the arms these
indices name, and `selftest-shards` checks these indices — so the gate exercises
the SAME function the shards do.

⛔ A FIRST DRAFT HAD THE GATE RECOMPUTE `i % n == j` FOR ITSELF, which is a
tautology wearing a gate's clothes: it agreed with the shard because both were
written from the same sentence, and it would have gone on agreeing if the shard's
rule changed underneath it.  That is the identical defect this session had
already made once, in `scripts/check_driver_cr4.py`'s selftest — a red arm that
cannot fail.  Naming a class confers no immunity from it.  One function, two
callers.

⚠️ STRIDE rather than contiguous block: arms differ in cost (the string group's
are dearer than the flag singles'), so a contiguous split would leave the
wall-clock decided by whichever shard inherited the expensive neighbours. -/
def shardIndices (k n : Nat) : List Nat :=
  (List.range selftestArms.length).filter (fun i => i % n == k - 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", out] =>
      let n := 8
      writeLines out (emitAll step n)
      IO.println s!"emitted {vectors.length} vectors × {(preStates 1 n).length} pre-states \
= {vectors.length * (preStates 1 n).length} cases → {out}"
      return 0
  | ["emit-acl2", out] =>
      let n := 8
      let cases := vectors.flatMap fun v =>
        (preStates 0x9E3779B97F4A7C15 n).zipIdx.map fun (pre, i) => acl2Case v i pre windows
      let hdr := ["; GENERATED by `x86lean-diff emit-acl2`. Do not edit.",
                  "; The differential cases as ACL2 data; scripts/x86isa_driver.lisp maps over it.",
                  "(in-package \"X86ISA\")", "", "(defconst *x86lean-cases*", " '("]
      writeLines out (hdr ++ cases ++ ["  ))"])
      IO.println s!"emitted {vectors.length * (preStates 1 n).length} ACL2 cases → {out}"
      return 0
  | ["emit-asm", out] =>
      let hdr := ["\t.text"]
      let body := vectors.map (fun v => s!"{v.id}:\t{v.asm}")
      writeLines out (hdr ++ body ++ ["\tnop"])
      IO.println s!"wrote {vectors.length} forms → {out}"
      return 0
  | ["expected-lengths", out] =>
      writeLines out (vectors.map (fun v => s!"{v.id} {v.instr.len} {v.bytes}"))
      return 0
  -- ⭐⭐ P2 ITEM 1: THE AST'S OWN ANSWER TO "does this vector carry a segment
  -- override", emitted so `seg_findings` in `scripts/check_encodings.py` can hold THREE
  -- independent sources against each other — the hand-written AT&T text, the
  -- ASSEMBLER's bytes, and this.  It replaces a Lean theorem that compared the
  -- AST against the bytes over all 784 vectors and cost 4 200 ms of kernel time
  -- doing it, almost all of that in `String.toList` (measured: 7.9 s for the
  -- byte half alone against 0.4 s for the AST half).  Reading a string is what
  -- Python is for; deciding a `match` is exhaustive is what the compiler is for.
  | ["segment-decls", out] =>
      -- ⭐ P2 ITEM 2 ADDED THE THIRD COLUMN.  The LOCK prefix has exactly the
      -- shape the segment override had — an AT&T token, a prefix byte, and an
      -- AST field — and it acquired the same three-source cross-check for the
      -- same reason, plus one this batch found the hard way: objdump prints
      -- `f0` as its OWN instruction line, so an ungated harness reads a locked
      -- vector as a one-byte instruction and a model that DROPPED the prefix
      -- would agree with that reading.
      writeLines out (vectors.map (fun v =>
        let eas := X86.Op.eas v.instr.op
        let segs := eas.filterMap Ea.seg
        s!"{v.id} {match segs with | [] => "-" | g :: _ => g.name} \
{if eas.any Ea.lock then "lock" else "-"}"))
      return 0
  | ["compare", a, b] =>
      let ra := parseRecords (← readLines a)
      let rb := parseRecords (← readLines b)
      let r := compareRecs knownDivergences ra rb
      IO.println (renderReport r)
      -- ⭐⭐ THE DIVERGENCE LIST, GATED IN THE OTHER DIRECTION.  A declared entry
      -- that produced NO disagreement in this run is a FAILURE, not a quiet
      -- success: either the oracle was fixed (delete the entry, and restore the
      -- vector to ordinary comparison) or THIS MODEL has drifted into agreeing
      -- with an answer the SDM and K say is wrong. Both need a human; neither
      -- may pass silently.
      --
      -- ⛔ WITHOUT THIS ARM THE LIST WOULD BE A PLACE TO HIDE RED — a declared
      -- divergence that no longer happens would go on excusing a field forever,
      -- and the excuse would be invisible because nothing prints an entry that
      -- never fires.
      let stale := knownDivergences.filter fun d =>
        !(r.details.any fun x =>
            x.cls == "oracle-divergence" && x.field == d.field
            && x.id.takeWhile (· != '/') == d.vec)
      if !stale.isEmpty then
        IO.println "⛔ DECLARED ORACLE DIVERGENCES THAT DID NOT OCCUR:"
        for d in stale do
          IO.println s!"   {d.vec} / {d.field} ({d.note}) — declared divergent \
against: {d.source}"
        IO.println "   Either the oracle was FIXED (delete the entry and let the \
field be compared again) or this model has drifted into agreeing with a \
known-wrong answer. A divergence list is only honest while every entry in it is \
still true."
        return 1
      if r.unexplained > 0 || r.missing > 0 || r.leaks > 0 then return 1 else return 0
  -- ⭐ `selftest <substring>` RUNS ONLY THE ARMS WHOSE NAME MATCHES, and it
  -- exists because of what a deletion probe costs.  Every batch here tests its
  -- "is this coverage load-bearing?" claim by DELETING the coverage and
  -- re-running the arm that depends on it (D13, D14, batch 5's constant, D21) —
  -- and a full `selftest` re-emits the whole vector table twice per arm,
  -- twenty-three times over, which at batch 10's size is about eleven minutes
  -- for a question about one arm.
  --
  -- ⚠️ IT IS A FILTER, NOT A SECOND SELFTEST.  The arms it runs are the same
  -- arms, driven by the same `driveWrong`, and the no-argument form is
  -- unchanged and is what CI runs.  A probe mode that could pass while the real
  -- gate failed would be worse than the eleven minutes.
  -- ⭐⭐⭐ THE SHARDED SELFTEST (P2 vector wave, batch 4 — a CI cost repair).
  --
  -- Step 9 of `ci.yml` runs every arm over every vector, and BOTH numbers grow
  -- every batch: 23 arms over 46,320 cases at P1 batch 14 became 90 over 70,950
  -- here, ~2.6 min per arm marginal, i.e. hours. It is the dominant cost of CI
  -- and it parallelises perfectly, because the arms are independent by
  -- construction.
  --
  -- ⛔ AND SHARDING A COVERAGE GATE IS EXACTLY HOW A COVERAGE GATE SILENTLY
  -- STOPS COVERING. If the shard arithmetic and the CI matrix ever disagree,
  -- some arms run twice (harmless) or NEVER (a gate reporting CLEAN about arms
  -- nobody ran) — the defect this repository keeps finding, introduced into the
  -- instrument that finds it. So the partition is computed HERE, from
  -- `selftestArms.length`, and never written down anywhere else: growing the arm
  -- list cannot leave an arm uncovered. `selftest-shards` is the gate that says
  -- so, and `scripts/check_ci_shards.py` is what holds the CI matrix to the same
  -- `n`.
  --
  -- ⚠️ THE SPLIT IS BY STRIDE, NOT BY CONTIGUOUS BLOCK: arms differ in cost (the
  -- string group's are dearer than the flag singles'), and a contiguous split
  -- would put the expensive neighbours in one shard and leave the wall-clock
  -- decided by that shard alone.
  | ["selftest-shard", ks, ns] =>
      match ks.toNat?, ns.toNat? with
      | some k, some n =>
        if n == 0 || k == 0 || k > n then
          IO.println s!"⛔ bad shard {k}/{n}: need 1 ≤ k ≤ n"; return 2
        else
          let arms := (shardIndices k n).filterMap (fun i => selftestArms[i]?)
          IO.println s!"harness selftest — SHARD {k} of {n}: \
{arms.length} of {selftestArms.length} arms"
          let mut ok := true
          for a in arms do
            let r ← driveWrong a.1 a.2.1 a.2.2
            ok := ok && r
          if ok then IO.println s!"shard {k}/{n}: PASS ({arms.length} arms)"; return 0
          else IO.println s!"shard {k}/{n}: FAIL"; return 1
      | _, _ => IO.println "⛔ selftest-shard takes two numbers: k n"; return 2

  -- ⭐ THE PARTITION GATE.  Runs NO arm — it is a property of the arithmetic
  -- alone — so it costs milliseconds and can be run on every push beside the
  -- shards it describes.  It asserts that shards 1..n TOGETHER name every arm
  -- EXACTLY ONCE: no arm missed (a silent coverage loss) and none duplicated
  -- (wasted wall-clock that would also hide a miss elsewhere in the count).
  | ["selftest-shards", ns] =>
      match ns.toNat? with
      | some n =>
        if n == 0 then IO.println "⛔ n must be ≥ 1"; return 2 else
        let total := selftestArms.length
        let covered := (List.range n).flatMap fun j => shardIndices (j + 1) n
        let sorted := covered.mergeSort (· ≤ ·)
        let expected := List.range total
        if sorted == expected then
          IO.println s!"shard partition gate: CLEAN — shards 1..{n} name all \
{total} arms exactly once"
          return 0
        else
          IO.println s!"⛔ shard partition gate: FAIL — shards 1..{n} name \
{sorted.length} arm slots for {total} arms; some arm is missed or duplicated"
          return 1
      | _ => IO.println "⛔ selftest-shards takes a number"; return 2

  | ["selftest", pat] =>
      let arms := selftestArms.filter (fun a => ((a.1.splitOn pat).length > 1))
      if arms.isEmpty then
        IO.println s!"no selftest arm matches \"{pat}\" — names are:"
        for a in selftestArms do IO.println s!"  {a.1}"
        return 2
      IO.println s!"harness selftest (filtered by \"{pat}\") — {arms.length} of \
{selftestArms.length} arms:"
      let mut ok := true
      for a in arms do
        let r ← driveWrong a.1 a.2.1 a.2.2
        ok := ok && r
      if ok then IO.println "filtered selftest: PASS"; return 0
      else IO.println "filtered selftest: FAIL"; return 1
  -- P1 BATCH 14: the `undefined` column on its own, so the gate is CHEAP to
  -- probe.  A discipline expensive to exercise gets exercised less; the full
  -- selftest is twenty minutes and this is seconds.
  | ["undefined-column"] =>
      -- ⛔ AND THE LEAK CHECK RUNS HERE TOO, because the batch that added it
      -- could not probe it: `driveWrong` compares two models and never looks at
      -- `Report.leaks`, so an arm that broke `undefinedLeaked` still reported
      -- PASS. The leak count was reachable only through the no-argument
      -- selftest's control — twenty-one minutes — which is a discipline
      -- expensive enough to exercise that it stops being exercised.
      let ok ← checkUndefinedColumn 4
      let recs := parseRecords (emitAll step 4)
      let leaks := (recs.filter (·.leak)).length
      if leaks == 0 then
        IO.println s!"  ✔ oracle leaks: 0 of {recs.length} cases (every undefined \
register equals the AST-level declaration)"
      else
        IO.println s!"  ⛔ oracle leaks: {leaks} of {recs.length} cases — an oracle bit \
reached something no form declares undefined, or a declared register did not move"
      return (if ok && leaks == 0 then 0 else 1)
  | ["selftest"] =>
      -- ⛔ THIS BRANCH USED TO BE TWENTY-THREE HAND-WRITTEN `driveWrong` CALLS
      -- WITH TWENTY-THREE HAND-NAMED BINDINGS AND A TWENTY-THREE-TERM
      -- CONJUNCTION, while `selftestArms` — introduced one batch earlier for the
      -- filtered probe — carried a doc comment claiming the two "cannot drift
      -- apart".  They had already drifted: the table was read ONLY by the
      -- filtered mode, so an arm added to it ran in a probe and NEVER IN CI.
      -- P1 batch 11 added four arms, watched them pass under `selftest <pat>`,
      -- and found the no-argument form still announcing "twenty-three".
      -- ⇒ The literal in the banner was the honest half; the doc comment was the
      -- lie, and a reassuring comment is what lets a false claim survive.
      -- See docs/DECISIONS.md D29.
      IO.println s!"harness selftest — {selftestArms.length} deliberately wrong \
models, each must be caught:"
      let mut ok := true
      for (name, wrong, field) in selftestArms do
        let caught ← driveWrong name wrong field
        ok := ok && caught
      -- and the control: the correct model against itself must be SILENT
      let good := parseRecords (emitAll step 4)
      let r := compareRecs [] good good
      let silent := r.unexplained == 0 && r.explained == 0 && r.missing == 0 && r.leaks == 0
      if silent then
        IO.println s!"  ✔ control: the model against itself is silent ({r.matched}/{r.cases} \
cases identical, 0 oracle leaks)"
      else
        IO.println s!"  ⛔ control: the model DISAGREES WITH ITSELF — {renderReport r}"
      -- P1 BATCH 14: the published `undefined` column against what is drawn.
      let colOk ← checkUndefinedColumn 4
      if ok && silent && colOk then
        IO.println s!"harness selftest: PASS ({selftestArms.length} arms + control \
+ undefined-column)"
        return 0
      else
        IO.println "harness selftest: FAIL"
        return 1
  -- ⭐⭐ P1 BATCH 19: THE NUMBER BELOW IS NO LONGER A HAND-MAINTAINED LITERAL.
  -- `scripts/claimed_forms.py` DERIVES it, and `--check` gates the published
  -- sentence against the derivation on every push.  Everything from here to the
  -- coverage command is now HISTORY: eighteen batches of counting rules, kept
  -- because the way they failed is the reason the tool exists.
  --
  -- ⛔ HOW THEY FAILED.  Each rule was right about its own batch and none of
  -- them was ever checked against the others, so the sum was never audited in
  -- EITHER direction.  It was SIXTEEN LOW — and low is exactly the error
  -- that survives, because an over-claim reads as a mistake and an under-claim
  -- reads as modesty.  The base-name arithmetic could not have got it right:
  -- 143 of the 525 rows are ALIAS SPELLINGS of another row (`jz` for `je`,
  -- `sal` for `shl`), so `$4 ~ /^(je)$/` claims three rows and leaves three
  -- identical ones behind, and no amount of care with the pattern fixes a rule
  -- that counts spellings when the machine counts encodings.
  --
  -- ⚠️ THE HISTORY BELOW IS STILL WORTH READING, and batch 12
  -- nearly got the literal wrong by two.  THE COUNTING RULE, since it is not obvious and
  -- the roster does not state it: a "form" is a ROW of `p1/roster.tsv`, NOT a
  -- width-expanded form.  The file has 525 rows and 1193 width-expanded forms,
  -- and the widths column reads `lw` (two widths) on rows that count ONCE.
  -- Verified against batch 11, which claimed 15 and has exactly 15 rows.
  --
  --   awk -F'\t' 'NR>2 && $4 ~ /^(nop|ud2|retq|leaveq)$/' p1/roster.tsv | wc -l
  --
  -- P1 BATCH 13 ran it and got 8 — `sarx`, `shlx`, `shrx` and `movbe` at two
  -- shapes each — taking 388 to 396.  The shapes the roster names for them are
  -- `r,r,r`/`r,m,r` and `r,m`/`m,r`, and there is a vector for every one.
  --
  -- P1 BATCH 14 ran it for `popcnt|lzcnt|tzcnt|bsf|bsr|blsi` and got 12 — six
  -- mnemonics at `r,r` and `r,m` — taking 396 to 408.
  --
  -- ⭐ P1 BATCH 15 ran it for `movs|stos|lods|cmps|scas` and got 21, WHICH IS
  -- NOT THE NUMBER TO ADD.  Eleven of those rows carry a `rep`/`repe`/`repne`/
  -- `repnz`/`repz` PREFIX (column 3) and are loop control, not data movement;
  -- this batch claims only the ten unprefixed rows.  The filtered count is
  --
  --   awk -F'\t' 'NR>2 && $4 ~ /^(movs|stos|lods|cmps|scas)$/ && $3 == ""' \
  --     p1/roster.tsv | wc -l
  --
  -- ⚠️ and the unfiltered form of that command is exactly how this literal would
  -- have been over-stated by eleven.  The base-name rule alone is not the
  -- counting rule whenever a group has prefixed variants — the FIRST group in
  -- this roster that does.  408 to 418.
  --
  -- ⭐ P1 BATCH 16 CLAIMS THOSE ELEVEN, and the counting command is batch 15's
  -- with the filter INVERTED — `$3 != ""` rather than `$3 == ""` — so the two
  -- batches partition the twenty-one rows exactly and neither can double-count:
  --
  --   awk -F'\t' 'NR>2 && $4 ~ /^(movs|stos|lods|cmps|scas)$/ && $3 != ""' \
  --     p1/roster.tsv | wc -l
  --
  -- 3 `rep` + 2 each of `repe`/`repne`/`repnz`/`repz` = 11.  418 to 429.
  -- ⚠️ ELEVEN ROWS, THREE ROSTER MNEMONICS, TWENTY-EIGHT VECTORS: the three
  -- counts differ on purpose and each is right for its own question.  `repz`
  -- and `repnz` are roster rows with no mnemonic and no vector of their own
  -- (they assemble to bytes identical to `repe`/`repne`), and each mnemonic
  -- spans several string ops at four widths.
  --
  -- ⛔⛔ AND BATCH 14 FOUND THE SENTENCE BELOW A WHOLE BATCH STALE.  The
  -- per-batch narrative stopped at "12 — the near-free four" while this count
  -- already read 396, which INCLUDES batch 13: batch 13 updated the number and
  -- not the prose, and every gate stayed green because nothing read the prose.
  -- ⇒ The literal has this comment and a stated counting rule, and it survived
  -- thirteen batches; the sentence beside it had neither, and it did not.
  -- `scripts/check_coverage_prose.py` now gates the narrative against the
  -- `docs/DIFFERENTIAL-P1-BATCH<N>.md` files, which are a per-batch artifact
  -- maintained for another reason and therefore cannot drift in step with it.
  --
  --
  -- ⭐⭐ P1 BATCH 17 COUNTS BY BASE NAME AND *NOT* BY FAMILY, and the difference
  -- is a finding rather than a preference.  The handover named this batch as
  -- "families 14/23/27/24".  Family 23 was already discharged (it is eight of
  -- batch 16's eleven prefixed rows); `cmpxchg` and `xadd` occupy family 10 as
  -- well as 14; `shld` and `shrd` occupy family 40 as well as 24.  A batch
  -- scoped by family number would have claimed rows it did not implement and
  -- orphaned rows it did.
  --
  --   awk -F'\t' 'NR>2 && $4 ~ /^(mul|imul|div|idiv)$/' p1/roster.tsv | wc -l
  --
  -- 12 — eight in family 27 (`mul`/`imul` at six shapes) and four in family 24
  -- (`div`/`idiv` at `r` and `m`).  These four base names occur in NO other
  -- family, so the rule cannot double-count with any earlier batch, and it
  -- splits family 24 exactly as batches 15 and 16 split the string family:
  -- `shld` and `shrd` are that family's other EIGHT rows and are NOT claimed
  -- here.  429 to 441.
  -- ⚠️ TWELVE ROWS, FOUR ROSTER MNEMONICS, THIRTY-TWO VECTORS — three counts
  -- again, and `imul` is the reason the middle one is not eight: it is ONE
  -- roster base name spread over SIX shapes and TWO of this model's
  -- constructors.
  -- Making this derivable needs a claimed-forms table keyed to the roster's
  -- (base, shape) pairs — real work, and a better batch than a tack-on. Until
  -- then: COUNT THE ROWS with the command above and do not reason from widths.
  --
  -- ⭐ P1 BATCH 18 RE-DERIVED ITS OWN SCOPE RATHER THAN READING THE HANDOVER'S,
  -- which is D49's whole point, and the two agreed — the agreement being the
  -- result of the check and not a reason to have skipped it:
  --
  --   awk -F'\t' 'NR>2 && $4 ~ /^(xadd|cmpxchg|shld|shrd)$/' p1/roster.tsv | wc -l
  --
  -- 12 — FOUR base names spread over FOUR families (10 and 14 for `cmpxchg` and
  -- `xadd` at `m,r` and `r,r`; 24 and 40 for `shld`/`shrd` at `r,r,cl|imm` and
  -- `m,r,cl|imm`).  Family 24's other four rows are `div`/`idiv`, discharged by
  -- batch 17, so the base-name rule cannot double-count.  441 to 453.
  -- ⚠️ TWELVE ROWS, FOUR ROSTER MNEMONICS, FORTY-ONE VECTORS — the three counts
  -- again, and the reason the last one is large is that `shld`/`shrd`'s
  -- IMMEDIATE is not a sample but a BRANCH SELECTOR: 0, 1, 5, 16 and 20 pick out
  -- the no-operation, the OF-defined, the ordinary, the exact-boundary and the
  -- bad-parameters cases, and none of them can be reached from another.
  | ["coverage", out] =>
      let (e, f, ab) := tierCounts tableP0
      let hdr := "<!-- GENERATED by `lake exe x86lean-diff coverage`. Do not edit by hand. -->\n\n\
# x86lean coverage\n\n\
Roster: " ++ toString rosterSize ++ " mnemonics in " ++ toString vectors.length ++ " differentially tested forms, covering **500 of the 525 rows** in `p1/roster.tsv` — which are **351 of the 374 distinct machine forms** those rows describe, because 149 rows are alias SPELLINGS or narrowings of another row (`jz` for `je`, `sal` for `shl`, `stos m` for `stos -`, `cmp m,label` for `cmp m,imm`) and 2 describe no encoding at all. Of the 500, **375 are spelled by a vector** and 125 are the same encoding under a different spelling. ⭐ ALL SIX NUMBERS ARE GATED — `scripts/claimed_forms.py` DERIVES them from two independent sources (every vector's own AT&T text and every roster row's own encoding, assembled by clang) and CI fails if this sentence disagrees. ⚠️ They are written here and CHECKED there, not computed here: this sentence said `ARE DERIVED` until P2 batch 23, which is the stronger word and was not true of the literals in front of it. Until P1 batch 19 the first was neither derived nor gated, and it was SIXTEEN LOW.\n\n\
P0 shipped twenty scalar mnemonics. P1 has added, by batch: 1 — AND/OR/XOR to a \
register at every width and shape; 2 — ADC/SBB, the first forms whose RESULT \
reads a flag; 3 — CMP/TEST at every operand shape, the first memory operand in \
a destination that is read and never written, and the first RIP-relative \
vector; 4 — the ALU read-modify-write to memory; 5 — every condition at rel8 \
and rel32, plus JRCXZ/JECXZ; 6 — SETcc and CMOVcc, 120 roster forms over two \
`step` cases; 7 — the shift group at a memory destination, plus SAR; 8 — the \
rotate group, ROL/ROR/RCL/RCR; 9 — the bit-test group, BT/BTS/BTR/BTC (the \
bit-string `m,r` shape declined, see D23); 10 — the width-changing and \
two-destination moves: MOVZX/MOVSX/MOVSXD, the six accumulator sign-extensions, \
XCHG and BSWAP, the first forms with a source width unlike their destination's \
and the first that write two registers, and the only batch so far that writes \
NO FLAG AT ALL (`xchg` at memory and `bswap` at 16 bits declined, see D25); 11 — \
the loop group LOOP/LOOPE/LOOPNE at both counter widths and the five \
flag-control singles CLC/STC/CMC/CLD/STD, which between them added the first \
instructions able to write DF at all (see D27); 12 — the near-free four of \
family 7, NOP at its three shapes plus UD2, RETQ and LEAVEQ: the first form \
whose whole meaning is a FAULT, and the first two forms that needed a new \
PRE-STATE to be reachable at all (see D34); 13 — the flagless shifts \
SARX/SHLX/SHRX and the byte-swapping move MOVBE, the table's first \
three-operand rows, whose `r,m,r` shape broke a memory-destination gate that \
had been repaired twice (see D36, D37); 14 — the bit-counting group \
POPCNT/LZCNT/TZCNT/BSF/BSR/BLSI, six mnemonics on one operand shape whose flag \
rules agree on almost nothing, and the first UNDEFINED DESTINATION in the \
model: `bsf`/`bsr` at a zero source leave the destination REGISTER undefined \
rather than unmodified, so the oracle-leak check had to learn the difference \
between an oracle bit that is admitted and one that is not (see D40); 15 — the \
string group MOVS/STOS/LODS/CMPS/SCAS at all four widths, the first forms in \
the model with NO OPERAND FIELD (their addresses are RSI and RDI by opcode) and \
the first that READ DF, which had been a bit only `cld`/`std` could write since \
batch 11; the batch widened the data window so a pointer moving BACKWARD stays \
observable (see D42) and added the first pre-states in which a pointer update \
CARRIES across a width boundary (see D43); 16 — the REPEAT PREFIXES over that \
same data movement, REP/REPE/REPZ/REPNE/REPNZ, eleven roster rows in which the \
model's RIP is for the first time sometimes its OWN address: x86isa performs \
exactly one iteration per step and signals a repeat by NOT advancing RIP, and \
COUNT EXHAUSTION DOES NOT ADVANCE IT EITHER — the count is tested only on entry, \
so `rep movs` with RCX=1 copies, leaves RCX=0, and stays put (see D46).  The \
batch needed no new pre-state: `adversarial` already contains the single value \
of RCX that separates that rule from the obvious one; 17 — the multiply-divide \
group MUL/IMUL/DIV/IDIV, twelve roster rows over two constructors, whose \
results are TWICE the operand width and live in `RDX:RAX` — or, at eight bits \
alone, in `AH:AL`, one register — and whose two divisions are the first forms \
in this model to REFUSE ON THEIR OPERANDS rather than on their opcode: measured \
against the oracle on all eighty-two pre-states before a vector existed, `div` \
and `idiv` fault in 51%-84% of them, so the batch's danger was never a wrong \
answer but a quotient nothing asks for, and the arm that refuses on every \
divisor is what proves it is asked (see D49, D50); 18 — the compare-exchange \
pair CMPXCHG/XADD and the double-precision shifts SHLD/SHRD, twelve roster rows \
over three constructors and four families, in which the SDM's own pseudo-code \
was found WRONG TWICE ABOUT 64-BIT MODE and both times in the same place: a \
register write the manual describes as a no-op is not one at 32 bits, where \
every write zero-extends.  CMPXCHG's `DEST := TEMP` on the unequal branch does \
not happen (80 differential cases) and SHLD/SHRD's \"IF COUNT = 0 THEN no \
operation\" writes the destination anyway (51 more) — ACL2 x86isa and K agree \
against the manual on both, and K's rule for the second carries the comment \
`// Intel Bug`.  SHLD/SHRD also bring this model its SECOND undefined \
DESTINATION, undefined here because of the COUNT rather than the source, in \
thirty-five of the eighty-two pre-states at `.w`; the 16-bit MEMORY destination \
with a count above 16 is REFUSED rather than answered, because an oracle bit in \
memory is the one thing the leak check has no declaration channel for (see D52, \
D53, D54); 19 — NO NEW FORMS AT ALL. This batch made the coverage number \
DERIVED. It had been a hand-maintained literal whose value was a running sum of \
eighteen independent `awk` rules, one written in a comment at each batch that \
added to it, and nothing had ever checked that those rules PARTITION the \
roster — batch 18's handover could account for only 32 of the 72 rows it \
believed remained. `scripts/claimed_forms.py` now computes the claim from two \
sources that are not derived from each other: every vector's own AT&T text, \
parsed against the roster's shape vocabulary, and every roster row's own \
encoding, assembled by clang. A vector may claim only a row whose encoding it \
MATCHES, so a mis-parse dies rather than counting. The literal was SIXTEEN LOW, \
and the DIRECTION is the finding: an over-claim reads as a mistake and an \
under-claim reads as modesty, so nothing had ever looked. The same derivation \
answers the residue batch 18 could not close — 149 of the 525 rows are alias \
SPELLINGS of another row, which is why base-name arithmetic could never \
partition them — and it finds two rows that describe NO ENCODING AT ALL: \
`jecxz rel32` and `jrcxz rel32`, which the assembler refuses because those \
instructions have only an 8-bit displacement (see D56, D57, D58); 20 — the shapes this model could always EXPRESS and had never been asked: the \
memory-DESTINATION and accumulator-short forms of ADD/SUB/ADC/SBB, `mov m,imm`, \
`neg`/`not` at memory, `push imm/m`, `pop m`, and the indirect JMP/CALL through \
memory — 28 roster rows and 71 vectors, with NOT ONE LINE of `X86/Semantics.lean` \
changed, because `Op` is keyed by mnemonic with a SHARED operand pair and these \
shapes have been expressible since P0.  The batch's finding is what its own green \
run did not contain: `unexplained=0` on the FIRST run with every one of the 5822 \
new cases MATCHED, and THREE ORDER CLAIMS in `step` that nothing in the repository \
could distinguish — `.push` reads its source before RSP moves, `.pop` computes its \
destination address after, and `.call .indirect` reads its target before pushing.  \
Every push/pop/call vector that existed named an operand that does not move with \
RSP, so a model with any of the three orders reversed was BIT-IDENTICAL to this \
one, and nineteen batches of agreement said nothing whatever about those lines.  \
Two are now tested by four vectors and three arms, with the pairing checked by \
DELETING the vectors and re-running the arms; the third cannot be, because \
`callq *(%rsp)` is refused by x86isa in 80 of the 82 pre-states and agreement where \
both models refuse is agreement about nothing.  The batch also MEASURED a DECLARED \
list — `movnti` is NOT available work, 82/82 refused, confirmed twice over by an \
identical-shape control that executed 82/82 in the same run and by x86isa's own \
section doc — though it recorded that finding in prose and in no gate, so the \
tool went on printing `movnti` as available until batch 21 — and it replaced the \
`Tests.Coverage` kernel ceiling's UNIT: the \
per-ROW ceiling divides by a variable the cost is not linear in, and the \
per-DECLARATION repair that batch 17 recorded as blocked was blocked only in the \
design it considered (see D59, D60, D61, D62); 21 — CMPXCHG8B, the LAST \
claimable row of the roster, and the batch that closes AVAILABLE WORK to ZERO.  \
One constructor with no `Size` field and a memory-only destination, whose flag \
rule is the OPPOSITE of the `cmpxchg` beside it — ZF alone, measured against the \
oracle over all 82 pre-states with `cmpxchg` as a control in the same run, \
because two forms of one family with opposite flag rules is where a reader \
assumes.  Its EQUAL branch was reachable in exactly ONE of the 82 inherited \
pre-states, and that one by accident: `mkPre` puts `~a` in RDX and `c` at the \
memory operand, so the comparison succeeds only where `c = a` and `a`'s high half \
is the complement of its low half.  Four purpose-built states make both branches \
deliberate — and the FIRST design of them was refused by a gate, \
`memory_operand_mirrors_rcx`, which named the cheaper build: move the accumulator \
pair, not the memory, and batch 3's invariant survives untouched.  ⛔ The comment \
justifying two of the four was FALSE and was caught by counting rather than \
believing: it claimed no inherited state could tell a half-width comparison from a \
full one, and 21 of the 82 already could.  The batch also stopped the residue's \
unavailable list being DECLARED: it is MEASURED now, by executing one form per \
mnemonic on the oracle with two positive controls, gated in BOTH directions and \
driven red-first in six seconds — the repair D61 named a batch earlier and wrote \
into two documents and no gate.  And `Tests.Coverage` lost 42% of its kernel time \
to a fact nobody had measured: the kernel's reduction cache spans a DECLARATION \
and not two, so six theorems were re-reducing the same sweeps (see D63, D64, \
D65).\n\n\
P2 has added, by batch: 1 — THE FS/GS SEGMENT BASE IN `Ea`, the first of the \
three scalar capabilities the Captain ordered into P2 and the first addition in \
this repository priced by MEASURED DEMAND rather than by a roster row: 29,943 \
instructions of the census's assembly class carry an FS or GS override, 3.26% \
of the uncovered gap, and the commonest of them is the stack-protector load \
`movq %fs:0x28, %rax` in the prologue of most compiled functions.  It claims NO \
new roster row — a segment override is a PREFIX on rows already claimed — so \
the roster's 498 does not move; what moves is what the model can execute.  In \
64-bit mode CS/DS/ES/SS have no base and FS/GS keep a 64-bit MSR-loaded one \
(SDM Vol. 3A §3.4.4), so the whole addition is two fields on `Cpu`, one field on \
`Ea`, and a SPLIT: `Ea.offset` is the effective address that `lea` writes and \
`Ea.addr` is the linear address a memory access uses, because LEA adds no \
segment base and a single function would have been wrong for it.  The batch's \
two findings are both about COST and OBSERVABILITY rather than about \
semantics.  Two fields on `Cpu` — read by nothing else in the batch — blew the \
heartbeat limit on three inherited `bsf`/`bsr` frame proofs that closed by \
`rfl` over the whole record, because `undefVal` had never been given the frame \
lemmas `undefBit` has had since P0; the repair makes those proofs independent \
of the field count rather than raising a margin.  And the segment bases are \
INPUTS no instruction writes, so by D27 they are deliberately absent from the \
compared record and are observed only through the ADDRESS they produce — which \
is why every vector's displacement is chosen to land inside a watched window: \
`%fs:0x28` with the base dropped is address 0x28, where both models read zeros \
and would have agreed about nothing.  A third finding is a cost one that bought \
a stronger claim: the completeness check on the AST walk cost 4 200 ms of \
kernel time, almost all of it `String.toList` over 784 literals, and the \
ceiling's refusal replaced it with an EXHAUSTIVE `Op` match — the compiler \
answers completeness now, for every constructor rather than only the ones some \
vector uses — plus a three-source cross-check in the assembler gate (see D70, \
D71, D72, D73, D74); 2 — THE LOCK VOCABULARY, the second of the Captain's three \
additions and the one whose value is in what it UNBLOCKS rather than in its own \
frequency.  `Ea.lock`, `Op.lockable` — the SDM's nineteen-mnemonic list, \
TRANSCRIBED and not inferred, because a list derived from `the \
memory-destination forms we have` would have admitted `mov`, the shifts and \
every `cmp` — and ONE well-formedness test in `step`.  ⭐ It UN-DECLINES `xchg` \
at a memory operand: D25 refused that shape because its implicit LOCK is an \
atomicity claim a model with no vocabulary for it could neither make nor break, \
and the roster goes 498 -> 500 rows.  ⛔ THE ROSTER SAID IT WOULD UNBLOCK SIX \
ROWS AND IT UNBLOCKS TWO: the other four are D23's signed BIT-STRING shape, \
which no LOCK vocabulary touches, and that false sentence sat inside a document \
CI re-derives byte-for-byte — a derivation gate is a wrapper a false sentence \
can sit inside (D76).  ⛔ AND THE BATCH HAS NO ARITHMETIC: `lock addq` and \
`addq` are the same function in a single-step semantics, so what is observable \
is the two EDGES — which forms the prefix makes #UD, and the form it \
un-declined — and all four planted arms live there, two of them moving the \
lockable list in OPPOSITE directions.  The harness needed teaching too: objdump \
prints `f0` as its OWN instruction line, so a locked vector read as a ONE-BYTE \
instruction, and a model that silently DROPPED the prefix would have agreed \
with that one byte (D79) (see D76, D77, D78, D79, D80, D81, D82); 3 — `movabs`, \
THE 64-BIT IMMEDIATE MOVE, and the batch that is honest about being CHEAP.  \
`Operand.imm` has carried a full `BitVec 64` since P0 and the decoder is trusted \
to have done any extension, so `movabsq $imm64, %r64` reaches `step` as the same \
shape `movq $imm32, %r64` does and NO SEMANTICS CHANGES — P1 batch 20's finding \
again, a shape the model could always express and had never been asked.  What \
the three vectors DO test is the LENGTH path (ten bytes, the longest encoding in \
this table) and the DECODE-TRUST boundary at the one place it is tempting to \
re-derive: two of them carry values — `0x00000000ffffffff` and \
`0xffffffff00000000` — that no 32-bit immediate can sign-extend to, so the one \
plausible wrong decoder is caught and every other `mov r,imm` vector is \
unaffected.  ⛔ AND THE LENGTH PATH IS WHERE THE FINDING WAS: ten bytes fills \
objdump's byte column exactly, so its final byte abuts the TAB rather than a \
space, and `check_encodings.py` had been silently DROPPING THE LAST BYTE of any \
instruction that long — latent since P0, exposed only by the first form wide \
enough to reach it, and in the direction that matters: the gate would have read \
`len=9`, so a model that claimed 9 would have AGREED WITH IT (see D83, D84); 4 — \
THE VECTOR HARNESS, and NO INSTRUCTION AT ALL.  `x86l-post` reported 16 GPRs, \
RIP, the flags and two memory windows; the oracle EXECUTES the vector forms \
(measured, not assumed); so a vector form run on both sides would have been \
compared on NONE of its results — and an unobserved region does not report \
`unknown`, it reports AGREEMENT.  ⇒ `THE ORACLE EXECUTES IT` IS NOT `THE \
HARNESS CAN SEE THE ANSWER`, and the register file had to exist and be COMPARED \
before one line of vector semantics was written anywhere.  Sixteen 128-bit \
registers nested in ONE `Cpu` field (D71: a whole-record `rfl` costs \
O(fields), and sixteen flat ones would have cost eight times two), their frame \
lemmas written the day the field was added rather than when a proof needed \
them, a pre-state pattern that is deliberately NOT zero — all-zero on both \
sides is the unobserved-region trap in its purest form — and a cross-check \
across the language boundary with seven arms, including the two that catch a \
renderer which is defined and never CALLED.  ⚠️ Its claim is narrow on purpose: \
nothing in this roster writes XMM, so by D27 the registers are constants and \
the comparator is watching one; what the batch proves is that the CHANNEL \
exists, both models report it, they agree, and a planted difference is CAUGHT — \
64,746 cases for one clobbered register (see D85); 5 — THE FIRST VECTOR \
SEMANTICS: `movdqa`/`movdqu` register-to-register and the eleven packed integer \
operations PADDB/W/D/Q, PSUBB/W/D/Q, PXOR, PAND and POR, sixteen vectors that \
between them make batch 4's channel NON-VACUOUS — until this batch nothing \
wrote an XMM register, so by D27 the comparator was watching sixteen constants \
and agreeing about them.  `movdqa` and `movdqu` are ONE constructor with an \
`aligned` flag rather than one row: they are different OPCODES, so the model \
must not print one name for the other, and the flag is INERT between registers \
because the alignment rule is stated of a MEMORY operand — a claim, so a theorem \
(`vmov_aligned_irrelevant`) and not a comment.  The lane WIDTH lives in the kind \
and the lane COUNT is derived from it, never written beside it.  ⛔ THE BATCH'S \
FINDING IS AN ARM THAT DID NOT FIRE: `wrongVmovFixedRegisters` — every \
`movdqa`/`movdqu` moves xmm1 into xmm0 whatever it encodes — was BIT-IDENTICAL \
to the real model on every vector in the table, because both `vmov` vectors \
moved xmm1 into xmm0, so the comparator reported ZERO disagreements against a \
known-wrong model and `Op.vmov`'s register fields were decoded by nothing.  The \
comment on the arm ASSERTED it was covered, by a `.vbin` vector that cannot \
exercise `vmov`'s operands at all.  `movdqa_x4x5` and `movdqu_x4x5` exist \
because the arm failed, and the pairing is proven by the failure rather than \
claimed — P1 batch 20's rule again, asking what a predicted green does not \
contain.  ⚠️ And the arm that COULD have passed silently did not: a wrong LANE \
WIDTH is invisible unless some lane actually carries across its boundary, and \
computing every packed add at 64-bit lanes is caught in 355 cases, so the \
pre-state pattern does exercise the rule (see D90); 6 — THE VECTOR MEMORY \
FORMS, and the point at which `movdqa` and `movdqu` STOP BEING THE SAME \
INSTRUCTION: `Op.vload`/`Op.vstore` (two constructors rather than one over an \
operand pair, so `movdqa (%rax),(%rbx)` is UNREPRESENTABLE rather than checked), \
a 128-bit memory path composed from the 64-bit one every vector since P0 has \
exercised, and the 16-byte alignment rule.  ⛔ THE BATCH'S FINDING IS ABOUT THE \
ORACLE: an unaligned `movdqa` is #GP(0) in hardware, and ACL2 x86isa DOES NOT \
IMPLEMENT THE CHECK — measured by executing it at 0x2008 with CR4.OSFXSR set, \
where the oracle executes what silicon faults on.  A vector for it would be a \
ONE-SIDED REFUSAL in every pre-state, which `classify` rightly counts \
UNEXPLAINED, so the run would go red about a model that is RIGHT.  ⇒ THE ORACLE \
IS EVIDENCE, NOT THE SPECIFICATION, and this is the first time in this project \
that the difference has cost something: batch 18 found the SDM wrong twice and \
followed x86isa against it, and here the arrow reverses — the oracle is \
INCOMPLETE, and following it would make the model compute a result where \
hardware faults.  So the rule is carried by THEOREM instead of by run \
(`vload_unaligned_faults`, with `vload_unaligned_movdqu_runs` as the half that \
makes the pair discriminate), it is the weakest claim in the repository because \
it has NO SECOND SOURCE, and it is a named item for the hardware co-simulation \
lane where real silicon IS the oracle for it.  ⚠️ And one arm is DELIBERATELY \
ABSENT: `movdqa ignores its alignment requirement` cannot be caught by any \
vector that can exist, and an arm no vector can distinguish is not a weak test \
but a FALSE ENTRY in the gate's own inventory (see D91); 7 — MOVD and MOVQ \
ACROSS THE REGISTER FILES, rank 4 and rank 8 of the measured demand list, and \
THE BATCH IN WHICH THE DIFFERENTIAL FOUND A DEFECT IN THE ORACLE.  Five vectors \
were written and the run came back with 159 unexplained `spec` disagreements in \
exactly two of them: `movd %ecx,%xmm0` and `movq %rcx,%xmm0`, where **ACL2 \
x86isa MERGES the destination's upper bits instead of CLEARING them** — the same \
wrong model this batch had already planted as an arm and caught in 151 cases \
against the Lean side.  ⭐ AND IT IS NOT THIS REPOSITORY'S WORD AGAINST THE \
ORACLE'S: K's semantics, vendored and public, give `movd r32 -> xmm` as \
`concatenateMInt(mi(96, 0), …)` — ninety-six zero bits and then the datum — and \
SDM Vol. 2B says `DEST[127:32] <- 0`.  ⇒ THE THIRD SOURCE IS WHAT TURNS A \
DISAGREEMENT INTO A FINDING: with two models a red run says only that one of \
them is wrong, and the tempting reading — the oracle has 500 roster rows of \
credibility behind it — is the wrong one here.  ⚠️ The defect is DIRECTIONAL, \
which sharpens it: x86isa gets `movq %xmm1,%xmm0` and both out-of-XMM \
directions right, so the other three vectors stay and remain validated, and \
failing exactly two is the signature of a specific defect rather than vagueness. \
The two into-XMM vectors are removed, their rule carried by \
`vmovg_to_xmm_zeroes_upper`, and the arm that guarded them is removed WITH them \
because an arm no vector can distinguish is a false entry in the gate's own \
inventory.  ⚠️ THE COST, STATED PLAINLY: this repository now has TWO rules its \
oracle cannot check — the alignment fault (oracle incomplete) and this one \
(oracle wrong) — both proved, neither differentially validated, and removing a \
vector stops the test PERMANENTLY AND SILENTLY.  Both point at the same next \
mechanism: a declared known-divergence channel carrying its third-source \
citation, gated in BOTH directions so it fires when the divergence disappears \
(see D93); 8 — THE KNOWN-DIVERGENCE CHANNEL, and NO INSTRUCTION AT ALL.  Twice \
the differential has been right and the ORACLE wrong — `movdqa` unaligned, which \
x86isa does not fault on, and `movd`/`movq` into XMM, which it MERGES where the \
SDM and K both say CLEAR — and both times the remedy was to DELETE the vector, \
which stops that test PERMANENTLY AND SILENTLY: if x86isa were fixed tomorrow, \
nothing would notice.  `oracle-divergence` is now its own class in the header of \
every run, NOT matched and NOT explained, and the two deleted vectors are back \
in the table and compared again.  ⛔ A PLACE TO PUT DISAGREEMENTS IS A PLACE TO \
HIDE RED, so three things keep it honest: it is GATED IN THE OTHER DIRECTION (an \
entry that produces no disagreement FAILS, because either the oracle was fixed \
or this model has drifted into agreeing with a known-wrong answer); every entry \
carries an INDEPENDENT SOURCE by file and section, since a two-model \
disagreement names no culprit; and it is narrow by construction, one vector \
prefix and one field.  ⚠️ And `classify` takes the list as a PARAMETER — \
`driveWrong` passes the empty one, because the selftest compares this model \
against a deliberately wrong copy of ITSELF, where an oracle's defect is \
irrelevant, and the planted bug there is EXACTLY the mistake x86isa makes.  \
Probed both ways: a declared divergence that does not occur fails, and deleting \
a real entry brings its 81 disagreements straight back as `spec` (see D95); 9 — THE UNPACK \
(INTERLEAVE) GROUP, `punpckl` and `punpckh` at all four lane widths: the first \
vector operations here that COMPUTE NOTHING AND ONLY CHOOSE.  The rule is \
generalised once — `128/(2w)` pairs, each `dst[base+i] : src[base+i]` with the \
destination LOW, `base` selecting the low or high half — and as with `vlanes` \
the COUNT is derived from the width rather than passed beside it.  ⭐ Checked by \
EVALUATION before the oracle was asked: five hand-computed cases on a byte-ramp, \
with the expected values taken from objdump's own disassembly comment and from \
K's rule rather than from one reading of the manual.  ⚠️ AND ONE ARM MEASURES \
THE PRE-STATES RATHER THAN THE MODEL: `punpckl` and `punpckh` read DISJOINT \
halves, so a pre-state whose halves agreed could not tell them apart, and a \
green run would have said nothing about which half is read.  Written into the \
AST as a worry, then measured — both arms fire in 656 of 656 cases, so batch 0's \
pattern distinguishes the halves everywhere, and had the number come back small \
THAT would have been the finding (see D96); \
10 — THE MOVE FAMILY COMPLETED, `movaps`/`movups`/`movss`/`movsd`, ranks 2, 5, \
6 and 11 of the measured demand list — 59,840 instructions, 11.2% of the gap, \
the largest group available and NOT the one the candidate list ranked first.  \
⛔ THE BATCH'S FINDING IS THAT TWO OF THE TOP THREE RANKS COULD NOT BE BUILT AT \
ALL: `pmaddwd` (rank 1) and `psubusw` (rank 3) REFUSE on ACL2 x86isa, measured \
live with both controls behaving, and this repository had held that reading in \
`oracle_availability.py` since P2 batch 1 while the roster — which joins DEMAND \
against SUPPLY and consults no third artifact — went on ranking them.  ⇒ A \
ROSTER THAT PRICES DEMAND DOES NOT PRICE BUILDABILITY, and the two look the \
same in a ranked table; the roster now carries an ORACLE column, emitted and \
consumed in the same batch, whose first draft reproduced D100 in the opposite \
direction by keying a `%zmm` verdict onto a `%ymm` row until it was keyed by \
(mnemonic, ISA bucket) — the same key the demand is counted by.  ⭐ AND \
`EXECUTES` WAS NOT TAKEN FOR `IMPLEMENTS`: `movss`/`movsd` have TWO operation \
clauses under one mnemonic — from a REGISTER the upper bits are PRESERVED, from \
MEMORY they are CLEARED — so the RULE was probed on the oracle with three \
controls covering all three candidate behaviours, and x86isa returned the SDM's \
answer in all four discriminating cases, which is what makes this batch \
differentially validatable where batch 7's `movd` was not.  A model that always \
merged and one that always zeroed are each BIT-IDENTICAL to this one on half \
the vectors, so both are planted.  `aligned : Bool` became `VMovKind`, four \
mnemonics from which the alignment rule is DERIVED rather than stored beside \
it, and `vload_unaligned_faults` now quantifies over `k.aligned` so the theorem \
GREW WITH THE TYPE instead of being restated.  ⚠️ AND THE KERNEL-COST GATE \
REFUSED, naming a cheaper build: 96% of `memDestSweep` is walking `Row.shapes` \
character by character, so a documentation field a kernel-reduced predicate \
reads is NOT a place for prose — the explanation moved to the AST docstrings \
and 1,500 ms went with it.  ⛔ The pass is 95% of the ceiling and the next \
batch crosses again; the margin is written down rather than the verdict \
(see D101, D102); 11 — THE PACKED SHIFT GROUP, `psllw`/`pslld`/`psllq`, \
`psrlw`/`psrld`/`psrlq`, `psraw`/`psrad` at THREE COUNT SHAPES each, plus the \
two whole-register byte shifts `pslldq`/`psrldq`: ten roster rows, 39 vectors, \
no new state, and worth 32,882 instructions of the assembly class.  ⛔ THE \
BATCH IS THE SATURATION RULE: a count at or above the lane width does not \
wrap, it zeroes a logical shift and sign-fills an arithmetic one, and a model \
taking the count MODULO the lane width is BIT-IDENTICAL to this one at every \
in-range count — which is every count a casual vector table contains.  The \
handover asserted the oracle implemented that rule and NO ARTIFACT SAID SO, so \
three models were run against x86isa in one probe: 42 rows, all 42 agree with \
the SDM, and 20 of them DISCRIMINATING — the other 22 are printed as pricing \
NOTHING rather than counted as support.  ⛔⛔ AND THE GUARD HAS A SECOND \
REASON NO THEOREM CAN STATE: the unguarded LEFT shift at a count a register \
operand can hold is `INTERNAL PANIC: Nat.shiftl exponent is too big`, in the \
interpreter AND in the kernel, while both RIGHT shifts saturate quietly at any \
count — so removing the guard leaves every `psrl`/`psra` vector passing and \
takes the BUILD down only on `psll`.  A declaration that panics kills the \
process rather than failing to elaborate, so it is a probe that PLANTS the \
unguarded spelling, with a held-out arm for the two shifts whose silence is \
the defect's cover.  ⭐ The AST departs from `VBinKind` — a product with an \
encodability table rather than the lane in the kind — because the shifts have \
two HOLES that `VBinKind` never had: no packed byte shift, and no `psraq` \
outside AVX-512, and the declined set is stated as the four PAIRS rather than \
as a count.  ⭐⭐ The census and the roster then disagreed by 2,822 and the \
third fact reconciled them exactly: that many of the group's instructions are \
MMX-register forms this model has no register file for, so the batch is \
published at 32,882 and not at the 35,704 the roster ranks — a demand figure \
and a coverage gain are different quantities whenever the model declines a \
register file (see D106, D107); 12 — THE PERMUTE GROUP, `pshufd`/`pshuflw`/\
`pshufhw` at BOTH operand shapes: three roster rows, 14 vectors, no new state, \
12,064 buildable instructions of the assembly class (`pshufw` is a fourth \
prefix of the same opcode and is DECLINED, 642 of 642 MMX-register).  ⛔⛔ THE \
BATCH'S FINDING IS ONE SCREEN ABOVE ITS OWN ARM: batch 11's `vshiftm` carried \
`NO ALIGNMENT CHECK … the absence is the rule`, and the SDM says otherwise in \
three lines — PSHUFD, PAND and MOVDQU are all Table 2-21 (Type 4), and MOVDQU \
alone is granted an operand that `may be unaligned … WITHOUT causing a \
general-protection exception`.  AN EXEMPTION IS PROOF OF THE RULE IT EXEMPTS \
FROM, so Type 4 carries a 16-byte #GP for every member not exempted and the \
packed shifts are not.  ⛔⛔ AND IT WAS NOT INVISIBLE FOR WANT OF A \
VECTOR: `psraw 0x8(%rbx),%xmm5` is 0x2008, UNALIGNED, was added in the same \
commit as the defect, and PASSED at all 88 pre-states -- because x86isa \
implements the 16-byte rule in ONE file of its tree and not in `pshift.lisp`, \
so the model's missing check and the oracle's missing check are THE SAME \
OMISSION.  Repairing the arm is what surfaced it: 264 unexplained, every one \
that single vector.  ⇒ TWO DEFECTS THAT CANCEL SURVIVE EVERY GREEN RUN THAT \
COMPARES THEM TO EACH OTHER, and a differential is blind to exactly the errors \
its two sides share.  ⭐ The oracle \
cannot settle it and CONTRADICTS ITSELF trying: x86isa implements the check in \
exactly one file of its tree, so it refuses `pand 8(%rbx)` at all 88 \
pre-states and executes `pshufd`, `psrlw` and `movdqa` at the same address — \
one exception class, three answers, with `pand` serving as the positive \
control that the refusal is visible at all.  So the rule is a THEOREM at both \
groups, and each alignment branch was DELETED in turn to prove the gate has \
teeth: each took its own theorem down and no other.  ⭐⭐ And `pshuflw` at a \
register source discriminates in only 60 of 88 pre-states, structurally — \
`xmmPattern`'s low quadword has four identical WORDS wherever the swept \
constant does — so a word-level permutation is the first operation here whose \
correctness is invisible unless the source's lanes differ; the repair needed no \
new pre-state, only an aligned window whose sixteen bytes are all distinct \
(see D109, D110, D111); 13 — THE PACKED BINARY GROUP AT A MEMORY SOURCE, the \
nineteen operations `Op.vbin` has carried since batches 5 and 7, at their other \
operand shape: one constructor, 22 vectors, NO new roster row and NO new state. \
⛔⛔ THIS BATCH ADDS NO COVERAGE AND THAT IS THE POINT — the census counts by \
MNEMONIC, so all 182,286 instructions of these nineteen were ALREADY counted as \
covered, including the 7,705 whose source is memory and which this model could \
not execute at all.  The published number does not move; what moves is that \
4.63% of it stops being a lie.  That is `vshiftm`'s 0.85% trade (D107) one order \
of magnitude up, and AN OVER-CLAIM IS INVISIBLE TO THE INSTRUMENT THAT PRODUCES \
IT.  ⭐⭐⭐ AND THE 16-BYTE #GP IS DIFFERENTIALLY VALIDATED HERE FOR THE FIRST \
TIME: D91 recorded that no vector could test it and that the arm `movdqa \
ignores its alignment requirement` was a FALSE ENTRY in the gate's inventory \
because nothing could distinguish it — true for nine batches.  D110 found why \
and thereby found the exception: x86isa implements the check in exactly ONE \
file of its tree, and that file is `pand`/`por`/`pxor`.  The split was \
PREDICTED from the source before it was measured — `por 8(%rbx)` refuses at all \
88 pre-states while `paddd`, `psubw` and `punpcklbw` at the same address execute \
at all 88 — so at those three both models refuse, `bothRefused` reports \
agreement, and the rule is carried by a RUN.  ⚠️ AGREEMENT BY MUTUAL REFUSAL IS \
SILENCE UNLESS SOMETHING PRICES IT, so the arm D91 called impossible is now \
written and reports in `refused` rather than in a value.  ⚠️ And the operand \
ORDER is the content: eleven of the nineteen commute, and the swapped arm is \
caught by only twelve of the vectors — the number to read, because an arm caught \
by a minority of a group's vectors is one whose group needed exactly those \
(see D112, D113); 14 — THE PACKED COMPARES, `pcmpeq{b,w,d}` and \
`pcmpgt{b,w,d}` at both operand shapes: six roster rows, 13 vectors, NO new \
constructor — they join `VBinKind`, so `Op.vbin` and `Op.vbinm` carry them and \
the 16-byte alignment rule comes with them.  ⭐ THE GROUP WAS PICKED FROM A \
MEASUREMENT AND NOT FROM A RANK: every other candidate of this size in the \
residue REFUSES on the oracle (D115), so the compares are what is left — 7,454 \
buildable instructions.  ⛔⛔ WHAT EACH VECTOR PRICES IS NOT UNIFORM: `pcmpeq` \
prices NOTHING about signedness or operand order, because equality is the same \
relation either way and both wrong models agree with it at all 88 pre-states BY \
CONSTRUCTION; only `pcmpgt` carries those rules, and the MEMORY forms carry them \
hardest (the unsigned model survives 15 of 88 there against 67 at the register \
shape).  ⛔⛔⛔ AND THE REGISTER-FIELD CONTROL IS BLIND TO THE RULE THE BATCH IS \
ABOUT: `pcmpgtb %xmm3,%xmm2` agrees with the UNSIGNED model at ALL 88 pre-states \
where `pcmpgtb %xmm1,%xmm0` agrees at 61, because `xmmPattern` gives xmm2 and \
xmm3 byte lanes that never differ in sign.  ⇒ A CONTROL CAN SHARE THE BLIND SPOT \
OF THE THING IT CONTROLS — it is a good control for register FIELDS and worth \
zero for signedness, and only measuring the two separately showed it.  ⚠️ Lean's \
`<` on `BitVec` is UNSIGNED, so the wrong model is not a strawman but what a \
model written without noticing the SDM's word `signed` type-checks to; and the \
result is a MASK, not a flag, which is bit-identical in the low bit of every \
lane (see D116); 15 — `packuswb`, THE ONE MEMBER OF THE PACK GROUP THE ORACLE \
CAN EXECUTE: one roster row, 2 vectors, one new `VBinKind` constructor and one \
combinator, 5,105 buildable instructions.  ⛔⛔ THE GROUP IS ONE MNEMONIC WIDE \
AND THAT IS A MEASUREMENT: `packsswb` and `packssdw` REFUSE at every pre-state \
(D115), and `packssdw` is roster rank 15 at 5,613 instructions.  A batch sampled \
at `packuswb` — the group's natural representative, adjacent opcode, same \
shapes, 88 of 88 against the SDM — WOULD HAVE PASSED while two thirds of the \
group could not be run.  ⭐ The saturation is ASYMMETRIC and it is the \
instruction: source lanes SIGNED, result lanes UNSIGNED, so a negative word \
saturates to 0 and one above 255 to 255.  ⚠️ THE TRUNCATION MODEL SCORES 0 OF 88 \
AND THAT NUMBER IS A PROPERTY OF THE PRE-STATES, NOT OF THE INSTRUCTION — \
keeping the low byte is bit-identical at every IN-RANGE value, and what refutes \
it is `adversarial` reaching 0x8000/0xFFFF/0x7FFF, a P0 choice for SCALAR \
arithmetic doing the work here by inheritance.  A table of small positive \
constants would have scored it 88 of 88 and reported green about a model that \
does not saturate at all ⇒ A WRONG MODEL'S SCORE IS A JOINT FACT ABOUT THE MODEL \
AND THE PRE-STATES.  ⛔ And it is not `vlanes`: this is the first operation here \
that NARROWS, so lane i of the result is not a function of lane i of the \
operands (see D117); 16 — `movhps`, AND THE HALF THAT DOES NOT MOVE.  One roster row for BOTH directions (one mnemonic at two opcodes, `0f 16` and `0f 17`), 6 vectors, two constructors, NO new state, 3,672 instructions.  ⭐ THE FIRST MEMBER OF A GROUP THE RESIDUE HAD BEEN REPORTING AS ABSENT: batch 19 measured six never-asked scalar-SSE-FP mnemonics worth 26,757 instructions, which a bank's closing sentence had partitioned two ways — `refuses or VEX` — for a three-valued remainder, and a category with no slot in the sentence reads as EMPTY rather than as unhandled (D118).  `movhps` is the one of the six needing no floating-point arithmetic at all; the other five need a soft-float IEEE-754 layer over `BitVec` plus MXCSR, because Lean's `Float` is an opaque extern the kernel cannot reduce.  ⛔ THE CONTENT IS THE HALF THAT DOES NOT MOVE: the load writes `dst[127:64]` and PRESERVES `dst[63:0]`, so the plausible wrong model is the one that CLEARS the low half — the exact MIRROR of D93, where the oracle MERGED what the SDM clears, the direction of the plausible error reversing with the rule.  It is caught in 152 cases, and that number is a joint fact about the model and the PRE-STATES: what refutes it is `xmmPattern` giving xmm0 a non-zero low quadword, and a table that zeroed the destination would have scored it 0 and reported green about a model that destroys half the register on every load.  ⛔ NO ALIGNMENT RULE, MEASURED RATHER THAN ASSERTED: the operand is eight bytes (Type 5), and D110 is why that sentence is not left to a comment — there `NO ALIGNMENT CHECK … the absence is the rule` was written about a group that DID have one.  Both directions execute at 16-, 8- and 4-byte alignment in a run where `pand 0x8(%rbx)` REFUSES and `pand (%rbx)` EXECUTES, so the harness demonstrably CAN see an alignment refusal and this silence is a reading.  ⚠️ The unaligned vectors sit at displacement FOUR, not eight: eight is still 8-byte aligned and could not tell `no rule at all` from `an 8-byte rule` (see D119); 17 — `PREFETCHh`, THE FORM THAT CHANGES NOTHING.  `prefetchnta` and `prefetcht0` at a memory operand, two roster rows, 4 vectors, one constructor, no new state, 466 instructions — found by batch 21's CENSUS, which measured the unprobed remainder instead of declaring it empty, so nobody knew it was buildable.  ⚠️ WHAT THE VECTORS PROVE IS NARROW AND THE RECORD SAYS SO: the form changes no architectural state, so the differential can witness only that BOTH models leave every watched register, flag and window alone and advance RIP by the right length.  That is the claim `prefetch` makes, and a model that read the memory, faulted on it, or mis-computed the length breaks it — but a form that writes nothing is one whose vectors agree with almost any wrong model, so the two arms are what stop the agreement being vacuous.  ⛔ AND NO ARM IS PLANTED FOR THE LOCALITY HINT: it is architecturally invisible, so no vector that can exist would distinguish it, and an arm no vector can distinguish is a FALSE ENTRY in the gate's own inventory (D91).  The spellings are held apart by `check_encodings.py`, which assembles each `asm` and compares bytes — the instrument that can actually see a `/reg` field.  ⛔⛔ TWO ROWS AND NOT FOUR, AND THE KERNEL-COST GATE NAMED THE CHEAPER BUILD: four hints put `Tests.Coverage`'s residue 700 ms over its ceiling, and `prefetcht1`/`prefetcht2` have ZERO measured demand, so modelling them was completionism rather than demand — the instinct this roster declines at `pshufw`.  The refusal named a cheaper build and the cheaper build was the more honest one (see D121).\n\n\
The mnemonic count is `rosterSize` rather than a literal, so it cannot drift \
from the AST the way the sentence it replaced had.\n\n\
Tiers: T-exact " ++ toString e ++ " · T-frame " ++ toString f ++ " · T-absent " ++
        toString ab ++ ".\n\n"
      let trust := "\n**Decode trust.** Every row reads `XED (trusted)`: the AST is built from \
Intel XED's structured output and nothing in this repository proves that the bytes were decoded \
correctly. The differential vectors close this for every form below by assembling each `asm` \
string with clang and checking the length against the model's `Instr.len`; a Lean decoder with a \
proof is P4.\n"
      IO.FS.writeFile out (hdr ++ renderTable tableP0 ++ trust)
      IO.println s!"wrote coverage table ({tableP0.length} rows) → {out}"
      return 0
  -- ⭐⭐ P2 BATCH 12 (D105): THE RUN-INDEX CERTIFICATE.  `Tests/Coverage.lean`'s
  -- `vectorCoverage` used to prove its facts by SEARCHING: a dedup of the 854
  -- vector mnemonics (quadratic in the DISTINCT count, which is why collapsing
  -- duplicates first bought 8%) and two inclusion sweeps over the table.  2 250
  -- ms of kernel time against a 2 320 ms ceiling, crossed by any batch.
  --
  -- The kernel is asked to CHECK A CERTIFICATE instead: for each RUN of equal
  -- mnemonics in the vector table, the INDEX of the coverage-table row that run
  -- exercises.  Emitted here and gated byte-for-byte in CI exactly as the
  -- coverage table is.  ⛔ It is worth NOTHING on its own — the theorem that
  -- gives it meaning compares the mnemonics it names against the table's own,
  -- so a lying certificate fails in the KERNEL, not here.  990 ms, same facts.
  | ["runs", out] =>
      let mns := vectors.map Vec.mnemonic
      let tm := tableP0.map Row.mnemonic
      -- The runs, in the vector table's own order; adjacent equal mnemonics
      -- collapse to one entry, exactly as `X86.Tests.mnemonicRuns` does.
      let runs := mns.foldl
        (fun acc m => if acc.getLast? == some m then acc else acc ++ [m]) []
      let idx := runs.map (fun m => tm.idxOf m)
      -- sixteen to a line: a generated file a human can still read in a diff.
      let chunk : Nat → List Nat → List (List Nat) := fun n xs =>
        let rec go (xs : List Nat) (fuel : Nat) : List (List Nat) :=
          match fuel, xs with
          | 0, _ => []
          | _, [] => []
          | Nat.succ f, xs => xs.take n :: go (xs.drop n) f
        go xs (xs.length + 1)
      let rows := (chunk 16 idx).map (fun ch =>
        String.intercalate ", " (ch.map toString))
      let hdr := String.intercalate "\n"
        [ "-- GENERATED by `lake exe x86lean-diff runs`. Do not edit by hand."
        , "-- ⛔ A STALE FILE HERE BREAKS `Tests/Coverage.lean` AND NOTHING ELSE:"
        , "-- this executable imports `Tests.Vectors` and never `Tests.Coverage`,"
        , "-- so it can always be rebuilt to regenerate the file it invalidated."
        , "--     lake exe x86lean-diff runs Tests/VectorRuns.lean"
        , ""
        , "namespace X86.Tests"
        , ""
        , "/-- The coverage-table row index of each RUN of equal mnemonics in the"
        , "differential vector table, in the vector table's own order.  A"
        , "CERTIFICATE, not a claim: `X86.Tests.vectorCoverage` checks it against"
        , "both tables and every coverage fact published about the vectors is read"
        , "off that check.  " ++ toString runs.length ++ " runs over " ++
          toString vectors.length ++ " vectors and " ++ toString tm.length ++ " rows. -/"
        , "def vectorRunIdx : List Nat :="
        , "  [" ++ String.intercalate ",\n   " rows ++ "]"
        , ""
        , "end X86.Tests"
        , "" ]
      IO.FS.writeFile out hdr
      IO.println s!"wrote run-index ({runs.length} runs over {vectors.length} vectors) → {out}"
      return 0
  | ["stats"] =>
      let n := 8
      IO.println s!"vectors={vectors.length} mnemonics={(vectors.map Vec.mnemonic).eraseDups.length} \
pre-states={(preStates 1 n).length} cases={vectors.length * (preStates 1 n).length}"
      return 0
  | _ =>
      IO.eprintln "usage: x86lean-diff (emit <out> | emit-asm <out> | expected-lengths <out> | \
compare <a> <b> | selftest [<arm-substring>] | coverage <out> | runs <out> | stats | emit-acl2 <out>)"
      return 2
