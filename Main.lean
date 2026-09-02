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
  let und := undefinedFlags v.instr pre
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

/-- The GPR alist, by x86isa register index. -/
def gprsToLisp (s : Cpu) : String :=
  "(" ++ String.intercalate " "
    (GPR.all.map (fun r => s!"({r.index.val} . #x{hex64 (s.regs.get r)})")) ++ ")"

/-- RFLAGS as a 32-bit word.  Bit 1 is the architecturally reserved one
(SDM Vol. 1 Figure 3-8); x86isa initialises through `!rflags`, so the value has
to be a real RFLAGS image rather than seven loose booleans. -/
def rflagsToLisp (f : Flags) : String :=
  let bit (b : Bool) (n : Nat) : Nat := if b then Nat.shiftLeft 1 n else 0
  let v := 2 + bit f.cf 0 + bit f.pf 2 + bit f.af 4 + bit f.zf 6
             + bit f.sf 7 + bit f.df 10 + bit f.of 11
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

def acl2Case (v : Vec) (idx : Nat) (pre : Cpu) (ws : List Window) : String :=
  s!"  (:id \"{v.id}/{idx}\" :rip #x{hex64 pre.rip} :len {v.instr.len}\n\
   :bytes {bytesToLisp v.bytes}\n\
   :gprs {gprsToLisp pre}\n\
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

/-- The seven flag names, so a disagreement in a flag can be tested against the
undefined set while a disagreement in a register never is. -/
def flagNames : List String := ["cf", "pf", "af", "zf", "sf", "of", "df"]

/-- ⭐ WHEN BOTH MODELS REFUSE, THEY AGREE.

A refused instruction has no post-state either model is claiming, so comparing
the registers, RIP and memory after a refusal compares two pieces of debris.
The claim being made is "this faults", and on that the two agree. Anything else
would make the fix for the non-canonical-branch gap look like eighty new
disagreements instead of eighty resolved ones.

A refusal on ONE side only is the real finding and gets its own class. -/
def bothRefused (a b : Rec) : Bool :=
  (a.post.lookup "refused" == some "1") && (b.post.lookup "refused" == some "1")

def classify (a b : Rec) : List Disagreement :=
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
        else if flagNames.contains k && a.undef.contains k then "undefined-region"
        else "spec"
      some { id := a.id, mnemonic := a.mnemonic, field := k, lhs := x, rhs := y, cls }

structure Report where
  cases : Nat := 0
  matched : Nat := 0
  explained : Nat := 0
  unexplained : Nat := 0
  leaks : Nat := 0
  missing : Nat := 0
  details : List Disagreement := []

def compareRecs (as bs : List Rec) : Report := Id.run do
  let mut r : Report := {}
  for a in as do
    r := { r with cases := r.cases + 1 }
    if a.leak then r := { r with leaks := r.leaks + 1 }
    match bs.find? (fun b => b.id == a.id) with
    | none => r := { r with missing := r.missing + 1 }
    | some b =>
      let ds := classify a b
      if ds.isEmpty then r := { r with matched := r.matched + 1 }
      else
        let expl := ds.filter (fun d => d.cls == "undefined-region")
        let unex := ds.filter (fun d => d.cls != "undefined-region")
        r := { r with
          explained := r.explained + expl.length
          unexplained := r.unexplained + unex.length
          details := r.details ++ ds }
  return r

def renderReport (r : Report) : String :=
  let head := s!"cases={r.cases} matched={r.matched} explained={r.explained} \
unexplained={r.unexplained} oracle-leaks={r.leaks} missing={r.missing}"
  let byClass := ["spec", "refusal", "harness", "undefined-region"].map fun c =>
    s!"  {c}: {(r.details.filter (fun d => d.cls == c)).length}"
  let sample := (r.details.filter (fun d => d.cls != "undefined-region")).take 20
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

/-! ## Main -/

def writeLines (path : String) (ls : List String) : IO Unit :=
  IO.FS.writeFile path (String.intercalate "\n" ls ++ "\n")

def readLines (path : String) : IO (List String) := do
  let s ← IO.FS.readFile path
  return (s.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)

/-- Run one wrong model against the correct one and REQUIRE a catch. -/
def driveWrong (name : String) (wrong : Instr → Cpu → Cpu) (expectField : String) :
    IO Bool := do
  let good := parseRecords (emitAll step 4)
  let bad := parseRecords (emitAll wrong 4)
  let r := compareRecs good bad
  let hits := r.details.filter (fun d => d.cls == "spec" && d.field == expectField)
  if r.unexplained == 0 then
    IO.println s!"  ⛔ {name}: comparator reported ZERO unexplained disagreements against a \
KNOWN-WRONG model. The comparator does not work."
    return false
  else if hits.isEmpty then
    IO.println s!"  ⛔ {name}: {r.unexplained} unexplained disagreements, but NONE in the \
field the bug is in ({expectField}). The comparator fires on the wrong thing."
    return false
  else
    IO.println s!"  ✔ {name}: caught — {hits.length} disagreement(s) in `{expectField}` \
(total unexplained {r.unexplained}, explained {r.explained})"
    return true

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
     "mem@0000000000001ff0")
  , ("a memory read-modify-write drops its STORE", wrongMemStoreDropped,
     "mem@0000000000001ff0")
  , ("a memory store ignores its operand WIDTH", wrongMemStoreWidth,
     "mem@0000000000001ff0")
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
  , ("cld is a no-op (the flag nothing could write)", wrongCldIsNoOp, "df") ]

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
  | ["compare", a, b] =>
      let ra := parseRecords (← readLines a)
      let rb := parseRecords (← readLines b)
      let r := compareRecs ra rb
      IO.println (renderReport r)
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
      let r := compareRecs good good
      let silent := r.unexplained == 0 && r.explained == 0 && r.missing == 0 && r.leaks == 0
      if silent then
        IO.println s!"  ✔ control: the model against itself is silent ({r.matched}/{r.cases} \
cases identical, 0 oracle leaks)"
      else
        IO.println s!"  ⛔ control: the model DISAGREES WITH ITSELF — {renderReport r}"
      if ok && silent then
        IO.println s!"harness selftest: PASS ({selftestArms.length} arms + control)"
        return 0
      else
        IO.println "harness selftest: FAIL"
        return 1
  | ["coverage", out] =>
      let (e, f, ab) := tierCounts tableP0
      let hdr := "<!-- GENERATED by `lake exe x86lean-diff coverage`. Do not edit by hand. -->\n\n\
# x86lean coverage\n\n\
Roster: " ++ toString rosterSize ++ " mnemonics in " ++ toString vectors.length ++ " differentially tested forms, covering **382 of the 525 forms** in `p1/roster.tsv`.\n\n\
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
instructions able to write DF at all (see D27).\n\n\
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
  | ["stats"] =>
      let n := 8
      IO.println s!"vectors={vectors.length} mnemonics={(vectors.map Vec.mnemonic).eraseDups.length} \
pre-states={(preStates 1 n).length} cases={vectors.length * (preStates 1 n).length}"
      return 0
  | _ =>
      IO.eprintln "usage: x86lean-diff (emit <out> | emit-asm <out> | expected-lengths <out> | \
compare <a> <b> | selftest [<arm-substring>] | coverage <out> | stats | emit-acl2 <out>)"
      return 2
