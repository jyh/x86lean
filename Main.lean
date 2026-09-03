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
        else if undefinableFields.contains k && a.undef.contains k then "undefined-region"
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
  let r := compareRecs good bad
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
     wrongDshiftCfFromResult, "cf") ]

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
      let r := compareRecs good good
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
Roster: " ++ toString rosterSize ++ " mnemonics in " ++ toString vectors.length ++ " differentially tested forms, covering **469 of the 525 rows** in `p1/roster.tsv` — which are **322 of the 374 distinct machine forms** those rows describe, because 149 rows are alias SPELLINGS or narrowings of another row (`jz` for `je`, `sal` for `shl`, `stos m` for `stos -`, `cmp m,label` for `cmp m,imm`) and 2 describe no encoding at all. Of the 469, **346 are spelled by a vector** and 123 are the same encoding under a different spelling. ⭐ ALL SIX NUMBERS ARE DERIVED, by `scripts/claimed_forms.py`, and gated in CI; until P1 batch 19 the first was a hand-maintained literal and it was SIXTEEN LOW.\n\n\
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
instructions have only an 8-bit displacement (see D56, D57, D58).\n\n\
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
