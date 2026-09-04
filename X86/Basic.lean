/-
# X86.Basic — widths, registers, and the flag record

PROVENANCE. Every fact encoded here is read from the Intel SDM (Vol. 1 §3.4.1
"General-Purpose Registers", Vol. 1 §3.4.3 "EFLAGS Register", Vol. 2A §2.1.5
"Addressing-Mode Encoding of ModR/M and SIB Bytes") and cross-read against the
two public executable models named in PROVENANCE.md (ACL2 x86isa, BSD-3; K
x86-64, NCSA).  No text is copied from any of them; the SDM is a READING
reference only.  See PROVENANCE.md for the reading log rule.

LANE. Personal lane, public sources only.  See CLAUDE.md.
-/

namespace X86

/-! ## Operand widths -/

/-- An operand width.  x86-64 user-level integer operands are 8, 16, 32 or 64
bits wide.  This is a *datum*, not a type index: the AST carries it and `step`
dispatches on it, which is what keeps `step` a total function of a first-order
inductive (plan v1 §3.2). -/
inductive Size where
  | b  -- 8 bits
  | w  -- 16 bits
  | d  -- 32 bits
  | q  -- 64 bits
  deriving DecidableEq, Repr, Inhabited, BEq

namespace Size

/-- Width in bits. -/
def bits : Size → Nat
  | .b => 8
  | .w => 16
  | .d => 32
  | .q => 64

/-- Width in bytes. -/
def bytes : Size → Nat
  | .b => 1
  | .w => 2
  | .d => 4
  | .q => 8

@[simp] theorem bits_b : Size.b.bits = 8 := rfl
@[simp] theorem bits_w : Size.w.bits = 16 := rfl
@[simp] theorem bits_d : Size.d.bits = 32 := rfl
@[simp] theorem bits_q : Size.q.bits = 64 := rfl

@[simp] theorem bytes_b : Size.b.bytes = 1 := rfl
@[simp] theorem bytes_w : Size.w.bytes = 2 := rfl
@[simp] theorem bytes_d : Size.d.bytes = 4 := rfl
@[simp] theorem bytes_q : Size.q.bytes = 8 := rfl

theorem bits_pos (sz : Size) : 0 < sz.bits := by cases sz <;> decide

end Size

/-! ## General-purpose registers

The constructor ORDER is the SDM's ModR/M `reg` field encoding (Vol. 2A Table
2-2): 0 RAX · 1 RCX · 2 RDX · 3 RBX · 4 RSP · 5 RBP · 6 RSI · 7 RDI, then
REX.R/REX.B extending to 8..15 = R8..R15.  `GPR.index` below is that encoding
and is the ONLY place the numbering is stated; everything else goes through it.
Getting this order wrong is a silent, total-model bug that no type checks, so it
carries its own anchor test (`Tests/Anchors.lean`, the `reg_encoding` block). -/
inductive GPR where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr, Inhabited, BEq

namespace GPR

/-- The ModR/M / REX encoding number of a register (SDM Vol. 2A Table 2-2). -/
def index : GPR → Fin 16
  | .rax => 0  | .rcx => 1  | .rdx => 2  | .rbx => 3
  | .rsp => 4  | .rbp => 5  | .rsi => 6  | .rdi => 7
  | .r8  => 8  | .r9  => 9  | .r10 => 10 | .r11 => 11
  | .r12 => 12 | .r13 => 13 | .r14 => 14 | .r15 => 15

/-- Inverse of `index`. -/
def ofIndex : Fin 16 → GPR
  | 0 => .rax  | 1 => .rcx  | 2 => .rdx  | 3 => .rbx
  | 4 => .rsp  | 5 => .rbp  | 6 => .rsi  | 7 => .rdi
  | 8 => .r8   | 9 => .r9   | 10 => .r10 | 11 => .r11
  | 12 => .r12 | 13 => .r13 | 14 => .r14 | 15 => .r15
  | ⟨_ + 16, h⟩ => absurd h (by omega)

/-- All sixteen registers, in encoding order. -/
def all : List GPR :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
   .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem ofIndex_index (r : GPR) : ofIndex r.index = r := by cases r <;> rfl

theorem index_ofIndex (i : Fin 16) : (ofIndex i).index = i := by
  match i with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩
  | ⟨8, _⟩ | ⟨9, _⟩ | ⟨10, _⟩ | ⟨11, _⟩ | ⟨12, _⟩ | ⟨13, _⟩ | ⟨14, _⟩ | ⟨15, _⟩ => rfl
  | ⟨n+16, h⟩ => omega

/-- The name a disassembler prints for the `sz`-wide view of this register.
`high8` selects AH/CH/DH/BH, which are legal only for `rax rcx rdx rbx` and only
without a REX prefix (SDM Vol. 2A §2.2.1.2). -/
def name (r : GPR) (sz : Size) (high8 : Bool := false) : String :=
  if high8 then
    match r with
    | .rax => "ah" | .rcx => "ch" | .rdx => "dh" | .rbx => "bh"
    | _ => "<illegal-high8>"
  else
    match sz, r with
    | .q, .rax => "rax" | .q, .rcx => "rcx" | .q, .rdx => "rdx" | .q, .rbx => "rbx"
    | .q, .rsp => "rsp" | .q, .rbp => "rbp" | .q, .rsi => "rsi" | .q, .rdi => "rdi"
    | .d, .rax => "eax" | .d, .rcx => "ecx" | .d, .rdx => "edx" | .d, .rbx => "ebx"
    | .d, .rsp => "esp" | .d, .rbp => "ebp" | .d, .rsi => "esi" | .d, .rdi => "edi"
    | .w, .rax => "ax"  | .w, .rcx => "cx"  | .w, .rdx => "dx"  | .w, .rbx => "bx"
    | .w, .rsp => "sp"  | .w, .rbp => "bp"  | .w, .rsi => "si"  | .w, .rdi => "di"
    | .b, .rax => "al"  | .b, .rcx => "cl"  | .b, .rdx => "dl"  | .b, .rbx => "bl"
    | .b, .rsp => "spl" | .b, .rbp => "bpl" | .b, .rsi => "sil" | .b, .rdi => "dil"
    | .q, r => s!"r{r.index.val}"
    | .d, r => s!"r{r.index.val}d"
    | .w, r => s!"r{r.index.val}w"
    | .b, r => s!"r{r.index.val}b"

instance : ToString GPR := ⟨fun r => r.name .q⟩

end GPR

/-! ## The two segment registers long mode still honours

⭐⭐ P2 ITEM 1 (the Captain's order, 09/03).  In 64-bit mode segmentation is
disabled for CS, DS, ES and SS: their bases are treated as zero and their limits
are not checked (SDM Vol. 3A §3.4.4, "Segmentation in IA-32e Mode").  **FS and
GS are the exception** — their 64-bit bases are still added to the effective
address, and are loaded from the IA32_FS_BASE and IA32_GS_BASE MSRs (SDM Vol. 3A
§3.4.4 and Vol. 4, Table 2-2).

⛔ SO THIS IS NOT "SEGMENTATION", AND THE DISTINCTION IS WHY THE ITEM IS CHEAP.
A model that admitted segmentation would owe descriptors, selectors, limits,
expand-down data segments and #GP on a null selector.  What long mode leaves is
**one 64-bit base register, chosen by a prefix, added modulo 2^64** — which is
why the whole addition is this inductive, two fields on `Cpu`, and one `+` in
`Ea.addr`.  There is no descriptor anywhere in this repository and none is
implied by this type.

The demand is measured, not argued: 29,943 instructions in the census's assembly
class carry an FS/GS override (docs/DEMAND-CENSUS.md), and the commonest of them
is the stack-protector load `movq %fs:0x28, %rax` that appears in the prologue
of most compiled functions. -/
inductive Seg where
  | fs | gs
  deriving DecidableEq, Repr, Inhabited, BEq

namespace Seg

/-- The name a disassembler prints in an AT&T segment override. -/
def name : Seg → String
  | .fs => "fs" | .gs => "gs"

/-- Both of them, so a sweep over the segments has one source. -/
def all : List Seg := [.fs, .gs]

instance : ToString Seg := ⟨Seg.name⟩

end Seg

/-! ## The register file

Sixteen named fields rather than a `Vector`/`Array`/function.  This is a
KERNEL-COST decision (plan v1 §3.7): a field read is one `Expr.proj` and a
structure update is one `Expr` node, so `decide` on an anchor never has to
reduce array indexing or `Function.update`.  The 16-way `match` in
`Regs.get`/`Regs.set` reduces by iota in one step. -/
structure Regs where
  rax : BitVec 64 := 0
  rcx : BitVec 64 := 0
  rdx : BitVec 64 := 0
  rbx : BitVec 64 := 0
  rsp : BitVec 64 := 0
  rbp : BitVec 64 := 0
  rsi : BitVec 64 := 0
  rdi : BitVec 64 := 0
  r8  : BitVec 64 := 0
  r9  : BitVec 64 := 0
  r10 : BitVec 64 := 0
  r11 : BitVec 64 := 0
  r12 : BitVec 64 := 0
  r13 : BitVec 64 := 0
  r14 : BitVec 64 := 0
  r15 : BitVec 64 := 0
  deriving DecidableEq, Repr, Inhabited, BEq

namespace Regs

/-- Read the full 64-bit register. -/
def get (rs : Regs) : GPR → BitVec 64
  | .rax => rs.rax | .rcx => rs.rcx | .rdx => rs.rdx | .rbx => rs.rbx
  | .rsp => rs.rsp | .rbp => rs.rbp | .rsi => rs.rsi | .rdi => rs.rdi
  | .r8  => rs.r8  | .r9  => rs.r9  | .r10 => rs.r10 | .r11 => rs.r11
  | .r12 => rs.r12 | .r13 => rs.r13 | .r14 => rs.r14 | .r15 => rs.r15

/-- Write the full 64-bit register. -/
def set (rs : Regs) : GPR → BitVec 64 → Regs
  | .rax, v => { rs with rax := v } | .rcx, v => { rs with rcx := v }
  | .rdx, v => { rs with rdx := v } | .rbx, v => { rs with rbx := v }
  | .rsp, v => { rs with rsp := v } | .rbp, v => { rs with rbp := v }
  | .rsi, v => { rs with rsi := v } | .rdi, v => { rs with rdi := v }
  | .r8,  v => { rs with r8  := v } | .r9,  v => { rs with r9  := v }
  | .r10, v => { rs with r10 := v } | .r11, v => { rs with r11 := v }
  | .r12, v => { rs with r12 := v } | .r13, v => { rs with r13 := v }
  | .r14, v => { rs with r14 := v } | .r15, v => { rs with r15 := v }

/-- ONE-SHOT PROJECTION PACK (plan v1 §3.7).  `get` after `set` on the same
register.  Proven by a 16×16 `decide`-free case split that the kernel does by
iota alone. -/
@[simp] theorem get_set_same (rs : Regs) (r : GPR) (v : BitVec 64) :
    (rs.set r v).get r = v := by
  cases r <;> rfl

/-- A second write to the same register wins.  Needed by `pop rsp`, where RSP is
written twice in one instruction and the LOADED value is the one that survives. -/
@[simp] theorem set_set_same (rs : Regs) (r : GPR) (v w : BitVec 64) :
    (rs.set r v).set r w = rs.set r w := by
  cases r <;> rfl

/-- `get` after `set` on a DIFFERENT register: the frame half of the pack. -/
@[simp] theorem get_set_ne (rs : Regs) (r r' : GPR) (v : BitVec 64) (h : r ≠ r') :
    (rs.set r v).get r' = rs.get r' := by
  cases r <;> cases r' <;> first | rfl | exact absurd rfl h

end Regs

/-! ## RFLAGS

Named `Bool` fields, not a bit vector (plan v1 §3.1).  Only the user-level
arithmetic flags plus DF are modelled; everything else in RFLAGS is outside the
v0.x non-goals fence (plan v1 §1).

SDM Vol. 1 §3.4.3.1 "Status Flags":
  CF carry/borrow out of the most-significant bit
  PF parity of the LOW-ORDER EIGHT BITS of the result
  AF carry/borrow out of BIT 3 (the "auxiliary" or BCD carry)
  ZF result is zero
  SF the most-significant bit of the result (its sign)
  OF signed overflow
DF (Vol. 1 §3.4.3.2) is a control flag.  It was carried from P0 with nothing able
to write it — which is exactly how it became D27, a flag every instrument reported
as watched while it was a CONSTANT.  `cld`/`std` (P1 batch 11) write it now. -/
structure Flags where
  cf : Bool := false
  pf : Bool := false
  af : Bool := false
  zf : Bool := false
  sf : Bool := false
  of : Bool := false
  df : Bool := false
  deriving DecidableEq, Repr, Inhabited, BEq

/-! ### ⭐ THE SEVEN FLAGS AS DATA — D30

THE FIELD LIST WAS HAND-WRITTEN IN FOUR PLACES, and one of them was on the path
that reports SUCCESS.  `Flags.render` (X86/Serialize.lean) is the WIRE FORMAT the
two models are compared through: a flag missing from that one string is never
emitted, never compared, and every differential run is green about it.  That is
not a hypothetical — it is precisely the shape of D27, where DF was carried,
printed and diffed for ten batches while being a constant nothing could write.
The other three (`undefinedFlags`, `flagNames`, `rflagsToLisp`) fail LOUDLY, as
a false RED or a pre-state disagreement.  ⇒ **The dangerous duplicate is the one
on the path that reports SUCCESS**, and the fix is to leave only one list.

⚠️ AND A TABLE IS NOT BY ITSELF A FIX.  D29 was a table that had drifted from its
hand-written twin while carrying a comment promising it could not — a duplicate
BORN IN AGREEMENT, which needs no mistake to diverge, only the next ordinary
append.  So this table does not merely exist; it is GUARDED, by
`flagFields_covers_Flags` below, and the guard is a compile-time arity check
rather than a sentence in a comment. -/

/-- One flag's name, projection, and architectural position in RFLAGS. -/
structure FlagField where
  name : String
  get : Flags → Bool
  /-- The bit's position in the RFLAGS image (SDM Vol. 1 Figure 3-8).  It lives
  here rather than in the ACL2 emitter because it is a fact about the
  architecture, not about the wire to x86isa. -/
  bit : Nat

/-- The one list.  Its ORDER is the wire order of `Flags.render`, so changing it
changes the record format both models are compared through. -/
def flagFields : List FlagField :=
  [ { name := "cf", get := (·.cf), bit := 0 }
  , { name := "pf", get := (·.pf), bit := 2 }
  , { name := "af", get := (·.af), bit := 4 }
  , { name := "zf", get := (·.zf), bit := 6 }
  , { name := "sf", get := (·.sf), bit := 7 }
  , { name := "of", get := (·.of), bit := 11 }
  , { name := "df", get := (·.df), bit := 10 } ]

/-- ⛔ THE GUARD, AND WHY IT IS THIS SHAPE.

It fails to COMPILE, not to prove, when a field is added to `Flags`: the
anonymous-constructor pattern is positional, so an eighth field makes this line
an arity error before any proof is attempted.  If the pattern is then repaired
without adding a row, the two lists have different lengths and `rfl` fails.  If a
row is added with the wrong projection, the order differs and `rfl` fails.

⚠️ IT IS DELIBERATELY NOT A `decide` OVER ALL 128 FLAG STATES.  That would need
an enumeration of `Flags`, which is a FIFTH hand-written field list — the guard
would then have the defect it exists to prevent, and would report agreement
because a missing field sits at its default in every enumerated state.  `cases f;
rfl` asks the structure itself and costs no kernel time worth measuring. -/
theorem flagFields_covers_Flags (f : Flags) :
    flagFields.map (fun r => r.get f)
      = (match f with | ⟨cf, pf, af, zf, sf, of, df⟩ => [cf, pf, af, zf, sf, of, df]) := by
  cases f; rfl

end X86
