/-
# Tests.Vectors — the differential test vectors

Plan v1 §5, the P0 EXIT CRITERION: "one differential run of 20 scalar forms
against x86isa with ZERO unexplained disagreements, every disagreement filed
with its class."

THE TWENTY MNEMONICS are `mov add sub and or xor cmp test shl shr lea inc dec
neg not push pop jmp jcc call`.  They appear below in 38 FORMS, because a
mnemonic at one operand shape is not the same instruction as the same mnemonic
at another and the interesting bugs live in the differences — `movl` zero-extends
where `movw` does not, `shlb $1` takes the OF rule that `shlq $3` does not.

⭐ THE BYTES AND THE LENGTHS ARE NOT MINE.  Each `asm` string below was
assembled by clang (`-target x86_64-unknown-linux-gnu`) on this machine and the
`bytes`/`len` fields were read out of the disassembly.  `x86lean-diff
check-lengths` re-assembles them and FAILS if any `len` here disagrees with the
assembler, which is what closes the decode-trust gap for these vectors: an
`Instr.len` is a datum the model cannot check about itself (see `X86/Syntax.lean`),
and a wrong length is a wrong RIP on every single vector.

LANE. Personal lane, public sources only.  clang/LLVM is the assembler; nothing
from it is copied.
-/
import X86

namespace X86.Tests
open X86

/-- One differential vector: a form, its authoritative encoding, and the AST the
model is asked to execute. -/
structure Vec where
  id : String
  mnemonic : String
  /-- AT&T-syntax source, as handed to clang. -/
  asm : String
  /-- The assembled bytes, lowercase hex, from the disassembly. -/
  bytes : String
  instr : Instr
  deriving Repr, Inhabited

private def R (r : GPR) : Operand := .reg r
private def M (b : GPR) : Operand := .mem { base := some b }

/-- THE VECTOR TABLE.  38 forms covering all twenty P0 mnemonics. -/
def vectors : List Vec :=
  [ { id := "mov_d",    mnemonic := "mov",  asm := "movl %ecx, %eax",  bytes := "89c8"
    , instr := ⟨.mov .d (R .rax) (R .rcx), 2⟩ }
  , { id := "mov_q",    mnemonic := "mov",  asm := "movq %rcx, %rax",  bytes := "4889c8"
    , instr := ⟨.mov .q (R .rax) (R .rcx), 3⟩ }
  , { id := "mov_b",    mnemonic := "mov",  asm := "movb %cl, %al",    bytes := "88c8"
    , instr := ⟨.mov .b (R .rax) (R .rcx), 2⟩ }
  , { id := "mov_w",    mnemonic := "mov",  asm := "movw %cx, %ax",    bytes := "6689c8"
    , instr := ⟨.mov .w (R .rax) (R .rcx), 3⟩ }
  , { id := "mov_ri",   mnemonic := "mov",  asm := "movq $0x12345678, %rax"
    , bytes := "48c7c078563412", instr := ⟨.mov .q (R .rax) (.imm 0x12345678), 7⟩ }
  , { id := "mov_rm",   mnemonic := "mov",  asm := "movq (%rbx), %rax", bytes := "488b03"
    , instr := ⟨.mov .q (R .rax) (M .rbx), 3⟩ }
  , { id := "mov_mr",   mnemonic := "mov",  asm := "movq %rax, (%rbx)", bytes := "488903"
    , instr := ⟨.mov .q (M .rbx) (R .rax), 3⟩ }
  , { id := "add_q",    mnemonic := "add",  asm := "addq %rcx, %rax",  bytes := "4801c8"
    , instr := ⟨.bin .add .q (R .rax) (R .rcx), 3⟩ }
  , { id := "add_b",    mnemonic := "add",  asm := "addb %cl, %al",    bytes := "00c8"
    , instr := ⟨.bin .add .b (R .rax) (R .rcx), 2⟩ }
  , { id := "add_ri",   mnemonic := "add",  asm := "addq $0x11, %rax", bytes := "4883c011"
    , instr := ⟨.bin .add .q (R .rax) (.imm 0x11), 4⟩ }
  , { id := "sub_q",    mnemonic := "sub",  asm := "subq %rcx, %rax",  bytes := "4829c8"
    , instr := ⟨.bin .sub .q (R .rax) (R .rcx), 3⟩ }
  , { id := "sub_b",    mnemonic := "sub",  asm := "subb %cl, %al",    bytes := "28c8"
    , instr := ⟨.bin .sub .b (R .rax) (R .rcx), 2⟩ }
  , { id := "and_q",    mnemonic := "and",  asm := "andq %rcx, %rax",  bytes := "4821c8"
    , instr := ⟨.bin .and .q (R .rax) (R .rcx), 3⟩ }
  , { id := "or_q",     mnemonic := "or",   asm := "orq %rcx, %rax",   bytes := "4809c8"
    , instr := ⟨.bin .or .q (R .rax) (R .rcx), 3⟩ }
  , { id := "xor_q",    mnemonic := "xor",  asm := "xorq %rcx, %rax",  bytes := "4831c8"
    , instr := ⟨.bin .xor .q (R .rax) (R .rcx), 3⟩ }
  , { id := "cmp_q",    mnemonic := "cmp",  asm := "cmpq %rcx, %rax",  bytes := "4839c8"
    , instr := ⟨.bin .cmp .q (R .rax) (R .rcx), 3⟩ }
  , { id := "test_q",   mnemonic := "test", asm := "testq %rcx, %rax", bytes := "4885c8"
    , instr := ⟨.bin .test .q (R .rax) (R .rcx), 3⟩ }
  , { id := "shl_q3",   mnemonic := "shl",  asm := "shlq $3, %rax",    bytes := "48c1e003"
    , instr := ⟨.shift .shl .q (R .rax) (.imm8 3), 4⟩ }
  , { id := "shl_b1",   mnemonic := "shl",  asm := "shlb $1, %al",     bytes := "d0e0"
    , instr := ⟨.shift .shl .b (R .rax) (.imm8 1), 2⟩ }
  , { id := "shl_cl",   mnemonic := "shl",  asm := "shlq %cl, %rax",   bytes := "48d3e0"
    , instr := ⟨.shift .shl .q (R .rax) .cl, 3⟩ }
  -- ⭐ THE MASKING BOUNDARY.  These four exist because the harness selftest
  -- FOUND THEIR ABSENCE: with only counts 1 and 3 in the table, a model that
  -- forgot to mask its shift count produced an identical result on every
  -- vector, and the planted bug went uncaught.  `shlq $64` masks to 0 (a
  -- no-op), `shlb $9` masks to 9 which is ≥ the 8-bit width (so CF is
  -- undefined), and `shrq $63` is the largest defined 64-bit count.
  , { id := "shl_q64",  mnemonic := "shl",  asm := "shlq $64, %rax",   bytes := "48c1e040"
    , instr := ⟨.shift .shl .q (R .rax) (.imm8 64), 4⟩ }
  , { id := "shl_b9",   mnemonic := "shl",  asm := "shlb $9, %al",     bytes := "c0e009"
    , instr := ⟨.shift .shl .b (R .rax) (.imm8 9), 3⟩ }
  , { id := "shr_q63",  mnemonic := "shr",  asm := "shrq $63, %rax",   bytes := "48c1e83f"
    , instr := ⟨.shift .shr .q (R .rax) (.imm8 63), 4⟩ }
  , { id := "shr_b9",   mnemonic := "shr",  asm := "shrb $9, %al",     bytes := "c0e809"
    , instr := ⟨.shift .shr .b (R .rax) (.imm8 9), 3⟩ }
  , { id := "shl_q1",   mnemonic := "shl",  asm := "shlq $1, %rax",    bytes := "48d1e0"
    , instr := ⟨.shift .shl .q (R .rax) (.imm8 1), 3⟩ }
  , { id := "shr_q3",   mnemonic := "shr",  asm := "shrq $3, %rax",    bytes := "48c1e803"
    , instr := ⟨.shift .shr .q (R .rax) (.imm8 3), 4⟩ }
  , { id := "shr_b1",   mnemonic := "shr",  asm := "shrb $1, %al",     bytes := "d0e8"
    , instr := ⟨.shift .shr .b (R .rax) (.imm8 1), 2⟩ }
  , { id := "lea",      mnemonic := "lea",  asm := "leaq 8(%rbx,%rcx,4), %rax"
    , bytes := "488d448b08"
    , instr := ⟨.lea .q .rax { base := some .rbx, index := some .rcx, scale := .s4, disp := 8 }, 5⟩ }
  , { id := "lea_d",    mnemonic := "lea",  asm := "leal 8(%rbx), %eax", bytes := "8d4308"
    , instr := ⟨.lea .d .rax { base := some .rbx, disp := 8 }, 3⟩ }
  , { id := "inc_q",    mnemonic := "inc",  asm := "incq %rax",        bytes := "48ffc0"
    , instr := ⟨.un .inc .q (R .rax), 3⟩ }
  , { id := "inc_b",    mnemonic := "inc",  asm := "incb %al",         bytes := "fec0"
    , instr := ⟨.un .inc .b (R .rax), 2⟩ }
  , { id := "dec_q",    mnemonic := "dec",  asm := "decq %rax",        bytes := "48ffc8"
    , instr := ⟨.un .dec .q (R .rax), 3⟩ }
  , { id := "neg_q",    mnemonic := "neg",  asm := "negq %rax",        bytes := "48f7d8"
    , instr := ⟨.un .neg .q (R .rax), 3⟩ }
  , { id := "neg_b",    mnemonic := "neg",  asm := "negb %al",         bytes := "f6d8"
    , instr := ⟨.un .neg .b (R .rax), 2⟩ }
  , { id := "not_q",    mnemonic := "not",  asm := "notq %rax",        bytes := "48f7d0"
    , instr := ⟨.un .not .q (R .rax), 3⟩ }
  , { id := "push_r",   mnemonic := "push", asm := "pushq %rax",       bytes := "50"
    , instr := ⟨.push .q (R .rax), 1⟩ }
  , { id := "pop_r",    mnemonic := "pop",  asm := "popq %rcx",        bytes := "59"
    , instr := ⟨.pop .q (R .rcx), 1⟩ }
  , { id := "jmp_ind",  mnemonic := "jmp",  asm := "jmp *%rax",        bytes := "ffe0"
    , instr := ⟨.jmp (.indirect (R .rax)), 2⟩ }
  , { id := "jmp_rel",  mnemonic := "jmp",  asm := "jmp .+11",         bytes := "eb09"
    , instr := ⟨.jmp (.rel 9), 2⟩ }
  , { id := "je_rel",   mnemonic := "jcc",  asm := "je .+9",           bytes := "7407"
    , instr := ⟨.jcc .e 7, 2⟩ }
  , { id := "jne_rel",  mnemonic := "jcc",  asm := "jne .+7",          bytes := "7505"
    , instr := ⟨.jcc .ne 5, 2⟩ }
  , { id := "call_ind", mnemonic := "call", asm := "call *%rax",       bytes := "ffd0"
    , instr := ⟨.call (.indirect (R .rax)), 2⟩ }
  , { id := "call_rel", mnemonic := "call", asm := "call .+5",         bytes := "e800000000"
    , instr := ⟨.call (.rel 0), 5⟩ }
  ]

/-! ## Pre-states: adversarial first, then pseudo-random

The adversarial list is not "interesting numbers" — every entry is a boundary
some flag rule turns on: the signed/unsigned boundary at each width, all-ones,
the alternating patterns that make PF and AF discriminate, and zero. -/

def adversarial : List (BitVec 64) :=
  [ 0, 1, 2, 0x0F, 0x10, 0x7F, 0x80, 0xFF
  , 0x7FFF, 0x8000, 0xFFFF
  , 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x100000000
  , 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF
  , 0xAAAAAAAAAAAAAAAA, 0x5555555555555555 ]

/-- xorshift64: a deterministic stream, so a run is reproducible from its seed
alone and a disagreement can be replayed without shipping the vector file. -/
def xorshift (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

def randStream (seed : UInt64) : Nat → List (BitVec 64)
  | 0 => []
  | n + 1 =>
    let s := xorshift seed
    BitVec.ofNat 64 s.toNat :: randStream s n

/-- The stack and data windows every vector observes.  Each is wider than any
operand span the vectors use, so a store that ran off the end of its span shows
as a difference in the MARGIN rather than not at all. -/
def windows : List Window :=
  [ { base := 0x1ff0, len := 32 }   -- data: rbx = 0x2000, margin either side
  , { base := 0x7fe0, len := 48 } ] -- stack: rsp = 0x8000, margin below and above

/-- A pre-state built from two operand values and a flag seed.  RBX and RSP are
fixed so the memory windows mean the same thing in every vector; RAX/RCX carry
the values under test. -/
def mkPre (a c : BitVec 64) (fseed : Nat) : Cpu :=
  let f : Flags :=
    { cf := fseed % 2 == 1, pf := fseed / 2 % 2 == 1, af := fseed / 4 % 2 == 1
    , zf := fseed / 8 % 2 == 1, sf := fseed / 16 % 2 == 1, of := fseed / 32 % 2 == 1
    , df := false }
  -- a known, non-uniform pattern in the data window, so a wrong load is visible
  let mem := (List.range 32).foldl
    (fun m i => m.write (0x1ff0 + BitVec.ofNat 64 i) (BitVec.ofNat 8 (0xA0 + i))) Mem.empty
  -- and a known pattern under the stack pointer, so `pop` has something to find
  let mem := (List.range 48).foldl
    (fun m i => m.write (0x7fe0 + BitVec.ofNat 64 i) (BitVec.ofNat 8 (0x10 + i))) mem
  { regs := { rax := a, rcx := c, rbx := 0x2000, rsp := 0x8000 }
    flags := f
    mem := mem
    rip := 0x400000
    oracle := zeroOracle }

/-- The pre-states for one vector: every adversarial pair on the diagonal and
its neighbours, plus a pseudo-random tail. -/
def preStates (seed : UInt64) (nRandom : Nat) : List Cpu :=
  let adv := adversarial
  let diag := adv.map (fun a => mkPre a a 0)
  let pairs := adv.zip (adv.rotateLeft 1) |>.map (fun (a, c) => mkPre a c 5)
  let pairs2 := adv.zip (adv.rotateLeft 7) |>.map (fun (a, c) => mkPre a c 63)
  let rs := randStream seed (2 * nRandom)
  let rnd := (rs.take nRandom).zip (rs.drop nRandom) |>.zipIdx.map
    (fun ((a, c), i) => mkPre a c i)
  diag ++ pairs ++ pairs2 ++ rnd

end X86.Tests
