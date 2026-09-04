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
/-- The HIGH-8 view: AH/CH/DH/BH, bits 15:8 of the named register.  P0 never
used one, so P1 batch 1 is the first differential evidence that `high8` reads
and writes the right eight bits. -/
private def H (r : GPR) : Operand := .reg r true
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
  -- `and_q`, `or_q` and `xor_q` WERE here.  P1 batch 1 covers the same three
  -- forms systematically at all four widths, as `and_rr_q` and its siblings, so
  -- keeping the P0 rows would have run three of the 68-state sweeps twice and
  -- left the batch's own table with a hole where its widest form should be.
  -- `cmp_q` and `test_q` WERE here.  P1 batch 3 covers both mnemonics
  -- systematically at every width and operand shape (`cmp_rr_q`, `test_rr_q`
  -- and their siblings), so the P0 rows would have run a 74-state sweep twice
  -- and left the batch's own table with a hole at its widest register form —
  -- the same reason batch 1 retired `and_q`/`or_q`/`xor_q`.
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
  -- `inc_q`, `inc_b` and `dec_q` WERE here.  P1 batch 4 covers roster families 5
  -- and 6 — `inc`/`dec` at a memory AND a register destination — at all four
  -- widths systematically, so these three would have run their sweeps twice.
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
  -- `jmp_rel`, `je_rel` and `jne_rel` WERE here.  P1 batch 5 covers every
  -- condition at BOTH relative encodings, and `jmp` at both, so these three
  -- were two conditions of sixteen and one encoding of two.
  , { id := "call_ind", mnemonic := "call", asm := "call *%rax",       bytes := "ffd0"
    , instr := ⟨.call (.indirect (R .rax)), 2⟩ }
  , { id := "call_rel", mnemonic := "call", asm := "call .+5",         bytes := "e800000000"
    , instr := ⟨.call (.rel 0), 5⟩ }

  -- ══ P1 BATCH 1 ═════════════════════════════════════════════════════════
  -- The family `0xuxx0-|-|reg` of `p1/roster.tsv`: AND, OR and XOR writing a
  -- REGISTER, clearing CF and OF, computing SF/ZF/PF and leaving AF undefined.
  -- 21 forms in K's roster, 72 K variants; here at every width, because
  -- `andl` zero-extends into the upper 32 bits and `andw` does not, and a
  -- vector set that never crosses that boundary cannot test it.
  --
  -- FOUR THINGS THESE VECTORS REACH THAT P0'S NEVER DID:
  --  * the 32-bit forms, i.e. the zero-extension rule of SDM Vol. 1 §3.4.1.1
  --    on the ALU path rather than only on `mov`;
  --  * a MEMORY SOURCE with a register destination (`andq (%rbx), %rax`);
  --  * the HIGH-8 registers AH/CH, in both operand positions;
  --  * an immediate that the DECODER sign-extended — `$-1` as an imm8 and
  --    `$-2147483648` as an imm32 — which is the convention `Operand.imm`
  --    rests on (X86/Syntax.lean) and which nothing had yet exercised.
  --
  -- ⭐ AND THE ACCUMULATOR FORMS ARE HERE FOR A REASON THAT IS NOT SEMANTIC.
  -- `andb $0x5a, %al` (opcode 24 ib) and `andb $0x5a, %cl` (opcode 80 /4 ib)
  -- decode to the SAME AST: this model is post-decode, so it cannot tell them
  -- apart and should not try.  They are separate vectors because the bytes
  -- differ, and the bytes are the half of the pair that XED is trusted for
  -- (TRUSTBASE.md).  A form whose only distinction is its encoding is exactly
  -- the form a decode bug hides in.
  , { id := "and_rr_b",     mnemonic := "and",   asm := "andb %cl, %al"
    , bytes := "20c8", instr := ⟨.bin .and .b (R .rax) (R .rcx), 2⟩ }
  , { id := "and_rm_b",     mnemonic := "and",   asm := "andb (%rbx), %al"
    , bytes := "2203", instr := ⟨.bin .and .b (R .rax) (M .rbx), 2⟩ }
  , { id := "and_rr_w",     mnemonic := "and",   asm := "andw %cx, %ax"
    , bytes := "6621c8", instr := ⟨.bin .and .w (R .rax) (R .rcx), 3⟩ }
  , { id := "and_rm_w",     mnemonic := "and",   asm := "andw (%rbx), %ax"
    , bytes := "662303", instr := ⟨.bin .and .w (R .rax) (M .rbx), 3⟩ }
  , { id := "and_rr_l",     mnemonic := "and",   asm := "andl %ecx, %eax"
    , bytes := "21c8", instr := ⟨.bin .and .d (R .rax) (R .rcx), 2⟩ }
  , { id := "and_rm_l",     mnemonic := "and",   asm := "andl (%rbx), %eax"
    , bytes := "2303", instr := ⟨.bin .and .d (R .rax) (M .rbx), 2⟩ }
  , { id := "and_rr_q",     mnemonic := "and",   asm := "andq %rcx, %rax"
    , bytes := "4821c8", instr := ⟨.bin .and .q (R .rax) (R .rcx), 3⟩ }
  , { id := "and_rm_q",     mnemonic := "and",   asm := "andq (%rbx), %rax"
    , bytes := "482303", instr := ⟨.bin .and .q (R .rax) (M .rbx), 3⟩ }
  , { id := "and_ri_b",     mnemonic := "and",   asm := "andb $0x5a, %cl"
    , bytes := "80e15a", instr := ⟨.bin .and .b (R .rcx) (.imm 0x5a), 3⟩ }
  , { id := "and_ri_w",     mnemonic := "and",   asm := "andw $0x1234, %cx"
    , bytes := "6681e13412", instr := ⟨.bin .and .w (R .rcx) (.imm 0x1234), 5⟩ }
  , { id := "and_ri_l",     mnemonic := "and",   asm := "andl $0x12345678, %ecx"
    , bytes := "81e178563412", instr := ⟨.bin .and .d (R .rcx) (.imm 0x12345678), 6⟩ }
  , { id := "and_ri_q",     mnemonic := "and",   asm := "andq $0x12345678, %rcx"
    , bytes := "4881e178563412", instr := ⟨.bin .and .q (R .rcx) (.imm 0x12345678), 7⟩ }
  , { id := "and_ri_q8n",   mnemonic := "and",   asm := "andq $-1, %rcx"
    , bytes := "4883e1ff", instr := ⟨.bin .and .q (R .rcx) (.imm 0xffffffffffffffff), 4⟩ }
  , { id := "and_ri_q32n",  mnemonic := "and",   asm := "andq $-2147483648, %rcx"
    , bytes := "4881e100000080", instr := ⟨.bin .and .q (R .rcx) (.imm 0xffffffff80000000), 7⟩ }
  , { id := "and_acc_b",    mnemonic := "and",   asm := "andb $0x5a, %al"
    , bytes := "245a", instr := ⟨.bin .and .b (R .rax) (.imm 0x5a), 2⟩ }
  , { id := "and_acc_w",    mnemonic := "and",   asm := "andw $0x1234, %ax"
    , bytes := "66253412", instr := ⟨.bin .and .w (R .rax) (.imm 0x1234), 4⟩ }
  , { id := "and_acc_l",    mnemonic := "and",   asm := "andl $0x12345678, %eax"
    , bytes := "2578563412", instr := ⟨.bin .and .d (R .rax) (.imm 0x12345678), 5⟩ }
  , { id := "and_acc_q",    mnemonic := "and",   asm := "andq $0x12345678, %rax"
    , bytes := "482578563412", instr := ⟨.bin .and .q (R .rax) (.imm 0x12345678), 6⟩ }
  , { id := "and_h8s",      mnemonic := "and",   asm := "andb %ch, %al"
    , bytes := "20e8", instr := ⟨.bin .and .b (R .rax) (H .rcx), 2⟩ }
  , { id := "and_h8d",      mnemonic := "and",   asm := "andb %cl, %ah"
    , bytes := "20cc", instr := ⟨.bin .and .b (H .rax) (R .rcx), 2⟩ }
  , { id := "or_rr_b",      mnemonic := "or",    asm := "orb %cl, %al"
    , bytes := "08c8", instr := ⟨.bin .or .b (R .rax) (R .rcx), 2⟩ }
  , { id := "or_rm_b",      mnemonic := "or",    asm := "orb (%rbx), %al"
    , bytes := "0a03", instr := ⟨.bin .or .b (R .rax) (M .rbx), 2⟩ }
  , { id := "or_rr_w",      mnemonic := "or",    asm := "orw %cx, %ax"
    , bytes := "6609c8", instr := ⟨.bin .or .w (R .rax) (R .rcx), 3⟩ }
  , { id := "or_rm_w",      mnemonic := "or",    asm := "orw (%rbx), %ax"
    , bytes := "660b03", instr := ⟨.bin .or .w (R .rax) (M .rbx), 3⟩ }
  , { id := "or_rr_l",      mnemonic := "or",    asm := "orl %ecx, %eax"
    , bytes := "09c8", instr := ⟨.bin .or .d (R .rax) (R .rcx), 2⟩ }
  , { id := "or_rm_l",      mnemonic := "or",    asm := "orl (%rbx), %eax"
    , bytes := "0b03", instr := ⟨.bin .or .d (R .rax) (M .rbx), 2⟩ }
  , { id := "or_rr_q",      mnemonic := "or",    asm := "orq %rcx, %rax"
    , bytes := "4809c8", instr := ⟨.bin .or .q (R .rax) (R .rcx), 3⟩ }
  , { id := "or_rm_q",      mnemonic := "or",    asm := "orq (%rbx), %rax"
    , bytes := "480b03", instr := ⟨.bin .or .q (R .rax) (M .rbx), 3⟩ }
  , { id := "or_ri_b",      mnemonic := "or",    asm := "orb $0x5a, %cl"
    , bytes := "80c95a", instr := ⟨.bin .or .b (R .rcx) (.imm 0x5a), 3⟩ }
  , { id := "or_ri_w",      mnemonic := "or",    asm := "orw $0x1234, %cx"
    , bytes := "6681c93412", instr := ⟨.bin .or .w (R .rcx) (.imm 0x1234), 5⟩ }
  , { id := "or_ri_l",      mnemonic := "or",    asm := "orl $0x12345678, %ecx"
    , bytes := "81c978563412", instr := ⟨.bin .or .d (R .rcx) (.imm 0x12345678), 6⟩ }
  , { id := "or_ri_q",      mnemonic := "or",    asm := "orq $0x12345678, %rcx"
    , bytes := "4881c978563412", instr := ⟨.bin .or .q (R .rcx) (.imm 0x12345678), 7⟩ }
  , { id := "or_ri_q8n",    mnemonic := "or",    asm := "orq $-1, %rcx"
    , bytes := "4883c9ff", instr := ⟨.bin .or .q (R .rcx) (.imm 0xffffffffffffffff), 4⟩ }
  , { id := "or_ri_q32n",   mnemonic := "or",    asm := "orq $-2147483648, %rcx"
    , bytes := "4881c900000080", instr := ⟨.bin .or .q (R .rcx) (.imm 0xffffffff80000000), 7⟩ }
  , { id := "or_acc_b",     mnemonic := "or",    asm := "orb $0x5a, %al"
    , bytes := "0c5a", instr := ⟨.bin .or .b (R .rax) (.imm 0x5a), 2⟩ }
  , { id := "or_acc_w",     mnemonic := "or",    asm := "orw $0x1234, %ax"
    , bytes := "660d3412", instr := ⟨.bin .or .w (R .rax) (.imm 0x1234), 4⟩ }
  , { id := "or_acc_l",     mnemonic := "or",    asm := "orl $0x12345678, %eax"
    , bytes := "0d78563412", instr := ⟨.bin .or .d (R .rax) (.imm 0x12345678), 5⟩ }
  , { id := "or_acc_q",     mnemonic := "or",    asm := "orq $0x12345678, %rax"
    , bytes := "480d78563412", instr := ⟨.bin .or .q (R .rax) (.imm 0x12345678), 6⟩ }
  , { id := "or_h8s",       mnemonic := "or",    asm := "orb %ch, %al"
    , bytes := "08e8", instr := ⟨.bin .or .b (R .rax) (H .rcx), 2⟩ }
  , { id := "or_h8d",       mnemonic := "or",    asm := "orb %cl, %ah"
    , bytes := "08cc", instr := ⟨.bin .or .b (H .rax) (R .rcx), 2⟩ }
  , { id := "xor_rr_b",     mnemonic := "xor",   asm := "xorb %cl, %al"
    , bytes := "30c8", instr := ⟨.bin .xor .b (R .rax) (R .rcx), 2⟩ }
  , { id := "xor_rm_b",     mnemonic := "xor",   asm := "xorb (%rbx), %al"
    , bytes := "3203", instr := ⟨.bin .xor .b (R .rax) (M .rbx), 2⟩ }
  , { id := "xor_rr_w",     mnemonic := "xor",   asm := "xorw %cx, %ax"
    , bytes := "6631c8", instr := ⟨.bin .xor .w (R .rax) (R .rcx), 3⟩ }
  , { id := "xor_rm_w",     mnemonic := "xor",   asm := "xorw (%rbx), %ax"
    , bytes := "663303", instr := ⟨.bin .xor .w (R .rax) (M .rbx), 3⟩ }
  , { id := "xor_rr_l",     mnemonic := "xor",   asm := "xorl %ecx, %eax"
    , bytes := "31c8", instr := ⟨.bin .xor .d (R .rax) (R .rcx), 2⟩ }
  , { id := "xor_rm_l",     mnemonic := "xor",   asm := "xorl (%rbx), %eax"
    , bytes := "3303", instr := ⟨.bin .xor .d (R .rax) (M .rbx), 2⟩ }
  , { id := "xor_rr_q",     mnemonic := "xor",   asm := "xorq %rcx, %rax"
    , bytes := "4831c8", instr := ⟨.bin .xor .q (R .rax) (R .rcx), 3⟩ }
  , { id := "xor_rm_q",     mnemonic := "xor",   asm := "xorq (%rbx), %rax"
    , bytes := "483303", instr := ⟨.bin .xor .q (R .rax) (M .rbx), 3⟩ }
  , { id := "xor_ri_b",     mnemonic := "xor",   asm := "xorb $0x5a, %cl"
    , bytes := "80f15a", instr := ⟨.bin .xor .b (R .rcx) (.imm 0x5a), 3⟩ }
  , { id := "xor_ri_w",     mnemonic := "xor",   asm := "xorw $0x1234, %cx"
    , bytes := "6681f13412", instr := ⟨.bin .xor .w (R .rcx) (.imm 0x1234), 5⟩ }
  , { id := "xor_ri_l",     mnemonic := "xor",   asm := "xorl $0x12345678, %ecx"
    , bytes := "81f178563412", instr := ⟨.bin .xor .d (R .rcx) (.imm 0x12345678), 6⟩ }
  , { id := "xor_ri_q",     mnemonic := "xor",   asm := "xorq $0x12345678, %rcx"
    , bytes := "4881f178563412", instr := ⟨.bin .xor .q (R .rcx) (.imm 0x12345678), 7⟩ }
  , { id := "xor_ri_q8n",   mnemonic := "xor",   asm := "xorq $-1, %rcx"
    , bytes := "4883f1ff", instr := ⟨.bin .xor .q (R .rcx) (.imm 0xffffffffffffffff), 4⟩ }
  , { id := "xor_ri_q32n",  mnemonic := "xor",   asm := "xorq $-2147483648, %rcx"
    , bytes := "4881f100000080", instr := ⟨.bin .xor .q (R .rcx) (.imm 0xffffffff80000000), 7⟩ }
  , { id := "xor_acc_b",    mnemonic := "xor",   asm := "xorb $0x5a, %al"
    , bytes := "345a", instr := ⟨.bin .xor .b (R .rax) (.imm 0x5a), 2⟩ }
  , { id := "xor_acc_w",    mnemonic := "xor",   asm := "xorw $0x1234, %ax"
    , bytes := "66353412", instr := ⟨.bin .xor .w (R .rax) (.imm 0x1234), 4⟩ }
  , { id := "xor_acc_l",    mnemonic := "xor",   asm := "xorl $0x12345678, %eax"
    , bytes := "3578563412", instr := ⟨.bin .xor .d (R .rax) (.imm 0x12345678), 5⟩ }
  , { id := "xor_acc_q",    mnemonic := "xor",   asm := "xorq $0x12345678, %rax"
    , bytes := "483578563412", instr := ⟨.bin .xor .q (R .rax) (.imm 0x12345678), 6⟩ }
  , { id := "xor_h8s",      mnemonic := "xor",   asm := "xorb %ch, %al"
    , bytes := "30e8", instr := ⟨.bin .xor .b (R .rax) (H .rcx), 2⟩ }
  , { id := "xor_h8d",      mnemonic := "xor",   asm := "xorb %cl, %ah"
    , bytes := "30cc", instr := ⟨.bin .xor .b (H .rax) (R .rcx), 2⟩ }

  -- ══ P1 BATCH 2 ═════════════════════════════════════════════════════════
  -- The family `xxxxxx-|cf|reg` of `p1/roster.tsv`: ADC and SBB, the first
  -- forms whose RESULT reads a flag.  14 forms in K's roster, 48 K variants.
  -- Same shape sweep as batch 1, because the shapes are the same shapes — the
  -- new content is entirely in the carry, and the carry lives in the
  -- PRE-STATES rather than in the vectors.
  , { id := "adc_rr_b",     mnemonic := "adc",   asm := "adcb %cl, %al"
    , bytes := "10c8", instr := ⟨.bin .adc .b (R .rax) (R .rcx), 2⟩ }
  , { id := "adc_rm_b",     mnemonic := "adc",   asm := "adcb (%rbx), %al"
    , bytes := "1203", instr := ⟨.bin .adc .b (R .rax) (M .rbx), 2⟩ }
  , { id := "adc_rr_w",     mnemonic := "adc",   asm := "adcw %cx, %ax"
    , bytes := "6611c8", instr := ⟨.bin .adc .w (R .rax) (R .rcx), 3⟩ }
  , { id := "adc_rm_w",     mnemonic := "adc",   asm := "adcw (%rbx), %ax"
    , bytes := "661303", instr := ⟨.bin .adc .w (R .rax) (M .rbx), 3⟩ }
  , { id := "adc_rr_l",     mnemonic := "adc",   asm := "adcl %ecx, %eax"
    , bytes := "11c8", instr := ⟨.bin .adc .d (R .rax) (R .rcx), 2⟩ }
  , { id := "adc_rm_l",     mnemonic := "adc",   asm := "adcl (%rbx), %eax"
    , bytes := "1303", instr := ⟨.bin .adc .d (R .rax) (M .rbx), 2⟩ }
  , { id := "adc_rr_q",     mnemonic := "adc",   asm := "adcq %rcx, %rax"
    , bytes := "4811c8", instr := ⟨.bin .adc .q (R .rax) (R .rcx), 3⟩ }
  , { id := "adc_rm_q",     mnemonic := "adc",   asm := "adcq (%rbx), %rax"
    , bytes := "481303", instr := ⟨.bin .adc .q (R .rax) (M .rbx), 3⟩ }
  , { id := "adc_ri_b",     mnemonic := "adc",   asm := "adcb $0x5a, %cl"
    , bytes := "80d15a", instr := ⟨.bin .adc .b (R .rcx) (.imm 0x5a), 3⟩ }
  , { id := "adc_ri_w",     mnemonic := "adc",   asm := "adcw $0x1234, %cx"
    , bytes := "6681d13412", instr := ⟨.bin .adc .w (R .rcx) (.imm 0x1234), 5⟩ }
  , { id := "adc_ri_l",     mnemonic := "adc",   asm := "adcl $0x12345678, %ecx"
    , bytes := "81d178563412", instr := ⟨.bin .adc .d (R .rcx) (.imm 0x12345678), 6⟩ }
  , { id := "adc_ri_q",     mnemonic := "adc",   asm := "adcq $0x12345678, %rcx"
    , bytes := "4881d178563412", instr := ⟨.bin .adc .q (R .rcx) (.imm 0x12345678), 7⟩ }
  , { id := "adc_ri_q8n",   mnemonic := "adc",   asm := "adcq $-1, %rcx"
    , bytes := "4883d1ff", instr := ⟨.bin .adc .q (R .rcx) (.imm 0xffffffffffffffff), 4⟩ }
  , { id := "adc_ri_q32n",  mnemonic := "adc",   asm := "adcq $-2147483648, %rcx"
    , bytes := "4881d100000080", instr := ⟨.bin .adc .q (R .rcx) (.imm 0xffffffff80000000), 7⟩ }
  , { id := "adc_acc_b",    mnemonic := "adc",   asm := "adcb $0x5a, %al"
    , bytes := "145a", instr := ⟨.bin .adc .b (R .rax) (.imm 0x5a), 2⟩ }
  , { id := "adc_acc_w",    mnemonic := "adc",   asm := "adcw $0x1234, %ax"
    , bytes := "66153412", instr := ⟨.bin .adc .w (R .rax) (.imm 0x1234), 4⟩ }
  , { id := "adc_acc_l",    mnemonic := "adc",   asm := "adcl $0x12345678, %eax"
    , bytes := "1578563412", instr := ⟨.bin .adc .d (R .rax) (.imm 0x12345678), 5⟩ }
  , { id := "adc_acc_q",    mnemonic := "adc",   asm := "adcq $0x12345678, %rax"
    , bytes := "481578563412", instr := ⟨.bin .adc .q (R .rax) (.imm 0x12345678), 6⟩ }
  , { id := "adc_h8s",      mnemonic := "adc",   asm := "adcb %ch, %al"
    , bytes := "10e8", instr := ⟨.bin .adc .b (R .rax) (H .rcx), 2⟩ }
  , { id := "adc_h8d",      mnemonic := "adc",   asm := "adcb %cl, %ah"
    , bytes := "10cc", instr := ⟨.bin .adc .b (H .rax) (R .rcx), 2⟩ }
  , { id := "sbb_rr_b",     mnemonic := "sbb",   asm := "sbbb %cl, %al"
    , bytes := "18c8", instr := ⟨.bin .sbb .b (R .rax) (R .rcx), 2⟩ }
  , { id := "sbb_rm_b",     mnemonic := "sbb",   asm := "sbbb (%rbx), %al"
    , bytes := "1a03", instr := ⟨.bin .sbb .b (R .rax) (M .rbx), 2⟩ }
  , { id := "sbb_rr_w",     mnemonic := "sbb",   asm := "sbbw %cx, %ax"
    , bytes := "6619c8", instr := ⟨.bin .sbb .w (R .rax) (R .rcx), 3⟩ }
  , { id := "sbb_rm_w",     mnemonic := "sbb",   asm := "sbbw (%rbx), %ax"
    , bytes := "661b03", instr := ⟨.bin .sbb .w (R .rax) (M .rbx), 3⟩ }
  , { id := "sbb_rr_l",     mnemonic := "sbb",   asm := "sbbl %ecx, %eax"
    , bytes := "19c8", instr := ⟨.bin .sbb .d (R .rax) (R .rcx), 2⟩ }
  , { id := "sbb_rm_l",     mnemonic := "sbb",   asm := "sbbl (%rbx), %eax"
    , bytes := "1b03", instr := ⟨.bin .sbb .d (R .rax) (M .rbx), 2⟩ }
  , { id := "sbb_rr_q",     mnemonic := "sbb",   asm := "sbbq %rcx, %rax"
    , bytes := "4819c8", instr := ⟨.bin .sbb .q (R .rax) (R .rcx), 3⟩ }
  , { id := "sbb_rm_q",     mnemonic := "sbb",   asm := "sbbq (%rbx), %rax"
    , bytes := "481b03", instr := ⟨.bin .sbb .q (R .rax) (M .rbx), 3⟩ }
  , { id := "sbb_ri_b",     mnemonic := "sbb",   asm := "sbbb $0x5a, %cl"
    , bytes := "80d95a", instr := ⟨.bin .sbb .b (R .rcx) (.imm 0x5a), 3⟩ }
  , { id := "sbb_ri_w",     mnemonic := "sbb",   asm := "sbbw $0x1234, %cx"
    , bytes := "6681d93412", instr := ⟨.bin .sbb .w (R .rcx) (.imm 0x1234), 5⟩ }
  , { id := "sbb_ri_l",     mnemonic := "sbb",   asm := "sbbl $0x12345678, %ecx"
    , bytes := "81d978563412", instr := ⟨.bin .sbb .d (R .rcx) (.imm 0x12345678), 6⟩ }
  , { id := "sbb_ri_q",     mnemonic := "sbb",   asm := "sbbq $0x12345678, %rcx"
    , bytes := "4881d978563412", instr := ⟨.bin .sbb .q (R .rcx) (.imm 0x12345678), 7⟩ }
  , { id := "sbb_ri_q8n",   mnemonic := "sbb",   asm := "sbbq $-1, %rcx"
    , bytes := "4883d9ff", instr := ⟨.bin .sbb .q (R .rcx) (.imm 0xffffffffffffffff), 4⟩ }
  , { id := "sbb_ri_q32n",  mnemonic := "sbb",   asm := "sbbq $-2147483648, %rcx"
    , bytes := "4881d900000080", instr := ⟨.bin .sbb .q (R .rcx) (.imm 0xffffffff80000000), 7⟩ }
  , { id := "sbb_acc_b",    mnemonic := "sbb",   asm := "sbbb $0x5a, %al"
    , bytes := "1c5a", instr := ⟨.bin .sbb .b (R .rax) (.imm 0x5a), 2⟩ }
  , { id := "sbb_acc_w",    mnemonic := "sbb",   asm := "sbbw $0x1234, %ax"
    , bytes := "661d3412", instr := ⟨.bin .sbb .w (R .rax) (.imm 0x1234), 4⟩ }
  , { id := "sbb_acc_l",    mnemonic := "sbb",   asm := "sbbl $0x12345678, %eax"
    , bytes := "1d78563412", instr := ⟨.bin .sbb .d (R .rax) (.imm 0x12345678), 5⟩ }
  , { id := "sbb_acc_q",    mnemonic := "sbb",   asm := "sbbq $0x12345678, %rax"
    , bytes := "481d78563412", instr := ⟨.bin .sbb .q (R .rax) (.imm 0x12345678), 6⟩ }
  , { id := "sbb_h8s",      mnemonic := "sbb",   asm := "sbbb %ch, %al"
    , bytes := "18e8", instr := ⟨.bin .sbb .b (R .rax) (H .rcx), 2⟩ }
  , { id := "sbb_h8d",      mnemonic := "sbb",   asm := "sbbb %cl, %ah"
    , bytes := "18cc", instr := ⟨.bin .sbb .b (H .rax) (R .rcx), 2⟩ }
  -- ══ P1 BATCH 3 ═════════════════════════════════════════════════════════
  -- Families `xxxxxx-|-|flags/ctl` (CMP, 11 forms, 38 K variants) and
  -- `0xuxx0-|-|flags/ctl` (TEST, 8 forms, 25 K variants) of `p1/roster.tsv`:
  -- the two mnemonics whose DESTINATION IS THE FLAGS.  Nineteen forms, run
  -- together because they are one template question — does the destination get
  -- written? — asked of `sub` and of `and` respectively.
  --
  -- NO NEW TEMPLATE AND NO NEW MNEMONIC: `cmp` and `test` were both in P0's
  -- roster and `step` already discards their results.  This is what a
  -- zero-surcharge batch looks like — vectors, anchors and evidence, no
  -- semantics.
  --
  -- FOUR THINGS THESE VECTORS REACH THAT NOTHING BEFORE THEM DID:
  --  * ⭐ A MEMORY OPERAND IN THE DESTINATION POSITION THAT IS READ AND NEVER
  --    WRITTEN (`cmpq %rax, (%rbx)`, `testq $imm, (%rbx)`).  Every earlier
  --    memory destination in this repository — `mov`, `push`, `call` — was
  --    written.  A model that wrote `cmp`'s result back would be caught here
  --    and nowhere else, which is why that is this batch's planted bug.
  --  * `cmp` and `test` at widths b, w and l.  P0 shipped one vector each, both
  --    at q, so three quarters of their width behaviour was untested — and the
  --    32-bit form is where the zero-extension rule would show if these
  --    instructions wrote anything at all.
  --  * ⭐ RIP-RELATIVE ADDRESSING (`cmp_rip_q`), which `Ea.addr` has always
  --    implemented and which NO differential vector has ever executed — the
  --    only prior evidence was one `lea` anchor, i.e. this model checked
  --    against itself.  The roster is what surfaced it: K files `cmpq $L, %r64`
  --    as its own form, and asking what a `label` operand is post-decode leads
  --    straight to the addressing mode nothing had exercised.
  --  * The accumulator short forms at all four widths, for both mnemonics.
  --
  -- ⭐ AND WHAT `label` TURNS OUT TO BE, since two of CMP's eleven forms are
  -- `r,label` and `m,label`.  K's rule reads the operand from `<functargets>`
  -- as a `PointerVal`: it is an address the ASSEMBLER has not yet resolved.
  -- By the time a linker is done it is an ordinary sign-extended imm32, and
  -- `cmpq $L, %rax` and `cmpq $0x12345678, %rax` are THE SAME BYTES with a
  -- different number in them.  A post-decode model cannot distinguish them and
  -- should not try (X86/Syntax.lean).  So those two forms are covered by
  -- `cmp_ri_q`/`cmp_mi_q` BY IDENTITY, stated here rather than counted twice —
  -- and the addressing mode a label actually implies, RIP-relative, is covered
  -- by a vector of its own above.
  , { id := "cmp_rr_b", mnemonic := "cmp", asm := "cmpb %cl, %al"
    , bytes := "38c8", instr := ⟨.bin .cmp .b (R .rax) (R .rcx), 2⟩ }
  , { id := "cmp_rr_w", mnemonic := "cmp", asm := "cmpw %cx, %ax"
    , bytes := "6639c8", instr := ⟨.bin .cmp .w (R .rax) (R .rcx), 3⟩ }
  , { id := "cmp_rr_l", mnemonic := "cmp", asm := "cmpl %ecx, %eax"
    , bytes := "39c8", instr := ⟨.bin .cmp .d (R .rax) (R .rcx), 2⟩ }
  , { id := "cmp_rr_q", mnemonic := "cmp", asm := "cmpq %rcx, %rax"
    , bytes := "4839c8", instr := ⟨.bin .cmp .q (R .rax) (R .rcx), 3⟩ }
  , { id := "cmp_rm_b", mnemonic := "cmp", asm := "cmpb (%rbx), %al"
    , bytes := "3a03", instr := ⟨.bin .cmp .b (R .rax) (M .rbx), 2⟩ }
  , { id := "cmp_rm_w", mnemonic := "cmp", asm := "cmpw (%rbx), %ax"
    , bytes := "663b03", instr := ⟨.bin .cmp .w (R .rax) (M .rbx), 3⟩ }
  , { id := "cmp_rm_l", mnemonic := "cmp", asm := "cmpl (%rbx), %eax"
    , bytes := "3b03", instr := ⟨.bin .cmp .d (R .rax) (M .rbx), 2⟩ }
  , { id := "cmp_rm_q", mnemonic := "cmp", asm := "cmpq (%rbx), %rax"
    , bytes := "483b03", instr := ⟨.bin .cmp .q (R .rax) (M .rbx), 3⟩ }
  , { id := "cmp_mr_b", mnemonic := "cmp", asm := "cmpb %al, (%rbx)"
    , bytes := "3803", instr := ⟨.bin .cmp .b (M .rbx) (R .rax), 2⟩ }
  , { id := "cmp_mr_w", mnemonic := "cmp", asm := "cmpw %ax, (%rbx)"
    , bytes := "663903", instr := ⟨.bin .cmp .w (M .rbx) (R .rax), 3⟩ }
  , { id := "cmp_mr_l", mnemonic := "cmp", asm := "cmpl %eax, (%rbx)"
    , bytes := "3903", instr := ⟨.bin .cmp .d (M .rbx) (R .rax), 2⟩ }
  , { id := "cmp_mr_q", mnemonic := "cmp", asm := "cmpq %rax, (%rbx)"
    , bytes := "483903", instr := ⟨.bin .cmp .q (M .rbx) (R .rax), 3⟩ }
  , { id := "cmp_ri_b", mnemonic := "cmp", asm := "cmpb $0x5a, %cl"
    , bytes := "80f95a", instr := ⟨.bin .cmp .b (R .rcx) (.imm 0x5a), 3⟩ }
  , { id := "cmp_ri_w", mnemonic := "cmp", asm := "cmpw $0x1234, %cx"
    , bytes := "6681f93412", instr := ⟨.bin .cmp .w (R .rcx) (.imm 0x1234), 5⟩ }
  , { id := "cmp_ri_l", mnemonic := "cmp", asm := "cmpl $0x12345678, %ecx"
    , bytes := "81f978563412", instr := ⟨.bin .cmp .d (R .rcx) (.imm 0x12345678), 6⟩ }
  , { id := "cmp_ri_q", mnemonic := "cmp", asm := "cmpq $0x12345678, %rcx"
    , bytes := "4881f978563412", instr := ⟨.bin .cmp .q (R .rcx) (.imm 0x12345678), 7⟩ }
  , { id := "cmp_ri_q8n", mnemonic := "cmp", asm := "cmpq $-1, %rcx"
    , bytes := "4883f9ff", instr := ⟨.bin .cmp .q (R .rcx) (.imm 0xffffffffffffffff), 4⟩ }
  , { id := "cmp_ri_q32n", mnemonic := "cmp", asm := "cmpq $-2147483648, %rcx"
    , bytes := "4881f900000080", instr := ⟨.bin .cmp .q (R .rcx) (.imm 0xffffffff80000000), 7⟩ }
  , { id := "cmp_acc_b", mnemonic := "cmp", asm := "cmpb $0x5a, %al"
    , bytes := "3c5a", instr := ⟨.bin .cmp .b (R .rax) (.imm 0x5a), 2⟩ }
  , { id := "cmp_acc_w", mnemonic := "cmp", asm := "cmpw $0x1234, %ax"
    , bytes := "663d3412", instr := ⟨.bin .cmp .w (R .rax) (.imm 0x1234), 4⟩ }
  , { id := "cmp_acc_l", mnemonic := "cmp", asm := "cmpl $0x12345678, %eax"
    , bytes := "3d78563412", instr := ⟨.bin .cmp .d (R .rax) (.imm 0x12345678), 5⟩ }
  , { id := "cmp_acc_q", mnemonic := "cmp", asm := "cmpq $0x12345678, %rax"
    , bytes := "483d78563412", instr := ⟨.bin .cmp .q (R .rax) (.imm 0x12345678), 6⟩ }
  , { id := "cmp_mi_b", mnemonic := "cmp", asm := "cmpb $0x5a, (%rbx)"
    , bytes := "803b5a", instr := ⟨.bin .cmp .b (M .rbx) (.imm 0x5a), 3⟩ }
  , { id := "cmp_mi_w", mnemonic := "cmp", asm := "cmpw $0x1234, (%rbx)"
    , bytes := "66813b3412", instr := ⟨.bin .cmp .w (M .rbx) (.imm 0x1234), 5⟩ }
  , { id := "cmp_mi_l", mnemonic := "cmp", asm := "cmpl $0x12345678, (%rbx)"
    , bytes := "813b78563412", instr := ⟨.bin .cmp .d (M .rbx) (.imm 0x12345678), 6⟩ }
  , { id := "cmp_mi_q", mnemonic := "cmp", asm := "cmpq $0x12345678, (%rbx)"
    , bytes := "48813b78563412", instr := ⟨.bin .cmp .q (M .rbx) (.imm 0x12345678), 7⟩ }
  , { id := "cmp_h8s", mnemonic := "cmp", asm := "cmpb %ch, %al"
    , bytes := "38e8", instr := ⟨.bin .cmp .b (R .rax) (H .rcx), 2⟩ }
  , { id := "cmp_h8d", mnemonic := "cmp", asm := "cmpb %cl, %ah"
    , bytes := "38cc", instr := ⟨.bin .cmp .b (H .rax) (R .rcx), 2⟩ }
  , { id := "cmp_rip_q", mnemonic := "cmp", asm := "cmpq $0x12345678, -0x3fe00b(%rip)"
    , bytes := "48813df51fc0ff78563412"
    , instr := ⟨.bin .cmp .q (.mem { ripRel := true, disp := 0xffffffffffc01ff5 })
                (.imm 0x12345678), 11⟩ }
  , { id := "test_rr_b", mnemonic := "test", asm := "testb %cl, %al"
    , bytes := "84c8", instr := ⟨.bin .test .b (R .rax) (R .rcx), 2⟩ }
  , { id := "test_rr_w", mnemonic := "test", asm := "testw %cx, %ax"
    , bytes := "6685c8", instr := ⟨.bin .test .w (R .rax) (R .rcx), 3⟩ }
  , { id := "test_rr_l", mnemonic := "test", asm := "testl %ecx, %eax"
    , bytes := "85c8", instr := ⟨.bin .test .d (R .rax) (R .rcx), 2⟩ }
  , { id := "test_rr_q", mnemonic := "test", asm := "testq %rcx, %rax"
    , bytes := "4885c8", instr := ⟨.bin .test .q (R .rax) (R .rcx), 3⟩ }
  , { id := "test_mr_b", mnemonic := "test", asm := "testb %al, (%rbx)"
    , bytes := "8403", instr := ⟨.bin .test .b (M .rbx) (R .rax), 2⟩ }
  , { id := "test_mr_w", mnemonic := "test", asm := "testw %ax, (%rbx)"
    , bytes := "668503", instr := ⟨.bin .test .w (M .rbx) (R .rax), 3⟩ }
  , { id := "test_mr_l", mnemonic := "test", asm := "testl %eax, (%rbx)"
    , bytes := "8503", instr := ⟨.bin .test .d (M .rbx) (R .rax), 2⟩ }
  , { id := "test_mr_q", mnemonic := "test", asm := "testq %rax, (%rbx)"
    , bytes := "488503", instr := ⟨.bin .test .q (M .rbx) (R .rax), 3⟩ }
  , { id := "test_ri_b", mnemonic := "test", asm := "testb $0x5a, %cl"
    , bytes := "f6c15a", instr := ⟨.bin .test .b (R .rcx) (.imm 0x5a), 3⟩ }
  , { id := "test_ri_w", mnemonic := "test", asm := "testw $0x1234, %cx"
    , bytes := "66f7c13412", instr := ⟨.bin .test .w (R .rcx) (.imm 0x1234), 5⟩ }
  , { id := "test_ri_l", mnemonic := "test", asm := "testl $0x12345678, %ecx"
    , bytes := "f7c178563412", instr := ⟨.bin .test .d (R .rcx) (.imm 0x12345678), 6⟩ }
  , { id := "test_ri_q", mnemonic := "test", asm := "testq $0x12345678, %rcx"
    , bytes := "48f7c178563412", instr := ⟨.bin .test .q (R .rcx) (.imm 0x12345678), 7⟩ }
  , { id := "test_ri_q32n", mnemonic := "test", asm := "testq $-2147483648, %rcx"
    , bytes := "48f7c100000080", instr := ⟨.bin .test .q (R .rcx) (.imm 0xffffffff80000000), 7⟩ }
  , { id := "test_acc_b", mnemonic := "test", asm := "testb $0x5a, %al"
    , bytes := "a85a", instr := ⟨.bin .test .b (R .rax) (.imm 0x5a), 2⟩ }
  , { id := "test_acc_w", mnemonic := "test", asm := "testw $0x1234, %ax"
    , bytes := "66a93412", instr := ⟨.bin .test .w (R .rax) (.imm 0x1234), 4⟩ }
  , { id := "test_acc_l", mnemonic := "test", asm := "testl $0x12345678, %eax"
    , bytes := "a978563412", instr := ⟨.bin .test .d (R .rax) (.imm 0x12345678), 5⟩ }
  , { id := "test_acc_q", mnemonic := "test", asm := "testq $0x12345678, %rax"
    , bytes := "48a978563412", instr := ⟨.bin .test .q (R .rax) (.imm 0x12345678), 6⟩ }
  , { id := "test_mi_b", mnemonic := "test", asm := "testb $0x5a, (%rbx)"
    , bytes := "f6035a", instr := ⟨.bin .test .b (M .rbx) (.imm 0x5a), 3⟩ }
  , { id := "test_mi_w", mnemonic := "test", asm := "testw $0x1234, (%rbx)"
    , bytes := "66f7033412", instr := ⟨.bin .test .w (M .rbx) (.imm 0x1234), 5⟩ }
  , { id := "test_mi_l", mnemonic := "test", asm := "testl $0x12345678, (%rbx)"
    , bytes := "f70378563412", instr := ⟨.bin .test .d (M .rbx) (.imm 0x12345678), 6⟩ }
  , { id := "test_mi_q", mnemonic := "test", asm := "testq $0x12345678, (%rbx)"
    , bytes := "48f70378563412", instr := ⟨.bin .test .q (M .rbx) (.imm 0x12345678), 7⟩ }
  , { id := "test_h8s", mnemonic := "test", asm := "testb %ch, %al"
    , bytes := "84e8", instr := ⟨.bin .test .b (R .rax) (H .rcx), 2⟩ }
  , { id := "test_h8d", mnemonic := "test", asm := "testb %cl, %ah"
    , bytes := "84cc", instr := ⟨.bin .test .b (H .rax) (R .rcx), 2⟩ }
  -- ══ P1 BATCH 4 ═════════════════════════════════════════════════════════
  -- Families `0xuxx0-|-|mem` (AND/OR/XOR to a MEMORY destination, 6 forms),
  -- `-xxxxx-|-|mem` (INC/DEC at a memory destination, 2 forms) and
  -- `-xxxxx-|-|reg` (INC/DEC at a register destination, 2 forms) of
  -- `p1/roster.tsv`.  Ten forms, and the LAST of the wave's zero-surcharge
  -- ones: every batch after this invents a template.
  --
  -- ⭐ THE NEW GROUND IS THE READ-MODIFY-WRITE TO MEMORY.  Batch 3 put a memory
  -- operand in a destination that is READ and never written.  These forms READ
  -- IT, COMPUTE, WRITE IT BACK AND SET FLAGS — and until now the only memory
  -- this repository ever WROTE was `mov`, `push` and `call`, none of which
  -- touch a flag and none of which read the location first.
  --
  -- ⛔ AND THESE ARE THE FORMS D15 REMOVED A FALSE CLAIM ABOUT.  The coverage
  -- table said `and`/`or`/`xor` covered the shape `m,r (q)` and no such vector
  -- existed; batch 3 deleted the claim and this batch is what earns it back.
  -- The row goes back with `m,r · m,imm` at ALL FOUR WIDTHS, which is more than
  -- the false claim ever asserted, and `mem_dest_claims_are_backed` is now what
  -- holds it rather than a comment.
  --
  -- THE WIDTH IS THE WHOLE RISK HERE.  A store that ignores its operand width
  -- is invisible at width q and invisible at every register destination — the
  -- register path truncates in `setReg` — and shows up only as clobbered
  -- NEIGHBOURS in the data window at b, w and l.  That is this batch's planted
  -- hard half, and it is why all four widths are here rather than q alone.
  , { id := "and_mr_b", mnemonic := "and", asm := "andb %al, (%rbx)"
    , bytes := "2003", instr := ⟨.bin .and .b (M .rbx) (R .rax), 2⟩ }
  , { id := "and_mr_w", mnemonic := "and", asm := "andw %ax, (%rbx)"
    , bytes := "662103", instr := ⟨.bin .and .w (M .rbx) (R .rax), 3⟩ }
  , { id := "and_mr_l", mnemonic := "and", asm := "andl %eax, (%rbx)"
    , bytes := "2103", instr := ⟨.bin .and .d (M .rbx) (R .rax), 2⟩ }
  , { id := "and_mr_q", mnemonic := "and", asm := "andq %rax, (%rbx)"
    , bytes := "482103", instr := ⟨.bin .and .q (M .rbx) (R .rax), 3⟩ }
  , { id := "and_mi_b", mnemonic := "and", asm := "andb $0x5a, (%rbx)"
    , bytes := "80235a", instr := ⟨.bin .and .b (M .rbx) (.imm 0x5a), 3⟩ }
  , { id := "and_mi_w", mnemonic := "and", asm := "andw $0x1234, (%rbx)"
    , bytes := "6681233412", instr := ⟨.bin .and .w (M .rbx) (.imm 0x1234), 5⟩ }
  , { id := "and_mi_l", mnemonic := "and", asm := "andl $0x12345678, (%rbx)"
    , bytes := "812378563412", instr := ⟨.bin .and .d (M .rbx) (.imm 0x12345678), 6⟩ }
  , { id := "and_mi_q", mnemonic := "and", asm := "andq $0x12345678, (%rbx)"
    , bytes := "48812378563412", instr := ⟨.bin .and .q (M .rbx) (.imm 0x12345678), 7⟩ }
  , { id := "or_mr_b", mnemonic := "or", asm := "orb %al, (%rbx)"
    , bytes := "0803", instr := ⟨.bin .or .b (M .rbx) (R .rax), 2⟩ }
  , { id := "or_mr_w", mnemonic := "or", asm := "orw %ax, (%rbx)"
    , bytes := "660903", instr := ⟨.bin .or .w (M .rbx) (R .rax), 3⟩ }
  , { id := "or_mr_l", mnemonic := "or", asm := "orl %eax, (%rbx)"
    , bytes := "0903", instr := ⟨.bin .or .d (M .rbx) (R .rax), 2⟩ }
  , { id := "or_mr_q", mnemonic := "or", asm := "orq %rax, (%rbx)"
    , bytes := "480903", instr := ⟨.bin .or .q (M .rbx) (R .rax), 3⟩ }
  , { id := "or_mi_b", mnemonic := "or", asm := "orb $0x5a, (%rbx)"
    , bytes := "800b5a", instr := ⟨.bin .or .b (M .rbx) (.imm 0x5a), 3⟩ }
  , { id := "or_mi_w", mnemonic := "or", asm := "orw $0x1234, (%rbx)"
    , bytes := "66810b3412", instr := ⟨.bin .or .w (M .rbx) (.imm 0x1234), 5⟩ }
  , { id := "or_mi_l", mnemonic := "or", asm := "orl $0x12345678, (%rbx)"
    , bytes := "810b78563412", instr := ⟨.bin .or .d (M .rbx) (.imm 0x12345678), 6⟩ }
  , { id := "or_mi_q", mnemonic := "or", asm := "orq $0x12345678, (%rbx)"
    , bytes := "48810b78563412", instr := ⟨.bin .or .q (M .rbx) (.imm 0x12345678), 7⟩ }
  , { id := "xor_mr_b", mnemonic := "xor", asm := "xorb %al, (%rbx)"
    , bytes := "3003", instr := ⟨.bin .xor .b (M .rbx) (R .rax), 2⟩ }
  , { id := "xor_mr_w", mnemonic := "xor", asm := "xorw %ax, (%rbx)"
    , bytes := "663103", instr := ⟨.bin .xor .w (M .rbx) (R .rax), 3⟩ }
  , { id := "xor_mr_l", mnemonic := "xor", asm := "xorl %eax, (%rbx)"
    , bytes := "3103", instr := ⟨.bin .xor .d (M .rbx) (R .rax), 2⟩ }
  , { id := "xor_mr_q", mnemonic := "xor", asm := "xorq %rax, (%rbx)"
    , bytes := "483103", instr := ⟨.bin .xor .q (M .rbx) (R .rax), 3⟩ }
  , { id := "xor_mi_b", mnemonic := "xor", asm := "xorb $0x5a, (%rbx)"
    , bytes := "80335a", instr := ⟨.bin .xor .b (M .rbx) (.imm 0x5a), 3⟩ }
  , { id := "xor_mi_w", mnemonic := "xor", asm := "xorw $0x1234, (%rbx)"
    , bytes := "6681333412", instr := ⟨.bin .xor .w (M .rbx) (.imm 0x1234), 5⟩ }
  , { id := "xor_mi_l", mnemonic := "xor", asm := "xorl $0x12345678, (%rbx)"
    , bytes := "813378563412", instr := ⟨.bin .xor .d (M .rbx) (.imm 0x12345678), 6⟩ }
  , { id := "xor_mi_q", mnemonic := "xor", asm := "xorq $0x12345678, (%rbx)"
    , bytes := "48813378563412", instr := ⟨.bin .xor .q (M .rbx) (.imm 0x12345678), 7⟩ }
  , { id := "inc_m_b", mnemonic := "inc", asm := "incb (%rbx)"
    , bytes := "fe03", instr := ⟨.un .inc .b (M .rbx), 2⟩ }
  , { id := "inc_m_w", mnemonic := "inc", asm := "incw (%rbx)"
    , bytes := "66ff03", instr := ⟨.un .inc .w (M .rbx), 3⟩ }
  , { id := "inc_m_l", mnemonic := "inc", asm := "incl (%rbx)"
    , bytes := "ff03", instr := ⟨.un .inc .d (M .rbx), 2⟩ }
  , { id := "inc_m_q", mnemonic := "inc", asm := "incq (%rbx)"
    , bytes := "48ff03", instr := ⟨.un .inc .q (M .rbx), 3⟩ }
  , { id := "inc_r_b", mnemonic := "inc", asm := "incb %al"
    , bytes := "fec0", instr := ⟨.un .inc .b (R .rax), 2⟩ }
  , { id := "inc_r_w", mnemonic := "inc", asm := "incw %ax"
    , bytes := "66ffc0", instr := ⟨.un .inc .w (R .rax), 3⟩ }
  , { id := "inc_r_l", mnemonic := "inc", asm := "incl %eax"
    , bytes := "ffc0", instr := ⟨.un .inc .d (R .rax), 2⟩ }
  , { id := "inc_r_q", mnemonic := "inc", asm := "incq %rax"
    , bytes := "48ffc0", instr := ⟨.un .inc .q (R .rax), 3⟩ }
  , { id := "dec_m_b", mnemonic := "dec", asm := "decb (%rbx)"
    , bytes := "fe0b", instr := ⟨.un .dec .b (M .rbx), 2⟩ }
  , { id := "dec_m_w", mnemonic := "dec", asm := "decw (%rbx)"
    , bytes := "66ff0b", instr := ⟨.un .dec .w (M .rbx), 3⟩ }
  , { id := "dec_m_l", mnemonic := "dec", asm := "decl (%rbx)"
    , bytes := "ff0b", instr := ⟨.un .dec .d (M .rbx), 2⟩ }
  , { id := "dec_m_q", mnemonic := "dec", asm := "decq (%rbx)"
    , bytes := "48ff0b", instr := ⟨.un .dec .q (M .rbx), 3⟩ }
  , { id := "dec_r_b", mnemonic := "dec", asm := "decb %al"
    , bytes := "fec8", instr := ⟨.un .dec .b (R .rax), 2⟩ }
  , { id := "dec_r_w", mnemonic := "dec", asm := "decw %ax"
    , bytes := "66ffc8", instr := ⟨.un .dec .w (R .rax), 3⟩ }
  , { id := "dec_r_l", mnemonic := "dec", asm := "decl %eax"
    , bytes := "ffc8", instr := ⟨.un .dec .d (R .rax), 2⟩ }
  , { id := "dec_r_q", mnemonic := "dec", asm := "decq %rax"
    , bytes := "48ffc8", instr := ⟨.un .dec .q (R .rax), 3⟩ }
  -- ══ P1 BATCH 5 ═════════════════════════════════════════════════════════
  -- The BRANCH subset of roster family `-------|-|flags/ctl`: 33 mnemonics at
  -- `rel8`, `rel32` and `label` — 99 of the family's 116 forms.
  --
  -- ⛔ AND THE FAMILY IS NOT THE BATCH, WHICH IS ITSELF THE FINDING.  Family 7
  -- keys on "writes no flag, destination is flags/ctl", and that description
  -- also fits `leaveq`, `lods`, `movs`, `nop`, `pdep`, `pext`, `retq`, `stos`
  -- and `ud2` — string operations, BMI2 bit-manipulation, and stack and misc
  -- forms, filed together with the branches because they agree about FLAGS.
  -- Those 17 forms are several different templates and are NOT in this batch.
  -- See docs/DECISIONS.md D17: the roster's family key is not a template key.
  --
  -- WHAT THE 33 MNEMONICS COME TO HERE: 30 of them are jcc SPELLINGS of the 16
  -- predicates in `Cc` (`jz` and `je` are one instruction; `Cc.synonyms` is the
  -- table and `thirty_branch_spellings` counts it), plus `jmp`, plus `jrcxz`
  -- and `jecxz` — the one branch whose condition is a REGISTER.
  --
  -- ⭐ AND THE ONE THING THE ROSTER GETS WRONG, found by trying to assemble it.
  -- K's tree carries `jecxz_rel32.k` and `jrcxz_rel32.k`, and **there is no
  -- rel32 encoding of either instruction**: `E3 cb` is rel8 only (SDM Vol. 2A,
  -- JCC).  clang refuses outright — "value of 297 is too large for field of 1
  -- byte".  Two of the roster's 525 forms cannot be assembled at all.
  --
  -- `label` is covered by identity with `rel8`/`rel32`, as in batch 3: the
  -- assembler picks the width and the linker fills the number in, and a
  -- post-decode model sees only the result.
  , { id := "jo_rel8", mnemonic := "jcc", asm := "jo .+18"
    , bytes := "7010", instr := ⟨.jcc .o 0x10, 2⟩ }
  , { id := "jno_rel8", mnemonic := "jcc", asm := "jno .+18"
    , bytes := "7110", instr := ⟨.jcc .no 0x10, 2⟩ }
  , { id := "jb_rel8", mnemonic := "jcc", asm := "jb .+18"
    , bytes := "7210", instr := ⟨.jcc .b 0x10, 2⟩ }
  , { id := "jae_rel8", mnemonic := "jcc", asm := "jae .+18"
    , bytes := "7310", instr := ⟨.jcc .ae 0x10, 2⟩ }
  , { id := "je_rel8", mnemonic := "jcc", asm := "je .+18"
    , bytes := "7410", instr := ⟨.jcc .e 0x10, 2⟩ }
  , { id := "jne_rel8", mnemonic := "jcc", asm := "jne .+18"
    , bytes := "7510", instr := ⟨.jcc .ne 0x10, 2⟩ }
  , { id := "jbe_rel8", mnemonic := "jcc", asm := "jbe .+18"
    , bytes := "7610", instr := ⟨.jcc .be 0x10, 2⟩ }
  , { id := "ja_rel8", mnemonic := "jcc", asm := "ja .+18"
    , bytes := "7710", instr := ⟨.jcc .a 0x10, 2⟩ }
  , { id := "js_rel8", mnemonic := "jcc", asm := "js .+18"
    , bytes := "7810", instr := ⟨.jcc .s 0x10, 2⟩ }
  , { id := "jns_rel8", mnemonic := "jcc", asm := "jns .+18"
    , bytes := "7910", instr := ⟨.jcc .ns 0x10, 2⟩ }
  , { id := "jp_rel8", mnemonic := "jcc", asm := "jp .+18"
    , bytes := "7a10", instr := ⟨.jcc .p 0x10, 2⟩ }
  , { id := "jnp_rel8", mnemonic := "jcc", asm := "jnp .+18"
    , bytes := "7b10", instr := ⟨.jcc .np 0x10, 2⟩ }
  , { id := "jl_rel8", mnemonic := "jcc", asm := "jl .+18"
    , bytes := "7c10", instr := ⟨.jcc .l 0x10, 2⟩ }
  , { id := "jge_rel8", mnemonic := "jcc", asm := "jge .+18"
    , bytes := "7d10", instr := ⟨.jcc .ge 0x10, 2⟩ }
  , { id := "jle_rel8", mnemonic := "jcc", asm := "jle .+18"
    , bytes := "7e10", instr := ⟨.jcc .le 0x10, 2⟩ }
  , { id := "jg_rel8", mnemonic := "jcc", asm := "jg .+18"
    , bytes := "7f10", instr := ⟨.jcc .g 0x10, 2⟩ }
  , { id := "jo_rel32", mnemonic := "jcc", asm := "jo .+200"
    , bytes := "0f80c2000000", instr := ⟨.jcc .o 0xc2, 6⟩ }
  , { id := "jno_rel32", mnemonic := "jcc", asm := "jno .+200"
    , bytes := "0f81c2000000", instr := ⟨.jcc .no 0xc2, 6⟩ }
  , { id := "jb_rel32", mnemonic := "jcc", asm := "jb .+200"
    , bytes := "0f82c2000000", instr := ⟨.jcc .b 0xc2, 6⟩ }
  , { id := "jae_rel32", mnemonic := "jcc", asm := "jae .+200"
    , bytes := "0f83c2000000", instr := ⟨.jcc .ae 0xc2, 6⟩ }
  , { id := "je_rel32", mnemonic := "jcc", asm := "je .+200"
    , bytes := "0f84c2000000", instr := ⟨.jcc .e 0xc2, 6⟩ }
  , { id := "jne_rel32", mnemonic := "jcc", asm := "jne .+200"
    , bytes := "0f85c2000000", instr := ⟨.jcc .ne 0xc2, 6⟩ }
  , { id := "jbe_rel32", mnemonic := "jcc", asm := "jbe .+200"
    , bytes := "0f86c2000000", instr := ⟨.jcc .be 0xc2, 6⟩ }
  , { id := "ja_rel32", mnemonic := "jcc", asm := "ja .+200"
    , bytes := "0f87c2000000", instr := ⟨.jcc .a 0xc2, 6⟩ }
  , { id := "js_rel32", mnemonic := "jcc", asm := "js .+200"
    , bytes := "0f88c2000000", instr := ⟨.jcc .s 0xc2, 6⟩ }
  , { id := "jns_rel32", mnemonic := "jcc", asm := "jns .+200"
    , bytes := "0f89c2000000", instr := ⟨.jcc .ns 0xc2, 6⟩ }
  , { id := "jp_rel32", mnemonic := "jcc", asm := "jp .+200"
    , bytes := "0f8ac2000000", instr := ⟨.jcc .p 0xc2, 6⟩ }
  , { id := "jnp_rel32", mnemonic := "jcc", asm := "jnp .+200"
    , bytes := "0f8bc2000000", instr := ⟨.jcc .np 0xc2, 6⟩ }
  , { id := "jl_rel32", mnemonic := "jcc", asm := "jl .+200"
    , bytes := "0f8cc2000000", instr := ⟨.jcc .l 0xc2, 6⟩ }
  , { id := "jge_rel32", mnemonic := "jcc", asm := "jge .+200"
    , bytes := "0f8dc2000000", instr := ⟨.jcc .ge 0xc2, 6⟩ }
  , { id := "jle_rel32", mnemonic := "jcc", asm := "jle .+200"
    , bytes := "0f8ec2000000", instr := ⟨.jcc .le 0xc2, 6⟩ }
  , { id := "jg_rel32", mnemonic := "jcc", asm := "jg .+200"
    , bytes := "0f8fc2000000", instr := ⟨.jcc .g 0xc2, 6⟩ }
  , { id := "jmp_rel8", mnemonic := "jmp", asm := "jmp .+18"
    , bytes := "eb10", instr := ⟨.jmp (.rel 0x10), 2⟩ }
  , { id := "jmp_rel32", mnemonic := "jmp", asm := "jmp .+200"
    , bytes := "e9c3000000", instr := ⟨.jmp (.rel 0xc3), 5⟩ }
  , { id := "jrcxz_rel8", mnemonic := "jrcxz", asm := "jrcxz .+18"
    , bytes := "e310", instr := ⟨.jcxz false 0x10, 2⟩ }
  , { id := "jecxz_rel8", mnemonic := "jecxz", asm := "jecxz .+18"
    , bytes := "67e30f", instr := ⟨.jcxz true 0x0f, 3⟩ }
  -- ══ P1 BATCH 6 ═════════════════════════════════════════════════════════
  -- The CONDITION-CODE families of `p1/roster.tsv` — 16, 18-22, 28-30, 34-38,
  -- 44 and 45 — **120 forms**: SETcc at a register and a memory destination
  -- (30 spellings × 2) and CMOVcc at `r,r` and `r,m` (30 × 2).
  --
  -- ⭐ 120 FORMS FOR TWO `step` CASES, AND THE REASON IS A P0 DESIGN CHOICE.
  -- `Cc` has one constructor per PREDICATE, not per mnemonic, so K's 30 `set`
  -- spellings and 30 `cmov` spellings are the SAME sixteen predicates the
  -- branches already use, read through a different opcode.  `Cc.suffixes` is
  -- that table and `Cc.setSpellings`/`Cc.cmovSpellings` derive the names; a
  -- model with one constructor per mnemonic would be writing 90 of them here.
  -- This is what "cheapest by BEHAVIOUR, not by form count" looks like when the
  -- earlier design was right.
  --
  -- ⚠️ AND THE ONE PLACE CMOVcc IS NOT WHAT IT LOOKS LIKE.  The destination is
  -- written WHETHER OR NOT the condition holds — only the VALUE is conditional.
  -- At widths w and q that is invisible.  At width `d` the write ZERO-EXTENDS
  -- (SDM Vol. 1 §3.4.1.1), so `cmovel %ecx, %eax` clears the upper half of RAX
  -- even when ZF is clear and nothing moves.  Every `cmov` vector here is at
  -- width `l` for exactly that reason, with `w` and `q` present for two
  -- conditions to give the contrast; and a model that skips the write on a
  -- false condition is this batch's planted hard half.
  , { id := "seto_r", mnemonic := "setcc", asm := "seto %al"
    , bytes := "0f90c0", instr := ⟨.setcc .o (R .rax), 3⟩ }
  , { id := "setno_r", mnemonic := "setcc", asm := "setno %al"
    , bytes := "0f91c0", instr := ⟨.setcc .no (R .rax), 3⟩ }
  , { id := "setb_r", mnemonic := "setcc", asm := "setb %al"
    , bytes := "0f92c0", instr := ⟨.setcc .b (R .rax), 3⟩ }
  , { id := "setae_r", mnemonic := "setcc", asm := "setae %al"
    , bytes := "0f93c0", instr := ⟨.setcc .ae (R .rax), 3⟩ }
  , { id := "sete_r", mnemonic := "setcc", asm := "sete %al"
    , bytes := "0f94c0", instr := ⟨.setcc .e (R .rax), 3⟩ }
  , { id := "setne_r", mnemonic := "setcc", asm := "setne %al"
    , bytes := "0f95c0", instr := ⟨.setcc .ne (R .rax), 3⟩ }
  , { id := "setbe_r", mnemonic := "setcc", asm := "setbe %al"
    , bytes := "0f96c0", instr := ⟨.setcc .be (R .rax), 3⟩ }
  , { id := "seta_r", mnemonic := "setcc", asm := "seta %al"
    , bytes := "0f97c0", instr := ⟨.setcc .a (R .rax), 3⟩ }
  , { id := "sets_r", mnemonic := "setcc", asm := "sets %al"
    , bytes := "0f98c0", instr := ⟨.setcc .s (R .rax), 3⟩ }
  , { id := "setns_r", mnemonic := "setcc", asm := "setns %al"
    , bytes := "0f99c0", instr := ⟨.setcc .ns (R .rax), 3⟩ }
  , { id := "setp_r", mnemonic := "setcc", asm := "setp %al"
    , bytes := "0f9ac0", instr := ⟨.setcc .p (R .rax), 3⟩ }
  , { id := "setnp_r", mnemonic := "setcc", asm := "setnp %al"
    , bytes := "0f9bc0", instr := ⟨.setcc .np (R .rax), 3⟩ }
  , { id := "setl_r", mnemonic := "setcc", asm := "setl %al"
    , bytes := "0f9cc0", instr := ⟨.setcc .l (R .rax), 3⟩ }
  , { id := "setge_r", mnemonic := "setcc", asm := "setge %al"
    , bytes := "0f9dc0", instr := ⟨.setcc .ge (R .rax), 3⟩ }
  , { id := "setle_r", mnemonic := "setcc", asm := "setle %al"
    , bytes := "0f9ec0", instr := ⟨.setcc .le (R .rax), 3⟩ }
  , { id := "setg_r", mnemonic := "setcc", asm := "setg %al"
    , bytes := "0f9fc0", instr := ⟨.setcc .g (R .rax), 3⟩ }
  , { id := "seto_m", mnemonic := "setcc", asm := "seto (%rbx)"
    , bytes := "0f9003", instr := ⟨.setcc .o (M .rbx), 3⟩ }
  , { id := "setno_m", mnemonic := "setcc", asm := "setno (%rbx)"
    , bytes := "0f9103", instr := ⟨.setcc .no (M .rbx), 3⟩ }
  , { id := "setb_m", mnemonic := "setcc", asm := "setb (%rbx)"
    , bytes := "0f9203", instr := ⟨.setcc .b (M .rbx), 3⟩ }
  , { id := "setae_m", mnemonic := "setcc", asm := "setae (%rbx)"
    , bytes := "0f9303", instr := ⟨.setcc .ae (M .rbx), 3⟩ }
  , { id := "sete_m", mnemonic := "setcc", asm := "sete (%rbx)"
    , bytes := "0f9403", instr := ⟨.setcc .e (M .rbx), 3⟩ }
  , { id := "setne_m", mnemonic := "setcc", asm := "setne (%rbx)"
    , bytes := "0f9503", instr := ⟨.setcc .ne (M .rbx), 3⟩ }
  , { id := "setbe_m", mnemonic := "setcc", asm := "setbe (%rbx)"
    , bytes := "0f9603", instr := ⟨.setcc .be (M .rbx), 3⟩ }
  , { id := "seta_m", mnemonic := "setcc", asm := "seta (%rbx)"
    , bytes := "0f9703", instr := ⟨.setcc .a (M .rbx), 3⟩ }
  , { id := "sets_m", mnemonic := "setcc", asm := "sets (%rbx)"
    , bytes := "0f9803", instr := ⟨.setcc .s (M .rbx), 3⟩ }
  , { id := "setns_m", mnemonic := "setcc", asm := "setns (%rbx)"
    , bytes := "0f9903", instr := ⟨.setcc .ns (M .rbx), 3⟩ }
  , { id := "setp_m", mnemonic := "setcc", asm := "setp (%rbx)"
    , bytes := "0f9a03", instr := ⟨.setcc .p (M .rbx), 3⟩ }
  , { id := "setnp_m", mnemonic := "setcc", asm := "setnp (%rbx)"
    , bytes := "0f9b03", instr := ⟨.setcc .np (M .rbx), 3⟩ }
  , { id := "setl_m", mnemonic := "setcc", asm := "setl (%rbx)"
    , bytes := "0f9c03", instr := ⟨.setcc .l (M .rbx), 3⟩ }
  , { id := "setge_m", mnemonic := "setcc", asm := "setge (%rbx)"
    , bytes := "0f9d03", instr := ⟨.setcc .ge (M .rbx), 3⟩ }
  , { id := "setle_m", mnemonic := "setcc", asm := "setle (%rbx)"
    , bytes := "0f9e03", instr := ⟨.setcc .le (M .rbx), 3⟩ }
  , { id := "setg_m", mnemonic := "setcc", asm := "setg (%rbx)"
    , bytes := "0f9f03", instr := ⟨.setcc .g (M .rbx), 3⟩ }
  , { id := "setne_h8", mnemonic := "setcc", asm := "setne %ah"
    , bytes := "0f95c4", instr := ⟨.setcc .ne (H .rax), 3⟩ }
  , { id := "cmovo_rr_l", mnemonic := "cmovcc", asm := "cmovo %ecx, %eax"
    , bytes := "0f40c1", instr := ⟨.cmov .o .d .rax (R .rcx), 3⟩ }
  , { id := "cmovno_rr_l", mnemonic := "cmovcc", asm := "cmovno %ecx, %eax"
    , bytes := "0f41c1", instr := ⟨.cmov .no .d .rax (R .rcx), 3⟩ }
  , { id := "cmovb_rr_l", mnemonic := "cmovcc", asm := "cmovb %ecx, %eax"
    , bytes := "0f42c1", instr := ⟨.cmov .b .d .rax (R .rcx), 3⟩ }
  , { id := "cmovae_rr_l", mnemonic := "cmovcc", asm := "cmovae %ecx, %eax"
    , bytes := "0f43c1", instr := ⟨.cmov .ae .d .rax (R .rcx), 3⟩ }
  , { id := "cmove_rr_l", mnemonic := "cmovcc", asm := "cmove %ecx, %eax"
    , bytes := "0f44c1", instr := ⟨.cmov .e .d .rax (R .rcx), 3⟩ }
  , { id := "cmovne_rr_l", mnemonic := "cmovcc", asm := "cmovne %ecx, %eax"
    , bytes := "0f45c1", instr := ⟨.cmov .ne .d .rax (R .rcx), 3⟩ }
  , { id := "cmovbe_rr_l", mnemonic := "cmovcc", asm := "cmovbe %ecx, %eax"
    , bytes := "0f46c1", instr := ⟨.cmov .be .d .rax (R .rcx), 3⟩ }
  , { id := "cmova_rr_l", mnemonic := "cmovcc", asm := "cmova %ecx, %eax"
    , bytes := "0f47c1", instr := ⟨.cmov .a .d .rax (R .rcx), 3⟩ }
  , { id := "cmovs_rr_l", mnemonic := "cmovcc", asm := "cmovs %ecx, %eax"
    , bytes := "0f48c1", instr := ⟨.cmov .s .d .rax (R .rcx), 3⟩ }
  , { id := "cmovns_rr_l", mnemonic := "cmovcc", asm := "cmovns %ecx, %eax"
    , bytes := "0f49c1", instr := ⟨.cmov .ns .d .rax (R .rcx), 3⟩ }
  , { id := "cmovp_rr_l", mnemonic := "cmovcc", asm := "cmovp %ecx, %eax"
    , bytes := "0f4ac1", instr := ⟨.cmov .p .d .rax (R .rcx), 3⟩ }
  , { id := "cmovnp_rr_l", mnemonic := "cmovcc", asm := "cmovnp %ecx, %eax"
    , bytes := "0f4bc1", instr := ⟨.cmov .np .d .rax (R .rcx), 3⟩ }
  , { id := "cmovl_rr_l", mnemonic := "cmovcc", asm := "cmovl %ecx, %eax"
    , bytes := "0f4cc1", instr := ⟨.cmov .l .d .rax (R .rcx), 3⟩ }
  , { id := "cmovge_rr_l", mnemonic := "cmovcc", asm := "cmovge %ecx, %eax"
    , bytes := "0f4dc1", instr := ⟨.cmov .ge .d .rax (R .rcx), 3⟩ }
  , { id := "cmovle_rr_l", mnemonic := "cmovcc", asm := "cmovle %ecx, %eax"
    , bytes := "0f4ec1", instr := ⟨.cmov .le .d .rax (R .rcx), 3⟩ }
  , { id := "cmovg_rr_l", mnemonic := "cmovcc", asm := "cmovg %ecx, %eax"
    , bytes := "0f4fc1", instr := ⟨.cmov .g .d .rax (R .rcx), 3⟩ }
  , { id := "cmovo_rm_l", mnemonic := "cmovcc", asm := "cmovo (%rbx), %eax"
    , bytes := "0f4003", instr := ⟨.cmov .o .d .rax (M .rbx), 3⟩ }
  , { id := "cmovno_rm_l", mnemonic := "cmovcc", asm := "cmovno (%rbx), %eax"
    , bytes := "0f4103", instr := ⟨.cmov .no .d .rax (M .rbx), 3⟩ }
  , { id := "cmovb_rm_l", mnemonic := "cmovcc", asm := "cmovb (%rbx), %eax"
    , bytes := "0f4203", instr := ⟨.cmov .b .d .rax (M .rbx), 3⟩ }
  , { id := "cmovae_rm_l", mnemonic := "cmovcc", asm := "cmovae (%rbx), %eax"
    , bytes := "0f4303", instr := ⟨.cmov .ae .d .rax (M .rbx), 3⟩ }
  , { id := "cmove_rm_l", mnemonic := "cmovcc", asm := "cmove (%rbx), %eax"
    , bytes := "0f4403", instr := ⟨.cmov .e .d .rax (M .rbx), 3⟩ }
  , { id := "cmovne_rm_l", mnemonic := "cmovcc", asm := "cmovne (%rbx), %eax"
    , bytes := "0f4503", instr := ⟨.cmov .ne .d .rax (M .rbx), 3⟩ }
  , { id := "cmovbe_rm_l", mnemonic := "cmovcc", asm := "cmovbe (%rbx), %eax"
    , bytes := "0f4603", instr := ⟨.cmov .be .d .rax (M .rbx), 3⟩ }
  , { id := "cmova_rm_l", mnemonic := "cmovcc", asm := "cmova (%rbx), %eax"
    , bytes := "0f4703", instr := ⟨.cmov .a .d .rax (M .rbx), 3⟩ }
  , { id := "cmovs_rm_l", mnemonic := "cmovcc", asm := "cmovs (%rbx), %eax"
    , bytes := "0f4803", instr := ⟨.cmov .s .d .rax (M .rbx), 3⟩ }
  , { id := "cmovns_rm_l", mnemonic := "cmovcc", asm := "cmovns (%rbx), %eax"
    , bytes := "0f4903", instr := ⟨.cmov .ns .d .rax (M .rbx), 3⟩ }
  , { id := "cmovp_rm_l", mnemonic := "cmovcc", asm := "cmovp (%rbx), %eax"
    , bytes := "0f4a03", instr := ⟨.cmov .p .d .rax (M .rbx), 3⟩ }
  , { id := "cmovnp_rm_l", mnemonic := "cmovcc", asm := "cmovnp (%rbx), %eax"
    , bytes := "0f4b03", instr := ⟨.cmov .np .d .rax (M .rbx), 3⟩ }
  , { id := "cmovl_rm_l", mnemonic := "cmovcc", asm := "cmovl (%rbx), %eax"
    , bytes := "0f4c03", instr := ⟨.cmov .l .d .rax (M .rbx), 3⟩ }
  , { id := "cmovge_rm_l", mnemonic := "cmovcc", asm := "cmovge (%rbx), %eax"
    , bytes := "0f4d03", instr := ⟨.cmov .ge .d .rax (M .rbx), 3⟩ }
  , { id := "cmovle_rm_l", mnemonic := "cmovcc", asm := "cmovle (%rbx), %eax"
    , bytes := "0f4e03", instr := ⟨.cmov .le .d .rax (M .rbx), 3⟩ }
  , { id := "cmovg_rm_l", mnemonic := "cmovcc", asm := "cmovg (%rbx), %eax"
    , bytes := "0f4f03", instr := ⟨.cmov .g .d .rax (M .rbx), 3⟩ }
  , { id := "cmove_rr_w", mnemonic := "cmovcc", asm := "cmove %cx, %ax"
    , bytes := "660f44c1", instr := ⟨.cmov .e .w .rax (R .rcx), 4⟩ }
  , { id := "cmove_rr_q", mnemonic := "cmovcc", asm := "cmove %rcx, %rax"
    , bytes := "480f44c1", instr := ⟨.cmov .e .q .rax (R .rcx), 4⟩ }
  , { id := "cmovne_rr_w", mnemonic := "cmovcc", asm := "cmovne %cx, %ax"
    , bytes := "660f45c1", instr := ⟨.cmov .ne .w .rax (R .rcx), 4⟩ }
  , { id := "cmovne_rr_q", mnemonic := "cmovcc", asm := "cmovne %rcx, %rax"
    , bytes := "480f45c1", instr := ⟨.cmov .ne .q .rax (R .rcx), 4⟩ }
  -- ══ P1 BATCH 7 ═════════════════════════════════════════════════════════
  -- The SHIFT group: roster families 8, 9, 12, 13, 60 and 61 — **24 forms**,
  -- `shl`/`sal`/`shr`/`sar` at a register AND a memory destination, in all
  -- three count encodings (`,one` = `D1 /r`, `,imm` = `C1 /r ib`, `,cl` =
  -- `D3 /r`).
  --
  -- TWO OF THE FOUR MNEMONICS COST NOTHING.  `sal` is an ALIAS of `shl` — the
  -- same opcode `/4` — so a post-decode model cannot distinguish them and must
  -- not try; it is covered by identity, like the `jcc` synonyms of batch 5.
  -- And `,one` is an ENCODING distinction: `D1` carries the count in the
  -- opcode, `C1 ib` in a byte, and both decode to `.imm8 1`.  Separate vectors
  -- because the BYTES differ and the bytes are what XED is trusted for.
  --
  -- ⭐ SAR IS THE ONE REAL ADDITION, AND ITS CF IS DEFINED WHERE SHL's AND
  -- SHR's IS NOT.  The SDM's undefined clause names "SHL and SHR instructions
  -- where the count is greater than or equal to the size of the destination
  -- operand" — SAR has NO such clause, because shifting right by more than the
  -- width still has an answer: every vacated bit, and the last one out, is the
  -- SIGN.  So `sar_b9` (count 9 at width 8) draws NO oracle bit for CF where
  -- `shr_b9` does, and that difference is a claim the differential arbitrates.
  , { id := "shl_r_one_b", mnemonic := "shl", asm := "shlb %al"
    , bytes := "d0e0", instr := ⟨.shift .shl .b (R .rax) (.imm8 1), 2⟩ }
  , { id := "shl_r_one_q", mnemonic := "shl", asm := "shlq %rax"
    , bytes := "48d1e0", instr := ⟨.shift .shl .q (R .rax) (.imm8 1), 3⟩ }
  , { id := "shl_ri5_b", mnemonic := "shl", asm := "shlb $5, %al"
    , bytes := "c0e005", instr := ⟨.shift .shl .b (R .rax) (.imm8 5), 3⟩ }
  , { id := "shl_ri5_w", mnemonic := "shl", asm := "shlw $5, %ax"
    , bytes := "66c1e005", instr := ⟨.shift .shl .w (R .rax) (.imm8 5), 4⟩ }
  , { id := "shl_ri5_l", mnemonic := "shl", asm := "shll $5, %eax"
    , bytes := "c1e005", instr := ⟨.shift .shl .d (R .rax) (.imm8 5), 3⟩ }
  , { id := "shl_ri5_q", mnemonic := "shl", asm := "shlq $5, %rax"
    , bytes := "48c1e005", instr := ⟨.shift .shl .q (R .rax) (.imm8 5), 4⟩ }
  , { id := "shl_r_cl_b", mnemonic := "shl", asm := "shlb %cl, %al"
    , bytes := "d2e0", instr := ⟨.shift .shl .b (R .rax) .cl, 2⟩ }
  , { id := "shl_r_cl_q", mnemonic := "shl", asm := "shlq %cl, %rax"
    , bytes := "48d3e0", instr := ⟨.shift .shl .q (R .rax) .cl, 3⟩ }
  , { id := "shl_m_one_b", mnemonic := "shl", asm := "shlb (%rbx)"
    , bytes := "d023", instr := ⟨.shift .shl .b (M .rbx) (.imm8 1), 2⟩ }
  , { id := "shl_m_one_q", mnemonic := "shl", asm := "shlq (%rbx)"
    , bytes := "48d123", instr := ⟨.shift .shl .q (M .rbx) (.imm8 1), 3⟩ }
  , { id := "shl_mi5_b", mnemonic := "shl", asm := "shlb $5, (%rbx)"
    , bytes := "c02305", instr := ⟨.shift .shl .b (M .rbx) (.imm8 5), 3⟩ }
  , { id := "shl_mi5_w", mnemonic := "shl", asm := "shlw $5, (%rbx)"
    , bytes := "66c12305", instr := ⟨.shift .shl .w (M .rbx) (.imm8 5), 4⟩ }
  , { id := "shl_mi5_l", mnemonic := "shl", asm := "shll $5, (%rbx)"
    , bytes := "c12305", instr := ⟨.shift .shl .d (M .rbx) (.imm8 5), 3⟩ }
  , { id := "shl_mi5_q", mnemonic := "shl", asm := "shlq $5, (%rbx)"
    , bytes := "48c12305", instr := ⟨.shift .shl .q (M .rbx) (.imm8 5), 4⟩ }
  , { id := "shl_m_cl_b", mnemonic := "shl", asm := "shlb %cl, (%rbx)"
    , bytes := "d223", instr := ⟨.shift .shl .b (M .rbx) .cl, 2⟩ }
  , { id := "shl_m_cl_q", mnemonic := "shl", asm := "shlq %cl, (%rbx)"
    , bytes := "48d323", instr := ⟨.shift .shl .q (M .rbx) .cl, 3⟩ }
  , { id := "shr_r_one_b", mnemonic := "shr", asm := "shrb %al"
    , bytes := "d0e8", instr := ⟨.shift .shr .b (R .rax) (.imm8 1), 2⟩ }
  , { id := "shr_r_one_q", mnemonic := "shr", asm := "shrq %rax"
    , bytes := "48d1e8", instr := ⟨.shift .shr .q (R .rax) (.imm8 1), 3⟩ }
  , { id := "shr_ri5_b", mnemonic := "shr", asm := "shrb $5, %al"
    , bytes := "c0e805", instr := ⟨.shift .shr .b (R .rax) (.imm8 5), 3⟩ }
  , { id := "shr_ri5_w", mnemonic := "shr", asm := "shrw $5, %ax"
    , bytes := "66c1e805", instr := ⟨.shift .shr .w (R .rax) (.imm8 5), 4⟩ }
  , { id := "shr_ri5_l", mnemonic := "shr", asm := "shrl $5, %eax"
    , bytes := "c1e805", instr := ⟨.shift .shr .d (R .rax) (.imm8 5), 3⟩ }
  , { id := "shr_ri5_q", mnemonic := "shr", asm := "shrq $5, %rax"
    , bytes := "48c1e805", instr := ⟨.shift .shr .q (R .rax) (.imm8 5), 4⟩ }
  , { id := "shr_r_cl_b", mnemonic := "shr", asm := "shrb %cl, %al"
    , bytes := "d2e8", instr := ⟨.shift .shr .b (R .rax) .cl, 2⟩ }
  , { id := "shr_r_cl_q", mnemonic := "shr", asm := "shrq %cl, %rax"
    , bytes := "48d3e8", instr := ⟨.shift .shr .q (R .rax) .cl, 3⟩ }
  , { id := "shr_m_one_b", mnemonic := "shr", asm := "shrb (%rbx)"
    , bytes := "d02b", instr := ⟨.shift .shr .b (M .rbx) (.imm8 1), 2⟩ }
  , { id := "shr_m_one_q", mnemonic := "shr", asm := "shrq (%rbx)"
    , bytes := "48d12b", instr := ⟨.shift .shr .q (M .rbx) (.imm8 1), 3⟩ }
  , { id := "shr_mi5_b", mnemonic := "shr", asm := "shrb $5, (%rbx)"
    , bytes := "c02b05", instr := ⟨.shift .shr .b (M .rbx) (.imm8 5), 3⟩ }
  , { id := "shr_mi5_w", mnemonic := "shr", asm := "shrw $5, (%rbx)"
    , bytes := "66c12b05", instr := ⟨.shift .shr .w (M .rbx) (.imm8 5), 4⟩ }
  , { id := "shr_mi5_l", mnemonic := "shr", asm := "shrl $5, (%rbx)"
    , bytes := "c12b05", instr := ⟨.shift .shr .d (M .rbx) (.imm8 5), 3⟩ }
  , { id := "shr_mi5_q", mnemonic := "shr", asm := "shrq $5, (%rbx)"
    , bytes := "48c12b05", instr := ⟨.shift .shr .q (M .rbx) (.imm8 5), 4⟩ }
  , { id := "shr_m_cl_b", mnemonic := "shr", asm := "shrb %cl, (%rbx)"
    , bytes := "d22b", instr := ⟨.shift .shr .b (M .rbx) .cl, 2⟩ }
  , { id := "shr_m_cl_q", mnemonic := "shr", asm := "shrq %cl, (%rbx)"
    , bytes := "48d32b", instr := ⟨.shift .shr .q (M .rbx) .cl, 3⟩ }
  , { id := "sar_r_one_b", mnemonic := "sar", asm := "sarb %al"
    , bytes := "d0f8", instr := ⟨.shift .sar .b (R .rax) (.imm8 1), 2⟩ }
  , { id := "sar_r_one_q", mnemonic := "sar", asm := "sarq %rax"
    , bytes := "48d1f8", instr := ⟨.shift .sar .q (R .rax) (.imm8 1), 3⟩ }
  , { id := "sar_ri5_b", mnemonic := "sar", asm := "sarb $5, %al"
    , bytes := "c0f805", instr := ⟨.shift .sar .b (R .rax) (.imm8 5), 3⟩ }
  , { id := "sar_ri5_w", mnemonic := "sar", asm := "sarw $5, %ax"
    , bytes := "66c1f805", instr := ⟨.shift .sar .w (R .rax) (.imm8 5), 4⟩ }
  , { id := "sar_ri5_l", mnemonic := "sar", asm := "sarl $5, %eax"
    , bytes := "c1f805", instr := ⟨.shift .sar .d (R .rax) (.imm8 5), 3⟩ }
  , { id := "sar_ri5_q", mnemonic := "sar", asm := "sarq $5, %rax"
    , bytes := "48c1f805", instr := ⟨.shift .sar .q (R .rax) (.imm8 5), 4⟩ }
  , { id := "sar_r_cl_b", mnemonic := "sar", asm := "sarb %cl, %al"
    , bytes := "d2f8", instr := ⟨.shift .sar .b (R .rax) .cl, 2⟩ }
  , { id := "sar_r_cl_q", mnemonic := "sar", asm := "sarq %cl, %rax"
    , bytes := "48d3f8", instr := ⟨.shift .sar .q (R .rax) .cl, 3⟩ }
  , { id := "sar_m_one_b", mnemonic := "sar", asm := "sarb (%rbx)"
    , bytes := "d03b", instr := ⟨.shift .sar .b (M .rbx) (.imm8 1), 2⟩ }
  , { id := "sar_m_one_q", mnemonic := "sar", asm := "sarq (%rbx)"
    , bytes := "48d13b", instr := ⟨.shift .sar .q (M .rbx) (.imm8 1), 3⟩ }
  , { id := "sar_mi5_b", mnemonic := "sar", asm := "sarb $5, (%rbx)"
    , bytes := "c03b05", instr := ⟨.shift .sar .b (M .rbx) (.imm8 5), 3⟩ }
  , { id := "sar_mi5_w", mnemonic := "sar", asm := "sarw $5, (%rbx)"
    , bytes := "66c13b05", instr := ⟨.shift .sar .w (M .rbx) (.imm8 5), 4⟩ }
  , { id := "sar_mi5_l", mnemonic := "sar", asm := "sarl $5, (%rbx)"
    , bytes := "c13b05", instr := ⟨.shift .sar .d (M .rbx) (.imm8 5), 3⟩ }
  , { id := "sar_mi5_q", mnemonic := "sar", asm := "sarq $5, (%rbx)"
    , bytes := "48c13b05", instr := ⟨.shift .sar .q (M .rbx) (.imm8 5), 4⟩ }
  , { id := "sar_m_cl_b", mnemonic := "sar", asm := "sarb %cl, (%rbx)"
    , bytes := "d23b", instr := ⟨.shift .sar .b (M .rbx) .cl, 2⟩ }
  , { id := "sar_m_cl_q", mnemonic := "sar", asm := "sarq %cl, (%rbx)"
    , bytes := "48d33b", instr := ⟨.shift .sar .q (M .rbx) .cl, 3⟩ }
  , { id := "sar_q63", mnemonic := "sar", asm := "sarq $63, %rax"
    , bytes := "48c1f83f", instr := ⟨.shift .sar .q (R .rax) (.imm8 63), 4⟩ }
  , { id := "sar_b9", mnemonic := "sar", asm := "sarb $9, %al"
    , bytes := "c0f809", instr := ⟨.shift .sar .b (R .rax) (.imm8 9), 3⟩ }
  -- ══ P1 BATCH 8 ═════════════════════════════════════════════════════════
  -- The ROTATE group: roster families 25, 26, 49, 50, 51 and 52 — **24 forms**,
  -- `rol`/`ror`/`rcl`/`rcr` at a register AND a memory destination, in all
  -- three count encodings.  Same opcode block as batch 7's shifts (`D0`-`D3`,
  -- `C0`/`C1`), a different `/r` field, and entirely different flag rules.
  --
  -- ⭐ THREE VECTORS AT THE END ARE THE WHOLE POINT.  The count is reduced
  -- TWICE and the two reductions differ: `rol`/`ror` reduce modulo the WIDTH,
  -- `rcl`/`rcr` modulo the width PLUS ONE (they rotate the operand and CF
  -- together, a `w+1`-bit ring).  And the FLAG rules key off the FIRST
  -- reduction, not the second:
  --   * `rol_b8` — masked 8, reduced 0.  The data does NOT move and CF is
  --     still written.  A model testing the reduced count for "did anything
  --     happen" leaves CF alone and is wrong here and nowhere else.
  --   * `rol_b9` — masked 9, reduced 1.  The data rotates by one and OF is
  --     UNDEFINED anyway, because the SDM's OF rule asks whether the count is
  --     1, and it is 9.
  --   * `rcl_b9` — masked 9, reduced 9 mod 9 = 0.  Nothing moves and CF is
  --     NOT written, because the SDM's loop simply does not execute — the
  --     opposite of `rol_b8`, at the same count, one opcode away.
  , { id := "rol_r_one_b", mnemonic := "rol", asm := "rolb %al"
    , bytes := "d0c0", instr := ⟨.rot .rol .b (R .rax) (.imm8 1), 2⟩ }
  , { id := "rol_r_one_q", mnemonic := "rol", asm := "rolq %rax"
    , bytes := "48d1c0", instr := ⟨.rot .rol .q (R .rax) (.imm8 1), 3⟩ }
  , { id := "rol_ri5_b", mnemonic := "rol", asm := "rolb $5, %al"
    , bytes := "c0c005", instr := ⟨.rot .rol .b (R .rax) (.imm8 5), 3⟩ }
  , { id := "rol_ri5_w", mnemonic := "rol", asm := "rolw $5, %ax"
    , bytes := "66c1c005", instr := ⟨.rot .rol .w (R .rax) (.imm8 5), 4⟩ }
  , { id := "rol_ri5_l", mnemonic := "rol", asm := "roll $5, %eax"
    , bytes := "c1c005", instr := ⟨.rot .rol .d (R .rax) (.imm8 5), 3⟩ }
  , { id := "rol_ri5_q", mnemonic := "rol", asm := "rolq $5, %rax"
    , bytes := "48c1c005", instr := ⟨.rot .rol .q (R .rax) (.imm8 5), 4⟩ }
  , { id := "rol_r_cl_b", mnemonic := "rol", asm := "rolb %cl, %al"
    , bytes := "d2c0", instr := ⟨.rot .rol .b (R .rax) .cl, 2⟩ }
  , { id := "rol_r_cl_q", mnemonic := "rol", asm := "rolq %cl, %rax"
    , bytes := "48d3c0", instr := ⟨.rot .rol .q (R .rax) .cl, 3⟩ }
  , { id := "rol_m_one_b", mnemonic := "rol", asm := "rolb (%rbx)"
    , bytes := "d003", instr := ⟨.rot .rol .b (M .rbx) (.imm8 1), 2⟩ }
  , { id := "rol_m_one_q", mnemonic := "rol", asm := "rolq (%rbx)"
    , bytes := "48d103", instr := ⟨.rot .rol .q (M .rbx) (.imm8 1), 3⟩ }
  , { id := "rol_mi5_b", mnemonic := "rol", asm := "rolb $5, (%rbx)"
    , bytes := "c00305", instr := ⟨.rot .rol .b (M .rbx) (.imm8 5), 3⟩ }
  , { id := "rol_mi5_q", mnemonic := "rol", asm := "rolq $5, (%rbx)"
    , bytes := "48c10305", instr := ⟨.rot .rol .q (M .rbx) (.imm8 5), 4⟩ }
  , { id := "rol_m_cl_b", mnemonic := "rol", asm := "rolb %cl, (%rbx)"
    , bytes := "d203", instr := ⟨.rot .rol .b (M .rbx) .cl, 2⟩ }
  , { id := "rol_m_cl_q", mnemonic := "rol", asm := "rolq %cl, (%rbx)"
    , bytes := "48d303", instr := ⟨.rot .rol .q (M .rbx) .cl, 3⟩ }
  , { id := "ror_r_one_b", mnemonic := "ror", asm := "rorb %al"
    , bytes := "d0c8", instr := ⟨.rot .ror .b (R .rax) (.imm8 1), 2⟩ }
  , { id := "ror_r_one_q", mnemonic := "ror", asm := "rorq %rax"
    , bytes := "48d1c8", instr := ⟨.rot .ror .q (R .rax) (.imm8 1), 3⟩ }
  , { id := "ror_ri5_b", mnemonic := "ror", asm := "rorb $5, %al"
    , bytes := "c0c805", instr := ⟨.rot .ror .b (R .rax) (.imm8 5), 3⟩ }
  , { id := "ror_ri5_w", mnemonic := "ror", asm := "rorw $5, %ax"
    , bytes := "66c1c805", instr := ⟨.rot .ror .w (R .rax) (.imm8 5), 4⟩ }
  , { id := "ror_ri5_l", mnemonic := "ror", asm := "rorl $5, %eax"
    , bytes := "c1c805", instr := ⟨.rot .ror .d (R .rax) (.imm8 5), 3⟩ }
  , { id := "ror_ri5_q", mnemonic := "ror", asm := "rorq $5, %rax"
    , bytes := "48c1c805", instr := ⟨.rot .ror .q (R .rax) (.imm8 5), 4⟩ }
  , { id := "ror_r_cl_b", mnemonic := "ror", asm := "rorb %cl, %al"
    , bytes := "d2c8", instr := ⟨.rot .ror .b (R .rax) .cl, 2⟩ }
  , { id := "ror_r_cl_q", mnemonic := "ror", asm := "rorq %cl, %rax"
    , bytes := "48d3c8", instr := ⟨.rot .ror .q (R .rax) .cl, 3⟩ }
  , { id := "ror_m_one_b", mnemonic := "ror", asm := "rorb (%rbx)"
    , bytes := "d00b", instr := ⟨.rot .ror .b (M .rbx) (.imm8 1), 2⟩ }
  , { id := "ror_m_one_q", mnemonic := "ror", asm := "rorq (%rbx)"
    , bytes := "48d10b", instr := ⟨.rot .ror .q (M .rbx) (.imm8 1), 3⟩ }
  , { id := "ror_mi5_b", mnemonic := "ror", asm := "rorb $5, (%rbx)"
    , bytes := "c00b05", instr := ⟨.rot .ror .b (M .rbx) (.imm8 5), 3⟩ }
  , { id := "ror_mi5_q", mnemonic := "ror", asm := "rorq $5, (%rbx)"
    , bytes := "48c10b05", instr := ⟨.rot .ror .q (M .rbx) (.imm8 5), 4⟩ }
  , { id := "ror_m_cl_b", mnemonic := "ror", asm := "rorb %cl, (%rbx)"
    , bytes := "d20b", instr := ⟨.rot .ror .b (M .rbx) .cl, 2⟩ }
  , { id := "ror_m_cl_q", mnemonic := "ror", asm := "rorq %cl, (%rbx)"
    , bytes := "48d30b", instr := ⟨.rot .ror .q (M .rbx) .cl, 3⟩ }
  , { id := "rcl_r_one_b", mnemonic := "rcl", asm := "rclb %al"
    , bytes := "d0d0", instr := ⟨.rot .rcl .b (R .rax) (.imm8 1), 2⟩ }
  , { id := "rcl_r_one_q", mnemonic := "rcl", asm := "rclq %rax"
    , bytes := "48d1d0", instr := ⟨.rot .rcl .q (R .rax) (.imm8 1), 3⟩ }
  , { id := "rcl_ri5_b", mnemonic := "rcl", asm := "rclb $5, %al"
    , bytes := "c0d005", instr := ⟨.rot .rcl .b (R .rax) (.imm8 5), 3⟩ }
  , { id := "rcl_ri5_w", mnemonic := "rcl", asm := "rclw $5, %ax"
    , bytes := "66c1d005", instr := ⟨.rot .rcl .w (R .rax) (.imm8 5), 4⟩ }
  , { id := "rcl_ri5_l", mnemonic := "rcl", asm := "rcll $5, %eax"
    , bytes := "c1d005", instr := ⟨.rot .rcl .d (R .rax) (.imm8 5), 3⟩ }
  , { id := "rcl_ri5_q", mnemonic := "rcl", asm := "rclq $5, %rax"
    , bytes := "48c1d005", instr := ⟨.rot .rcl .q (R .rax) (.imm8 5), 4⟩ }
  , { id := "rcl_r_cl_b", mnemonic := "rcl", asm := "rclb %cl, %al"
    , bytes := "d2d0", instr := ⟨.rot .rcl .b (R .rax) .cl, 2⟩ }
  , { id := "rcl_r_cl_q", mnemonic := "rcl", asm := "rclq %cl, %rax"
    , bytes := "48d3d0", instr := ⟨.rot .rcl .q (R .rax) .cl, 3⟩ }
  , { id := "rcl_m_one_b", mnemonic := "rcl", asm := "rclb (%rbx)"
    , bytes := "d013", instr := ⟨.rot .rcl .b (M .rbx) (.imm8 1), 2⟩ }
  , { id := "rcl_m_one_q", mnemonic := "rcl", asm := "rclq (%rbx)"
    , bytes := "48d113", instr := ⟨.rot .rcl .q (M .rbx) (.imm8 1), 3⟩ }
  , { id := "rcl_mi5_b", mnemonic := "rcl", asm := "rclb $5, (%rbx)"
    , bytes := "c01305", instr := ⟨.rot .rcl .b (M .rbx) (.imm8 5), 3⟩ }
  , { id := "rcl_mi5_q", mnemonic := "rcl", asm := "rclq $5, (%rbx)"
    , bytes := "48c11305", instr := ⟨.rot .rcl .q (M .rbx) (.imm8 5), 4⟩ }
  , { id := "rcl_m_cl_b", mnemonic := "rcl", asm := "rclb %cl, (%rbx)"
    , bytes := "d213", instr := ⟨.rot .rcl .b (M .rbx) .cl, 2⟩ }
  , { id := "rcl_m_cl_q", mnemonic := "rcl", asm := "rclq %cl, (%rbx)"
    , bytes := "48d313", instr := ⟨.rot .rcl .q (M .rbx) .cl, 3⟩ }
  , { id := "rcr_r_one_b", mnemonic := "rcr", asm := "rcrb %al"
    , bytes := "d0d8", instr := ⟨.rot .rcr .b (R .rax) (.imm8 1), 2⟩ }
  , { id := "rcr_r_one_q", mnemonic := "rcr", asm := "rcrq %rax"
    , bytes := "48d1d8", instr := ⟨.rot .rcr .q (R .rax) (.imm8 1), 3⟩ }
  , { id := "rcr_ri5_b", mnemonic := "rcr", asm := "rcrb $5, %al"
    , bytes := "c0d805", instr := ⟨.rot .rcr .b (R .rax) (.imm8 5), 3⟩ }
  , { id := "rcr_ri5_w", mnemonic := "rcr", asm := "rcrw $5, %ax"
    , bytes := "66c1d805", instr := ⟨.rot .rcr .w (R .rax) (.imm8 5), 4⟩ }
  , { id := "rcr_ri5_l", mnemonic := "rcr", asm := "rcrl $5, %eax"
    , bytes := "c1d805", instr := ⟨.rot .rcr .d (R .rax) (.imm8 5), 3⟩ }
  , { id := "rcr_ri5_q", mnemonic := "rcr", asm := "rcrq $5, %rax"
    , bytes := "48c1d805", instr := ⟨.rot .rcr .q (R .rax) (.imm8 5), 4⟩ }
  , { id := "rcr_r_cl_b", mnemonic := "rcr", asm := "rcrb %cl, %al"
    , bytes := "d2d8", instr := ⟨.rot .rcr .b (R .rax) .cl, 2⟩ }
  , { id := "rcr_r_cl_q", mnemonic := "rcr", asm := "rcrq %cl, %rax"
    , bytes := "48d3d8", instr := ⟨.rot .rcr .q (R .rax) .cl, 3⟩ }
  , { id := "rcr_m_one_b", mnemonic := "rcr", asm := "rcrb (%rbx)"
    , bytes := "d01b", instr := ⟨.rot .rcr .b (M .rbx) (.imm8 1), 2⟩ }
  , { id := "rcr_m_one_q", mnemonic := "rcr", asm := "rcrq (%rbx)"
    , bytes := "48d11b", instr := ⟨.rot .rcr .q (M .rbx) (.imm8 1), 3⟩ }
  , { id := "rcr_mi5_b", mnemonic := "rcr", asm := "rcrb $5, (%rbx)"
    , bytes := "c01b05", instr := ⟨.rot .rcr .b (M .rbx) (.imm8 5), 3⟩ }
  , { id := "rcr_mi5_q", mnemonic := "rcr", asm := "rcrq $5, (%rbx)"
    , bytes := "48c11b05", instr := ⟨.rot .rcr .q (M .rbx) (.imm8 5), 4⟩ }
  , { id := "rcr_m_cl_b", mnemonic := "rcr", asm := "rcrb %cl, (%rbx)"
    , bytes := "d21b", instr := ⟨.rot .rcr .b (M .rbx) .cl, 2⟩ }
  , { id := "rcr_m_cl_q", mnemonic := "rcr", asm := "rcrq %cl, (%rbx)"
    , bytes := "48d31b", instr := ⟨.rot .rcr .q (M .rbx) .cl, 3⟩ }
  , { id := "rol_b8", mnemonic := "rol", asm := "rolb $8, %al"
    , bytes := "c0c008", instr := ⟨.rot .rol .b (R .rax) (.imm8 8), 3⟩ }
  , { id := "rol_b9", mnemonic := "rol", asm := "rolb $9, %al"
    , bytes := "c0c009", instr := ⟨.rot .rol .b (R .rax) (.imm8 9), 3⟩ }
  , { id := "rcl_b9", mnemonic := "rcl", asm := "rclb $9, %al"
    , bytes := "c0d009", instr := ⟨.rot .rcl .b (R .rax) (.imm8 9), 3⟩ }
  -- ══ P1 BATCH 9 ═════════════════════════════════════════════════════════
  -- The BIT-TEST group: roster families 31, 32 and 41 — `bt`/`bts`/`btr`/`btc`
  -- at `r,imm`, `r,r` and `m,imm`, widths w/l/q (there is no 8-bit form).
  -- **12 of the group's 16 forms.**
  --
  -- ⛔ THE FOUR `m,r` FORMS ARE DELIBERATELY NOT HERE, and the reason is not
  -- time.  With a MEMORY destination and a REGISTER offset the operand is not a
  -- word with a bit selected in it — it is the base of a BIT STRING, the offset
  -- is SIGNED and may reach far outside the addressed operand, and the
  -- effective address moves with it.  That is a different addressing mode
  -- wearing the same mnemonic.  Guessing at it would be worse than declining,
  -- so it is declined and named (docs/DECISIONS.md D23).
  --
  -- ⭐ `bt` IS TO THIS GROUP WHAT `cmp` IS TO THE ALU: the test happens, CF
  -- takes the selected bit, and the destination is NOT written.  The other
  -- three do the identical test and then set, clear or complement.
  --
  -- ⚠️ AND ZF IS THE ONLY ARITHMETIC FLAG THAT SURVIVES.  The SDM: "the ZF flag
  -- is unaffected... the OF, SF, AF, and PF flags are undefined".  That is four
  -- oracle draws on an instruction that computes almost nothing — the widest
  -- undefined set in the model so far, and the reason these rows are T-frame.
  , { id := "bt_ri_w", mnemonic := "bt", asm := "bt $5, %ax"
    , bytes := "660fbae005", instr := ⟨.bit .bt .w (R .rax) (.imm 5), 5⟩ }
  , { id := "bt_ri_l", mnemonic := "bt", asm := "bt $5, %eax"
    , bytes := "0fbae005", instr := ⟨.bit .bt .d (R .rax) (.imm 5), 4⟩ }
  , { id := "bt_ri_q", mnemonic := "bt", asm := "bt $5, %rax"
    , bytes := "480fbae005", instr := ⟨.bit .bt .q (R .rax) (.imm 5), 5⟩ }
  , { id := "bt_rr_w", mnemonic := "bt", asm := "bt %cx, %ax"
    , bytes := "660fa3c8", instr := ⟨.bit .bt .w (R .rax) (R .rcx), 4⟩ }
  , { id := "bt_rr_l", mnemonic := "bt", asm := "bt %ecx, %eax"
    , bytes := "0fa3c8", instr := ⟨.bit .bt .d (R .rax) (R .rcx), 3⟩ }
  , { id := "bt_rr_q", mnemonic := "bt", asm := "bt %rcx, %rax"
    , bytes := "480fa3c8", instr := ⟨.bit .bt .q (R .rax) (R .rcx), 4⟩ }
  , { id := "bt_mi_w", mnemonic := "bt", asm := "btw $5, (%rbx)"
    , bytes := "660fba2305", instr := ⟨.bit .bt .w (M .rbx) (.imm 5), 5⟩ }
  , { id := "bt_mi_l", mnemonic := "bt", asm := "btl $5, (%rbx)"
    , bytes := "0fba2305", instr := ⟨.bit .bt .d (M .rbx) (.imm 5), 4⟩ }
  , { id := "bt_mi_q", mnemonic := "bt", asm := "btq $5, (%rbx)"
    , bytes := "480fba2305", instr := ⟨.bit .bt .q (M .rbx) (.imm 5), 5⟩ }
  , { id := "bts_ri_w", mnemonic := "bts", asm := "bts $5, %ax"
    , bytes := "660fbae805", instr := ⟨.bit .bts .w (R .rax) (.imm 5), 5⟩ }
  , { id := "bts_ri_l", mnemonic := "bts", asm := "bts $5, %eax"
    , bytes := "0fbae805", instr := ⟨.bit .bts .d (R .rax) (.imm 5), 4⟩ }
  , { id := "bts_ri_q", mnemonic := "bts", asm := "bts $5, %rax"
    , bytes := "480fbae805", instr := ⟨.bit .bts .q (R .rax) (.imm 5), 5⟩ }
  , { id := "bts_rr_w", mnemonic := "bts", asm := "bts %cx, %ax"
    , bytes := "660fabc8", instr := ⟨.bit .bts .w (R .rax) (R .rcx), 4⟩ }
  , { id := "bts_rr_l", mnemonic := "bts", asm := "bts %ecx, %eax"
    , bytes := "0fabc8", instr := ⟨.bit .bts .d (R .rax) (R .rcx), 3⟩ }
  , { id := "bts_rr_q", mnemonic := "bts", asm := "bts %rcx, %rax"
    , bytes := "480fabc8", instr := ⟨.bit .bts .q (R .rax) (R .rcx), 4⟩ }
  , { id := "bts_mi_w", mnemonic := "bts", asm := "btsw $5, (%rbx)"
    , bytes := "660fba2b05", instr := ⟨.bit .bts .w (M .rbx) (.imm 5), 5⟩ }
  , { id := "bts_mi_l", mnemonic := "bts", asm := "btsl $5, (%rbx)"
    , bytes := "0fba2b05", instr := ⟨.bit .bts .d (M .rbx) (.imm 5), 4⟩ }
  , { id := "bts_mi_q", mnemonic := "bts", asm := "btsq $5, (%rbx)"
    , bytes := "480fba2b05", instr := ⟨.bit .bts .q (M .rbx) (.imm 5), 5⟩ }
  , { id := "btr_ri_w", mnemonic := "btr", asm := "btr $5, %ax"
    , bytes := "660fbaf005", instr := ⟨.bit .btr .w (R .rax) (.imm 5), 5⟩ }
  , { id := "btr_ri_l", mnemonic := "btr", asm := "btr $5, %eax"
    , bytes := "0fbaf005", instr := ⟨.bit .btr .d (R .rax) (.imm 5), 4⟩ }
  , { id := "btr_ri_q", mnemonic := "btr", asm := "btr $5, %rax"
    , bytes := "480fbaf005", instr := ⟨.bit .btr .q (R .rax) (.imm 5), 5⟩ }
  , { id := "btr_rr_w", mnemonic := "btr", asm := "btr %cx, %ax"
    , bytes := "660fb3c8", instr := ⟨.bit .btr .w (R .rax) (R .rcx), 4⟩ }
  , { id := "btr_rr_l", mnemonic := "btr", asm := "btr %ecx, %eax"
    , bytes := "0fb3c8", instr := ⟨.bit .btr .d (R .rax) (R .rcx), 3⟩ }
  , { id := "btr_rr_q", mnemonic := "btr", asm := "btr %rcx, %rax"
    , bytes := "480fb3c8", instr := ⟨.bit .btr .q (R .rax) (R .rcx), 4⟩ }
  , { id := "btr_mi_w", mnemonic := "btr", asm := "btrw $5, (%rbx)"
    , bytes := "660fba3305", instr := ⟨.bit .btr .w (M .rbx) (.imm 5), 5⟩ }
  , { id := "btr_mi_l", mnemonic := "btr", asm := "btrl $5, (%rbx)"
    , bytes := "0fba3305", instr := ⟨.bit .btr .d (M .rbx) (.imm 5), 4⟩ }
  , { id := "btr_mi_q", mnemonic := "btr", asm := "btrq $5, (%rbx)"
    , bytes := "480fba3305", instr := ⟨.bit .btr .q (M .rbx) (.imm 5), 5⟩ }
  , { id := "btc_ri_w", mnemonic := "btc", asm := "btc $5, %ax"
    , bytes := "660fbaf805", instr := ⟨.bit .btc .w (R .rax) (.imm 5), 5⟩ }
  , { id := "btc_ri_l", mnemonic := "btc", asm := "btc $5, %eax"
    , bytes := "0fbaf805", instr := ⟨.bit .btc .d (R .rax) (.imm 5), 4⟩ }
  , { id := "btc_ri_q", mnemonic := "btc", asm := "btc $5, %rax"
    , bytes := "480fbaf805", instr := ⟨.bit .btc .q (R .rax) (.imm 5), 5⟩ }
  , { id := "btc_rr_w", mnemonic := "btc", asm := "btc %cx, %ax"
    , bytes := "660fbbc8", instr := ⟨.bit .btc .w (R .rax) (R .rcx), 4⟩ }
  , { id := "btc_rr_l", mnemonic := "btc", asm := "btc %ecx, %eax"
    , bytes := "0fbbc8", instr := ⟨.bit .btc .d (R .rax) (R .rcx), 3⟩ }
  , { id := "btc_rr_q", mnemonic := "btc", asm := "btc %rcx, %rax"
    , bytes := "480fbbc8", instr := ⟨.bit .btc .q (R .rax) (R .rcx), 4⟩ }
  , { id := "btc_mi_w", mnemonic := "btc", asm := "btcw $5, (%rbx)"
    , bytes := "660fba3b05", instr := ⟨.bit .btc .w (M .rbx) (.imm 5), 5⟩ }
  , { id := "btc_mi_l", mnemonic := "btc", asm := "btcl $5, (%rbx)"
    , bytes := "0fba3b05", instr := ⟨.bit .btc .d (M .rbx) (.imm 5), 4⟩ }
  , { id := "btc_mi_q", mnemonic := "btc", asm := "btcq $5, (%rbx)"
    , bytes := "480fba3b05", instr := ⟨.bit .btc .q (M .rbx) (.imm 5), 5⟩ }

  -- ══ P1 BATCH 10 ═══════════════════════════════════════════════════════════
  -- Roster family 15 (`-------|-|reg`), its NO-FLAG core: the width-changing
  -- and two-destination moves.  Not one of these instructions writes a flag,
  -- so the whole batch is a test of the DATA path.
  --
  -- ⭐ MOVZX / MOVSX: the first forms whose SOURCE WIDTH DIFFERS FROM THEIR
  -- DESTINATION WIDTH.  The three destination widths are all here on purpose:
  -- `.w` PRESERVES the bits above it, `.d` ZERO-EXTENDS over them and `.q`
  -- replaces the register (SDM Vol. 1 §3.4.1.1).  A model that extended to 64
  -- bits and wrote all of them would be right at `.d` and `.q` and wrong only
  -- at `.w` — which is the batch's second planted bug, and these two `bw` rows
  -- are the only vectors that can see it.
  , { id := "movzx_rr_bw", mnemonic := "movzx", asm := "movzbw %cl, %ax"
    , bytes := "660fb6c1", instr := ⟨.movx .zero .w .b .rax (R .rcx), 4⟩ }
  , { id := "movzx_rr_bl", mnemonic := "movzx", asm := "movzbl %cl, %eax"
    , bytes := "0fb6c1", instr := ⟨.movx .zero .d .b .rax (R .rcx), 3⟩ }
  , { id := "movzx_rr_bq", mnemonic := "movzx", asm := "movzbq %cl, %rax"
    , bytes := "480fb6c1", instr := ⟨.movx .zero .q .b .rax (R .rcx), 4⟩ }
  -- the HIGH-8 source: bits 15:8 of RCX, zero-extended into EAX.  The only
  -- vector in this batch whose source is not at the bottom of its register.
  , { id := "movzx_rr_h8", mnemonic := "movzx", asm := "movzbl %ch, %eax"
    , bytes := "0fb6c5", instr := ⟨.movx .zero .d .b .rax (H .rcx), 3⟩ }
  , { id := "movzx_rm_bl", mnemonic := "movzx", asm := "movzbl (%rbx), %eax"
    , bytes := "0fb603", instr := ⟨.movx .zero .d .b .rax (M .rbx), 3⟩ }
  , { id := "movzx_rm_bq", mnemonic := "movzx", asm := "movzbq (%rbx), %rax"
    , bytes := "480fb603", instr := ⟨.movx .zero .q .b .rax (M .rbx), 4⟩ }
  , { id := "movzx_rr_wl", mnemonic := "movzx", asm := "movzwl %cx, %eax"
    , bytes := "0fb7c1", instr := ⟨.movx .zero .d .w .rax (R .rcx), 3⟩ }
  , { id := "movzx_rr_wq", mnemonic := "movzx", asm := "movzwq %cx, %rax"
    , bytes := "480fb7c1", instr := ⟨.movx .zero .q .w .rax (R .rcx), 4⟩ }
  , { id := "movzx_rm_wl", mnemonic := "movzx", asm := "movzwl (%rbx), %eax"
    , bytes := "0fb703", instr := ⟨.movx .zero .d .w .rax (M .rbx), 3⟩ }
  , { id := "movsx_rr_bw", mnemonic := "movsx", asm := "movsbw %cl, %ax"
    , bytes := "660fbec1", instr := ⟨.movx .sign .w .b .rax (R .rcx), 4⟩ }
  , { id := "movsx_rr_bl", mnemonic := "movsx", asm := "movsbl %cl, %eax"
    , bytes := "0fbec1", instr := ⟨.movx .sign .d .b .rax (R .rcx), 3⟩ }
  , { id := "movsx_rr_bq", mnemonic := "movsx", asm := "movsbq %cl, %rax"
    , bytes := "480fbec1", instr := ⟨.movx .sign .q .b .rax (R .rcx), 4⟩ }
  , { id := "movsx_rm_bl", mnemonic := "movsx", asm := "movsbl (%rbx), %eax"
    , bytes := "0fbe03", instr := ⟨.movx .sign .d .b .rax (M .rbx), 3⟩ }
  , { id := "movsx_rr_wl", mnemonic := "movsx", asm := "movswl %cx, %eax"
    , bytes := "0fbfc1", instr := ⟨.movx .sign .d .w .rax (R .rcx), 3⟩ }
  , { id := "movsx_rr_wq", mnemonic := "movsx", asm := "movswq %cx, %rax"
    , bytes := "480fbfc1", instr := ⟨.movx .sign .q .w .rax (R .rcx), 4⟩ }
  , { id := "movsx_rm_wq", mnemonic := "movsx", asm := "movswq (%rbx), %rax"
    , bytes := "480fbf03", instr := ⟨.movx .sign .q .w .rax (M .rbx), 4⟩ }
  -- MOVSXD (`movslq`): a DIFFERENT OPCODE — `63 /r`, one byte, no `0f` escape —
  -- for the same rule.  It is the same constructor because the rule is what the
  -- model implements; the opcode difference lives in the bytes, which the
  -- encoding cross-check holds.
  , { id := "movsx_rr_lq", mnemonic := "movsx", asm := "movslq %ecx, %rax"
    , bytes := "4863c1", instr := ⟨.movx .sign .q .d .rax (R .rcx), 3⟩ }
  , { id := "movsx_rm_lq", mnemonic := "movsx", asm := "movslq (%rbx), %rax"
    , bytes := "486303", instr := ⟨.movx .sign .q .d .rax (M .rbx), 3⟩ }

  -- ⭐ THE IMPLICIT-ACCUMULATOR SIGN EXTENSIONS.  Six instructions, no operands,
  -- one bit apart in the opcode (`98` vs `99`) and writing DIFFERENT REGISTERS:
  -- the `98` trio widens RAX in place, the `99` trio fills RDX with RAX's sign
  -- and leaves RAX alone.  `cwtl` and `cltd` are the two whose write is 32 bits
  -- wide, so they CLEAR the upper half of the register they write — and for
  -- `cltd` that is only visible because `mkPre` now puts something in RDX.
  , { id := "cbtw", mnemonic := "cbtw", asm := "cbtw", bytes := "6698"
    , instr := ⟨.cext .cbw, 2⟩ }
  , { id := "cwtl", mnemonic := "cwtl", asm := "cwtl", bytes := "98"
    , instr := ⟨.cext .cwde, 1⟩ }
  , { id := "cltq", mnemonic := "cltq", asm := "cltq", bytes := "4898"
    , instr := ⟨.cext .cdqe, 2⟩ }
  , { id := "cwtd", mnemonic := "cwtd", asm := "cwtd", bytes := "6699"
    , instr := ⟨.cext .cwd, 2⟩ }
  , { id := "cltd", mnemonic := "cltd", asm := "cltd", bytes := "99"
    , instr := ⟨.cext .cdq, 1⟩ }
  , { id := "cqto", mnemonic := "cqto", asm := "cqto", bytes := "4899"
    , instr := ⟨.cext .cqo, 2⟩ }

  -- ⭐ XCHG, THE FIRST FORM THAT WRITES BOTH OF ITS OPERANDS.
  --
  -- ⚠️ `xchg_rr_w` AND `xchg_ar_w` ARE THE SAME BYTES, `6691`, and that is why
  -- both are here: the roster counts `ax,r` and `r,ax` as two forms, the
  -- assembler emits ONE encoding for both, and the encoding cross-check on the
  -- two rows is the evidence for saying so.  Without the second row the claim
  -- would be a sentence in a comment.
  , { id := "xchg_rr_b", mnemonic := "xchg", asm := "xchg %cl, %al"
    , bytes := "86c1", instr := ⟨.xchg .b (R .rax) (R .rcx), 2⟩ }
  , { id := "xchg_rr_w", mnemonic := "xchg", asm := "xchg %cx, %ax"
    , bytes := "6691", instr := ⟨.xchg .w (R .rax) (R .rcx), 2⟩ }
  , { id := "xchg_ar_w", mnemonic := "xchg", asm := "xchg %ax, %cx"
    , bytes := "6691", instr := ⟨.xchg .w (R .rcx) (R .rax), 2⟩ }
  , { id := "xchg_rr_l", mnemonic := "xchg", asm := "xchg %ecx, %eax"
    , bytes := "91", instr := ⟨.xchg .d (R .rax) (R .rcx), 1⟩ }
  , { id := "xchg_rr_q", mnemonic := "xchg", asm := "xchg %rcx, %rax"
    , bytes := "4891", instr := ⟨.xchg .q (R .rax) (R .rcx), 2⟩ }
  -- neither operand is the accumulator, so this one cannot take the `90+r`
  -- short encoding and goes through ModR/M
  , { id := "xchg_nn_q", mnemonic := "xchg", asm := "xchg %rbx, %rcx"
    , bytes := "4887cb", instr := ⟨.xchg .q (R .rcx) (R .rbx), 3⟩ }
  -- ⭐ AND THE ONE THAT SAYS WHY `xchg` IS NOT A SWAP OF VALUES BUT A PAIR OF
  -- WRITES.  `xchg %eax, %eax` moves no data and still CLEARS the upper half of
  -- RAX, because a 32-bit write zero-extends.  The assembler proves the point
  -- rather than the manual: it will NOT encode this as `90`, though `90` is
  -- "xchg eax, eax" in every opcode table — it emits `87 c0` — because `90` in
  -- 64-bit mode is NOP and NOP does not touch RAX.  `xchg %rax, %rax` DOES
  -- assemble to `90`, and is therefore not this instruction at all and is not
  -- in this table (docs/DECISIONS.md D24).
  , { id := "xchg_same_l", mnemonic := "xchg", asm := "xchg %eax, %eax"
    , bytes := "87c0", instr := ⟨.xchg .d (R .rax) (R .rax), 2⟩ }

  -- BSWAP at the two widths the SDM defines.  `bswapl` reverses four bytes and
  -- then zero-extends; `bswapq` reverses eight.
  , { id := "bswap_l", mnemonic := "bswap", asm := "bswap %eax", bytes := "0fc8"
    , instr := ⟨.bswap .d .rax, 2⟩ }
  , { id := "bswap_q", mnemonic := "bswap", asm := "bswap %rax", bytes := "480fc8"
    , instr := ⟨.bswap .q .rax, 3⟩ }

  -- ══ P1 BATCH 11 ═══════════════════════════════════════════════════════
  -- THE LOOP GROUP.  Each predicate at BOTH counter widths, because `addr32` is
  -- a width on the read, on the wrap AND on the write-back, and the three are
  -- separately wrong-able.
  --
  -- ⚠️ THE BYTES ARE THE AUTHORITY AND THE `.+18` IS NOT.  For the prefixed
  -- forms clang computes `.` from the address AFTER the `0x67` byte, so
  -- `addr32 loop .+18` encodes rel8 = 0x10 and actually targets `.+19`.  The
  -- model's `d` is the ENCODED rel8, which is what `scripts/check_encodings.py`
  -- compares against the disassembly — so this row is right and the comment is
  -- the only place the discrepancy in the source string is visible at all.
  , { id := "loop_rel8", mnemonic := "loop", asm := "loop .+18"
    , bytes := "e210", instr := ⟨.loop .loop false 0x10, 2⟩ }
  , { id := "loope_rel8", mnemonic := "loope", asm := "loope .+18"
    , bytes := "e110", instr := ⟨.loop .loope false 0x10, 2⟩ }
  , { id := "loopne_rel8", mnemonic := "loopne", asm := "loopne .+18"
    , bytes := "e010", instr := ⟨.loop .loopne false 0x10, 2⟩ }
  -- ⭐ THE BACKWARD BRANCH, which is the shape every real loop has.  `loop .-2`
  -- encodes rel8 = 0xFC = -4, so the target is two bytes BEFORE this
  -- instruction.  It is here because every other branch vector in this
  -- repository jumps forward, and a sign error in the displacement is invisible
  -- against a table of positive ones.
  , { id := "loop_back", mnemonic := "loop", asm := "loop .-2"
    , bytes := "e2fc", instr := ⟨.loop .loop false 0xFFFFFFFFFFFFFFFC, 2⟩ }
  -- The address-size-prefixed forms: the counter is ECX and the write-back
  -- zero-extends into RCX.
  , { id := "loop_a32", mnemonic := "loop", asm := "addr32 loop .+18"
    , bytes := "67e210", instr := ⟨.loop .loop true 0x10, 3⟩ }
  , { id := "loope_a32", mnemonic := "loope", asm := "addr32 loope .+18"
    , bytes := "67e110", instr := ⟨.loop .loope true 0x10, 3⟩ }
  , { id := "loopne_a32", mnemonic := "loopne", asm := "addr32 loopne .+18"
    , bytes := "67e010", instr := ⟨.loop .loopne true 0x10, 3⟩ }

  -- THE FLAG-CONTROL SINGLES.  One byte each, one flag each, and the whole
  -- group exists in this batch because `cld` and `std` are the model's only
  -- writers of DF.
  , { id := "clc", mnemonic := "clc", asm := "clc", bytes := "f8"
    , instr := ⟨.flagop .clc, 1⟩ }
  , { id := "stc", mnemonic := "stc", asm := "stc", bytes := "f9"
    , instr := ⟨.flagop .stc, 1⟩ }
  , { id := "cmc", mnemonic := "cmc", asm := "cmc", bytes := "f5"
    , instr := ⟨.flagop .cmc, 1⟩ }
  , { id := "cld", mnemonic := "cld", asm := "cld", bytes := "fc"
    , instr := ⟨.flagop .cld, 1⟩ }
  , { id := "std", mnemonic := "std", asm := "std", bytes := "fd"
    , instr := ⟨.flagop .std, 1⟩ }

  -- ══ P1 BATCH 12 ═══════════════════════════════════════════════════════
  -- The near-free four of roster family 7: `nop` at its three shapes, `ud2`,
  -- `retq` and `leaveq`.  Cheap in SEMANTICS — none of them touches a flag —
  -- and NOT cheap in STATE, which is the batch's finding: two of the four are
  -- unreachable against the existing pre-states.  See `frameStates` below.
  --
  -- ⛔ `lods` IS NOT HERE ALTHOUGH THE BANK LISTED IT AS A CHEAP CANDIDATE.
  -- ACL2 x86isa does not implement it: `machine/catalogue-data.lisp`, section
  -- "5.1.8 String Instructions", says in as many words "Unimplemented
  -- instructions: SCAS and LODS variations".  A form the oracle cannot execute
  -- cannot be differentially validated, so it is not a cheap form — it is a
  -- form that needs a different oracle.
  --
  -- ⛔⛔ AND THAT PARAGRAPH IS FALSE.  P1 BATCH 13 RAN THE OPCODES INSTEAD OF
  -- READING THE PROSE: `lodsb/w/l/q` and `scasb/w/l/q` all EXECUTE in ACL2
  -- x86isa — `lodsq` loads eight bytes and advances RSI by 8, `scasq` compares
  -- and advances RDI — while `blsr`, `blsmsk`, `bzhi`, `pdep`, `pext`, `andn`,
  -- `bextr`, `mulx` and `rorx` refuse in the same run, so the probe was
  -- calibrated in BOTH directions.  The same `:doc` is wrong the other way
  -- about `lzcnt` (listed unimplemented, executes) and silent about `blsi`
  -- (listed in neither its implemented nor its unimplemented set, executes).
  --
  -- ⇒ **A CATALOGUE'S PROSE IS A CLAIM ABOUT THE MODEL, NOT A MEASUREMENT OF
  -- IT** — and the previous batch's own bank had made "check the oracle's
  -- catalogue FIRST" the rule for pricing a form, which turned one file's stale
  -- doc-string into this project's roster policy.  `lods`/`scas` are back on
  -- the candidate list.  See docs/DECISIONS.md D36.
  --
  -- NOP's three shapes are ONE instruction and one constructor.  The bare `0x90`
  -- and the multi-byte `0F 1F /0` differ only in how many bytes they occupy;
  -- the operand of the long form exists to pad, and `step` never reads it.
  , { id := "nop", mnemonic := "nop", asm := "nop", bytes := "90"
    , instr := ⟨.nop none, 1⟩ }
  , { id := "nop_r_l", mnemonic := "nop", asm := "nopl %eax", bytes := "0f1fc0"
    , instr := ⟨.nop (some (R .rax)), 3⟩ }
  , { id := "nop_r_w", mnemonic := "nop", asm := "nopw %ax", bytes := "660f1fc0"
    , instr := ⟨.nop (some (R .rax)), 4⟩ }
  -- ⭐ THE MEMORY SHAPE IS THE ONE WITH A CLAIM IN IT.  `nopl (%rbx)` addresses
  -- the data window, and the assertion is that it does NOT read it: the post
  -- state must be RIP+3 and nothing else, with the window untouched.
  , { id := "nop_m_l", mnemonic := "nop", asm := "nopl (%rbx)", bytes := "0f1f03"
    , instr := ⟨.nop (some (M .rbx)), 3⟩ }
  , { id := "nop_m_w", mnemonic := "nop", asm := "nopw (%rbx)", bytes := "660f1f03"
    , instr := ⟨.nop (some (M .rbx)), 4⟩ }
  -- UD2: the first vector in the roster whose EXPECTED result is a refusal on
  -- both sides.  `bothRefused` is what makes the two models agree here.
  , { id := "ud2", mnemonic := "ud2", asm := "ud2", bytes := "0f0b"
    , instr := ⟨.ud2, 2⟩ }
  , { id := "retq", mnemonic := "retq", asm := "retq", bytes := "c3"
    , instr := ⟨.ret, 1⟩ }
  , { id := "leaveq", mnemonic := "leaveq", asm := "leaveq", bytes := "c9"
    , instr := ⟨.leave, 1⟩ }

  -- ══ P1 BATCH 13 ═══════════════════════════════════════════════════════
  -- The flagless shifts (roster family 15: `sarx`, `shlx`, `shrx` at `r,r,r`
  -- and `r,m,r`) and the byte-swapping move (`movbe` at `r,m` and `m,r`).
  --
  -- ⭐ THE COUNT REGISTER IS RDX, AND THAT IS WHY THIS BATCH NEEDS NO NEW
  -- PRE-STATE.  `mkPre` sets `rdx := ~~~a` — added in batch 10 so that `cltd`
  -- had a non-constant RDX to clobber — so the shift count sweeps over the
  -- complements of the whole adversarial list.  It reaches a masked count of
  -- ZERO (from `a = 0xFF`, whose complement's low byte is 0) and a masked count
  -- of 63/31 (from `a = 0`), which are the two ends of the mask.
  -- ⇒ The batch-12 rule — the cost of a form is a fact about the STATE it needs
  -- — cuts the other way here: these forms are cheap in state precisely because
  -- an EARLIER batch paid for the component they read.
  --
  -- ⚠️ AND THE MASK IS OBSERVABLE, which is what makes the sweep worth having:
  -- `a = 0` gives an unmasked count of 255, and a model that failed to mask
  -- would shift everything out and answer 0 where the machine answers
  -- `src >> 63`.
  , { id := "shlx_rrr_q", mnemonic := "shlx", asm := "shlxq %rdx, %rcx, %rax"
    , bytes := "c4e2e9f7c1", instr := ⟨.shiftx .shl .q .rax (R .rcx) .rdx, 5⟩ }
  , { id := "shlx_rrr_d", mnemonic := "shlx", asm := "shlxl %edx, %ecx, %eax"
    , bytes := "c4e269f7c1", instr := ⟨.shiftx .shl .d .rax (R .rcx) .rdx, 5⟩ }
  , { id := "shrx_rrr_q", mnemonic := "shrx", asm := "shrxq %rdx, %rcx, %rax"
    , bytes := "c4e2ebf7c1", instr := ⟨.shiftx .shr .q .rax (R .rcx) .rdx, 5⟩ }
  , { id := "shrx_rrr_d", mnemonic := "shrx", asm := "shrxl %edx, %ecx, %eax"
    , bytes := "c4e26bf7c1", instr := ⟨.shiftx .shr .d .rax (R .rcx) .rdx, 5⟩ }
  , { id := "sarx_rrr_q", mnemonic := "sarx", asm := "sarxq %rdx, %rcx, %rax"
    , bytes := "c4e2eaf7c1", instr := ⟨.shiftx .sar .q .rax (R .rcx) .rdx, 5⟩ }
  , { id := "sarx_rrr_d", mnemonic := "sarx", asm := "sarxl %edx, %ecx, %eax"
    , bytes := "c4e26af7c1", instr := ⟨.shiftx .sar .d .rax (R .rcx) .rdx, 5⟩ }
  -- The `r,m,r` shape: the SOURCE is memory and the destination is still a
  -- register.  `(%rbx)` is the data window, whose eight bytes carry `c` — the
  -- same value RCX carries — so these six sweep exactly as the six above do.
  , { id := "shlx_rmr_q", mnemonic := "shlx", asm := "shlxq %rdx, (%rbx), %rax"
    , bytes := "c4e2e9f703", instr := ⟨.shiftx .shl .q .rax (M .rbx) .rdx, 5⟩ }
  , { id := "shlx_rmr_d", mnemonic := "shlx", asm := "shlxl %edx, (%rbx), %eax"
    , bytes := "c4e269f703", instr := ⟨.shiftx .shl .d .rax (M .rbx) .rdx, 5⟩ }
  , { id := "shrx_rmr_q", mnemonic := "shrx", asm := "shrxq %rdx, (%rbx), %rax"
    , bytes := "c4e2ebf703", instr := ⟨.shiftx .shr .q .rax (M .rbx) .rdx, 5⟩ }
  , { id := "shrx_rmr_d", mnemonic := "shrx", asm := "shrxl %edx, (%rbx), %eax"
    , bytes := "c4e26bf703", instr := ⟨.shiftx .shr .d .rax (M .rbx) .rdx, 5⟩ }
  , { id := "sarx_rmr_q", mnemonic := "sarx", asm := "sarxq %rdx, (%rbx), %rax"
    , bytes := "c4e2eaf703", instr := ⟨.shiftx .sar .q .rax (M .rbx) .rdx, 5⟩ }
  , { id := "sarx_rmr_d", mnemonic := "sarx", asm := "sarxl %edx, (%rbx), %eax"
    , bytes := "c4e26af703", instr := ⟨.shiftx .sar .d .rax (M .rbx) .rdx, 5⟩ }
  -- MOVBE, both directions at all three widths.
  --
  -- ⚠️ THE THREE WIDTHS ARE THE INSTRUCTION.  A model that byte-reversed at 64
  -- bits and truncated afterwards agrees with this one at `.q` and disagrees at
  -- `.w` and `.d` in EVERY pre-state where the operand is not a palindrome —
  -- so the narrow widths are not width-padding, they are the only vectors that
  -- can tell the two apart.  `wrongMovbeFullWidth` is that model.
  , { id := "movbe_rm_q", mnemonic := "movbe", asm := "movbeq (%rbx), %rax"
    , bytes := "480f38f003", instr := ⟨.movbe .q (R .rax) (M .rbx), 5⟩ }
  , { id := "movbe_rm_d", mnemonic := "movbe", asm := "movbel (%rbx), %eax"
    , bytes := "0f38f003", instr := ⟨.movbe .d (R .rax) (M .rbx), 4⟩ }
  , { id := "movbe_rm_w", mnemonic := "movbe", asm := "movbew (%rbx), %ax"
    , bytes := "660f38f003", instr := ⟨.movbe .w (R .rax) (M .rbx), 5⟩ }
  -- The STORE direction — the batch's memory-DESTINATION claim, spelled `m(w)`
  -- in the coverage table.  At `.w` it writes TWO bytes into the middle of the
  -- eight-byte span the window carries, so a store of the wrong width shows as
  -- a difference in the bytes it should not have touched.
  , { id := "movbe_mr_q", mnemonic := "movbe", asm := "movbeq %rax, (%rbx)"
    , bytes := "480f38f103", instr := ⟨.movbe .q (M .rbx) (R .rax), 5⟩ }
  , { id := "movbe_mr_d", mnemonic := "movbe", asm := "movbel %eax, (%rbx)"
    , bytes := "0f38f103", instr := ⟨.movbe .d (M .rbx) (R .rax), 4⟩ }
  , { id := "movbe_mr_w", mnemonic := "movbe", asm := "movbew %ax, (%rbx)"
    , bytes := "660f38f103", instr := ⟨.movbe .w (M .rbx) (R .rax), 5⟩ }

  -- ══ P1 BATCH 14 ═══════════════════════════════════════════════════════
  -- The bit-counting group: POPCNT, LZCNT, TZCNT, BSF, BSR, BLSI at `r,r` and
  -- `r,m`, every width each of them has an encoding for.  Twelve roster rows,
  -- and NO NEW PRE-STATE — `preStates`' `diag` arm is `mkPre a a 0`, so RCX and
  -- the eight bytes at RBX both carry `a`, and `adversarial` contains 0.  The
  -- zero source is therefore reached by BOTH shapes rather than being a case
  -- this batch would have had to construct.  ⚠️ That is asserted rather than
  -- assumed: `bit_counting_reaches_a_zero_register_source` and
  -- `bit_counting_reaches_a_zero_memory_source` in `Tests/Coverage.lean`
  -- (cited here as one name until batch 16; the theorem was split in two and
  -- the citation was not).
  --
  -- ⭐⭐ LZCNT IS BSR PLUS AN F3 PREFIX, AND TZCNT IS BSF PLUS AN F3 PREFIX.
  -- Read the assembled bytes above: `bsrq %rcx, %rax` is `480fbdc1` and
  -- `lzcntq %rcx, %rax` is `f3480fbdc1` — the SAME OPCODE 0F BD, one byte
  -- apart.  That is not a coincidence of this table, it is the encoding: a CPU
  -- without the LZCNT feature executes `lzcnt` AS `bsr`, silently, because F3
  -- is a prefix it is entitled to ignore.
  --
  -- ⇒ THE TWO ANSWER DIFFERENT QUESTIONS ABOUT THE SAME BITS.  BSR reports the
  -- INDEX of the highest set bit; LZCNT counts the zeros ABOVE it.  They sum to
  -- the width minus one, so they agree at exactly one source per width and
  -- differ everywhere else.  Batch 13 measured this against the oracle and
  -- recorded the witness — `lzcntq 0x123456789ABCDEF0` = 3 where `bsr` = 60 —
  -- and `X86.Value.bitScanReverse`'s own comment names the confusion; the
  -- deliberately wrong model `wrongBsrIsLzcnt` is it, planted.
  --
  -- ⚠️ AND THE ZERO SOURCE SEPARATES THEM AGAIN, differently: `lzcnt` and
  -- `tzcnt` answer the WIDTH and set CF, while `bsf` and `bsr` leave the
  -- DESTINATION UNDEFINED and set ZF.  Four instructions on two opcodes, and
  -- every pair of them differs somewhere in this vector table.
  , { id := "popcnt_rr_w", mnemonic := "popcnt", asm := "popcntw %cx, %ax"
    , bytes := "66f30fb8c1", instr := ⟨.bitcnt .popcnt .w .rax (R .rcx), 5⟩ }
  , { id := "popcnt_rm_w", mnemonic := "popcnt", asm := "popcntw (%rbx), %ax"
    , bytes := "66f30fb803", instr := ⟨.bitcnt .popcnt .w .rax (M .rbx), 5⟩ }
  , { id := "popcnt_rr_d", mnemonic := "popcnt", asm := "popcntl %ecx, %eax"
    , bytes := "f30fb8c1", instr := ⟨.bitcnt .popcnt .d .rax (R .rcx), 4⟩ }
  , { id := "popcnt_rm_d", mnemonic := "popcnt", asm := "popcntl (%rbx), %eax"
    , bytes := "f30fb803", instr := ⟨.bitcnt .popcnt .d .rax (M .rbx), 4⟩ }
  , { id := "popcnt_rr_q", mnemonic := "popcnt", asm := "popcntq %rcx, %rax"
    , bytes := "f3480fb8c1", instr := ⟨.bitcnt .popcnt .q .rax (R .rcx), 5⟩ }
  , { id := "popcnt_rm_q", mnemonic := "popcnt", asm := "popcntq (%rbx), %rax"
    , bytes := "f3480fb803", instr := ⟨.bitcnt .popcnt .q .rax (M .rbx), 5⟩ }
  , { id := "lzcnt_rr_w", mnemonic := "lzcnt", asm := "lzcntw %cx, %ax"
    , bytes := "66f30fbdc1", instr := ⟨.bitcnt .lzcnt .w .rax (R .rcx), 5⟩ }
  , { id := "lzcnt_rm_w", mnemonic := "lzcnt", asm := "lzcntw (%rbx), %ax"
    , bytes := "66f30fbd03", instr := ⟨.bitcnt .lzcnt .w .rax (M .rbx), 5⟩ }
  , { id := "lzcnt_rr_d", mnemonic := "lzcnt", asm := "lzcntl %ecx, %eax"
    , bytes := "f30fbdc1", instr := ⟨.bitcnt .lzcnt .d .rax (R .rcx), 4⟩ }
  , { id := "lzcnt_rm_d", mnemonic := "lzcnt", asm := "lzcntl (%rbx), %eax"
    , bytes := "f30fbd03", instr := ⟨.bitcnt .lzcnt .d .rax (M .rbx), 4⟩ }
  , { id := "lzcnt_rr_q", mnemonic := "lzcnt", asm := "lzcntq %rcx, %rax"
    , bytes := "f3480fbdc1", instr := ⟨.bitcnt .lzcnt .q .rax (R .rcx), 5⟩ }
  , { id := "lzcnt_rm_q", mnemonic := "lzcnt", asm := "lzcntq (%rbx), %rax"
    , bytes := "f3480fbd03", instr := ⟨.bitcnt .lzcnt .q .rax (M .rbx), 5⟩ }
  , { id := "tzcnt_rr_w", mnemonic := "tzcnt", asm := "tzcntw %cx, %ax"
    , bytes := "66f30fbcc1", instr := ⟨.bitcnt .tzcnt .w .rax (R .rcx), 5⟩ }
  , { id := "tzcnt_rm_w", mnemonic := "tzcnt", asm := "tzcntw (%rbx), %ax"
    , bytes := "66f30fbc03", instr := ⟨.bitcnt .tzcnt .w .rax (M .rbx), 5⟩ }
  , { id := "tzcnt_rr_d", mnemonic := "tzcnt", asm := "tzcntl %ecx, %eax"
    , bytes := "f30fbcc1", instr := ⟨.bitcnt .tzcnt .d .rax (R .rcx), 4⟩ }
  , { id := "tzcnt_rm_d", mnemonic := "tzcnt", asm := "tzcntl (%rbx), %eax"
    , bytes := "f30fbc03", instr := ⟨.bitcnt .tzcnt .d .rax (M .rbx), 4⟩ }
  , { id := "tzcnt_rr_q", mnemonic := "tzcnt", asm := "tzcntq %rcx, %rax"
    , bytes := "f3480fbcc1", instr := ⟨.bitcnt .tzcnt .q .rax (R .rcx), 5⟩ }
  , { id := "tzcnt_rm_q", mnemonic := "tzcnt", asm := "tzcntq (%rbx), %rax"
    , bytes := "f3480fbc03", instr := ⟨.bitcnt .tzcnt .q .rax (M .rbx), 5⟩ }
  , { id := "bsf_rr_w", mnemonic := "bsf", asm := "bsfw %cx, %ax"
    , bytes := "660fbcc1", instr := ⟨.bitcnt .bsf .w .rax (R .rcx), 4⟩ }
  , { id := "bsf_rm_w", mnemonic := "bsf", asm := "bsfw (%rbx), %ax"
    , bytes := "660fbc03", instr := ⟨.bitcnt .bsf .w .rax (M .rbx), 4⟩ }
  , { id := "bsf_rr_d", mnemonic := "bsf", asm := "bsfl %ecx, %eax"
    , bytes := "0fbcc1", instr := ⟨.bitcnt .bsf .d .rax (R .rcx), 3⟩ }
  , { id := "bsf_rm_d", mnemonic := "bsf", asm := "bsfl (%rbx), %eax"
    , bytes := "0fbc03", instr := ⟨.bitcnt .bsf .d .rax (M .rbx), 3⟩ }
  , { id := "bsf_rr_q", mnemonic := "bsf", asm := "bsfq %rcx, %rax"
    , bytes := "480fbcc1", instr := ⟨.bitcnt .bsf .q .rax (R .rcx), 4⟩ }
  , { id := "bsf_rm_q", mnemonic := "bsf", asm := "bsfq (%rbx), %rax"
    , bytes := "480fbc03", instr := ⟨.bitcnt .bsf .q .rax (M .rbx), 4⟩ }
  , { id := "bsr_rr_w", mnemonic := "bsr", asm := "bsrw %cx, %ax"
    , bytes := "660fbdc1", instr := ⟨.bitcnt .bsr .w .rax (R .rcx), 4⟩ }
  , { id := "bsr_rm_w", mnemonic := "bsr", asm := "bsrw (%rbx), %ax"
    , bytes := "660fbd03", instr := ⟨.bitcnt .bsr .w .rax (M .rbx), 4⟩ }
  , { id := "bsr_rr_d", mnemonic := "bsr", asm := "bsrl %ecx, %eax"
    , bytes := "0fbdc1", instr := ⟨.bitcnt .bsr .d .rax (R .rcx), 3⟩ }
  , { id := "bsr_rm_d", mnemonic := "bsr", asm := "bsrl (%rbx), %eax"
    , bytes := "0fbd03", instr := ⟨.bitcnt .bsr .d .rax (M .rbx), 3⟩ }
  , { id := "bsr_rr_q", mnemonic := "bsr", asm := "bsrq %rcx, %rax"
    , bytes := "480fbdc1", instr := ⟨.bitcnt .bsr .q .rax (R .rcx), 4⟩ }
  , { id := "bsr_rm_q", mnemonic := "bsr", asm := "bsrq (%rbx), %rax"
    , bytes := "480fbd03", instr := ⟨.bitcnt .bsr .q .rax (M .rbx), 4⟩ }
  , { id := "blsi_rr_d", mnemonic := "blsi", asm := "blsil %ecx, %eax"
    , bytes := "c4e278f3d9", instr := ⟨.bitcnt .blsi .d .rax (R .rcx), 5⟩ }
  , { id := "blsi_rm_d", mnemonic := "blsi", asm := "blsil (%rbx), %eax"
    , bytes := "c4e278f31b", instr := ⟨.bitcnt .blsi .d .rax (M .rbx), 5⟩ }
  , { id := "blsi_rr_q", mnemonic := "blsi", asm := "blsiq %rcx, %rax"
    , bytes := "c4e2f8f3d9", instr := ⟨.bitcnt .blsi .q .rax (R .rcx), 5⟩ }
  , { id := "blsi_rm_q", mnemonic := "blsi", asm := "blsiq (%rbx), %rax"
    , bytes := "c4e2f8f31b", instr := ⟨.bitcnt .blsi .q .rax (M .rbx), 5⟩ }
  -- ⭐ P1 BATCH 15: the string group.  TWENTY VECTORS, FIVE MNEMONICS, FOUR
  -- WIDTHS, AND NOT ONE OPERAND BETWEEN THEM — the `asm` field is the bare
  -- mnemonic because that is the whole of the source form.
  --
  -- ⚠️ THE WIDTH IS CARRIED BY A PREFIX, NOT BY A ModR/M BYTE, and the four
  -- encodings of each form are the reason to spell all four out rather than
  -- trust a pattern: `l` is the BARE opcode, `w` is that opcode behind `66`,
  -- `q` is it behind `48`, and `b` is a DIFFERENT OPCODE (`a4` against `a5`).
  -- A table generated from "opcode plus width prefix" would have produced
  -- `66 a4` and `48 a4` for the byte forms, which no assembler emits.
  --
  -- ⛔ THESE ARE THE STRING MOVES, NOT THE SIGN-EXTENDING ONES.  `movsb` here
  -- assembles to `a4` and copies `[rsi]` to `[rdi]`; batch 10's `movsbl`
  -- assembles to `0f be` and sign-extends a byte into a register.  AT&T gives
  -- the two the same first six characters, and `scripts/check_encodings.py` is
  -- what makes the distinction a checked fact rather than a careful reading.
  , { id := "movs_b", mnemonic := "movs", asm := "movsb"
    , bytes := "a4", instr := ⟨.strop .movs .b, 1⟩ }
  , { id := "movs_w", mnemonic := "movs", asm := "movsw"
    , bytes := "66a5", instr := ⟨.strop .movs .w, 2⟩ }
  , { id := "movs_l", mnemonic := "movs", asm := "movsl"
    , bytes := "a5", instr := ⟨.strop .movs .d, 1⟩ }
  , { id := "movs_q", mnemonic := "movs", asm := "movsq"
    , bytes := "48a5", instr := ⟨.strop .movs .q, 2⟩ }
  , { id := "stos_b", mnemonic := "stos", asm := "stosb"
    , bytes := "aa", instr := ⟨.strop .stos .b, 1⟩ }
  , { id := "stos_w", mnemonic := "stos", asm := "stosw"
    , bytes := "66ab", instr := ⟨.strop .stos .w, 2⟩ }
  , { id := "stos_l", mnemonic := "stos", asm := "stosl"
    , bytes := "ab", instr := ⟨.strop .stos .d, 1⟩ }
  , { id := "stos_q", mnemonic := "stos", asm := "stosq"
    , bytes := "48ab", instr := ⟨.strop .stos .q, 2⟩ }
  , { id := "lods_b", mnemonic := "lods", asm := "lodsb"
    , bytes := "ac", instr := ⟨.strop .lods .b, 1⟩ }
  , { id := "lods_w", mnemonic := "lods", asm := "lodsw"
    , bytes := "66ad", instr := ⟨.strop .lods .w, 2⟩ }
  , { id := "lods_l", mnemonic := "lods", asm := "lodsl"
    , bytes := "ad", instr := ⟨.strop .lods .d, 1⟩ }
  , { id := "lods_q", mnemonic := "lods", asm := "lodsq"
    , bytes := "48ad", instr := ⟨.strop .lods .q, 2⟩ }
  , { id := "cmps_b", mnemonic := "cmps", asm := "cmpsb"
    , bytes := "a6", instr := ⟨.strop .cmps .b, 1⟩ }
  , { id := "cmps_w", mnemonic := "cmps", asm := "cmpsw"
    , bytes := "66a7", instr := ⟨.strop .cmps .w, 2⟩ }
  , { id := "cmps_l", mnemonic := "cmps", asm := "cmpsl"
    , bytes := "a7", instr := ⟨.strop .cmps .d, 1⟩ }
  , { id := "cmps_q", mnemonic := "cmps", asm := "cmpsq"
    , bytes := "48a7", instr := ⟨.strop .cmps .q, 2⟩ }
  , { id := "scas_b", mnemonic := "scas", asm := "scasb"
    , bytes := "ae", instr := ⟨.strop .scas .b, 1⟩ }
  , { id := "scas_w", mnemonic := "scas", asm := "scasw"
    , bytes := "66af", instr := ⟨.strop .scas .w, 2⟩ }
  , { id := "scas_l", mnemonic := "scas", asm := "scasl"
    , bytes := "af", instr := ⟨.strop .scas .d, 1⟩ }
  , { id := "scas_q", mnemonic := "scas", asm := "scasq"
    , bytes := "48af", instr := ⟨.strop .scas .q, 2⟩ }

  -- ⭐ P1 BATCH 16: THE ELEVEN `rep`-PREFIXED ROWS.  Twenty-eight vectors over
  -- three prefixes: `rep` on the three data movers, `repe` and `repne` on the
  -- two comparisons, each at all four widths.
  --
  -- ⚠️ THE PREFIX BYTE IS A PREFIX OF THE BYTES, and at width `w` it lands
  -- BEFORE the `66` operand-size prefix (`f3 66 a5`), not after it — the order
  -- clang emits and the only width where two prefixes meet.  Every one of these
  -- twenty-eight is checked against clang by `scripts/check_encodings.py`.
  --
  -- ⛔ `repz`/`repnz` HAVE NO VECTORS OF THEIR OWN AND MUST NOT: they assemble
  -- to bytes identical to `repe`/`repne` (`repSpellings`), so a vector apiece
  -- would be the same instruction differentially tested twice.
  --
  -- ⚠️ THE IDENTITY IS CHECKED AGAINST AN ASSEMBLER, NOT ASSERTED HERE — the
  -- `SYNONYMS` table of `scripts/check_encodings.py`.  A first draft of this
  -- comment cited a theorem "in Tests/Coverage.lean" that had not been written,
  -- which is verbatim the defect batch 11 left in `loopSpellings` and which
  -- `scripts/check_citations.py` caught in the same sweep.  The convention was
  -- copied together with its hole.  See docs/DECISIONS.md D48.
  , { id := "rep_movs_b", mnemonic := "rep", asm := "rep movsb"
    , bytes := "f3a4", instr := ⟨.repstrop .rep .movs .b, 2⟩ }
  , { id := "rep_movs_w", mnemonic := "rep", asm := "rep movsw"
    , bytes := "f366a5", instr := ⟨.repstrop .rep .movs .w, 3⟩ }
  , { id := "rep_movs_l", mnemonic := "rep", asm := "rep movsl"
    , bytes := "f3a5", instr := ⟨.repstrop .rep .movs .d, 2⟩ }
  , { id := "rep_movs_q", mnemonic := "rep", asm := "rep movsq"
    , bytes := "f348a5", instr := ⟨.repstrop .rep .movs .q, 3⟩ }
  , { id := "rep_stos_b", mnemonic := "rep", asm := "rep stosb"
    , bytes := "f3aa", instr := ⟨.repstrop .rep .stos .b, 2⟩ }
  , { id := "rep_stos_w", mnemonic := "rep", asm := "rep stosw"
    , bytes := "f366ab", instr := ⟨.repstrop .rep .stos .w, 3⟩ }
  , { id := "rep_stos_l", mnemonic := "rep", asm := "rep stosl"
    , bytes := "f3ab", instr := ⟨.repstrop .rep .stos .d, 2⟩ }
  , { id := "rep_stos_q", mnemonic := "rep", asm := "rep stosq"
    , bytes := "f348ab", instr := ⟨.repstrop .rep .stos .q, 3⟩ }
  , { id := "rep_lods_b", mnemonic := "rep", asm := "rep lodsb"
    , bytes := "f3ac", instr := ⟨.repstrop .rep .lods .b, 2⟩ }
  , { id := "rep_lods_w", mnemonic := "rep", asm := "rep lodsw"
    , bytes := "f366ad", instr := ⟨.repstrop .rep .lods .w, 3⟩ }
  , { id := "rep_lods_l", mnemonic := "rep", asm := "rep lodsl"
    , bytes := "f3ad", instr := ⟨.repstrop .rep .lods .d, 2⟩ }
  , { id := "rep_lods_q", mnemonic := "rep", asm := "rep lodsq"
    , bytes := "f348ad", instr := ⟨.repstrop .rep .lods .q, 3⟩ }
  , { id := "repe_cmps_b", mnemonic := "repe", asm := "repe cmpsb"
    , bytes := "f3a6", instr := ⟨.repstrop .repe .cmps .b, 2⟩ }
  , { id := "repe_cmps_w", mnemonic := "repe", asm := "repe cmpsw"
    , bytes := "f366a7", instr := ⟨.repstrop .repe .cmps .w, 3⟩ }
  , { id := "repe_cmps_l", mnemonic := "repe", asm := "repe cmpsl"
    , bytes := "f3a7", instr := ⟨.repstrop .repe .cmps .d, 2⟩ }
  , { id := "repe_cmps_q", mnemonic := "repe", asm := "repe cmpsq"
    , bytes := "f348a7", instr := ⟨.repstrop .repe .cmps .q, 3⟩ }
  , { id := "repe_scas_b", mnemonic := "repe", asm := "repe scasb"
    , bytes := "f3ae", instr := ⟨.repstrop .repe .scas .b, 2⟩ }
  , { id := "repe_scas_w", mnemonic := "repe", asm := "repe scasw"
    , bytes := "f366af", instr := ⟨.repstrop .repe .scas .w, 3⟩ }
  , { id := "repe_scas_l", mnemonic := "repe", asm := "repe scasl"
    , bytes := "f3af", instr := ⟨.repstrop .repe .scas .d, 2⟩ }
  , { id := "repe_scas_q", mnemonic := "repe", asm := "repe scasq"
    , bytes := "f348af", instr := ⟨.repstrop .repe .scas .q, 3⟩ }
  , { id := "repne_cmps_b", mnemonic := "repne", asm := "repne cmpsb"
    , bytes := "f2a6", instr := ⟨.repstrop .repn .cmps .b, 2⟩ }
  , { id := "repne_cmps_w", mnemonic := "repne", asm := "repne cmpsw"
    , bytes := "f266a7", instr := ⟨.repstrop .repn .cmps .w, 3⟩ }
  , { id := "repne_cmps_l", mnemonic := "repne", asm := "repne cmpsl"
    , bytes := "f2a7", instr := ⟨.repstrop .repn .cmps .d, 2⟩ }
  , { id := "repne_cmps_q", mnemonic := "repne", asm := "repne cmpsq"
    , bytes := "f248a7", instr := ⟨.repstrop .repn .cmps .q, 3⟩ }
  , { id := "repne_scas_b", mnemonic := "repne", asm := "repne scasb"
    , bytes := "f2ae", instr := ⟨.repstrop .repn .scas .b, 2⟩ }
  , { id := "repne_scas_w", mnemonic := "repne", asm := "repne scasw"
    , bytes := "f266af", instr := ⟨.repstrop .repn .scas .w, 3⟩ }
  , { id := "repne_scas_l", mnemonic := "repne", asm := "repne scasl"
    , bytes := "f2af", instr := ⟨.repstrop .repn .scas .d, 2⟩ }
  , { id := "repne_scas_q", mnemonic := "repne", asm := "repne scasq"
    , bytes := "f248af", instr := ⟨.repstrop .repn .scas .q, 3⟩ }
  -- ⭐⭐ P1 BATCH 17 — THE MULTIPLY-DIVIDE GROUP.  Thirty-two vectors over four
  -- mnemonics and two constructors, and the first vectors in this table for
  -- which a REFUSAL is the expected answer at most pre-states: measured on the
  -- oracle before any of them existed, `div` and `idiv` fault in 51%–84% of the
  -- eighty-two, depending on width and signedness.
  --
  -- ⚠️ THE MEMORY FORMS ARE AT `.b` AND `.q`, NOT ONE WIDTH, and the choice is
  -- structural rather than generous: `.b` is the width at which the destination
  -- pair is `AH:AL` — one register — and every other width puts the high half
  -- in RDX.  A memory-source vector at `.q` alone would leave the byte pair's
  -- write path tested only through register sources.  ⚠️ `imul`'s two- and
  -- three-operand forms have NO `.b` encoding at all, so their memory vector is
  -- `.q` and the shapes column says so.
  --
  -- ⭐ `imul3_q`'s IMMEDIATE IS NEGATIVE, alone in this table.  `69`/`6B` carry
  -- an imm32 that the decoder SIGN-EXTENDS to the operand width, so a positive
  -- immediate cannot tell a sign-extending decoder from a zero-extending one at
  -- `.q`.  `$-0x12345678` assembles to `88 a9 cb ed` and the AST carries
  -- `0xFFFFFFFFEDCBA988` — the extension already done, as this AST's `imm`
  -- always is.
  , { id := "mul_b", mnemonic := "mul", asm := "mulb %cl"
    , bytes := "f6e1", instr := ⟨.muldiv .mul .b (R .rcx), 2⟩ }
  , { id := "mul_w", mnemonic := "mul", asm := "mulw %cx"
    , bytes := "66f7e1", instr := ⟨.muldiv .mul .w (R .rcx), 3⟩ }
  , { id := "mul_l", mnemonic := "mul", asm := "mull %ecx"
    , bytes := "f7e1", instr := ⟨.muldiv .mul .d (R .rcx), 2⟩ }
  , { id := "mul_q", mnemonic := "mul", asm := "mulq %rcx"
    , bytes := "48f7e1", instr := ⟨.muldiv .mul .q (R .rcx), 3⟩ }
  , { id := "mul_mb", mnemonic := "mul", asm := "mulb (%rbx)"
    , bytes := "f623", instr := ⟨.muldiv .mul .b (M .rbx), 2⟩ }
  , { id := "mul_mq", mnemonic := "mul", asm := "mulq (%rbx)"
    , bytes := "48f723", instr := ⟨.muldiv .mul .q (M .rbx), 3⟩ }
  , { id := "imul1_b", mnemonic := "imul", asm := "imulb %cl"
    , bytes := "f6e9", instr := ⟨.muldiv .imul .b (R .rcx), 2⟩ }
  , { id := "imul1_w", mnemonic := "imul", asm := "imulw %cx"
    , bytes := "66f7e9", instr := ⟨.muldiv .imul .w (R .rcx), 3⟩ }
  , { id := "imul1_l", mnemonic := "imul", asm := "imull %ecx"
    , bytes := "f7e9", instr := ⟨.muldiv .imul .d (R .rcx), 2⟩ }
  , { id := "imul1_q", mnemonic := "imul", asm := "imulq %rcx"
    , bytes := "48f7e9", instr := ⟨.muldiv .imul .q (R .rcx), 3⟩ }
  , { id := "imul1_mb", mnemonic := "imul", asm := "imulb (%rbx)"
    , bytes := "f62b", instr := ⟨.muldiv .imul .b (M .rbx), 2⟩ }
  , { id := "imul1_mq", mnemonic := "imul", asm := "imulq (%rbx)"
    , bytes := "48f72b", instr := ⟨.muldiv .imul .q (M .rbx), 3⟩ }
  , { id := "imul2_w", mnemonic := "imul", asm := "imulw %cx, %ax"
    , bytes := "660fafc1", instr := ⟨.imulr .w .rax (R .rcx) none, 4⟩ }
  , { id := "imul2_l", mnemonic := "imul", asm := "imull %ecx, %eax"
    , bytes := "0fafc1", instr := ⟨.imulr .d .rax (R .rcx) none, 3⟩ }
  , { id := "imul2_q", mnemonic := "imul", asm := "imulq %rcx, %rax"
    , bytes := "480fafc1", instr := ⟨.imulr .q .rax (R .rcx) none, 4⟩ }
  , { id := "imul2_mq", mnemonic := "imul", asm := "imulq (%rbx), %rax"
    , bytes := "480faf03", instr := ⟨.imulr .q .rax (M .rbx) none, 4⟩ }
  , { id := "imul3_w", mnemonic := "imul", asm := "imulw $0x1234, %cx, %ax"
    , bytes := "6669c13412", instr := ⟨.imulr .w .rax (R .rcx) (some 0x1234), 5⟩ }
  , { id := "imul3_l", mnemonic := "imul", asm := "imull $0x12345678, %ecx, %eax"
    , bytes := "69c178563412", instr := ⟨.imulr .d .rax (R .rcx) (some 0x12345678), 6⟩ }
  , { id := "imul3_q", mnemonic := "imul", asm := "imulq $-0x12345678, %rcx, %rax"
    , bytes := "4869c188a9cbed", instr := ⟨.imulr .q .rax (R .rcx) (some 0xFFFFFFFFEDCBA988), 7⟩ }
  , { id := "imul3_mq", mnemonic := "imul", asm := "imulq $0x12345678, (%rbx), %rax"
    , bytes := "48690378563412", instr := ⟨.imulr .q .rax (M .rbx) (some 0x12345678), 7⟩ }
  , { id := "div_b", mnemonic := "div", asm := "divb %cl"
    , bytes := "f6f1", instr := ⟨.muldiv .div .b (R .rcx), 2⟩ }
  , { id := "div_w", mnemonic := "div", asm := "divw %cx"
    , bytes := "66f7f1", instr := ⟨.muldiv .div .w (R .rcx), 3⟩ }
  , { id := "div_l", mnemonic := "div", asm := "divl %ecx"
    , bytes := "f7f1", instr := ⟨.muldiv .div .d (R .rcx), 2⟩ }
  , { id := "div_q", mnemonic := "div", asm := "divq %rcx"
    , bytes := "48f7f1", instr := ⟨.muldiv .div .q (R .rcx), 3⟩ }
  , { id := "div_mb", mnemonic := "div", asm := "divb (%rbx)"
    , bytes := "f633", instr := ⟨.muldiv .div .b (M .rbx), 2⟩ }
  , { id := "div_mq", mnemonic := "div", asm := "divq (%rbx)"
    , bytes := "48f733", instr := ⟨.muldiv .div .q (M .rbx), 3⟩ }
  , { id := "idiv_b", mnemonic := "idiv", asm := "idivb %cl"
    , bytes := "f6f9", instr := ⟨.muldiv .idiv .b (R .rcx), 2⟩ }
  , { id := "idiv_w", mnemonic := "idiv", asm := "idivw %cx"
    , bytes := "66f7f9", instr := ⟨.muldiv .idiv .w (R .rcx), 3⟩ }
  , { id := "idiv_l", mnemonic := "idiv", asm := "idivl %ecx"
    , bytes := "f7f9", instr := ⟨.muldiv .idiv .d (R .rcx), 2⟩ }
  , { id := "idiv_q", mnemonic := "idiv", asm := "idivq %rcx"
    , bytes := "48f7f9", instr := ⟨.muldiv .idiv .q (R .rcx), 3⟩ }
  , { id := "idiv_mb", mnemonic := "idiv", asm := "idivb (%rbx)"
    , bytes := "f63b", instr := ⟨.muldiv .idiv .b (M .rbx), 2⟩ }
  , { id := "idiv_mq", mnemonic := "idiv", asm := "idivq (%rbx)"
    , bytes := "48f73b", instr := ⟨.muldiv .idiv .q (M .rbx), 3⟩ }
  -- ⭐⭐ P1 BATCH 18 — THE COMPARE-EXCHANGE PAIR AND THE DOUBLE SHIFTS.  Forty-one
  -- vectors over four mnemonics and three constructors.
  --
  -- ⛔ `cmpxchg`'s DESTINATION IS NEVER RAX, AND THAT IS THE WHOLE DESIGN OF
  -- THESE SEVEN.  The accumulator is not an operand: `cmpxchg` compares
  -- AL/AX/EAX/RAX with the destination, so `cmpxchg %rdx, %rax` compares RAX
  -- with itself, ZF is 1 in every pre-state, and the branch that writes the
  -- accumulator is UNREACHABLE.  With RCX and `(%rbx)` as destinations the split
  -- is real and was MEASURED on the oracle before a vector existed: 22 to 27 of
  -- the eighty-two take the equal branch, 55 to 60 the unequal, depending on
  -- width.  `mkPre`'s diagonal is where the two values meet.
  --
  -- ⚠️ THE DOUBLE SHIFTS TAKE THEIR SOURCE FROM RDX AND NOT FROM RCX, alone in
  -- this table among the register-destination forms.  The count is CL — the low
  -- byte of RCX — so a source in RCX would put the count INSIDE the source
  -- operand at `.w`, where CX and CL overlap, and a model that read the source
  -- at the wrong width would be shielded by the coincidence.  RDX carries
  -- `~~~a`, so the bits shifted in are the complement of the bits shifted out
  -- and any confusion between the two operands is loud.
  --
  -- ⭐ THE FIVE IMMEDIATES ARE FIVE DIFFERENT BRANCHES, not five samples of one.
  -- `$5` is the ordinary case; `$1` is the ONE count at which OF is defined
  -- rather than drawn from the oracle; `$0` is the branch that does nothing at
  -- all and touches no flag; `$16` at `.w` is the exact boundary, where the
  -- count equals the operand size and the answer is the SOURCE; and `$20` at
  -- `.w` is past it, where the SDM leaves the destination and all six flags
  -- undefined.
  --
  -- ⚠️ `shld_ri20_w` TESTS NO ARITHMETIC AND IS HERE ANYWAY.  Its destination is
  -- undefined in all eighty-two pre-states, so the comparator explains every
  -- disagreement in RAX and no wrong shift could ever be caught by it.  What it
  -- does test is the DECLARATION: `undefinedLeaked` demands that the registers
  -- the model declares undefined are exactly the registers that move between the
  -- two opposite oracle runs, in both directions, so this vector is the one that
  -- fails if the declaration is missing AND the one that fails if it is invented.
  -- The `_cl_w` vectors reach the same branch in 35 of 82 and the defined branch
  -- in 24, which is where the shift itself is observed.
  --
  -- ⛔ THERE IS NO `m,cl` VECTOR AT `.w`, AND THE MODEL REFUSES THAT COMBINATION
  -- RATHER THAN ANSWERING IT.  A 16-bit memory destination with a count above 16
  -- would put an oracle-drawn value into MEMORY, which `undefinedLeaked` has no
  -- declaration channel for and the comparator's `undefinableFields` is a closed
  -- list against.  Refusing is why this table has no vector there: the oracle
  -- COMPUTES that case, so a vector would be a refusal disagreement rather than
  -- a test.  See `dshiftMemUndefined` and docs/DECISIONS.md D52.
  , { id := "cmpxchg_r_b", mnemonic := "cmpxchg", asm := "cmpxchgb %dl, %cl"
    , bytes := "0fb0d1", instr := ⟨.cmpxchg .b (R .rcx) .rdx, 3⟩ }
  , { id := "cmpxchg_r_w", mnemonic := "cmpxchg", asm := "cmpxchgw %dx, %cx"
    , bytes := "660fb1d1", instr := ⟨.cmpxchg .w (R .rcx) .rdx, 4⟩ }
  , { id := "cmpxchg_r_l", mnemonic := "cmpxchg", asm := "cmpxchgl %edx, %ecx"
    , bytes := "0fb1d1", instr := ⟨.cmpxchg .d (R .rcx) .rdx, 3⟩ }
  , { id := "cmpxchg_r_q", mnemonic := "cmpxchg", asm := "cmpxchgq %rdx, %rcx"
    , bytes := "480fb1d1", instr := ⟨.cmpxchg .q (R .rcx) .rdx, 4⟩ }
  , { id := "cmpxchg_m_b", mnemonic := "cmpxchg", asm := "cmpxchgb %dl, (%rbx)"
    , bytes := "0fb013", instr := ⟨.cmpxchg .b (M .rbx) .rdx, 3⟩ }
  , { id := "cmpxchg_m_l", mnemonic := "cmpxchg", asm := "cmpxchgl %edx, (%rbx)"
    , bytes := "0fb113", instr := ⟨.cmpxchg .d (M .rbx) .rdx, 3⟩ }
  , { id := "cmpxchg_m_q", mnemonic := "cmpxchg", asm := "cmpxchgq %rdx, (%rbx)"
    , bytes := "480fb113", instr := ⟨.cmpxchg .q (M .rbx) .rdx, 4⟩ }
  , { id := "xadd_r_b", mnemonic := "xadd", asm := "xaddb %cl, %al"
    , bytes := "0fc0c8", instr := ⟨.xadd .b (R .rax) .rcx, 3⟩ }
  , { id := "xadd_r_w", mnemonic := "xadd", asm := "xaddw %cx, %ax"
    , bytes := "660fc1c8", instr := ⟨.xadd .w (R .rax) .rcx, 4⟩ }
  , { id := "xadd_r_l", mnemonic := "xadd", asm := "xaddl %ecx, %eax"
    , bytes := "0fc1c8", instr := ⟨.xadd .d (R .rax) .rcx, 3⟩ }
  , { id := "xadd_r_q", mnemonic := "xadd", asm := "xaddq %rcx, %rax"
    , bytes := "480fc1c8", instr := ⟨.xadd .q (R .rax) .rcx, 4⟩ }
  , { id := "xadd_m_b", mnemonic := "xadd", asm := "xaddb %al, (%rbx)"
    , bytes := "0fc003", instr := ⟨.xadd .b (M .rbx) .rax, 3⟩ }
  , { id := "xadd_m_l", mnemonic := "xadd", asm := "xaddl %eax, (%rbx)"
    , bytes := "0fc103", instr := ⟨.xadd .d (M .rbx) .rax, 3⟩ }
  , { id := "xadd_m_q", mnemonic := "xadd", asm := "xaddq %rax, (%rbx)"
    , bytes := "480fc103", instr := ⟨.xadd .q (M .rbx) .rax, 4⟩ }
  , { id := "shld_r_cl_w", mnemonic := "shld", asm := "shldw %cl, %dx, %ax"
    , bytes := "660fa5d0", instr := ⟨.dshift .shld .w (R .rax) .rdx .cl, 4⟩ }
  , { id := "shld_r_cl_l", mnemonic := "shld", asm := "shldl %cl, %edx, %eax"
    , bytes := "0fa5d0", instr := ⟨.dshift .shld .d (R .rax) .rdx .cl, 3⟩ }
  , { id := "shld_r_cl_q", mnemonic := "shld", asm := "shldq %cl, %rdx, %rax"
    , bytes := "480fa5d0", instr := ⟨.dshift .shld .q (R .rax) .rdx .cl, 4⟩ }
  , { id := "shrd_r_cl_w", mnemonic := "shrd", asm := "shrdw %cl, %dx, %ax"
    , bytes := "660fadd0", instr := ⟨.dshift .shrd .w (R .rax) .rdx .cl, 4⟩ }
  , { id := "shrd_r_cl_l", mnemonic := "shrd", asm := "shrdl %cl, %edx, %eax"
    , bytes := "0fadd0", instr := ⟨.dshift .shrd .d (R .rax) .rdx .cl, 3⟩ }
  , { id := "shrd_r_cl_q", mnemonic := "shrd", asm := "shrdq %cl, %rdx, %rax"
    , bytes := "480fadd0", instr := ⟨.dshift .shrd .q (R .rax) .rdx .cl, 4⟩ }
  , { id := "shld_ri5_w", mnemonic := "shld", asm := "shldw $5, %dx, %ax"
    , bytes := "660fa4d005", instr := ⟨.dshift .shld .w (R .rax) .rdx (.imm8 5), 5⟩ }
  , { id := "shld_ri5_l", mnemonic := "shld", asm := "shldl $5, %edx, %eax"
    , bytes := "0fa4d005", instr := ⟨.dshift .shld .d (R .rax) .rdx (.imm8 5), 4⟩ }
  , { id := "shld_ri5_q", mnemonic := "shld", asm := "shldq $5, %rdx, %rax"
    , bytes := "480fa4d005", instr := ⟨.dshift .shld .q (R .rax) .rdx (.imm8 5), 5⟩ }
  , { id := "shrd_ri5_w", mnemonic := "shrd", asm := "shrdw $5, %dx, %ax"
    , bytes := "660facd005", instr := ⟨.dshift .shrd .w (R .rax) .rdx (.imm8 5), 5⟩ }
  , { id := "shrd_ri5_l", mnemonic := "shrd", asm := "shrdl $5, %edx, %eax"
    , bytes := "0facd005", instr := ⟨.dshift .shrd .d (R .rax) .rdx (.imm8 5), 4⟩ }
  , { id := "shrd_ri5_q", mnemonic := "shrd", asm := "shrdq $5, %rdx, %rax"
    , bytes := "480facd005", instr := ⟨.dshift .shrd .q (R .rax) .rdx (.imm8 5), 5⟩ }
  , { id := "shld_ri1_l", mnemonic := "shld", asm := "shldl $1, %edx, %eax"
    , bytes := "0fa4d001", instr := ⟨.dshift .shld .d (R .rax) .rdx (.imm8 1), 4⟩ }
  , { id := "shrd_ri1_l", mnemonic := "shrd", asm := "shrdl $1, %edx, %eax"
    , bytes := "0facd001", instr := ⟨.dshift .shrd .d (R .rax) .rdx (.imm8 1), 4⟩ }
  , { id := "shld_ri0_l", mnemonic := "shld", asm := "shldl $0, %edx, %eax"
    , bytes := "0fa4d000", instr := ⟨.dshift .shld .d (R .rax) .rdx (.imm8 0), 4⟩ }
  , { id := "shld_ri16_w", mnemonic := "shld", asm := "shldw $16, %dx, %ax"
    , bytes := "660fa4d010", instr := ⟨.dshift .shld .w (R .rax) .rdx (.imm8 16), 5⟩ }
  , { id := "shld_ri20_w", mnemonic := "shld", asm := "shldw $20, %dx, %ax"
    , bytes := "660fa4d014", instr := ⟨.dshift .shld .w (R .rax) .rdx (.imm8 20), 5⟩ }
  , { id := "shld_mi5_w", mnemonic := "shld", asm := "shldw $5, %ax, (%rbx)"
    , bytes := "660fa40305", instr := ⟨.dshift .shld .w (M .rbx) .rax (.imm8 5), 5⟩ }
  , { id := "shld_mi5_l", mnemonic := "shld", asm := "shldl $5, %eax, (%rbx)"
    , bytes := "0fa40305", instr := ⟨.dshift .shld .d (M .rbx) .rax (.imm8 5), 4⟩ }
  , { id := "shld_mi5_q", mnemonic := "shld", asm := "shldq $5, %rax, (%rbx)"
    , bytes := "480fa40305", instr := ⟨.dshift .shld .q (M .rbx) .rax (.imm8 5), 5⟩ }
  , { id := "shrd_mi5_w", mnemonic := "shrd", asm := "shrdw $5, %ax, (%rbx)"
    , bytes := "660fac0305", instr := ⟨.dshift .shrd .w (M .rbx) .rax (.imm8 5), 5⟩ }
  , { id := "shrd_mi5_l", mnemonic := "shrd", asm := "shrdl $5, %eax, (%rbx)"
    , bytes := "0fac0305", instr := ⟨.dshift .shrd .d (M .rbx) .rax (.imm8 5), 4⟩ }
  , { id := "shrd_mi5_q", mnemonic := "shrd", asm := "shrdq $5, %rax, (%rbx)"
    , bytes := "480fac0305", instr := ⟨.dshift .shrd .q (M .rbx) .rax (.imm8 5), 5⟩ }
  , { id := "shld_m_cl_l", mnemonic := "shld", asm := "shldl %cl, %eax, (%rbx)"
    , bytes := "0fa503", instr := ⟨.dshift .shld .d (M .rbx) .rax .cl, 3⟩ }
  , { id := "shld_m_cl_q", mnemonic := "shld", asm := "shldq %cl, %rax, (%rbx)"
    , bytes := "480fa503", instr := ⟨.dshift .shld .q (M .rbx) .rax .cl, 4⟩ }
  , { id := "shrd_m_cl_l", mnemonic := "shrd", asm := "shrdl %cl, %eax, (%rbx)"
    , bytes := "0fad03", instr := ⟨.dshift .shrd .d (M .rbx) .rax .cl, 3⟩ }
  , { id := "shrd_m_cl_q", mnemonic := "shrd", asm := "shrdq %cl, %rax, (%rbx)"
    , bytes := "480fad03", instr := ⟨.dshift .shrd .q (M .rbx) .rax .cl, 4⟩ }
  -- ══ P1 BATCH 20 ═══════════════════════════════════════════════════════
  -- THE SHAPES THIS MODEL COULD ALWAYS EXPRESS AND HAD NEVER BEEN ASKED.
  --
  -- ⭐ NOT ONE LINE OF `X86/Semantics.lean` CHANGES FOR THE SEVENTY-ONE
  -- VECTORS BELOW.  `Op` is keyed by mnemonic with a SHARED operand pair
  -- (X86/Syntax.lean's header: "20 mnemonics x 4 shapes would be 80
  -- constructors"), so `add` at a memory destination, `sub` against an
  -- immediate and `push` of a memory operand were all expressible from P0
  -- onward.  What was missing was the EVIDENCE, and a shape that is
  -- expressible and untested is a claim nobody made and nobody checked.
  --
  -- ⚠️ THAT IS PRECISELY WHY THE BATCH IS WORTH RUNNING RATHER THAN
  -- ASSUMING.  A generic constructor makes a whole family compile; it does
  -- not make the family right.  Batch 4's memory-DESTINATION work was
  -- exactly this discovery for `and`/`or`/`xor`, and it found real defects
  -- in code that already type-checked.
  --
  -- WHAT SWEEPS, AND AGAINST WHAT.  The memory operand at RBX carries `c`
  -- and RAX carries `a` (see `mkPre`), so `addq %rax, (%rbx)` computes
  -- `a + c` and moves in both arguments -- D14's rule, which is why the
  -- register operand here is the accumulator and not RCX (RCX carries `c`
  -- too, and `c + c` is one test reported as eighty-two).
  --
  -- ⛔ THE THREE ROWS THIS BATCH DOES NOT TAKE, EACH FOR A MEASURED REASON:
  -- `movnti` (the oracle does not implement it -- 82/82 refused, against an
  -- identical-shape control that executed 82/82), the four `bt*` bit-string
  -- forms (D23) and the two `xchg` memory forms (D25).  See
  -- docs/DIFFERENTIAL-P1-BATCH20.md.
  , { id := "add_mi_b", mnemonic := "add", asm := "addb $0x5a, (%rbx)"
    , bytes := "80035a", instr := ⟨.bin .add .b (M .rbx) (.imm 0x5a), 3⟩ }
  , { id := "add_mr_b", mnemonic := "add", asm := "addb %al, (%rbx)"
    , bytes := "0003", instr := ⟨.bin .add .b (M .rbx) (R .rax), 2⟩ }
  , { id := "add_mi_w", mnemonic := "add", asm := "addw $0x1234, (%rbx)"
    , bytes := "6681033412", instr := ⟨.bin .add .w (M .rbx) (.imm 0x1234), 5⟩ }
  , { id := "add_mr_w", mnemonic := "add", asm := "addw %ax, (%rbx)"
    , bytes := "660103", instr := ⟨.bin .add .w (M .rbx) (R .rax), 3⟩ }
  , { id := "add_mi_l", mnemonic := "add", asm := "addl $0x12345678, (%rbx)"
    , bytes := "810378563412", instr := ⟨.bin .add .d (M .rbx) (.imm 0x12345678), 6⟩ }
  , { id := "add_mr_l", mnemonic := "add", asm := "addl %eax, (%rbx)"
    , bytes := "0103", instr := ⟨.bin .add .d (M .rbx) (R .rax), 2⟩ }
  , { id := "add_mi_q", mnemonic := "add", asm := "addq $0x12345678, (%rbx)"
    , bytes := "48810378563412", instr := ⟨.bin .add .q (M .rbx) (.imm 0x12345678), 7⟩ }
  , { id := "add_mr_q", mnemonic := "add", asm := "addq %rax, (%rbx)"
    , bytes := "480103", instr := ⟨.bin .add .q (M .rbx) (R .rax), 3⟩ }
  , { id := "sub_mi_b", mnemonic := "sub", asm := "subb $0x5a, (%rbx)"
    , bytes := "802b5a", instr := ⟨.bin .sub .b (M .rbx) (.imm 0x5a), 3⟩ }
  , { id := "sub_mr_b", mnemonic := "sub", asm := "subb %al, (%rbx)"
    , bytes := "2803", instr := ⟨.bin .sub .b (M .rbx) (R .rax), 2⟩ }
  , { id := "sub_mi_w", mnemonic := "sub", asm := "subw $0x1234, (%rbx)"
    , bytes := "66812b3412", instr := ⟨.bin .sub .w (M .rbx) (.imm 0x1234), 5⟩ }
  , { id := "sub_mr_w", mnemonic := "sub", asm := "subw %ax, (%rbx)"
    , bytes := "662903", instr := ⟨.bin .sub .w (M .rbx) (R .rax), 3⟩ }
  , { id := "sub_mi_l", mnemonic := "sub", asm := "subl $0x12345678, (%rbx)"
    , bytes := "812b78563412", instr := ⟨.bin .sub .d (M .rbx) (.imm 0x12345678), 6⟩ }
  , { id := "sub_mr_l", mnemonic := "sub", asm := "subl %eax, (%rbx)"
    , bytes := "2903", instr := ⟨.bin .sub .d (M .rbx) (R .rax), 2⟩ }
  , { id := "sub_mi_q", mnemonic := "sub", asm := "subq $0x12345678, (%rbx)"
    , bytes := "48812b78563412", instr := ⟨.bin .sub .q (M .rbx) (.imm 0x12345678), 7⟩ }
  , { id := "sub_mr_q", mnemonic := "sub", asm := "subq %rax, (%rbx)"
    , bytes := "482903", instr := ⟨.bin .sub .q (M .rbx) (R .rax), 3⟩ }
  , { id := "adc_mi_b", mnemonic := "adc", asm := "adcb $0x5a, (%rbx)"
    , bytes := "80135a", instr := ⟨.bin .adc .b (M .rbx) (.imm 0x5a), 3⟩ }
  , { id := "adc_mr_b", mnemonic := "adc", asm := "adcb %al, (%rbx)"
    , bytes := "1003", instr := ⟨.bin .adc .b (M .rbx) (R .rax), 2⟩ }
  , { id := "adc_mi_w", mnemonic := "adc", asm := "adcw $0x1234, (%rbx)"
    , bytes := "6681133412", instr := ⟨.bin .adc .w (M .rbx) (.imm 0x1234), 5⟩ }
  , { id := "adc_mr_w", mnemonic := "adc", asm := "adcw %ax, (%rbx)"
    , bytes := "661103", instr := ⟨.bin .adc .w (M .rbx) (R .rax), 3⟩ }
  , { id := "adc_mi_l", mnemonic := "adc", asm := "adcl $0x12345678, (%rbx)"
    , bytes := "811378563412", instr := ⟨.bin .adc .d (M .rbx) (.imm 0x12345678), 6⟩ }
  , { id := "adc_mr_l", mnemonic := "adc", asm := "adcl %eax, (%rbx)"
    , bytes := "1103", instr := ⟨.bin .adc .d (M .rbx) (R .rax), 2⟩ }
  , { id := "adc_mi_q", mnemonic := "adc", asm := "adcq $0x12345678, (%rbx)"
    , bytes := "48811378563412", instr := ⟨.bin .adc .q (M .rbx) (.imm 0x12345678), 7⟩ }
  , { id := "adc_mr_q", mnemonic := "adc", asm := "adcq %rax, (%rbx)"
    , bytes := "481103", instr := ⟨.bin .adc .q (M .rbx) (R .rax), 3⟩ }
  , { id := "sbb_mi_b", mnemonic := "sbb", asm := "sbbb $0x5a, (%rbx)"
    , bytes := "801b5a", instr := ⟨.bin .sbb .b (M .rbx) (.imm 0x5a), 3⟩ }
  , { id := "sbb_mr_b", mnemonic := "sbb", asm := "sbbb %al, (%rbx)"
    , bytes := "1803", instr := ⟨.bin .sbb .b (M .rbx) (R .rax), 2⟩ }
  , { id := "sbb_mi_w", mnemonic := "sbb", asm := "sbbw $0x1234, (%rbx)"
    , bytes := "66811b3412", instr := ⟨.bin .sbb .w (M .rbx) (.imm 0x1234), 5⟩ }
  , { id := "sbb_mr_w", mnemonic := "sbb", asm := "sbbw %ax, (%rbx)"
    , bytes := "661903", instr := ⟨.bin .sbb .w (M .rbx) (R .rax), 3⟩ }
  , { id := "sbb_mi_l", mnemonic := "sbb", asm := "sbbl $0x12345678, (%rbx)"
    , bytes := "811b78563412", instr := ⟨.bin .sbb .d (M .rbx) (.imm 0x12345678), 6⟩ }
  , { id := "sbb_mr_l", mnemonic := "sbb", asm := "sbbl %eax, (%rbx)"
    , bytes := "1903", instr := ⟨.bin .sbb .d (M .rbx) (R .rax), 2⟩ }
  , { id := "sbb_mi_q", mnemonic := "sbb", asm := "sbbq $0x12345678, (%rbx)"
    , bytes := "48811b78563412", instr := ⟨.bin .sbb .q (M .rbx) (.imm 0x12345678), 7⟩ }
  , { id := "sbb_mr_q", mnemonic := "sbb", asm := "sbbq %rax, (%rbx)"
    , bytes := "481903", instr := ⟨.bin .sbb .q (M .rbx) (R .rax), 3⟩ }
  , { id := "add_rm_b", mnemonic := "add", asm := "addb (%rbx), %al"
    , bytes := "0203", instr := ⟨.bin .add .b (R .rax) (M .rbx), 2⟩ }
  , { id := "add_rm_w", mnemonic := "add", asm := "addw (%rbx), %ax"
    , bytes := "660303", instr := ⟨.bin .add .w (R .rax) (M .rbx), 3⟩ }
  , { id := "add_rm_l", mnemonic := "add", asm := "addl (%rbx), %eax"
    , bytes := "0303", instr := ⟨.bin .add .d (R .rax) (M .rbx), 2⟩ }
  , { id := "add_rm_q", mnemonic := "add", asm := "addq (%rbx), %rax"
    , bytes := "480303", instr := ⟨.bin .add .q (R .rax) (M .rbx), 3⟩ }
  , { id := "sub_rm_b", mnemonic := "sub", asm := "subb (%rbx), %al"
    , bytes := "2a03", instr := ⟨.bin .sub .b (R .rax) (M .rbx), 2⟩ }
  , { id := "sub_rm_w", mnemonic := "sub", asm := "subw (%rbx), %ax"
    , bytes := "662b03", instr := ⟨.bin .sub .w (R .rax) (M .rbx), 3⟩ }
  , { id := "sub_rm_l", mnemonic := "sub", asm := "subl (%rbx), %eax"
    , bytes := "2b03", instr := ⟨.bin .sub .d (R .rax) (M .rbx), 2⟩ }
  , { id := "sub_rm_q", mnemonic := "sub", asm := "subq (%rbx), %rax"
    , bytes := "482b03", instr := ⟨.bin .sub .q (R .rax) (M .rbx), 3⟩ }
  , { id := "sub_ri_b", mnemonic := "sub", asm := "subb $0x5a, %cl"
    , bytes := "80e95a", instr := ⟨.bin .sub .b (R .rcx) (.imm 0x5a), 3⟩ }
  , { id := "sub_ri_w", mnemonic := "sub", asm := "subw $0x1234, %cx"
    , bytes := "6681e93412", instr := ⟨.bin .sub .w (R .rcx) (.imm 0x1234), 5⟩ }
  , { id := "sub_ri_l", mnemonic := "sub", asm := "subl $0x12345678, %ecx"
    , bytes := "81e978563412", instr := ⟨.bin .sub .d (R .rcx) (.imm 0x12345678), 6⟩ }
  , { id := "sub_ri_q", mnemonic := "sub", asm := "subq $0x12345678, %rcx"
    , bytes := "4881e978563412", instr := ⟨.bin .sub .q (R .rcx) (.imm 0x12345678), 7⟩ }
  , { id := "add_acc_b", mnemonic := "add", asm := "addb $0x5a, %al"
    , bytes := "045a", instr := ⟨.bin .add .b (R .rax) (.imm 0x5a), 2⟩ }
  , { id := "add_acc_w", mnemonic := "add", asm := "addw $0x1234, %ax"
    , bytes := "66053412", instr := ⟨.bin .add .w (R .rax) (.imm 0x1234), 4⟩ }
  , { id := "add_acc_l", mnemonic := "add", asm := "addl $0x12345678, %eax"
    , bytes := "0578563412", instr := ⟨.bin .add .d (R .rax) (.imm 0x12345678), 5⟩ }
  , { id := "add_acc_q", mnemonic := "add", asm := "addq $0x12345678, %rax"
    , bytes := "480578563412", instr := ⟨.bin .add .q (R .rax) (.imm 0x12345678), 6⟩ }
  , { id := "sub_acc_b", mnemonic := "sub", asm := "subb $0x5a, %al"
    , bytes := "2c5a", instr := ⟨.bin .sub .b (R .rax) (.imm 0x5a), 2⟩ }
  , { id := "sub_acc_w", mnemonic := "sub", asm := "subw $0x1234, %ax"
    , bytes := "662d3412", instr := ⟨.bin .sub .w (R .rax) (.imm 0x1234), 4⟩ }
  , { id := "sub_acc_l", mnemonic := "sub", asm := "subl $0x12345678, %eax"
    , bytes := "2d78563412", instr := ⟨.bin .sub .d (R .rax) (.imm 0x12345678), 5⟩ }
  , { id := "sub_acc_q", mnemonic := "sub", asm := "subq $0x12345678, %rax"
    , bytes := "482d78563412", instr := ⟨.bin .sub .q (R .rax) (.imm 0x12345678), 6⟩ }
  , { id := "mov_mi_b", mnemonic := "mov", asm := "movb $0x5a, (%rbx)"
    , bytes := "c6035a", instr := ⟨.mov .b (M .rbx) (.imm 0x5a), 3⟩ }
  , { id := "mov_mi_w", mnemonic := "mov", asm := "movw $0x1234, (%rbx)"
    , bytes := "66c7033412", instr := ⟨.mov .w (M .rbx) (.imm 0x1234), 5⟩ }
  , { id := "mov_mi_l", mnemonic := "mov", asm := "movl $0x12345678, (%rbx)"
    , bytes := "c70378563412", instr := ⟨.mov .d (M .rbx) (.imm 0x12345678), 6⟩ }
  , { id := "mov_mi_q", mnemonic := "mov", asm := "movq $0x12345678, (%rbx)"
    , bytes := "48c70378563412", instr := ⟨.mov .q (M .rbx) (.imm 0x12345678), 7⟩ }
  , { id := "neg_m_b", mnemonic := "neg", asm := "negb (%rbx)"
    , bytes := "f61b", instr := ⟨.un .neg .b (M .rbx), 2⟩ }
  , { id := "neg_m_w", mnemonic := "neg", asm := "negw (%rbx)"
    , bytes := "66f71b", instr := ⟨.un .neg .w (M .rbx), 3⟩ }
  , { id := "neg_m_l", mnemonic := "neg", asm := "negl (%rbx)"
    , bytes := "f71b", instr := ⟨.un .neg .d (M .rbx), 2⟩ }
  , { id := "neg_m_q", mnemonic := "neg", asm := "negq (%rbx)"
    , bytes := "48f71b", instr := ⟨.un .neg .q (M .rbx), 3⟩ }
  , { id := "not_m_b", mnemonic := "not", asm := "notb (%rbx)"
    , bytes := "f613", instr := ⟨.un .not .b (M .rbx), 2⟩ }
  , { id := "not_m_w", mnemonic := "not", asm := "notw (%rbx)"
    , bytes := "66f713", instr := ⟨.un .not .w (M .rbx), 3⟩ }
  , { id := "not_m_l", mnemonic := "not", asm := "notl (%rbx)"
    , bytes := "f713", instr := ⟨.un .not .d (M .rbx), 2⟩ }
  , { id := "not_m_q", mnemonic := "not", asm := "notq (%rbx)"
    , bytes := "48f713", instr := ⟨.un .not .q (M .rbx), 3⟩ }
  , { id := "push_i_q", mnemonic := "push", asm := "pushq $0x12345678"
    , bytes := "6878563412", instr := ⟨.push .q (.imm 0x12345678), 5⟩ }
  , { id := "push_m_q", mnemonic := "push", asm := "pushq (%rbx)"
    , bytes := "ff33", instr := ⟨.push .q (M .rbx), 2⟩ }
  , { id := "push_m_w", mnemonic := "push", asm := "pushw (%rbx)"
    , bytes := "66ff33", instr := ⟨.push .w (M .rbx), 3⟩ }
  , { id := "pop_m_q", mnemonic := "pop", asm := "popq (%rbx)"
    , bytes := "8f03", instr := ⟨.pop .q (M .rbx), 2⟩ }
  , { id := "pop_m_w", mnemonic := "pop", asm := "popw (%rbx)"
    , bytes := "668f03", instr := ⟨.pop .w (M .rbx), 3⟩ }
  , { id := "jmp_m",  mnemonic := "jmp", asm := "jmp *(%rbx)"
    , bytes := "ff23", instr := ⟨.jmp (.indirect (M .rbx)), 2⟩ }
  , { id := "call_m", mnemonic := "call", asm := "callq *(%rbx)"
    , bytes := "ff13", instr := ⟨.call (.indirect (M .rbx)), 2⟩ }
  -- ⭐⭐ THE FOUR VECTORS THAT MAKE THIS MODEL'S TWO ORDER CLAIMS VISIBLE.
  --
  -- `step`'s `.push` case says "the value is read BEFORE RSP moves, so `push
  -- rsp` pushes the OLD RSP", and its `.pop` case says "RSP is incremented
  -- BEFORE the destination's effective address is computed ... a `pop rsp`
  -- therefore ends with the LOADED value".  Both sentences have been in the
  -- semantics since P0 and NEITHER WAS TESTED BY ANYTHING, because every
  -- push/pop vector in this table names an operand that does not move with
  -- RSP: `push_r` pushes RAX, `pop_r` pops into RCX, and batch 20's own
  -- `push_m_q`/`pop_m_q` address memory through RBX.  Against all of those a
  -- model that read the source after the decrement, or computed the
  -- destination address before the increment, is BIT-IDENTICAL to this one.
  --
  -- ⇒ A CLAIM THE VECTORS CANNOT DISTINGUISH IS NOT TESTED BY THEM, however
  -- many of them there are and however green the run is.  The 71 vectors above
  -- passed the differential on the FIRST run, and this is what that green did
  -- not contain.  Each vector below is paired with an arm in `selftestArms`
  -- (`wrongPushValueAfterDecrement`, `wrongPopAddressBeforeIncrement`), so the
  -- pairing is checked rather than asserted.
  --
  -- ⚠️ EVERY ACCESS STAYS INSIDE THE WATCHED STACK WINDOW (0x7fe0..0x800f), and
  -- the two orders differ INSIDE it, which is what makes the difference
  -- observable rather than merely real: at RSP = 0x8000 the popped address is
  -- 0x8008 under this model and 0x8000 under the wrong one, and both are
  -- watched bytes.  An access that fell off the end of the window would make
  -- the wrong model agree by construction.
  , { id := "push_rsp", mnemonic := "push", asm := "pushq %rsp"
    , bytes := "54", instr := ⟨.push .q (R .rsp), 1⟩ }
  , { id := "pop_rsp",  mnemonic := "pop",  asm := "popq %rsp"
    , bytes := "5c", instr := ⟨.pop .q (R .rsp), 1⟩ }
  , { id := "push_m_rsp", mnemonic := "push", asm := "pushq (%rsp)"
    , bytes := "ff3424", instr := ⟨.push .q (M .rsp), 3⟩ }
  , { id := "pop_m_rsp",  mnemonic := "pop",  asm := "popq (%rsp)"
    , bytes := "8f0424", instr := ⟨.pop .q (M .rsp), 3⟩ }
  -- ⭐⭐ P1 BATCH 21: CMPXCHG8B, THE LAST CLAIMABLE ROSTER ROW — one vector,
  -- because the instruction has exactly one operand shape.
  --
  -- ⚠️ ONE VECTOR IS NOT ONE TEST HERE AND IS NOT EIGHTY-SIX EITHER.  Measured
  -- against the oracle before this form existed, `cmpxchg8b (%rbx)` executes at
  -- ALL 82 pre-states and reaches its EQUAL branch in exactly ONE of them —
  -- `mkPre a a 0` at `a = 0x00000000ffffffff`, where `a`'s high half happens to
  -- equal the low half of `~a`.  So without `cmpxchg8bStates` below, 81 of 82
  -- cases would exercise one branch and the other would be tested by an
  -- accident nobody chose.  See D64.
  , { id := "cmpxchg8b_m", mnemonic := "cmpxchg8b", asm := "cmpxchg8b (%rbx)"
    , bytes := "0fc70b", instr := ⟨.cmpxchg8b (M .rbx), 3⟩ }
  -- ⭐⭐⭐ P2 ITEM 1 (BATCH 22): THE FS/GS SEGMENT BASE.  Eight vectors, and the
  -- DISPLACEMENT IS 0x28 IN SEVEN OF THEM ON PURPOSE — that is the
  -- stack-protector load `movq %fs:0x28, %rax` that the census counts 29,943
  -- times in the assembly class, not a number chosen to be convenient.
  --
  -- ⛔⛔ WHAT MAKES 0x28 WORK IS THE BASE, AND THE BASE IS WHY THIS BATCH IS NOT
  -- ONE LINE.  `%fs:0x28` is address 0x28 unless a segment base is added, and
  -- 0x28 is outside BOTH watched windows — where our `Mem` reads 0 and the ACL2
  -- driver renders an unmapped byte as `00`.  A vector whose access lands there
  -- is batch 12's `leaveq` trap and batch 15's backward string step for the
  -- third time: **both models unobserved, and agreement that tested nothing.**
  -- So `fsBase` is 0x1fd8 and `gsBase` 0x1fe8 (see `mkPre`), chosen so that the
  -- REAL displacement lands on the swept operand at 0x2000 through FS and on
  -- the second swept operand at 0x2010 through GS — two DIFFERENT values, so a
  -- model that swapped the two bases differs too, not merely one that dropped
  -- them.
  --
  -- ⚠️ AND THE `lea` IS NOT DECORATION.  `leaq %fs:0x28, %rax` is the only
  -- vector in this repository that can distinguish `Ea.offset` from `Ea.addr`:
  -- LEA must write 0x28, and a model that added the segment base would write
  -- 0x2000 — in EVERY pre-state, which is what makes the claim testable rather
  -- than sampled.  Without this row the split into two functions would be an
  -- assertion no vector could contradict.
  , { id := "mov_fs_abs_q", mnemonic := "mov", asm := "movq %fs:0x28, %rax"
    , bytes := "64488b042528000000"
    , instr := ⟨.mov .q (R .rax) (.mem { disp := 0x28, seg := some .fs }), 9⟩ }
  , { id := "mov_gs_abs_q", mnemonic := "mov", asm := "movq %gs:0x28, %rax"
    , bytes := "65488b042528000000"
    , instr := ⟨.mov .q (R .rax) (.mem { disp := 0x28, seg := some .gs }), 9⟩ }
  , { id := "mov_fs_abs_d", mnemonic := "mov", asm := "movl %fs:0x28, %eax"
    , bytes := "648b042528000000"
    , instr := ⟨.mov .d (R .rax) (.mem { disp := 0x28, seg := some .fs }), 8⟩ }
  -- ⭐ THE BASE-REGISTER SHAPE, so the segment base is shown to be added to a
  -- COMPUTED effective address and not only to a bare displacement.  RBX is
  -- 0x2000 in every pre-state, so -0x1fd8 + 0x2000 + 0x1fd8 = 0x2000 again.
  , { id := "mov_fs_base_q", mnemonic := "mov", asm := "movq %fs:-0x1fd8(%rbx), %rax"
    , bytes := "64488b8328e0ffff"
    , instr := ⟨.mov .q (R .rax) (.mem { base := some .rbx, disp := 0xFFFFFFFFFFFFE028, seg := some .fs }), 8⟩ }
  , { id := "mov_fs_store_q", mnemonic := "mov", asm := "movq %rax, %fs:0x28"
    , bytes := "644889042528000000"
    , instr := ⟨.mov .q (.mem { disp := 0x28, seg := some .fs }) (R .rax), 9⟩ }
  -- ⭐ A NARROW STORE THROUGH THE SEGMENT: a model that got the address right
  -- and the width wrong writes eight bytes where one belongs, and the window's
  -- margin is what sees it.
  , { id := "mov_fs_store_b", mnemonic := "mov", asm := "movb %al, %fs:0x28"
    , bytes := "6488042528000000"
    , instr := ⟨.mov .b (.mem { disp := 0x28, seg := some .fs }) (R .rax), 8⟩ }
  -- ⭐ A READ-MODIFY-WRITE through one segmented address: the load and the store
  -- must resolve to the SAME linear address, which a form that only loads or
  -- only stores cannot say.
  , { id := "add_fs_rmw_q", mnemonic := "add", asm := "addq %rcx, %fs:0x28"
    , bytes := "6448010c2528000000"
    , instr := ⟨.bin .add .q (.mem { disp := 0x28, seg := some .fs }) (R .rcx), 9⟩ }
  -- ⭐ THE INERT PREFIX.  LEA writes the EFFECTIVE address: 0x28, never 0x2000.
  , { id := "lea_fs_abs_q", mnemonic := "lea", asm := "leaq %fs:0x28, %rax"
    , bytes := "64488d042528000000"
    , instr := ⟨.lea .q .rax { disp := 0x28, seg := some .fs }, 9⟩ }
  -- ⭐⭐⭐ P2 ITEM 2 (BATCH 23): THE LOCK VOCABULARY.  Two things at once, and
  -- they are worth separating because only one of them is a new instruction.
  --
  -- (1) THE UN-DECLINED `xchg` AT MEMORY.  D25 refused it because its implicit
  -- LOCK is an atomicity claim the model had no vocabulary for; `Ea.lock` is
  -- that vocabulary, so the form executes and the two roster rows come back.
  -- ⚠️ NO `lock := true` HERE: `xchg` at memory asserts LOCK whether or not the
  -- prefix is written (SDM Vol. 2A, XCHG), so the flag would be recording a
  -- prefix the encoding does not carry — the bytes are `48 87 03`, no `f0`.
  , { id := "xchg_m_q", mnemonic := "xchg", asm := "xchgq %rax, (%rbx)"
    , bytes := "488703", instr := ⟨.xchg .q (M .rbx) (R .rax), 3⟩ }
  , { id := "xchg_m_d", mnemonic := "xchg", asm := "xchgl %eax, (%rbx)"
    , bytes := "8703", instr := ⟨.xchg .d (M .rbx) (R .rax), 2⟩ }
  , { id := "xchg_m_b", mnemonic := "xchg", asm := "xchgb %al, (%rbx)"
    , bytes := "8603", instr := ⟨.xchg .b (M .rbx) (R .rax), 2⟩ }
  , { id := "xchg_m_w", mnemonic := "xchg", asm := "xchgw %ax, (%rbx)"
    , bytes := "668703", instr := ⟨.xchg .w (M .rbx) (R .rax), 3⟩ }
  -- (2) THE PREFIX ITSELF, on eight of the nineteen forms the SDM lists.  Each
  -- computes exactly what its unlocked sibling computes — that is the point:
  -- a single-step semantics has no observation that distinguishes atomic from
  -- non-atomic, so what these vectors test is the DECODE-to-AST path and the
  -- well-formedness rule, not a new arithmetic.
  , { id := "lock_inc_m_d", mnemonic := "inc", asm := "lock incl (%rbx)"
    , bytes := "f0ff03", instr := ⟨.un .inc .d (.mem { base := some .rbx, lock := true }), 3⟩ }
  , { id := "lock_dec_m_d", mnemonic := "dec", asm := "lock decl (%rbx)"
    , bytes := "f0ff0b", instr := ⟨.un .dec .d (.mem { base := some .rbx, lock := true }), 3⟩ }
  , { id := "lock_add_m_q", mnemonic := "add", asm := "lock addq %rcx, (%rbx)"
    , bytes := "f048010b"
    , instr := ⟨.bin .add .q (.mem { base := some .rbx, lock := true }) (R .rcx), 4⟩ }
  , { id := "lock_or_m_q", mnemonic := "or", asm := "lock orq %rcx, (%rbx)"
    , bytes := "f048090b"
    , instr := ⟨.bin .or .q (.mem { base := some .rbx, lock := true }) (R .rcx), 4⟩ }
  , { id := "lock_not_m_q", mnemonic := "not", asm := "lock notq (%rbx)"
    , bytes := "f048f713", instr := ⟨.un .not .q (.mem { base := some .rbx, lock := true }), 4⟩ }
  , { id := "lock_neg_m_q", mnemonic := "neg", asm := "lock negq (%rbx)"
    , bytes := "f048f71b", instr := ⟨.un .neg .q (.mem { base := some .rbx, lock := true }), 4⟩ }
  , { id := "lock_bts_m_q", mnemonic := "bts", asm := "lock btsq $3, (%rbx)"
    , bytes := "f0480fba2b03"
    , instr := ⟨.bit .bts .q (.mem { base := some .rbx, lock := true }) (.imm 3), 6⟩ }
  , { id := "lock_xadd_m_q", mnemonic := "xadd", asm := "lock xaddq %rcx, (%rbx)"
    , bytes := "f0480fc10b"
    , instr := ⟨.xadd .q (.mem { base := some .rbx, lock := true }) .rcx, 5⟩ }
  , { id := "lock_cmpxchg_m_q", mnemonic := "cmpxchg", asm := "lock cmpxchgq %rcx, (%rbx)"
    , bytes := "f0480fb10b"
    , instr := ⟨.cmpxchg .q (.mem { base := some .rbx, lock := true }) .rcx, 5⟩ }
  , { id := "lock_cmpxchg8b_m", mnemonic := "cmpxchg8b", asm := "lock cmpxchg8b (%rbx)"
    , bytes := "f00fc70b"
    , instr := ⟨.cmpxchg8b (.mem { base := some .rbx, lock := true }), 4⟩ }
  -- ⛔⛔ (3) THE #UD ARM, AND IT IS THE ONE THIS BATCH IS ABOUT.  `mov` is NOT on
  -- the SDM's lockable list and `lock movq %rax, (%rbx)` is #UD on silicon — and
  -- it is the form a reader most expects to be lockable, because it looks
  -- exactly like the atomic store somebody wants.  The assembler accepts it, so
  -- it can be a vector; the model halts; x86isa raises #UD; the comparator's
  -- `refused` channel is where they meet.
  --
  -- ⚠️ AGREEMENT WHERE BOTH MODELS REFUSE IS AGREEMENT ABOUT NOTHING (batch 20),
  -- so the CONTROL is in the same run and was already there: `mov_mr`
  -- (`movq %rax, (%rbx)`, same operands, no prefix) EXECUTES in all 86 cases.
  -- The pair is what makes this row evidence rather than silence.
  , { id := "lock_mov_m_q_ud", mnemonic := "mov", asm := "lock movq %rax, (%rbx)"
    , bytes := "f0488903"
    , instr := ⟨.mov .q (.mem { base := some .rbx, lock := true }) (R .rax), 4⟩ }
  -- ⭐⭐ TWO MORE #UD ROWS, AND THEY ARE HERE BECAUSE THE FIRST SELFTEST RUN
  -- SHOWED TWO ARMS REPORTING THE SAME 60 DISAGREEMENTS IN THE SAME FIELD.
  --
  -- ⛔ "the lock prefix is ignored" and "the lockable list is widened to any
  -- memory destination" are different CLAIMS and were, on the vector set as it
  -- first stood, the same OBSERVATION: the only unlisted form carrying a lock
  -- was `mov`, so the arm that strips every lock and the arm that strips only
  -- `mov`'s were indistinguishable.  A claim the vectors cannot distinguish is
  -- a claim nothing tests ([[a-claim-the-vectors-cannot-distinguish]]), and two
  -- arms agreeing to the case is how that looks from outside.
  --
  -- ⇒ `lock leaq` and `lock shlq` give the wider arm a subject the narrower one
  -- does not touch: `lea` computes an address and writes no memory at all, and
  -- the shift group has a memory destination and is still not on the manual's
  -- list.  Both are #UD on silicon and both assemble.
  , { id := "lock_lea_ud", mnemonic := "lea", asm := "lock leaq (%rbx), %rax"
    , bytes := "f0488d03"
    , instr := ⟨.lea .q .rax { base := some .rbx, lock := true }, 4⟩ }
  , { id := "lock_shl_m_q_ud", mnemonic := "shl", asm := "lock shlq $3, (%rbx)"
    , bytes := "f048c12303"
    , instr := ⟨.shift .shl .q (.mem { base := some .rbx, lock := true }) (.imm8 3), 5⟩ }
  -- ⭐⭐⭐ P2 ITEM 3 (BATCH 24): `movabs`, THE 64-BIT IMMEDIATE MOVE.  Three
  -- vectors, and the batch's honesty depends on being clear about what they
  -- test and what they cannot.
  --
  -- ⛔ THE AST COULD ALWAYS EXPRESS THIS FORM.  `Operand.imm` carries a `Val`,
  -- which is a `BitVec 64`, and the decoder is trusted to have done any
  -- extension (X86/Syntax.lean's header).  So `movabsq $imm64, %r64` and
  -- `movq $imm32, %r64` reach `step` as the same shape with different values,
  -- and NO SEMANTICS CHANGE.  This is P1 batch 20's finding again — a shape the
  -- model could always express and had never been asked — and the same rule
  -- applies: what a green here does NOT contain has to be said out loud.
  --
  -- ⚠️ WHAT IT DOES TEST, in order of what could actually be wrong:
  --   * the LENGTH path.  Ten bytes is the longest encoding in this table, and
  --     `Instr.len` is a datum the model cannot check about itself; the
  --     assembler cross-check and the RIP the differential compares are what
  --     close it.
  --   * the DECODE-TRUST boundary, at the one place it is most tempting to
  --     re-derive: a decoder that reused the `imm32` path would sign-extend,
  --     and the two values below are chosen so that it MUST differ.
  --   * the demand, which is measured: 3,791 occurrences, 0.41% of the gap.
  --
  -- ⛔ IT CLAIMS NO NEW ROSTER ROW.  K files `mov r,imm` as ONE row with six
  -- variants and `blqw` widths; `mov_ri` already claims it.  Like the segment
  -- override and the LOCK prefix before it, this addition changes what the
  -- model can EXECUTE and not what it covers.
  , { id := "movabs_q", mnemonic := "mov", asm := "movabsq $0x1122334455667788, %rax"
    , bytes := "48b88877665544332211"
    , instr := ⟨.mov .q (R .rax) (.imm 0x1122334455667788), 10⟩ }
  -- ⭐⭐ THE TWO DISCRIMINATING VALUES, and they are the whole test.
  --
  -- `0x00000000ffffffff` is what a 32-bit immediate of `-1` SIGN-EXTENDS to
  -- `0xffffffffffffffff` from — so a model that took `movabs`'s low 32 bits
  -- through the `imm32` path writes all-ones where this writes 4 294 967 295.
  -- `0xffffffff00000000` is the mirror: its low 32 bits are ZERO, so the same
  -- wrong model writes 0.  Neither value can be reached by extending anything.
  , { id := "movabs_lo32_ones", mnemonic := "mov", asm := "movabsq $0x00000000ffffffff, %rax"
    , bytes := "48b8ffffffff00000000"
    , instr := ⟨.mov .q (R .rax) (.imm 0x00000000FFFFFFFF), 10⟩ }
  , { id := "movabs_hi32_ones", mnemonic := "mov", asm := "movabsq $0xffffffff00000000, %rbx"
    , bytes := "48bb00000000ffffffff"
    , instr := ⟨.mov .q (R .rbx) (.imm 0xFFFFFFFF00000000), 10⟩ }

  -- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 2 — THE FIRST VECTORS WHOSE INSTRUCTIONS WRITE
  -- AN XMM REGISTER.
  --
  -- Batch 0 built the sixteen-register channel and proved, honestly and
  -- narrowly, that it TRANSPORTS a value: both models report xmm0…xmm15, they
  -- agree, and a planted clobber is caught.  What it could not prove is that
  -- anything FLOWS through it, because no instruction in the roster could move a
  -- vector register — so the comparator was watching sixteen constants, and D27
  -- says a comparator watching a constant reports agreement it did not test.
  -- These rows are what close that gap.
  --
  -- ⚠️ EVERY ONE IS REGISTER-TO-REGISTER.  The memory forms need a 128-bit
  -- memory path and they are where `movdqa` and `movdqu` stop being the same
  -- instruction (an unaligned `movdqa` is #GP); that is a batch of its own.
  --
  -- ⚠️ `paddd_x2x3` IS NOT A DUPLICATE OF `paddd_x0x1`.  Every other row here
  -- writes xmm0 and reads xmm1, so a model that ignored the register FIELDS
  -- entirely — always reading xmm1 into xmm0 — would agree with the oracle on
  -- all of them.  One row at a different register pair is what makes the operand
  -- decoding observable, and it is the same reason the GPR vectors do not all
  -- use %rax.
  , { id := "movdqa_xx", mnemonic := "movdqa", asm := "movdqa %xmm1, %xmm0"
    , bytes := "660f6fc1", instr := ⟨.vmov true .x0 .x1, 4⟩ }
  , { id := "movdqu_xx", mnemonic := "movdqu", asm := "movdqu %xmm1, %xmm0"
    , bytes := "f30f6fc1", instr := ⟨.vmov false .x0 .x1, 4⟩ }
  , { id := "paddb_xx", mnemonic := "paddb", asm := "paddb %xmm1, %xmm0"
    , bytes := "660ffcc1", instr := ⟨.vbin .addb .x0 .x1, 4⟩ }
  , { id := "paddw_xx", mnemonic := "paddw", asm := "paddw %xmm1, %xmm0"
    , bytes := "660ffdc1", instr := ⟨.vbin .addw .x0 .x1, 4⟩ }
  , { id := "paddd_xx", mnemonic := "paddd", asm := "paddd %xmm1, %xmm0"
    , bytes := "660ffec1", instr := ⟨.vbin .addd .x0 .x1, 4⟩ }
  , { id := "paddq_xx", mnemonic := "paddq", asm := "paddq %xmm1, %xmm0"
    , bytes := "660fd4c1", instr := ⟨.vbin .addq .x0 .x1, 4⟩ }
  , { id := "psubb_xx", mnemonic := "psubb", asm := "psubb %xmm1, %xmm0"
    , bytes := "660ff8c1", instr := ⟨.vbin .subb .x0 .x1, 4⟩ }
  , { id := "psubw_xx", mnemonic := "psubw", asm := "psubw %xmm1, %xmm0"
    , bytes := "660ff9c1", instr := ⟨.vbin .subw .x0 .x1, 4⟩ }
  , { id := "psubd_xx", mnemonic := "psubd", asm := "psubd %xmm1, %xmm0"
    , bytes := "660ffac1", instr := ⟨.vbin .subd .x0 .x1, 4⟩ }
  , { id := "psubq_xx", mnemonic := "psubq", asm := "psubq %xmm1, %xmm0"
    , bytes := "660ffbc1", instr := ⟨.vbin .subq .x0 .x1, 4⟩ }
  , { id := "pxor_xx", mnemonic := "pxor", asm := "pxor %xmm1, %xmm0"
    , bytes := "660fefc1", instr := ⟨.vbin .xor .x0 .x1, 4⟩ }
  , { id := "pand_xx", mnemonic := "pand", asm := "pand %xmm1, %xmm0"
    , bytes := "660fdbc1", instr := ⟨.vbin .and .x0 .x1, 4⟩ }
  , { id := "por_xx", mnemonic := "por", asm := "por %xmm1, %xmm0"
    , bytes := "660febc1", instr := ⟨.vbin .or .x0 .x1, 4⟩ }
  , { id := "paddd_x2x3", mnemonic := "paddd", asm := "paddd %xmm3, %xmm2"
    , bytes := "660ffed3", instr := ⟨.vbin .addd .x2 .x3, 4⟩ }
  -- ⛔⛔ THESE TWO EXIST BECAUSE AN ARM FAILED, AND THE ARM WAS RIGHT.
  --
  -- `wrongVmovFixedRegisters` makes every `movdqa`/`movdqu` move xmm1 into xmm0
  -- whatever it encodes.  With only `movdqa_xx` and `movdqu_xx` in the table —
  -- BOTH of which move xmm1 into xmm0 — that wrong model is BIT-IDENTICAL to
  -- this one on every vector, and the comparator reported ZERO disagreements
  -- against a known-wrong model.  The register fields of `Op.vmov` were decoded
  -- by nothing.
  --
  -- ⚠️ AND THE COMMENT ON THAT ARM ASSERTED THE OPPOSITE.  It said the arm was
  -- caught by `paddd_x2x3` — which is a `.vbin`, not a `.vmov`, and therefore
  -- cannot exercise `vmov`'s operands at all.  A pairing was CLAIMED in prose
  -- and was false; the arm is what found it, exactly as P1 batch 20's three
  -- order claims were found by asking what a predicted green does not contain.
  , { id := "movdqa_x4x5", mnemonic := "movdqa", asm := "movdqa %xmm5, %xmm4"
    , bytes := "660f6fe5", instr := ⟨.vmov true .x4 .x5, 4⟩ }
  , { id := "movdqu_x4x5", mnemonic := "movdqu", asm := "movdqu %xmm5, %xmm4"
    , bytes := "f30f6fe5", instr := ⟨.vmov false .x4 .x5, 4⟩ }

  -- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 3 — THE MEMORY FORMS.  RBX is 0x2000 in every
  -- pre-state, which is 16-byte ALIGNED and sits inside the 64-byte data window
  -- at 0x1fe0, so a sixteen-byte access at `(%rbx)` is fully observable on both
  -- sides.  The low eight bytes sweep with `c`; the high eight are baseMem's
  -- 0xB8…0xBF — constant across pre-states but all DISTINCT and non-zero, so a
  -- model that read only eight bytes, or swapped the halves, differs.
  --
  -- ⛔⛔ THERE IS NO UNALIGNED `movdqa` VECTOR HERE, AND ITS ABSENCE IS THE
  -- BATCH'S CENTRAL FINDING RATHER THAN AN OMISSION.  An unaligned `movdqa` is
  -- #GP(0) in hardware (SDM Vol. 2B) and this model faults on it — but ACL2
  -- x86isa DOES NOT IMPLEMENT THE CHECK: measured, not assumed, by executing
  -- `movdqa 8(%rbx),%xmm0` at 0x2008 on the oracle with CR4.OSFXSR set, where it
  -- EXECUTES.  A vector for it would put a one-sided refusal into every
  -- pre-state, and `classify` rightly calls that the `refusal` class and counts
  -- it UNEXPLAINED.  So the rule is modelled and asserted by theorem
  -- (`vload_unaligned_faults`), and it is NOT differentially validated, because
  -- the oracle cannot validate it.  See D91 — and it is a concrete item for the
  -- hardware co-simulation lane, where real silicon IS the oracle for this.
  --
  -- ⚠️ `movdqu_load_unal` IS the unaligned case that CAN be validated: both
  -- models execute it, and it is what says the effective address is computed and
  -- used rather than the base register being read directly.
  , { id := "movdqa_load_m", mnemonic := "movdqa", asm := "movdqa (%rbx), %xmm0"
    , bytes := "660f6f03", instr := ⟨.vload true .x0 { base := some .rbx }, 4⟩ }
  , { id := "movdqa_store_m", mnemonic := "movdqa", asm := "movdqa %xmm0, (%rbx)"
    , bytes := "660f7f03", instr := ⟨.vstore true { base := some .rbx } .x0, 4⟩ }
  , { id := "movdqu_load_m", mnemonic := "movdqu", asm := "movdqu (%rbx), %xmm0"
    , bytes := "f30f6f03", instr := ⟨.vload false .x0 { base := some .rbx }, 4⟩ }
  , { id := "movdqu_store_m", mnemonic := "movdqu", asm := "movdqu %xmm0, (%rbx)"
    , bytes := "f30f7f03", instr := ⟨.vstore false { base := some .rbx } .x0, 4⟩ }
  , { id := "movdqu_load_unal", mnemonic := "movdqu", asm := "movdqu 8(%rbx), %xmm0"
    , bytes := "f30f6f4308"
    , instr := ⟨.vload false .x0 { base := some .rbx, disp := 8 }, 5⟩ }

  -- ⭐⭐⭐ P2 VECTOR WAVE, BATCH 5 — MOVD / MOVQ ACROSS THE REGISTER FILES.
  -- Rank 4 and rank 8 of the measured demand list.  Both directions of each
  -- width, so the zeroing is observable in BOTH files:
  --   * `movd %ecx,%xmm0` must clear xmm0's bits 127:32, not merge into them —
  --     and the XMM pre-state pattern is deliberately NON-ZERO (batch 0), which
  --     is the only reason a model that preserved them could be caught;
  --   * `movd %xmm0,%ecx` is an ordinary 32-bit GPR write and must zero-extend
  --     to 64, the rule every other form here already obeys.
  -- ⚠️ `movq_xx` is NOT `movdqa` at 64 bits: it moves the low quadword and ZEROES
  -- the upper one (objdump says so itself: `xmm0 = xmm1[0],zero`).
  -- ⭐⭐⭐ THE TWO INTO-XMM VECTORS ARE BACK, AND THE ROUND TRIP IS THE POINT.
  -- They were written, run, and REMOVED at batch 5 because ACL2 x86isa MERGES
  -- the destination's upper bits where the SDM and K both say CLEAR — 81 of 86
  -- and 78 of 86 unexplained `spec` disagreements. Removing them kept the run
  -- green and stopped the test PERMANENTLY AND SILENTLY: if x86isa were fixed
  -- tomorrow, nothing would notice.
  --
  -- They are restored under `knownDivergences` (Main.lean), which compares them
  -- on every run, reports them in their own class, and — the half that makes it
  -- safe — FAILS if either stops diverging. See D95.
  , { id := "movd_to_x", mnemonic := "movd", asm := "movd %ecx, %xmm0"
    , bytes := "660f6ec1", instr := ⟨.vmovg true .d .x0 .rcx, 4⟩ }
  , { id := "movq_to_x", mnemonic := "movq", asm := "movq %rcx, %xmm0"
    , bytes := "66480f6ec1", instr := ⟨.vmovg true .q .x0 .rcx, 5⟩ }
  , { id := "movd_from_x", mnemonic := "movd", asm := "movd %xmm0, %ecx"
    , bytes := "660f7ec1", instr := ⟨.vmovg false .d .x0 .rcx, 4⟩ }
  , { id := "movq_from_x", mnemonic := "movq", asm := "movq %xmm0, %rax"
    , bytes := "66480f7ec0", instr := ⟨.vmovg false .q .x0 .rax, 5⟩ }
  , { id := "movq_xx", mnemonic := "movq", asm := "movq %xmm1, %xmm0"
    , bytes := "f30f7ec1", instr := ⟨.vmovq .x0 .x1, 4⟩ }
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
  -- ⭐ P1 BATCH 15 WIDENED THE DATA WINDOW FROM 32 BYTES TO 64, and every one of
  -- the original 32 kept its address, its contents and its meaning.  The string
  -- group is the first in this model whose operands MOVE, so RSI and RDI need a
  -- full operation plus a margin in BOTH directions inside watched memory.
  --
  -- ⛔ THE ALTERNATIVE WAS NOT "A SMALLER WINDOW", IT WAS AN UNTESTED DF CASE.
  -- Off the end of a window, our `Mem` reads 0 for an unwritten byte and the
  -- ACL2 driver renders an unmapped read as `00` — so a pointer that decremented
  -- when it should have incremented would have the two models AGREEING ON
  -- ZEROES.  A backward step landing outside the watched bytes is not a weak
  -- test, it is a test that passes by construction.
  --
  -- ⚠️ Widening rather than adding a THIRD window is what keeps the cost at
  -- +32 bytes a case instead of +48 or more, and keeps one window constant on
  -- each side of the oracle boundary instead of two.
  [ { base := 0x1fe0, len := 64 }   -- data: rsi = 0x1fe8, rbx = 0x2000, rdi = 0x2010
  , { base := 0x7fe0, len := 48 } ] -- stack: rsp = 0x8000, margin below and above

/-- ⭐ THE WATCHED WINDOWS' BACKGROUND PATTERN, BUILT ONCE.

A known, non-uniform pattern in the data window so a wrong load is visible, and
a known pattern under the stack pointer so `pop` has something to find.  It is
the SAME eighty bytes in every pre-state, and it used to be built inside
`mkPre` — eighty map insertions per state, 5 920 per evaluation of
`preStates`, re-done by every `decide` in `Tests/Coverage.lean` that mentions
the pre-state set.

Hoisting it to a closed constant is not a style preference: it is the half of
batch 9's scaling finding that the measurement in `Tests/Coverage.lean`'s
header leaves over.  Nothing about the pre-states changes — the bytes are
identical and every existing assertion about the window and its margin still
holds, which is what says the change is a factoring and not a weakening. -/
def baseMem : Mem :=
  let m := (List.range 32).foldl
    (fun m i => m.write (0x1ff0 + BitVec.ofNat 64 i) (BitVec.ofNat 8 (0xA0 + i))) Mem.empty
  -- ⭐ P1 BATCH 15: THE TWO NEW FLANKS GET THEIR OWN PATTERNS RATHER THAN A
  -- RE-BASED `0xA0 + i`.  Re-basing the existing run at 0x1fe0 would have been
  -- the obvious edit and would have moved every byte of the old window: 0x1ff0
  -- would then read 0xB0, and `memory_window_margin_is_fixed` — which asserts
  -- 0xA0 there — would have failed, along with every anchor and differential
  -- result that depends on the data window's contents.
  --
  -- ⇒ Three disjoint runs (0x60.., 0xA0.., 0xE0..) instead of one, so the
  -- widening is PURELY ADDITIVE: all 64 bytes are still distinct, so a load
  -- from the wrong address is still visible, and not one previously-existing
  -- byte changed.  Batch 11 did the same thing when it made DF bit 6 of the
  -- flag seed rather than renumbering the six below it.
  let m := (List.range 16).foldl
    (fun m i => m.write (0x1fe0 + BitVec.ofNat 64 i) (BitVec.ofNat 8 (0x60 + i))) m
  let m := (List.range 16).foldl
    (fun m i => m.write (0x2010 + BitVec.ofNat 64 i) (BitVec.ofNat 8 (0xE0 + i))) m
  (List.range 48).foldl
    (fun m i => m.write (0x7fe0 + BitVec.ofNat 64 i) (BitVec.ofNat 8 (0x10 + i))) m

/-- ⭐ THE XMM PATTERN, BUILT FROM THE SWEPT VALUES.  See the note at its use
site in `mkPre` for why all-zero would have been the worst choice available. -/
def xmmPattern (a c : BitVec 64) : Xmms :=
  XmmReg.all.foldl (fun xs r =>
    let i : BitVec 64 := BitVec.ofNat 64 r.index.val
    let hi : BitVec 64 := a + i
    let lo : BitVec 64 := c ^^^ (i * 0x1111111111111111)
    xs.set r ((hi.setWidth 128) <<< 64 ||| lo.setWidth 128)) {}

/-- A pre-state built from two operand values and a flag seed.  RBX and RSP are
fixed so the memory windows mean the same thing in every vector; RAX/RCX carry
the values under test. -/
def mkPre (a c : BitVec 64) (fseed : Nat) : Cpu :=
  let f : Flags :=
    { cf := fseed % 2 == 1, pf := fseed / 2 % 2 == 1, af := fseed / 4 % 2 == 1
    , zf := fseed / 8 % 2 == 1, sf := fseed / 16 % 2 == 1, of := fseed / 32 % 2 == 1
    -- ⭐ DF JOINED THE SWEEP IN P1 BATCH 11, AS BIT 6, AND THE BIT POSITION IS
    -- WHY NOTHING ELSE MOVED.  Every pre-existing call site passes a seed below
    -- 64 (0, 1, 5, 63, and the random tail's index i < 8), so all seventy-four
    -- original pre-states keep `df := false` and every existing case is
    -- byte-identical.  The states that actually SET it are `dfStates` below.
    , df := fseed / 64 % 2 == 1 }
  let mem := baseMem
  -- ⭐ AND THE MEMORY OPERAND ITSELF SWEEPS, added by P1 BATCH 3.  The eight
  -- bytes at RBX — the span every memory-operand vector addresses — carry `c`,
  -- the same value RCX carries, so `cmpq %rax, (%rbx)` sweeps exactly as
  -- `cmpq %rcx, %rax` does and a memory operand is a full peer of a register
  -- one in the adversarial sweep.
  --
  -- ⛔ WITHOUT THIS THE WINDOW WAS A CONSTANT IN ALL 74 PRE-STATES, and that is
  -- a finding about batches 1 and 2, not only about this one: every `_rm_`
  -- form they shipped read the SAME source value 74 times over.  Those runs
  -- were green and their green was real, but a form whose source operand never
  -- moves is one test reported as seventy-four.  See docs/DECISIONS.md D14.
  --
  -- The MARGIN keeps its 0xA0+i pattern on both sides, so a store or load that
  -- ran off the end of its span still shows up as a difference outside it.
  let mem := mem.writeSize .q 0x2000 c
  -- ⭐ P1 BATCH 15: THE STRING OPERANDS SWEEP TOO, and they must be a THIRD and
  -- FOURTH value rather than reusing `a` and `c`, because of what each of the
  -- five forms would otherwise become.
  --
  -- ⛔ WITH `[RSI] = a` THE WHOLE OF `lods` IS A NO-OP: it loads RAX from RSI,
  -- RAX already holds `a`, and a model that did not write the accumulator at
  -- all would agree with this one in every state.  With `[RDI] = a` the same
  -- is true of `stos`.  The trap is D14's ("a form whose source operand never
  -- moves is one test reported as seventy-four") in its sharper form: here the
  -- operand DOES sweep, and the form is still untested, because it sweeps in
  -- lockstep with the register it is compared against.
  --
  -- So: `[RSI] = c` and `[RDI] = a XOR c`.  Then `lods` moves RAX except on the
  -- diagonal, `stos` moves memory except where `c = 0`, `movs` moves it except
  -- where `a = 0` — and, deliberately, the two comparisons still reach ZF:
  -- `cmps` is `c − (a XOR c)`, zero exactly when `a = 0`, and `scas` is
  -- `a − (a XOR c)`, zero exactly when `c = 0`.  Both values are in
  -- `adversarial`, so both zero cases are reached rather than hoped for.
  let mem := mem.writeSize .q 0x1fe8 c
  let mem := mem.writeSize .q 0x2010 (a ^^^ c)
  -- ⭐ AND RDX CARRIES A VALUE, added by P1 BATCH 10, for the same reason the
  -- memory window stopped being a constant in batch 3.  `cwtd`/`cltd`/`cqto`
  -- are the first instructions in this model to write a register their operands
  -- do not name, and `cltd`'s write is THIRTY-TWO BITS WIDE — so it clears
  -- RDX's upper half, and a model that merged instead of zero-extending would
  -- be indistinguishable from the correct one in EVERY pre-state where RDX is
  -- zero.  It was zero in all 74.  The complement of `a` is used so the value
  -- sweeps with the rest of the state and is all-ones exactly where `a` is
  -- zero.  See docs/DECISIONS.md D26.
  -- ⭐ P1 BATCH 15: RSI AND RDI POINT SOMEWHERE.  They were 0 in all eighty
  -- pre-states — measured in the emitted cases, not only read off this record —
  -- and address 0 is outside both watched windows, so the string group would
  -- have been the `leaveq` trap of batch 12 all over again: both models
  -- unobserved, and agreement that tested nothing.
  --
  -- ⚠️ THE ADDRESSES ARE FIXED, LIKE RBX AND RSP, AND ONLY THE DATA SWEEPS.
  -- 0x1fe8 has eight bytes of operand with the 0x60.. margin below it and the
  -- 0xA0.. margin above; 0x2010 has eight with the 0xB8.. margin below and the
  -- 0xE8.. margin above.  Forty bytes apart, so no width overlaps the other,
  -- and one step in EITHER direction stays inside the watched window.
  -- ⭐⭐ P2 ITEM 1: THE TWO SEGMENT BASES, AND THE TWO VALUES ARE CHOSEN, NOT
  -- ARBITRARY.  `fsBase + 0x28 = 0x2000` and `gsBase + 0x28 = 0x2010` — the two
  -- swept operands in the data window, holding `c` and `a XOR c` respectively.
  --
  -- ⛔ THEY ARE FIXED IN EVERY PRE-STATE, LIKE RBX AND RSP, AND THEY ARE NOT IN
  -- THE COMPARED RECORD.  No instruction in this roster writes either (D27: a
  -- component nothing writes is a constant, and a comparator watching a
  -- constant reports agreement it did not test), so what is compared is the
  -- ADDRESS they produce and never the bases themselves.
  --
  -- ⚠️ AND THE TWO VALUES DIFFER BY 0x10 RATHER THAN BEING EQUAL, which is what
  -- makes `fs` and `gs` DISTINGUISHABLE: with one base for both, a model that
  -- read GS's base for an FS access would agree in every case, and this batch
  -- would ship an untested half. `X86.Seg` has exactly two constructors and a
  -- pre-state that cannot tell them apart tests one.
  { regs := { rax := a, rcx := c, rdx := ~~~a, rbx := 0x2000, rsp := 0x8000
            , rsi := 0x1fe8, rdi := 0x2010 }
    flags := f
    mem := mem
    rip := 0x400000
    fsBase := 0x1fd8
    gsBase := 0x1fe8
    -- ⭐⭐⭐ THE VECTOR REGISTERS (P2 vector wave, batch 0 — THE HARNESS).
    --
    -- ⛔ ALL-ZERO WOULD HAVE BEEN THE WORST POSSIBLE CHOICE, and it is the one
    -- that costs nothing to write.  With sixteen zero registers on both sides,
    -- a model that reported the wrong REGISTER, or reported a constant, or
    -- reported nothing at all, agrees with the oracle in every case — the
    -- unobserved-region trap in its purest form, dressed as a green run.
    --
    -- ⇒ Each register gets a DISTINCT value that MOVES with the pre-state:
    -- the high half is `a + i` and the low half is `c XOR (i * 0x1111…)`, so
    --   * no two registers are equal (a swap or a wrong index is visible),
    --   * none is a constant across cases (the channel is not a constant),
    --   * and none is zero except at the one swept value where it must be.
    --
    -- ⚠️ NOTHING IN THIS ROSTER WRITES THEM, so by D27 they are still inputs and
    -- the comparator is still watching a constant PER CASE.  What the pattern
    -- buys is that the constant is a DIFFERENT constant in every register and
    -- every case, which is what a wrong reading has to survive.
    xmm := xmmPattern a c
    oracle := zeroOracle }

/-- ⭐ THE CARRY BOUNDARY, added by P1 BATCH 2 — and it is the same finding P0's
harness selftest made about the shift counts, arriving a second time in a
different rule.

`adc` and `sbb` differ from `add` and `sub` in exactly one place: an operand
pair that does not carry can carry once CF is added, and one that does not
borrow can borrow once CF is subtracted.  `0xFF + 0x00 + 1` and `0x00 - 0x00 - 1`
are the states where the carry ALONE decides the answer.

⛔ THIS BLOCK WAS FIRST WRITTEN CLAIMING THE THREE SWEEPS ABOVE COULD NOT REACH
THOSE STATES.  The claim was tested by deleting this list and re-running the
harness selftest's boundary arm, and it was WRONG: the bug was still caught.
Two accidents reach the boundary.  `0xAAAA…AA` and `0x5555…55` are adjacent in
`adversarial` and are exact complements, so the `pairs` sweep hands `adc` a sum
of `2^64 - 1` with CF set; and truncating `0x100000000` to a byte gives zero, so
several pairs become `0xFF + 0x00` at width b.  Neither was put there for this.

⇒ **COVERAGE THAT ARISES INCIDENTALLY FROM A LIST WRITTEN FOR ANOTHER PURPOSE IS
COVERAGE NOBODY IS MAINTAINING.**  Reordering `adversarial` or dropping one of
those two constants would remove the only states exercising the carry rule, and
every gate would stay green.  So this list stays — not because it is the only
way to reach the boundary, but because it is the only DELIBERATE one — and
`Tests/Coverage.lean` asserts the boundary is crossed, so the accident can no
longer be the thing holding the rule up.

Six states, three operand pairs against both values of CF.  `0xFFFF…FF` is
all-ones at EVERY width and `0` is zero at every width, so one pair covers the
boundary at b, w, l and q at once. -/
def carryBoundary : List Cpu :=
  let ones : BitVec 64 := 0xFFFFFFFFFFFFFFFF
  [ mkPre ones 0 0, mkPre ones 0 1      -- adc: overflows only because of CF
  , mkPre 0 0 0,    mkPre 0 0 1         -- sbb: borrows only because of CF
  , mkPre 0 ones 0, mkPre 0 ones 1 ]    -- and the borrow that happens either way

/-- ⭐ P1 BATCH 11: THE STATES IN WHICH DF IS SET, AND THE FIRST STATES IN THIS
REPOSITORY THAT SET IT AT ALL.

⛔ `df` HAS BEEN IN `Flags` SINCE P0, PRINTED BY `Serialize.lean` SINCE P0, AND
DIFFED BY THE COMPARATOR SINCE P0 — and it was `false` in all seventy-four
pre-states and no instruction could write it, so for ten batches the comparator
faithfully compared a bit that could not differ.  `cld` clears DF; against a
pre-state set where DF is already clear, **`cld` and a no-op are the same
function**, and an unimplemented `cld` would have passed every case.

⇒ This is docs/DECISIONS.md D26 arriving a THIRD time — after D14's constant
memory window and D26's own constant RDX — and the third instance is the one
that says the rule is not about registers: *a state component that no
instruction writes is a constant, and a comparator that watches a constant
reports agreement it did not test.*  See D27.

Two states rather than one so the sweep still has both values of the other six
flags: seed 64 sets DF alone, seed 127 sets DF and all six arithmetic flags. -/
def dfStates : List Cpu :=
  let ones : BitVec 64 := 0xFFFFFFFFFFFFFFFF
  [ mkPre ones 0 64, mkPre 0 ones 127 ]

/-- ⭐ P1 BATCH 11: THE STATE THAT SEPARATES THE `addr32` LOOP'S COUNTER WIDTHS.

`addr32 loop` tests `ECX - 1`; a model that tested `RCX - 1` instead differs
from it on exactly the states where one is zero and the other is not — that is,
where **the low 32 bits of RCX are 1 while its upper half is not**.  Not one of
the seventy-four pre-states was such a state: `adversarial` contains 1 (upper
half zero) and `0x100000000` (low half zero), and no value with a non-zero upper
half and a low half of 1.  So the bug was invisible and the vector could not
have caught it.

⚠️ AND IT IS THE SAME DEFECT AS `dfStates` ABOVE IN A DIFFERENT DRESS: there the
gap was a component nothing wrote, here it is a COMBINATION no value reached.
An adversarial list is adversarial with respect to the questions already being
asked of it, and `addr32` asks a question about the two halves of RCX
SEPARATELY that nothing before this batch asked. -/
def loopCounterStates : List Cpu :=
  [ mkPre 0x5555555555555555 0xDEADBEEF00000001 0     -- ecx = 1, rcx ≠ 1
  , mkPre 0xAAAAAAAAAAAAAAAA 0xDEADBEEF00000001 8 ]   -- ... and with ZF set

/-- ⭐⭐ P1 BATCH 12: THE STATES THAT GIVE `retq` AND `leaveq` A FRAME TO FIND,
AND THE REASON THE BATCH IS NOT AS CHEAP AS ITS SEMANTICS.

⛔ AGAINST THE SEVENTY-EIGHT EXISTING PRE-STATES, `retq` CAN ONLY REFUSE.  The
stack window's background is `0x10 + i` from 0x7fe0, so the eight bytes at
RSP = 0x8000 read little-endian as `0x3736353433323130` — whose bits 63:47 are
not all equal, i.e. NOT CANONICAL.  Every existing state therefore drives `retq`
down the #GP path, and **a model whose `retq` did nothing at all but refuse would
pass every one of them**.  `leaveq` is worse: RBP is 0 in all seventy-eight, so
it would set RSP to 0 and pop from an address outside BOTH watched windows,
where neither model is observed.

This is D27's rule applied BEFORE the fact instead of after it.  DF was found to
be a constant after ten batches of being diffed; here the constant — a stack that
never holds a returnable address, and an RBP that never points anywhere — was
looked for while writing the vectors, because the question "what in the state
does this form actually read?" is now part of adding a form.  ⇒ **The cheapness
of a form is a fact about its SEMANTICS; its cost is a fact about the STATE it
needs.**  These four instructions are one line of `step` each and needed a new
pre-state constructor.

The two states differ in the SIGN of the canonical target: `0x401000` sits in
the low half and `0xFFFFFFFFFFFF8000` in the high half, so a `canonical` written
as an unsigned range check rather than a bits-63:47-agree check fails on the
second and passes the first. -/
def mkFrame (a c : BitVec 64) (fseed : Nat) (ret rbp frameVal : BitVec 64) : Cpu :=
  let s := mkPre a c fseed
  let s := s.setReg .q .rbp rbp
  -- the return address where `retq` looks, and a distinct value where `leaveq`
  -- looks after it has moved RSP to RBP.  Both land inside the stack window, so
  -- both models are handed the same bytes and both are observed.
  let s := s.writeMem .q (s.regs.get .rsp) ret
  s.writeMem .q rbp frameVal

def frameStates : List Cpu :=
  [ mkFrame 0x5555555555555555 0x0F0F0F0F0F0F0F0F 0
      0x0000000000401000 0x7ff0 0x00000000DEADBEEF
  , mkFrame 0xAAAAAAAAAAAAAAAA 0xF0F0F0F0F0F0F0F0 63
      0xFFFFFFFFFFFF8000 0x7ff8 0x123456789ABCDEF0 ]

/-- ⭐⭐ P1 BATCH 15: THE STATES IN WHICH A STRING POINTER CROSSES A WIDTH
BOUNDARY — and the third time this repository has had to add a pre-state for a
COMBINATION rather than for a value.

⛔ THE DEFECT THAT FOUND THEM.  A planted arm updated RSI and RDI through the
ordinary operand-width rule (`setReg sz`) instead of writing the whole 64 bits,
which is the natural mistake because every other register write in this model
DOES go through that rule.  The comparator reported **zero disagreements against
that known-wrong model** — the harness selftest's own failure message, not a
guess.

⚠️ AND THE ARM WAS RIGHT; THE PRE-STATES WERE THE PROBLEM.  A merged write and a
full write differ only when the new pointer differs from the old ABOVE the
operand width — that is, only when the update CARRIES or BORROWS across a byte
or word boundary.  With RSI at 0x1fe8 and RDI at 0x2010, `±1` and `±2` never
touch bit 8, so the two writes are bit-identical at every width and in both
directions, and the wrong model IS the right model on all eighty states.

⇒ D27's rule again, in its `loopCounterStates` form: **an adversarial set is
adversarial only with respect to the questions already asked of it.** The
pointers were chosen to keep every access inside the watched windows, which is a
question about ADDRESSES; nothing had yet asked a question about the ARITHMETIC
that produces the next address.

The two states are the two directions.  Forward, both pointers sit at `…FF` so
the increment carries; backward, both sit at `…00` so the decrement borrows.
⚠️ Every access still lands inside a watched window at every width — 0x1fff and
0x2000 are in the data window (which reaches 0x201f), and 0x7fff and 0x8000 are
in the stack window (which reaches 0x800f) — so the states test the pointer
arithmetic WITHOUT giving up the observation that made the group testable. -/
def mkStringPtr (a c : BitVec 64) (fseed : Nat) (si di : BitVec 64) : Cpu :=
  let s := mkPre a c fseed
  { s with regs := { s.regs with rsi := si, rdi := di } }

/-- ⭐⭐ P1 BATCH 21: THE STATES IN WHICH `cmpxchg8b` CAN TAKE EITHER BRANCH,
and the states that tell a 64-bit comparison from a 32-bit one.

⛔ THE MEASUREMENT THAT MADE THEM NECESSARY, taken on the oracle BEFORE the
constructor existed: `cmpxchg8b (%rbx)` executes at all 82 pre-states and
reaches its EQUAL branch in exactly ONE. `mkPre` puts `~a` in RDX and `c` in the
eight bytes at RBX, so `EDX:EAX` is `(~a)[31:0] : a[31:0]` and the comparison
succeeds only where `c = a` AND `a`'s high half is the complement of its low
half — which is `a = 0x00000000ffffffff`, one entry of `adversarial`, and true
by accident.
⇒ **A BRANCH REACHED BY ONE ACCIDENTAL STATE IS A BRANCH NOBODY IS MAINTAINING**
(the `carryBoundary` finding, batch 2, in a control-flow shape): reordering
`adversarial` or dropping one constant would take the equal branch out of the
run and every gate would stay green.

⚠️ THE TWO UNEQUAL STATES DISCRIMINATE A HALF-WIDTH COMPARISON, AND THEY ARE
NOT WHAT MAKES IT CATCHABLE. The comparison is 64 bits wide and is assembled
from two 32-bit register views, so the defect this form invites is comparing ONE
half. `delta` is XORed into the accumulator pair: `1` differs in the LOW half
alone, `1 <<< 32` in the HIGH half alone, so a model comparing only EAX calls
the second EQUAL, one comparing only EDX calls the first EQUAL, and this model
calls both UNEQUAL.

⛔ AND THE SENTENCE THAT USED TO STAND HERE — *"no inherited pre-state is such a
state"* — WAS FALSE, caught by counting the states instead of believing it.
Measured over the emitted cases: **21 of the 82 inherited pre-states** already
agree in the low half and differ in the high half, and **11** do the reverse.
The reason is `mkPre` itself: it sets `[0x2000] = RCX` and RDX to `~RAX`, so on
the whole diagonal (where `RCX = RAX`) the low halves match by construction.
Both half-width arms are caught with or without these two states.
⇒ 🔑 **A STATE ADDED FOR A DEFECT IS NOT EVIDENCE THAT THE DEFECT NEEDED IT** —
the plausible sentence about a new pre-state is the one saying it was necessary,
and it costs one count to check.

⭐ THEY ARE KEPT ANYWAY, AND THE REASON IS `carryBoundary`'s (batch 2): the
inherited coverage is INCIDENTAL — it arises from a diagonal written for the
adversarial sweep and would vanish if that list were reordered — while these two
are the only DELIBERATE ones. The same holds, and matters more, for the two
EQUAL states: the equal branch is reached in ONE of the 82 inherited states and
that one is an accident, so without them a branch of this instruction is
exercised by a coincidence nobody is maintaining.

⭐⭐ MEASURED BY DELETION, not asserted — this whole list removed from
`preStates` and the five arms re-run:

    arm                                with these states   without
    cmpxchg8b never stores                     3                1
    cmpxchg8b stores EBX:ECX                   3                1
    cmpxchg8b compares EAX alone              22               21
    cmpxchg8b merges EDX:EAX                  71               71
    cmpxchg8b always stores                   79               77

The two EQUAL-branch arms fall to a SINGLE disagreement, which is the accidental
state and nothing else. And `22 → 21` is the second route to the count above: the
half-width arm loses exactly the one state added for it, out of the 21 that were
already there.

⚠️ THE ADDRESS AND THE WIDTH KEEP THE OBSERVATION. The eight bytes at 0x2000 are
inside the watched data window (0x1fe0..0x201f), so both models are read on
every one of these states — an operand written outside the window would make any
wrong model agree by construction.

⛔ AND A NAMED GAP, because it is not covered and saying so is cheaper than
discovering it: **EBX is 0x2000 in every pre-state this harness has**, since RBX
is the fixed data-window pointer, so the low half of the value stored on the
equal branch is a CONSTANT. Swapping the stored halves is still caught (ECX
sweeps), and so is storing any other register (they sweep too); what no state
here can catch is a model that stores the literal 0x2000 in that half by some
other route. Making EBX sweep means moving RBX, which moves every memory
vector's address at once — a second instrument change in the same batch, which
is how two defects cancel. -/
def mkCmpxchg8b (a c : BitVec 64) (fseed : Nat) (delta : BitVec 64) : Cpu :=
  let s := mkPre a c fseed
  -- ⭐ THE ACCUMULATOR PAIR MOVES, NOT THE MEMORY, AND A GATE IS WHY.  The first
  -- version of this constructor wrote the wanted value into the eight bytes at
  -- RBX — and `memory_operand_mirrors_rcx` refused it: batch 3 made
  -- `[0x2000] = RCX` an invariant of EVERY pre-state, and that invariant is the
  -- only reason a memory operand sweeps like a register one instead of being a
  -- constant wearing its shape (D14).  Setting EDX:EAX instead reaches exactly
  -- the same four comparisons and **weakens nothing** — no exemption, no
  -- widened window, no gate to re-probe.
  -- ⇒ 🔑 A GATE THAT REFUSES A NEW PRE-STATE IS USUALLY NAMING A CHEAPER WAY TO
  -- BUILD IT.
  let want := c ^^^ delta
  let s := s.setReg .d .rax want
  s.setReg .d .rdx (want >>> 32)

def cmpxchg8bStates : List Cpu :=
  [ -- EQUAL, deliberately, at two different value pairs so the branch is not
    -- reached by one state.
    mkCmpxchg8b 0x5555555555555555 0x0F0F0F0F0F0F0F0F 0  0
  , mkCmpxchg8b 0xAAAAAAAAAAAAAAAA 0xF0F0F0F0F0F0F0F0 63 0
    -- UNEQUAL in the LOW half alone, and in the HIGH half alone.
  , mkCmpxchg8b 0x5555555555555555 0x0F0F0F0F0F0F0F0F 0  1
  , mkCmpxchg8b 0x5555555555555555 0x0F0F0F0F0F0F0F0F 0  (1 <<< 32) ]

def stringBoundaryStates : List Cpu :=
  [ -- DF clear: `…FF + 1` carries out of the byte, and out of the word at 0x7fff.
    mkStringPtr 0x5555555555555555 0x0F0F0F0F0F0F0F0F 0  0x1fff 0x7fff
    -- DF set: `…00 − 1` borrows.  Seed 64 sets DF and leaves the six arithmetic
    -- flags clear, exactly as `dfStates` does.
  , mkStringPtr 0xAAAAAAAAAAAAAAAA 0xF0F0F0F0F0F0F0F0 64 0x2000 0x8000 ]

/-- The pre-states for one vector: every adversarial pair on the diagonal and
its neighbours, the carry boundary, the two DF states, the two `addr32`
counter states, the two stack frames, the two string-pointer boundaries, the
four `cmpxchg8b` branch states, then a pseudo-random tail. -/
def preStates (seed : UInt64) (nRandom : Nat) : List Cpu :=
  let adv := adversarial
  let diag := adv.map (fun a => mkPre a a 0)
  let pairs := adv.zip (adv.rotateLeft 1) |>.map (fun (a, c) => mkPre a c 5)
  let pairs2 := adv.zip (adv.rotateLeft 7) |>.map (fun (a, c) => mkPre a c 63)
  let rs := randStream seed (2 * nRandom)
  let rnd := (rs.take nRandom).zip (rs.drop nRandom) |>.zipIdx.map
    (fun ((a, c), i) => mkPre a c i)
  diag ++ pairs ++ pairs2 ++ carryBoundary ++ dfStates ++ loopCounterStates
    ++ frameStates ++ stringBoundaryStates ++ cmpxchg8bStates ++ rnd

end X86.Tests
