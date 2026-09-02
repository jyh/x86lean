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
