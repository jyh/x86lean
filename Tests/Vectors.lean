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
  { regs := { rax := a, rcx := c, rbx := 0x2000, rsp := 0x8000 }
    flags := f
    mem := mem
    rip := 0x400000
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

/-- The pre-states for one vector: every adversarial pair on the diagonal and
its neighbours, the carry boundary, then a pseudo-random tail. -/
def preStates (seed : UInt64) (nRandom : Nat) : List Cpu :=
  let adv := adversarial
  let diag := adv.map (fun a => mkPre a a 0)
  let pairs := adv.zip (adv.rotateLeft 1) |>.map (fun (a, c) => mkPre a c 5)
  let pairs2 := adv.zip (adv.rotateLeft 7) |>.map (fun (a, c) => mkPre a c 63)
  let rs := randStream seed (2 * nRandom)
  let rnd := (rs.take nRandom).zip (rs.drop nRandom) |>.zipIdx.map
    (fun ((a, c), i) => mkPre a c i)
  diag ++ pairs ++ pairs2 ++ carryBoundary ++ rnd

end X86.Tests
