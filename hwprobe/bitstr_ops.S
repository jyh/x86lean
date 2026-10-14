/* hwprobe/bitstr_ops.S — D333: one function per BIT-STRING form under test (BT/BTS/BTR/BTC with a memory base and a
   register offset), so the bytes the processor executes are the assembler's encoding of the line written here, and
   `bitstr_probe.c` refuses the run unless they are the bytes `mk_bitstr_rows.py` declares (read back at each `_at` label).

   C signature: void b_X(struct bio *p), with
       struct bio { uint64_t base, off, f, fo; }      offsets 0 8 16 24
   On entry to the instruction under test:
       RBX = base (a pointer into the middle of the probe's buffer)      RCX = off (the full 64-bit register, junk
       above the operand size included)      RFLAGS = the process's RFLAGS with its six arithmetic bits (0x8d5)
       replaced by f's
   On exit: fo = RFLAGS, read immediately after the instruction. Memory is read by the probe. RBX is callee-saved and
   restored. */

#ifdef __APPLE__
#define SYM(x) _##x
#else
#define SYM(x) x
#endif

        .text

#define PRE                     \
        pushq %rbx;             \
        movq %rdi, %r11;        \
        movq 0(%r11), %rbx;     \
        movq 8(%r11), %rcx;     \
        pushfq;                 \
        popq %r10;              \
        andq $-0x8d6, %r10;     \
        movq 16(%r11), %rsi;    \
        andq $0x8d5, %rsi;      \
        orq %rsi, %r10;         \
        pushq %r10;             \
        popfq

#define POST                    \
        pushfq;                 \
        popq %r10;              \
        movq %r10, 24(%r11);    \
        popq %rbx;              \
        ret

#define FN(name) .globl SYM(name); SYM(name):
#define AT(name) .globl SYM(name); SYM(name):

FN(b_btw_mr)
        PRE
AT(b_btw_mr_at)
        btw %cx, (%rbx)                 /* 66 0f a3 0b */
        POST

FN(b_btl_mr)
        PRE
AT(b_btl_mr_at)
        btl %ecx, (%rbx)                /* 0f a3 0b */
        POST

FN(b_btq_mr)
        PRE
AT(b_btq_mr_at)
        btq %rcx, (%rbx)                /* 48 0f a3 0b */
        POST

FN(b_btsw_mr)
        PRE
AT(b_btsw_mr_at)
        btsw %cx, (%rbx)                /* 66 0f ab 0b */
        POST

FN(b_btsl_mr)
        PRE
AT(b_btsl_mr_at)
        btsl %ecx, (%rbx)               /* 0f ab 0b */
        POST

FN(b_btsq_mr)
        PRE
AT(b_btsq_mr_at)
        btsq %rcx, (%rbx)               /* 48 0f ab 0b */
        POST

FN(b_btrw_mr)
        PRE
AT(b_btrw_mr_at)
        btrw %cx, (%rbx)                /* 66 0f b3 0b */
        POST

FN(b_btrl_mr)
        PRE
AT(b_btrl_mr_at)
        btrl %ecx, (%rbx)               /* 0f b3 0b */
        POST

FN(b_btrq_mr)
        PRE
AT(b_btrq_mr_at)
        btrq %rcx, (%rbx)               /* 48 0f b3 0b */
        POST

FN(b_btcw_mr)
        PRE
AT(b_btcw_mr_at)
        btcw %cx, (%rbx)                /* 66 0f bb 0b */
        POST

FN(b_btcl_mr)
        PRE
AT(b_btcl_mr_at)
        btcl %ecx, (%rbx)               /* 0f bb 0b */
        POST

FN(b_btcq_mr)
        PRE
AT(b_btcq_mr_at)
        btcq %rcx, (%rbx)               /* 48 0f bb 0b */
        POST
