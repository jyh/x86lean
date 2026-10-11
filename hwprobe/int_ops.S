/* hwprobe/int_ops.S — D330: one function per INTEGER form under test (ADCX, ADOX, MULX), so the bytes the processor
   executes are the assembler's encoding of the line written here, and `int_probe.c` refuses the run unless they are
   the bytes `mk_int_rows.py` declares (read back at each function's `_at` label).

   C signature: void i_X(struct iio *p), with
       struct iio { uint64_t a, b, d, f, r0, r1, fo; }      offsets 0 8 16 24 32 40 48
   On entry to the instruction under test:
       RAX = a  (ADCX/ADOX's destination)      RCX = b  (the register source)
       RBX = &p->b  (the memory source, so a memory form reads the same b)
       RDX = d  (MULX's implicit source)       R8 = R9 = a  (MULX's destinations, pre-filled: a is the canary)
       RFLAGS = the process's RFLAGS with its six arithmetic bits (0x8d5) replaced by f's
   On exit: r0 = RAX (ADCX/ADOX) or R8 (MULX, the high half / the same-destination register), r1 = R9 (MULX's low
   half), fo = RFLAGS, read immediately after the instruction. RBX is callee-saved and restored. */

#ifdef __APPLE__
#define SYM(x) _##x
#else
#define SYM(x) x
#endif

        .text

#define PRE                     \
        pushq %rbx;             \
        movq %rdi, %r11;        \
        movq 0(%r11), %rax;     \
        movq 8(%r11), %rcx;     \
        movq 16(%r11), %rdx;    \
        leaq 8(%r11), %rbx;     \
        movq %rax, %r8;         \
        movq %rax, %r9;         \
        pushfq;                 \
        popq %r10;              \
        andq $-0x8d6, %r10;     \
        movq 24(%r11), %rsi;    \
        andq $0x8d5, %rsi;      \
        orq %rsi, %r10;         \
        pushq %r10;             \
        popfq

#define POST_ADD                \
        pushfq;                 \
        popq %r10;              \
        movq %r10, 48(%r11);    \
        movq %rax, 32(%r11);    \
        popq %rbx;              \
        ret

#define POST_MUL                \
        pushfq;                 \
        popq %r10;              \
        movq %r10, 48(%r11);    \
        movq %r8, 32(%r11);     \
        movq %r9, 40(%r11);     \
        popq %rbx;              \
        ret

#define FN(name) .globl SYM(name); SYM(name):
#define AT(name) .globl SYM(name); SYM(name):

FN(i_adcxq_rr)
        PRE
AT(i_adcxq_rr_at)
        adcxq %rcx, %rax                /* 66 48 0f 38 f6 c1 */
        POST_ADD

FN(i_adcxq_rm)
        PRE
AT(i_adcxq_rm_at)
        adcxq (%rbx), %rax              /* 66 48 0f 38 f6 03 */
        POST_ADD

FN(i_adcxl_rr)
        PRE
AT(i_adcxl_rr_at)
        adcxl %ecx, %eax                /* 66 0f 38 f6 c1 */
        POST_ADD

FN(i_adcxl_rm)
        PRE
AT(i_adcxl_rm_at)
        adcxl (%rbx), %eax              /* 66 0f 38 f6 03 */
        POST_ADD

FN(i_adoxq_rr)
        PRE
AT(i_adoxq_rr_at)
        adoxq %rcx, %rax                /* f3 48 0f 38 f6 c1 */
        POST_ADD

FN(i_adoxq_rm)
        PRE
AT(i_adoxq_rm_at)
        adoxq (%rbx), %rax              /* f3 48 0f 38 f6 03 */
        POST_ADD

FN(i_adoxl_rr)
        PRE
AT(i_adoxl_rr_at)
        adoxl %ecx, %eax                /* f3 0f 38 f6 c1 */
        POST_ADD

FN(i_adoxl_rm)
        PRE
AT(i_adoxl_rm_at)
        adoxl (%rbx), %eax              /* f3 0f 38 f6 03 */
        POST_ADD

FN(i_mulxq_rr)
        PRE
AT(i_mulxq_rr_at)
        mulxq %rcx, %r9, %r8            /* c4 62 b3 f6 c1 : hi -> r8 (ModRM.reg), lo -> r9 (VEX.vvvv) */
        POST_MUL

FN(i_mulxq_rm)
        PRE
AT(i_mulxq_rm_at)
        mulxq (%rbx), %r9, %r8          /* c4 62 b3 f6 03 */
        POST_MUL

FN(i_mulxq_same)
        PRE
AT(i_mulxq_same_at)
        mulxq %rcx, %r8, %r8            /* c4 62 bb f6 c1 : both destinations r8 */
        POST_MUL

FN(i_mulxl_rr)
        PRE
AT(i_mulxl_rr_at)
        mulxl %ecx, %r9d, %r8d          /* c4 62 33 f6 c1 */
        POST_MUL

FN(i_mulxl_rm)
        PRE
AT(i_mulxl_rm_at)
        mulxl (%rbx), %r9d, %r8d        /* c4 62 33 f6 03 */
        POST_MUL

FN(i_mulxl_same)
        PRE
AT(i_mulxl_same_at)
        mulxl %ecx, %r8d, %r8d          /* c4 62 3b f6 c1 */
        POST_MUL
