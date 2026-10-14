/* hwprobe/int_ops.S — D330: one function per INTEGER form under test (ADCX, ADOX, MULX; D334 adds the W1c forms at
   the end), so the bytes the processor executes are the assembler's encoding of the line written here, and
   `int_probe.c` refuses the run unless they are the bytes `mk_int_rows.py` declares (read back at each function's
   `_at` label).

   C signature: void i_X(struct iio *p), with
       struct iio { uint64_t a, b, d, f, r0, r1, fo; }      offsets 0 8 16 24 32 40 48
   On entry to the instruction under test:
       RAX = a  (ADCX/ADOX's destination)      RCX = b  (the register source)
       RBX = &p->b  (the memory source, so a memory form reads the same b)
       RDX = d  (MULX's implicit source)       R8 = R9 = a  (MULX's destinations, pre-filled: a is the canary)
       RFLAGS = the process's RFLAGS with its six arithmetic bits (0x8d5) replaced by f's
   On exit: r0 = RAX (ADCX/ADOX) or R8 (MULX, the high half / the same-destination register), r1 = R9 (MULX's low
   half), fo = RFLAGS, read immediately after the instruction. RBX is callee-saved and restored.
   D334 (W1c): every BMI form writes R8 (r0) and leaves R9 (r1, the canary) alone; RDX is the VEX.vvvv source (ANDN's
   SRC1, PDEP/PEXT's value, BEXTR's control, BZHI's index) and RCX or [RBX] the r/m source. MOVNTI stores RAX to [RBX],
   and r0 is that quadword read back after SFENCE (POST_MEM). */

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

/* D334: MOVNTI's destination is memory. RFLAGS is read first, then SFENCE orders the non-temporal store before the
   ordinary load that reads the quadword back (SDM Vol. 2B MOVNTI: the WC protocol is weakly ordered), and r0 is that
   quadword; r1 is R9, which no operand names. */
#define POST_MEM                \
        pushfq;                 \
        popq %r10;              \
        movq %r10, 48(%r11);    \
        sfence;                 \
        movq (%rbx), %r10;      \
        movq %r10, 32(%r11);    \
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

/* ══ D334 (W1c): the BMI1/BMI2 forms x86isa refuses, and MOVNTI. Destination R8 (R8D); R9 is named by no operand and
   must still hold the canary. ══ */

FN(i_andnq_rr)
        PRE
AT(i_andnq_rr_at)
        andnq %rcx, %rdx, %r8           /* r8 := ~RDX & RCX */
        POST_MUL

FN(i_andnq_rm)
        PRE
AT(i_andnq_rm_at)
        andnq (%rbx), %rdx, %r8         /* r8 := ~RDX & [RBX] */
        POST_MUL

FN(i_andnl_rr)
        PRE
AT(i_andnl_rr_at)
        andnl %ecx, %edx, %r8d          /* r8 := ~RDX & RCX */
        POST_MUL

FN(i_andnl_rm)
        PRE
AT(i_andnl_rm_at)
        andnl (%rbx), %edx, %r8d        /* r8 := ~RDX & [RBX] */
        POST_MUL

FN(i_bextrq_rr)
        PRE
AT(i_bextrq_rr_at)
        bextrq %rdx, %rcx, %r8          /* source RCX, control RDX */
        POST_MUL

FN(i_bextrq_rm)
        PRE
AT(i_bextrq_rm_at)
        bextrq %rdx, (%rbx), %r8        /* source [RBX], control RDX */
        POST_MUL

FN(i_bextrl_rr)
        PRE
AT(i_bextrl_rr_at)
        bextrl %edx, %ecx, %r8d         /* source RCX, control RDX */
        POST_MUL

FN(i_bextrl_rm)
        PRE
AT(i_bextrl_rm_at)
        bextrl %edx, (%rbx), %r8d       /* source [RBX], control RDX */
        POST_MUL

FN(i_bzhiq_rr)
        PRE
AT(i_bzhiq_rr_at)
        bzhiq %rdx, %rcx, %r8           /* source RCX, control RDX */
        POST_MUL

FN(i_bzhiq_rm)
        PRE
AT(i_bzhiq_rm_at)
        bzhiq %rdx, (%rbx), %r8         /* source [RBX], control RDX */
        POST_MUL

FN(i_bzhil_rr)
        PRE
AT(i_bzhil_rr_at)
        bzhil %edx, %ecx, %r8d          /* source RCX, control RDX */
        POST_MUL

FN(i_bzhil_rm)
        PRE
AT(i_bzhil_rm_at)
        bzhil %edx, (%rbx), %r8d        /* source [RBX], control RDX */
        POST_MUL

FN(i_blsmskq_rr)
        PRE
AT(i_blsmskq_rr_at)
        blsmskq %rcx, %r8               /* source RCX */
        POST_MUL

FN(i_blsmskq_rm)
        PRE
AT(i_blsmskq_rm_at)
        blsmskq (%rbx), %r8             /* source [RBX] */
        POST_MUL

FN(i_blsmskl_rr)
        PRE
AT(i_blsmskl_rr_at)
        blsmskl %ecx, %r8d              /* source RCX */
        POST_MUL

FN(i_blsmskl_rm)
        PRE
AT(i_blsmskl_rm_at)
        blsmskl (%rbx), %r8d            /* source [RBX] */
        POST_MUL

FN(i_blsrq_rr)
        PRE
AT(i_blsrq_rr_at)
        blsrq %rcx, %r8                 /* source RCX */
        POST_MUL

FN(i_blsrq_rm)
        PRE
AT(i_blsrq_rm_at)
        blsrq (%rbx), %r8               /* source [RBX] */
        POST_MUL

FN(i_blsrl_rr)
        PRE
AT(i_blsrl_rr_at)
        blsrl %ecx, %r8d                /* source RCX */
        POST_MUL

FN(i_blsrl_rm)
        PRE
AT(i_blsrl_rm_at)
        blsrl (%rbx), %r8d              /* source [RBX] */
        POST_MUL

FN(i_pdepq_rr)
        PRE
AT(i_pdepq_rr_at)
        pdepq %rcx, %rdx, %r8           /* value RDX, mask RCX */
        POST_MUL

FN(i_pdepq_rm)
        PRE
AT(i_pdepq_rm_at)
        pdepq (%rbx), %rdx, %r8         /* value RDX, mask [RBX] */
        POST_MUL

FN(i_pdepl_rr)
        PRE
AT(i_pdepl_rr_at)
        pdepl %ecx, %edx, %r8d          /* value RDX, mask RCX */
        POST_MUL

FN(i_pdepl_rm)
        PRE
AT(i_pdepl_rm_at)
        pdepl (%rbx), %edx, %r8d        /* value RDX, mask [RBX] */
        POST_MUL

FN(i_pextq_rr)
        PRE
AT(i_pextq_rr_at)
        pextq %rcx, %rdx, %r8           /* value RDX, mask RCX */
        POST_MUL

FN(i_pextq_rm)
        PRE
AT(i_pextq_rm_at)
        pextq (%rbx), %rdx, %r8         /* value RDX, mask [RBX] */
        POST_MUL

FN(i_pextl_rr)
        PRE
AT(i_pextl_rr_at)
        pextl %ecx, %edx, %r8d          /* value RDX, mask RCX */
        POST_MUL

FN(i_pextl_rm)
        PRE
AT(i_pextl_rm_at)
        pextl (%rbx), %edx, %r8d        /* value RDX, mask [RBX] */
        POST_MUL

FN(i_rorxq_rr_i0)
        PRE
AT(i_rorxq_rr_i0_at)
        rorxq $0, %rcx, %r8             /* source RCX */
        POST_MUL

FN(i_rorxq_rr_i1)
        PRE
AT(i_rorxq_rr_i1_at)
        rorxq $1, %rcx, %r8             /* source RCX */
        POST_MUL

FN(i_rorxq_rr_i63)
        PRE
AT(i_rorxq_rr_i63_at)
        rorxq $63, %rcx, %r8            /* source RCX */
        POST_MUL

FN(i_rorxq_rr_i69)
        PRE
AT(i_rorxq_rr_i69_at)
        rorxq $69, %rcx, %r8            /* source RCX */
        POST_MUL

FN(i_rorxq_rm_i7)
        PRE
AT(i_rorxq_rm_i7_at)
        rorxq $7, (%rbx), %r8           /* source [RBX] */
        POST_MUL

FN(i_rorxl_rr_i0)
        PRE
AT(i_rorxl_rr_i0_at)
        rorxl $0, %ecx, %r8d            /* source RCX */
        POST_MUL

FN(i_rorxl_rr_i1)
        PRE
AT(i_rorxl_rr_i1_at)
        rorxl $1, %ecx, %r8d            /* source RCX */
        POST_MUL

FN(i_rorxl_rr_i31)
        PRE
AT(i_rorxl_rr_i31_at)
        rorxl $31, %ecx, %r8d           /* source RCX */
        POST_MUL

FN(i_rorxl_rr_i37)
        PRE
AT(i_rorxl_rr_i37_at)
        rorxl $37, %ecx, %r8d           /* source RCX */
        POST_MUL

FN(i_rorxl_rm_i7)
        PRE
AT(i_rorxl_rm_i7_at)
        rorxl $7, (%rbx), %r8d          /* source [RBX] */
        POST_MUL

FN(i_movntiq_mr)
        PRE
AT(i_movntiq_mr_at)
        movntiq %rax, (%rbx)            /* store RAX to [RBX] */
        POST_MEM

FN(i_movntil_mr)
        PRE
AT(i_movntil_mr_at)
        movntil %eax, (%rbx)            /* store EAX to [RBX] */
        POST_MEM
