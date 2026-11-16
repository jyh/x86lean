/* hwprobe/vexsilg_ops.S — D374: the VEX twins of eleven modelled packed-integer kinds, one function per form and
   length, in D361's frame (`vexsile_ops.S`, copied below unchanged), so `vexsile_probe.c` runs them against
   `vexsilg_rows.h`: YMM1 = SRC1 (VEX.vvvv), YMM2 = SRC2 (a register form), RBX = &mem[off] (a memory form), YMM3 = DEST.
   `mk_vexsilg_rows.py` declares each function's bytes; the probe refuses the run unless they are the ones assembled. */

#ifdef __APPLE__
#define SYM(x) _##x
#else
#define SYM(x) x
#endif

        .text

#define PRE                       \
        pushq %rbx;               \
        movq %rdi, %r11;          \
        leaq 256(%r11), %rbx;     \
        addq 240(%r11), %rbx;     \
        subq $8, %rsp;            \
        stmxcsr (%rsp);           \
        vmovdqu 0(%r11), %ymm1;   \
        vmovdqu 32(%r11), %ymm2;  \
        vmovdqu 64(%r11), %ymm3;  \
        ldmxcsr 208(%r11);        \
        movq 224(%r11), %rax;     \
        pushfq;                   \
        popq %r10;                \
        andq $-0x8d6, %r10;       \
        movq 192(%r11), %rsi;     \
        andq $0x8d5, %rsi;        \
        orq %rsi, %r10;           \
        pushq %r10;               \
        popfq

#define POST                      \
        pushfq;                   \
        popq %r10;                \
        movq %r10, 200(%r11);     \
        stmxcsr 216(%r11);        \
        movq %rax, 232(%r11);     \
        vmovdqu %ymm1, 96(%r11);  \
        vmovdqu %ymm2, 128(%r11); \
        vmovdqu %ymm3, 160(%r11); \
        ldmxcsr (%rsp);           \
        addq $8, %rsp;            \
        vzeroupper;               \
        popq %rbx;                \
        ret

#define FN(name) .globl SYM(name); SYM(name):
#define AT(name) .globl SYM(name); SYM(name):

FN(x_vpaddsw128_r)
        PRE
AT(x_vpaddsw128_r_at)
        vpaddsw %xmm2, %xmm1, %xmm3     /* c5 f1 ed da */
        POST

FN(x_vpaddsw128_m)
        PRE
AT(x_vpaddsw128_m_at)
        vpaddsw (%rbx), %xmm1, %xmm3    /* c5 f1 ed 1b */
        POST

FN(x_vpaddsw256_r)
        PRE
AT(x_vpaddsw256_r_at)
        vpaddsw %ymm2, %ymm1, %ymm3     /* c5 f5 ed da */
        POST

FN(x_vpaddsw256_m)
        PRE
AT(x_vpaddsw256_m_at)
        vpaddsw (%rbx), %ymm1, %ymm3    /* c5 f5 ed 1b */
        POST

FN(x_vpmaxsw128_r)
        PRE
AT(x_vpmaxsw128_r_at)
        vpmaxsw %xmm2, %xmm1, %xmm3     /* c5 f1 ee da */
        POST

FN(x_vpmaxsw128_m)
        PRE
AT(x_vpmaxsw128_m_at)
        vpmaxsw (%rbx), %xmm1, %xmm3    /* c5 f1 ee 1b */
        POST

FN(x_vpmaxsw256_r)
        PRE
AT(x_vpmaxsw256_r_at)
        vpmaxsw %ymm2, %ymm1, %ymm3     /* c5 f5 ee da */
        POST

FN(x_vpmaxsw256_m)
        PRE
AT(x_vpmaxsw256_m_at)
        vpmaxsw (%rbx), %ymm1, %ymm3    /* c5 f5 ee 1b */
        POST

FN(x_vpminsw128_r)
        PRE
AT(x_vpminsw128_r_at)
        vpminsw %xmm2, %xmm1, %xmm3     /* c5 f1 ea da */
        POST

FN(x_vpminsw128_m)
        PRE
AT(x_vpminsw128_m_at)
        vpminsw (%rbx), %xmm1, %xmm3    /* c5 f1 ea 1b */
        POST

FN(x_vpminsw256_r)
        PRE
AT(x_vpminsw256_r_at)
        vpminsw %ymm2, %ymm1, %ymm3     /* c5 f5 ea da */
        POST

FN(x_vpminsw256_m)
        PRE
AT(x_vpminsw256_m_at)
        vpminsw (%rbx), %ymm1, %ymm3    /* c5 f5 ea 1b */
        POST

FN(x_vpsubusb128_r)
        PRE
AT(x_vpsubusb128_r_at)
        vpsubusb %xmm2, %xmm1, %xmm3    /* c5 f1 d8 da */
        POST

FN(x_vpsubusb128_m)
        PRE
AT(x_vpsubusb128_m_at)
        vpsubusb (%rbx), %xmm1, %xmm3   /* c5 f1 d8 1b */
        POST

FN(x_vpsubusb256_r)
        PRE
AT(x_vpsubusb256_r_at)
        vpsubusb %ymm2, %ymm1, %ymm3    /* c5 f5 d8 da */
        POST

FN(x_vpsubusb256_m)
        PRE
AT(x_vpsubusb256_m_at)
        vpsubusb (%rbx), %ymm1, %ymm3   /* c5 f5 d8 1b */
        POST

FN(x_vpsadbw128_r)
        PRE
AT(x_vpsadbw128_r_at)
        vpsadbw %xmm2, %xmm1, %xmm3     /* c5 f1 f6 da */
        POST

FN(x_vpsadbw128_m)
        PRE
AT(x_vpsadbw128_m_at)
        vpsadbw (%rbx), %xmm1, %xmm3    /* c5 f1 f6 1b */
        POST

FN(x_vpsadbw256_r)
        PRE
AT(x_vpsadbw256_r_at)
        vpsadbw %ymm2, %ymm1, %ymm3     /* c5 f5 f6 da */
        POST

FN(x_vpsadbw256_m)
        PRE
AT(x_vpsadbw256_m_at)
        vpsadbw (%rbx), %ymm1, %ymm3    /* c5 f5 f6 1b */
        POST

FN(x_vpmullw128_r)
        PRE
AT(x_vpmullw128_r_at)
        vpmullw %xmm2, %xmm1, %xmm3     /* c5 f1 d5 da */
        POST

FN(x_vpmullw128_m)
        PRE
AT(x_vpmullw128_m_at)
        vpmullw (%rbx), %xmm1, %xmm3    /* c5 f1 d5 1b */
        POST

FN(x_vpmullw256_r)
        PRE
AT(x_vpmullw256_r_at)
        vpmullw %ymm2, %ymm1, %ymm3     /* c5 f5 d5 da */
        POST

FN(x_vpmullw256_m)
        PRE
AT(x_vpmullw256_m_at)
        vpmullw (%rbx), %ymm1, %ymm3    /* c5 f5 d5 1b */
        POST

FN(x_vpavgb128_r)
        PRE
AT(x_vpavgb128_r_at)
        vpavgb %xmm2, %xmm1, %xmm3      /* c5 f1 e0 da */
        POST

FN(x_vpavgb128_m)
        PRE
AT(x_vpavgb128_m_at)
        vpavgb (%rbx), %xmm1, %xmm3     /* c5 f1 e0 1b */
        POST

FN(x_vpavgb256_r)
        PRE
AT(x_vpavgb256_r_at)
        vpavgb %ymm2, %ymm1, %ymm3      /* c5 f5 e0 da */
        POST

FN(x_vpavgb256_m)
        PRE
AT(x_vpavgb256_m_at)
        vpavgb (%rbx), %ymm1, %ymm3     /* c5 f5 e0 1b */
        POST

FN(x_vpsubusw128_r)
        PRE
AT(x_vpsubusw128_r_at)
        vpsubusw %xmm2, %xmm1, %xmm3    /* c5 f1 d9 da */
        POST

FN(x_vpsubusw128_m)
        PRE
AT(x_vpsubusw128_m_at)
        vpsubusw (%rbx), %xmm1, %xmm3   /* c5 f1 d9 1b */
        POST

FN(x_vpsubusw256_r)
        PRE
AT(x_vpsubusw256_r_at)
        vpsubusw %ymm2, %ymm1, %ymm3    /* c5 f5 d9 da */
        POST

FN(x_vpsubusw256_m)
        PRE
AT(x_vpsubusw256_m_at)
        vpsubusw (%rbx), %ymm1, %ymm3   /* c5 f5 d9 1b */
        POST

FN(x_vpmulhw128_r)
        PRE
AT(x_vpmulhw128_r_at)
        vpmulhw %xmm2, %xmm1, %xmm3     /* c5 f1 e5 da */
        POST

FN(x_vpmulhw128_m)
        PRE
AT(x_vpmulhw128_m_at)
        vpmulhw (%rbx), %xmm1, %xmm3    /* c5 f1 e5 1b */
        POST

FN(x_vpmulhw256_r)
        PRE
AT(x_vpmulhw256_r_at)
        vpmulhw %ymm2, %ymm1, %ymm3     /* c5 f5 e5 da */
        POST

FN(x_vpmulhw256_m)
        PRE
AT(x_vpmulhw256_m_at)
        vpmulhw (%rbx), %ymm1, %ymm3    /* c5 f5 e5 1b */
        POST

FN(x_vpmulhuw128_r)
        PRE
AT(x_vpmulhuw128_r_at)
        vpmulhuw %xmm2, %xmm1, %xmm3    /* c5 f1 e4 da */
        POST

FN(x_vpmulhuw128_m)
        PRE
AT(x_vpmulhuw128_m_at)
        vpmulhuw (%rbx), %xmm1, %xmm3   /* c5 f1 e4 1b */
        POST

FN(x_vpmulhuw256_r)
        PRE
AT(x_vpmulhuw256_r_at)
        vpmulhuw %ymm2, %ymm1, %ymm3    /* c5 f5 e4 da */
        POST

FN(x_vpmulhuw256_m)
        PRE
AT(x_vpmulhuw256_m_at)
        vpmulhuw (%rbx), %ymm1, %ymm3   /* c5 f5 e4 1b */
        POST

FN(x_vpmuludq128_r)
        PRE
AT(x_vpmuludq128_r_at)
        vpmuludq %xmm2, %xmm1, %xmm3    /* c5 f1 f4 da */
        POST

FN(x_vpmuludq128_m)
        PRE
AT(x_vpmuludq128_m_at)
        vpmuludq (%rbx), %xmm1, %xmm3   /* c5 f1 f4 1b */
        POST

FN(x_vpmuludq256_r)
        PRE
AT(x_vpmuludq256_r_at)
        vpmuludq %ymm2, %ymm1, %ymm3    /* c5 f5 f4 da */
        POST

FN(x_vpmuludq256_m)
        PRE
AT(x_vpmuludq256_m_at)
        vpmuludq (%rbx), %ymm1, %ymm3   /* c5 f5 f4 1b */
        POST
