/* hwprobe/vexsilk_ops.S — D384: the VEX twins of wave E's three kinds (vpsubsw vpavgw vpmuldq), one function per form and
   length, in D361's frame (`vexsile_ops.S`, copied below unchanged), so `vexsile_probe.c` runs them against
   `vexsilk_rows.h`: YMM1 = SRC1 (VEX.vvvv), YMM2 = SRC2 (a register form), RBX = &mem[off] (a memory form), YMM3 = DEST.
   `mk_vexsilk_rows.py` declares each function's bytes; the probe refuses the run unless they are the ones assembled. */

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

FN(x_vpsubsw128_r)
        PRE
AT(x_vpsubsw128_r_at)
        vpsubsw %xmm2, %xmm1, %xmm3     /* c5 f1 e9 da */
        POST

FN(x_vpsubsw128_m)
        PRE
AT(x_vpsubsw128_m_at)
        vpsubsw (%rbx), %xmm1, %xmm3    /* c5 f1 e9 1b */
        POST

FN(x_vpsubsw256_r)
        PRE
AT(x_vpsubsw256_r_at)
        vpsubsw %ymm2, %ymm1, %ymm3     /* c5 f5 e9 da */
        POST

FN(x_vpsubsw256_m)
        PRE
AT(x_vpsubsw256_m_at)
        vpsubsw (%rbx), %ymm1, %ymm3    /* c5 f5 e9 1b */
        POST

FN(x_vpavgw128_r)
        PRE
AT(x_vpavgw128_r_at)
        vpavgw %xmm2, %xmm1, %xmm3      /* c5 f1 e3 da */
        POST

FN(x_vpavgw128_m)
        PRE
AT(x_vpavgw128_m_at)
        vpavgw (%rbx), %xmm1, %xmm3     /* c5 f1 e3 1b */
        POST

FN(x_vpavgw256_r)
        PRE
AT(x_vpavgw256_r_at)
        vpavgw %ymm2, %ymm1, %ymm3      /* c5 f5 e3 da */
        POST

FN(x_vpavgw256_m)
        PRE
AT(x_vpavgw256_m_at)
        vpavgw (%rbx), %ymm1, %ymm3     /* c5 f5 e3 1b */
        POST

FN(x_vpmuldq128_r)
        PRE
AT(x_vpmuldq128_r_at)
        vpmuldq %xmm2, %xmm1, %xmm3     /* c4 e2 71 28 da */
        POST

FN(x_vpmuldq128_m)
        PRE
AT(x_vpmuldq128_m_at)
        vpmuldq (%rbx), %xmm1, %xmm3    /* c4 e2 71 28 1b */
        POST

FN(x_vpmuldq256_r)
        PRE
AT(x_vpmuldq256_r_at)
        vpmuldq %ymm2, %ymm1, %ymm3     /* c4 e2 75 28 da */
        POST

FN(x_vpmuldq256_m)
        PRE
AT(x_vpmuldq256_m_at)
        vpmuldq (%rbx), %ymm1, %ymm3    /* c4 e2 75 28 1b */
        POST
