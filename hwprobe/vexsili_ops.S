/* hwprobe/vexsili_ops.S — D376: `movntdqa` and the VEX half-moves, one function per form, in D371's frame
   (`vexsilf_ops.S`, copied below unchanged), so `vexsilf_probe.c` runs them against `vexsili_rows.h`: YMM1 = SRC1 (a
   load's VEX.vvvv) or SRC (a store's), RBX = &mem[off], YMM3 = DEST. `mk_vexsili_rows.py` declares each function's
   bytes; the probe refuses the run unless they are the ones assembled. */

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

FN(x_movntdqa)
        PRE
AT(x_movntdqa_at)
        movntdqa (%rbx), %xmm3          /* 66 0f 38 2a 1b */
        POST

FN(x_vmovhps_ld)
        PRE
AT(x_vmovhps_ld_at)
        vmovhps (%rbx), %xmm1, %xmm3    /* c5 f0 16 1b */
        POST

FN(x_vmovhps_st)
        PRE
AT(x_vmovhps_st_at)
        vmovhps %xmm1, (%rbx)           /* c5 f8 17 0b */
        POST

FN(x_vmovhpd_ld)
        PRE
AT(x_vmovhpd_ld_at)
        vmovhpd (%rbx), %xmm1, %xmm3    /* c5 f1 16 1b */
        POST

FN(x_vmovhpd_st)
        PRE
AT(x_vmovhpd_st_at)
        vmovhpd %xmm1, (%rbx)           /* c5 f9 17 0b */
        POST

FN(x_vmovlps_ld)
        PRE
AT(x_vmovlps_ld_at)
        vmovlps (%rbx), %xmm1, %xmm3    /* c5 f0 12 1b */
        POST

FN(x_vmovlps_st)
        PRE
AT(x_vmovlps_st_at)
        vmovlps %xmm1, (%rbx)           /* c5 f8 13 0b */
        POST

FN(x_vmovlpd_ld)
        PRE
AT(x_vmovlpd_ld_at)
        vmovlpd (%rbx), %xmm1, %xmm3    /* c5 f1 12 1b */
        POST

FN(x_vmovlpd_st)
        PRE
AT(x_vmovlpd_st_at)
        vmovlpd %xmm1, (%rbx)           /* c5 f9 13 0b */
        POST
