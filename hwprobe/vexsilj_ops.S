/* hwprobe/vexsilj_ops.S — D379: `pabs{b,w,d}` and `pmulld`, legacy, VEX.128 and VEX.256, one function per form, in
   D371's frame (`vexsilf_ops.S`, copied below unchanged), so `vexsilf_probe.c` runs them against `vexsilj_rows.h`:
   YMM1 = the abs source (or pmulld's SRC1), YMM2 = VEX pmulld's SRC2, RBX = &mem[off], YMM3 = DEST.
   `mk_vexsilj_rows.py` declares each function's bytes; the probe refuses the run unless they are the ones assembled. */

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

FN(x_pabsb_r)
        PRE
AT(x_pabsb_r_at)
        pabsb %xmm1, %xmm3              /* 66 0f 38 1c d9 */
        POST

FN(x_pabsb_m)
        PRE
AT(x_pabsb_m_at)
        pabsb (%rbx), %xmm3             /* 66 0f 38 1c 1b */
        POST

FN(x_pabsw_r)
        PRE
AT(x_pabsw_r_at)
        pabsw %xmm1, %xmm3              /* 66 0f 38 1d d9 */
        POST

FN(x_pabsw_m)
        PRE
AT(x_pabsw_m_at)
        pabsw (%rbx), %xmm3             /* 66 0f 38 1d 1b */
        POST

FN(x_pabsd_r)
        PRE
AT(x_pabsd_r_at)
        pabsd %xmm1, %xmm3              /* 66 0f 38 1e d9 */
        POST

FN(x_pabsd_m)
        PRE
AT(x_pabsd_m_at)
        pabsd (%rbx), %xmm3             /* 66 0f 38 1e 1b */
        POST

FN(x_pmulld_r)
        PRE
AT(x_pmulld_r_at)
        pmulld %xmm1, %xmm3             /* 66 0f 38 40 d9 */
        POST

FN(x_pmulld_m)
        PRE
AT(x_pmulld_m_at)
        pmulld (%rbx), %xmm3            /* 66 0f 38 40 1b */
        POST

FN(x_vpabsb_r)
        PRE
AT(x_vpabsb_r_at)
        vpabsb %xmm1, %xmm3             /* c4 e2 79 1c d9 */
        POST

FN(x_vpabsb_m)
        PRE
AT(x_vpabsb_m_at)
        vpabsb (%rbx), %xmm3            /* c4 e2 79 1c 1b */
        POST

FN(x_vpabsw_r)
        PRE
AT(x_vpabsw_r_at)
        vpabsw %xmm1, %xmm3             /* c4 e2 79 1d d9 */
        POST

FN(x_vpabsw_m)
        PRE
AT(x_vpabsw_m_at)
        vpabsw (%rbx), %xmm3            /* c4 e2 79 1d 1b */
        POST

FN(x_vpabsd_r)
        PRE
AT(x_vpabsd_r_at)
        vpabsd %xmm1, %xmm3             /* c4 e2 79 1e d9 */
        POST

FN(x_vpabsd_m)
        PRE
AT(x_vpabsd_m_at)
        vpabsd (%rbx), %xmm3            /* c4 e2 79 1e 1b */
        POST

FN(x_vpmulld_r)
        PRE
AT(x_vpmulld_r_at)
        vpmulld %xmm2, %xmm1, %xmm3     /* c4 e2 71 40 da */
        POST

FN(x_vpmulld_m)
        PRE
AT(x_vpmulld_m_at)
        vpmulld (%rbx), %xmm1, %xmm3    /* c4 e2 71 40 1b */
        POST

FN(x_vpabsby_r)
        PRE
AT(x_vpabsby_r_at)
        vpabsb %ymm1, %ymm3             /* c4 e2 7d 1c d9 */
        POST

FN(x_vpabsby_m)
        PRE
AT(x_vpabsby_m_at)
        vpabsb (%rbx), %ymm3            /* c4 e2 7d 1c 1b */
        POST

FN(x_vpabswy_r)
        PRE
AT(x_vpabswy_r_at)
        vpabsw %ymm1, %ymm3             /* c4 e2 7d 1d d9 */
        POST

FN(x_vpabswy_m)
        PRE
AT(x_vpabswy_m_at)
        vpabsw (%rbx), %ymm3            /* c4 e2 7d 1d 1b */
        POST

FN(x_vpabsdy_r)
        PRE
AT(x_vpabsdy_r_at)
        vpabsd %ymm1, %ymm3             /* c4 e2 7d 1e d9 */
        POST

FN(x_vpabsdy_m)
        PRE
AT(x_vpabsdy_m_at)
        vpabsd (%rbx), %ymm3            /* c4 e2 7d 1e 1b */
        POST

FN(x_vpmulldy_r)
        PRE
AT(x_vpmulldy_r_at)
        vpmulld %ymm2, %ymm1, %ymm3     /* c4 e2 75 40 da */
        POST

FN(x_vpmulldy_m)
        PRE
AT(x_vpmulldy_m_at)
        vpmulld (%rbx), %ymm1, %ymm3    /* c4 e2 75 40 1b */
        POST
