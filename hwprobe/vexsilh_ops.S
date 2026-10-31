/* hwprobe/vexsilh_ops.S — D375: the VEX.256 128-bit lane insert and extract, one function per (mnemonic, shape, imm8),
   in D371's frame (`vexsilf_ops.S`, copied below unchanged), so `vexsilf_probe.c` runs them against `vexsilh_rows.h`:
   YMM1 = SRC1 (an insert's VEX.vvvv) or SRC (an extract's ModRM.reg), YMM2 = an insert's xmm source, RBX = &mem[off],
   YMM3 = DEST. `mk_vexsilh_rows.py` declares each function's bytes; the probe refuses the run unless they are the ones
   assembled. */

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

FN(x_vinserti128_r_i0)
        PRE
AT(x_vinserti128_r_i0_at)
        vinserti128 $0, %xmm2, %ymm1, %ymm3     /* c4 e3 75 38 da 00 */
        POST

FN(x_vinserti128_r_i1)
        PRE
AT(x_vinserti128_r_i1_at)
        vinserti128 $1, %xmm2, %ymm1, %ymm3     /* c4 e3 75 38 da 01 */
        POST

FN(x_vinserti128_r_i2)
        PRE
AT(x_vinserti128_r_i2_at)
        vinserti128 $2, %xmm2, %ymm1, %ymm3     /* c4 e3 75 38 da 02 */
        POST

FN(x_vinserti128_r_i3)
        PRE
AT(x_vinserti128_r_i3_at)
        vinserti128 $3, %xmm2, %ymm1, %ymm3     /* c4 e3 75 38 da 03 */
        POST

FN(x_vinserti128_r_ife)
        PRE
AT(x_vinserti128_r_ife_at)
        vinserti128 $254, %xmm2, %ymm1, %ymm3   /* c4 e3 75 38 da fe */
        POST

FN(x_vinserti128_r_iff)
        PRE
AT(x_vinserti128_r_iff_at)
        vinserti128 $255, %xmm2, %ymm1, %ymm3   /* c4 e3 75 38 da ff */
        POST

FN(x_vinserti128_m_i0)
        PRE
AT(x_vinserti128_m_i0_at)
        vinserti128 $0, (%rbx), %ymm1, %ymm3    /* c4 e3 75 38 1b 00 */
        POST

FN(x_vinserti128_m_i1)
        PRE
AT(x_vinserti128_m_i1_at)
        vinserti128 $1, (%rbx), %ymm1, %ymm3    /* c4 e3 75 38 1b 01 */
        POST

FN(x_vinserti128_m_i2)
        PRE
AT(x_vinserti128_m_i2_at)
        vinserti128 $2, (%rbx), %ymm1, %ymm3    /* c4 e3 75 38 1b 02 */
        POST

FN(x_vinserti128_m_i3)
        PRE
AT(x_vinserti128_m_i3_at)
        vinserti128 $3, (%rbx), %ymm1, %ymm3    /* c4 e3 75 38 1b 03 */
        POST

FN(x_vinserti128_m_ife)
        PRE
AT(x_vinserti128_m_ife_at)
        vinserti128 $254, (%rbx), %ymm1, %ymm3  /* c4 e3 75 38 1b fe */
        POST

FN(x_vinserti128_m_iff)
        PRE
AT(x_vinserti128_m_iff_at)
        vinserti128 $255, (%rbx), %ymm1, %ymm3  /* c4 e3 75 38 1b ff */
        POST

FN(x_vinsertf128_r_i0)
        PRE
AT(x_vinsertf128_r_i0_at)
        vinsertf128 $0, %xmm2, %ymm1, %ymm3     /* c4 e3 75 18 da 00 */
        POST

FN(x_vinsertf128_r_i1)
        PRE
AT(x_vinsertf128_r_i1_at)
        vinsertf128 $1, %xmm2, %ymm1, %ymm3     /* c4 e3 75 18 da 01 */
        POST

FN(x_vinsertf128_r_i2)
        PRE
AT(x_vinsertf128_r_i2_at)
        vinsertf128 $2, %xmm2, %ymm1, %ymm3     /* c4 e3 75 18 da 02 */
        POST

FN(x_vinsertf128_r_i3)
        PRE
AT(x_vinsertf128_r_i3_at)
        vinsertf128 $3, %xmm2, %ymm1, %ymm3     /* c4 e3 75 18 da 03 */
        POST

FN(x_vinsertf128_r_ife)
        PRE
AT(x_vinsertf128_r_ife_at)
        vinsertf128 $254, %xmm2, %ymm1, %ymm3   /* c4 e3 75 18 da fe */
        POST

FN(x_vinsertf128_r_iff)
        PRE
AT(x_vinsertf128_r_iff_at)
        vinsertf128 $255, %xmm2, %ymm1, %ymm3   /* c4 e3 75 18 da ff */
        POST

FN(x_vinsertf128_m_i0)
        PRE
AT(x_vinsertf128_m_i0_at)
        vinsertf128 $0, (%rbx), %ymm1, %ymm3    /* c4 e3 75 18 1b 00 */
        POST

FN(x_vinsertf128_m_i1)
        PRE
AT(x_vinsertf128_m_i1_at)
        vinsertf128 $1, (%rbx), %ymm1, %ymm3    /* c4 e3 75 18 1b 01 */
        POST

FN(x_vinsertf128_m_i2)
        PRE
AT(x_vinsertf128_m_i2_at)
        vinsertf128 $2, (%rbx), %ymm1, %ymm3    /* c4 e3 75 18 1b 02 */
        POST

FN(x_vinsertf128_m_i3)
        PRE
AT(x_vinsertf128_m_i3_at)
        vinsertf128 $3, (%rbx), %ymm1, %ymm3    /* c4 e3 75 18 1b 03 */
        POST

FN(x_vinsertf128_m_ife)
        PRE
AT(x_vinsertf128_m_ife_at)
        vinsertf128 $254, (%rbx), %ymm1, %ymm3  /* c4 e3 75 18 1b fe */
        POST

FN(x_vinsertf128_m_iff)
        PRE
AT(x_vinsertf128_m_iff_at)
        vinsertf128 $255, (%rbx), %ymm1, %ymm3  /* c4 e3 75 18 1b ff */
        POST

FN(x_vextracti128_r_i0)
        PRE
AT(x_vextracti128_r_i0_at)
        vextracti128 $0, %ymm1, %xmm3           /* c4 e3 7d 39 cb 00 */
        POST

FN(x_vextracti128_r_i1)
        PRE
AT(x_vextracti128_r_i1_at)
        vextracti128 $1, %ymm1, %xmm3           /* c4 e3 7d 39 cb 01 */
        POST

FN(x_vextracti128_r_i2)
        PRE
AT(x_vextracti128_r_i2_at)
        vextracti128 $2, %ymm1, %xmm3           /* c4 e3 7d 39 cb 02 */
        POST

FN(x_vextracti128_r_i3)
        PRE
AT(x_vextracti128_r_i3_at)
        vextracti128 $3, %ymm1, %xmm3           /* c4 e3 7d 39 cb 03 */
        POST

FN(x_vextracti128_r_ife)
        PRE
AT(x_vextracti128_r_ife_at)
        vextracti128 $254, %ymm1, %xmm3         /* c4 e3 7d 39 cb fe */
        POST

FN(x_vextracti128_r_iff)
        PRE
AT(x_vextracti128_r_iff_at)
        vextracti128 $255, %ymm1, %xmm3         /* c4 e3 7d 39 cb ff */
        POST

FN(x_vextracti128_m_i0)
        PRE
AT(x_vextracti128_m_i0_at)
        vextracti128 $0, %ymm1, (%rbx)          /* c4 e3 7d 39 0b 00 */
        POST

FN(x_vextracti128_m_i1)
        PRE
AT(x_vextracti128_m_i1_at)
        vextracti128 $1, %ymm1, (%rbx)          /* c4 e3 7d 39 0b 01 */
        POST

FN(x_vextracti128_m_i2)
        PRE
AT(x_vextracti128_m_i2_at)
        vextracti128 $2, %ymm1, (%rbx)          /* c4 e3 7d 39 0b 02 */
        POST

FN(x_vextracti128_m_i3)
        PRE
AT(x_vextracti128_m_i3_at)
        vextracti128 $3, %ymm1, (%rbx)          /* c4 e3 7d 39 0b 03 */
        POST

FN(x_vextracti128_m_ife)
        PRE
AT(x_vextracti128_m_ife_at)
        vextracti128 $254, %ymm1, (%rbx)        /* c4 e3 7d 39 0b fe */
        POST

FN(x_vextracti128_m_iff)
        PRE
AT(x_vextracti128_m_iff_at)
        vextracti128 $255, %ymm1, (%rbx)        /* c4 e3 7d 39 0b ff */
        POST

FN(x_vextractf128_r_i0)
        PRE
AT(x_vextractf128_r_i0_at)
        vextractf128 $0, %ymm1, %xmm3           /* c4 e3 7d 19 cb 00 */
        POST

FN(x_vextractf128_r_i1)
        PRE
AT(x_vextractf128_r_i1_at)
        vextractf128 $1, %ymm1, %xmm3           /* c4 e3 7d 19 cb 01 */
        POST

FN(x_vextractf128_r_i2)
        PRE
AT(x_vextractf128_r_i2_at)
        vextractf128 $2, %ymm1, %xmm3           /* c4 e3 7d 19 cb 02 */
        POST

FN(x_vextractf128_r_i3)
        PRE
AT(x_vextractf128_r_i3_at)
        vextractf128 $3, %ymm1, %xmm3           /* c4 e3 7d 19 cb 03 */
        POST

FN(x_vextractf128_r_ife)
        PRE
AT(x_vextractf128_r_ife_at)
        vextractf128 $254, %ymm1, %xmm3         /* c4 e3 7d 19 cb fe */
        POST

FN(x_vextractf128_r_iff)
        PRE
AT(x_vextractf128_r_iff_at)
        vextractf128 $255, %ymm1, %xmm3         /* c4 e3 7d 19 cb ff */
        POST

FN(x_vextractf128_m_i0)
        PRE
AT(x_vextractf128_m_i0_at)
        vextractf128 $0, %ymm1, (%rbx)          /* c4 e3 7d 19 0b 00 */
        POST

FN(x_vextractf128_m_i1)
        PRE
AT(x_vextractf128_m_i1_at)
        vextractf128 $1, %ymm1, (%rbx)          /* c4 e3 7d 19 0b 01 */
        POST

FN(x_vextractf128_m_i2)
        PRE
AT(x_vextractf128_m_i2_at)
        vextractf128 $2, %ymm1, (%rbx)          /* c4 e3 7d 19 0b 02 */
        POST

FN(x_vextractf128_m_i3)
        PRE
AT(x_vextractf128_m_i3_at)
        vextractf128 $3, %ymm1, (%rbx)          /* c4 e3 7d 19 0b 03 */
        POST

FN(x_vextractf128_m_ife)
        PRE
AT(x_vextractf128_m_ife_at)
        vextractf128 $254, %ymm1, (%rbx)        /* c4 e3 7d 19 0b fe */
        POST

FN(x_vextractf128_m_iff)
        PRE
AT(x_vextractf128_m_iff_at)
        vextractf128 $255, %ymm1, (%rbx)        /* c4 e3 7d 19 0b ff */
        POST
