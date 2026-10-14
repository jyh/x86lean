/* hwprobe/simda_ops.S — D335 (V1a): one function per SSE-legacy PACKED-INTEGER ARITHMETIC form under test, so the
   bytes the processor executes are the assembler's encoding of the line written here, and `simda_probe.c` refuses the
   run unless they are the bytes `mk_simda_rows.py` declares (read back at each function's `_at` label). It shares
   nothing with sse_ops.S, int_ops.S or bitstr_ops.S.

   C signature: void v_X(struct sio *p), with
       struct sio { uint64_t a[2], b[2], r[2], s[2], f, fo; }   offsets 0 16 32 48 64 72, the struct 16-byte aligned
   On entry to the instruction under test:
       XMM0 = a  (DEST, all 128 bits)          XMM1 = b  (the register source, all 128 bits)
       RBX  = &p->b  (the m128 source: 16-byte aligned, holding the same b — a legacy-SSE m128 must be, #GP otherwise)
       RFLAGS = the process's RFLAGS with its six arithmetic bits (0x8d5) replaced by f's
   On exit: r = XMM0, s = XMM1, fo = RFLAGS, read immediately after the instruction; the probe also re-reads p->b, so
   a write to the memory source would be seen. RBX is callee-saved and restored. */

#ifdef __APPLE__
#define SYM(x) _##x
#else
#define SYM(x) x
#endif

        .text

#define PRE                     \
        pushq %rbx;             \
        movq %rdi, %r11;        \
        movdqu 0(%r11), %xmm0;  \
        movdqu 16(%r11), %xmm1; \
        leaq 16(%r11), %rbx;    \
        pushfq;                 \
        popq %r10;              \
        andq $-0x8d6, %r10;     \
        movq 64(%r11), %rsi;    \
        andq $0x8d5, %rsi;      \
        orq %rsi, %r10;         \
        pushq %r10;             \
        popfq

#define POST                    \
        pushfq;                 \
        popq %r10;              \
        movq %r10, 72(%r11);    \
        movdqu %xmm0, 32(%r11); \
        movdqu %xmm1, 48(%r11); \
        popq %rbx;              \
        ret

#define FN(name) .globl SYM(name); SYM(name):
#define AT(name) .globl SYM(name); SYM(name):

FN(v_pmaddwd_xx)
        PRE
AT(v_pmaddwd_xx_at)
        pmaddwd %xmm1, %xmm0        /* 66 0f f5 c1 */
        POST

FN(v_pmaddwd_xm)
        PRE
AT(v_pmaddwd_xm_at)
        pmaddwd (%rbx), %xmm0       /* 66 0f f5 03 */
        POST

FN(v_pmaddubsw_xx)
        PRE
AT(v_pmaddubsw_xx_at)
        pmaddubsw %xmm1, %xmm0      /* 66 0f 38 04 c1 */
        POST

FN(v_pmaddubsw_xm)
        PRE
AT(v_pmaddubsw_xm_at)
        pmaddubsw (%rbx), %xmm0     /* 66 0f 38 04 03 */
        POST

FN(v_pmullw_xx)
        PRE
AT(v_pmullw_xx_at)
        pmullw %xmm1, %xmm0         /* 66 0f d5 c1 */
        POST

FN(v_pmullw_xm)
        PRE
AT(v_pmullw_xm_at)
        pmullw (%rbx), %xmm0        /* 66 0f d5 03 */
        POST

FN(v_pmulhrsw_xx)
        PRE
AT(v_pmulhrsw_xx_at)
        pmulhrsw %xmm1, %xmm0       /* 66 0f 38 0b c1 */
        POST

FN(v_pmulhrsw_xm)
        PRE
AT(v_pmulhrsw_xm_at)
        pmulhrsw (%rbx), %xmm0      /* 66 0f 38 0b 03 */
        POST

FN(v_pmuludq_xx)
        PRE
AT(v_pmuludq_xx_at)
        pmuludq %xmm1, %xmm0        /* 66 0f f4 c1 */
        POST

FN(v_pmuludq_xm)
        PRE
AT(v_pmuludq_xm_at)
        pmuludq (%rbx), %xmm0       /* 66 0f f4 03 */
        POST

FN(v_paddsw_xx)
        PRE
AT(v_paddsw_xx_at)
        paddsw %xmm1, %xmm0         /* 66 0f ed c1 */
        POST

FN(v_paddsw_xm)
        PRE
AT(v_paddsw_xm_at)
        paddsw (%rbx), %xmm0        /* 66 0f ed 03 */
        POST

FN(v_psubusw_xx)
        PRE
AT(v_psubusw_xx_at)
        psubusw %xmm1, %xmm0        /* 66 0f d9 c1 */
        POST

FN(v_psubusw_xm)
        PRE
AT(v_psubusw_xm_at)
        psubusw (%rbx), %xmm0       /* 66 0f d9 03 */
        POST

FN(v_psubusb_xx)
        PRE
AT(v_psubusb_xx_at)
        psubusb %xmm1, %xmm0        /* 66 0f d8 c1 */
        POST

FN(v_psubusb_xm)
        PRE
AT(v_psubusb_xm_at)
        psubusb (%rbx), %xmm0       /* 66 0f d8 03 */
        POST

FN(v_pmaxsw_xx)
        PRE
AT(v_pmaxsw_xx_at)
        pmaxsw %xmm1, %xmm0         /* 66 0f ee c1 */
        POST

FN(v_pmaxsw_xm)
        PRE
AT(v_pmaxsw_xm_at)
        pmaxsw (%rbx), %xmm0        /* 66 0f ee 03 */
        POST

FN(v_psadbw_xx)
        PRE
AT(v_psadbw_xx_at)
        psadbw %xmm1, %xmm0         /* 66 0f f6 c1 */
        POST

FN(v_psadbw_xm)
        PRE
AT(v_psadbw_xm_at)
        psadbw (%rbx), %xmm0        /* 66 0f f6 03 */
        POST

FN(v_packssdw_xx)
        PRE
AT(v_packssdw_xx_at)
        packssdw %xmm1, %xmm0       /* 66 0f 6b c1 */
        POST

FN(v_packssdw_xm)
        PRE
AT(v_packssdw_xm_at)
        packssdw (%rbx), %xmm0      /* 66 0f 6b 03 */
        POST

