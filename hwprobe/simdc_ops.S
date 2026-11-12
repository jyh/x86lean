/* hwprobe/simdc_ops.S — D384: set C of `mk_simda_rows.py` (PSUBSW PAVGW PMULDQ), one function per form, the
   same frame as D335's simda_ops.S, so `simda_probe.c` runs it unchanged against `simdc_rows.h` and refuses the run
   unless the bytes at each `_at` label are the ones `mk_simda_rows.py --set-c` declares.

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

FN(v_psubsw_xx)
        PRE
AT(v_psubsw_xx_at)
        psubsw %xmm1, %xmm0         /* 66 0f e9 c1 */
        POST

FN(v_psubsw_xm)
        PRE
AT(v_psubsw_xm_at)
        psubsw (%rbx), %xmm0        /* 66 0f e9 03 */
        POST

FN(v_pavgw_xx)
        PRE
AT(v_pavgw_xx_at)
        pavgw %xmm1, %xmm0          /* 66 0f e3 c1 */
        POST

FN(v_pavgw_xm)
        PRE
AT(v_pavgw_xm_at)
        pavgw (%rbx), %xmm0         /* 66 0f e3 03 */
        POST

FN(v_pmuldq_xx)
        PRE
AT(v_pmuldq_xx_at)
        pmuldq %xmm1, %xmm0         /* 66 0f 38 28 c1 */
        POST

FN(v_pmuldq_xm)
        PRE
AT(v_pmuldq_xm_at)
        pmuldq (%rbx), %xmm0        /* 66 0f 38 28 03 */
        POST
