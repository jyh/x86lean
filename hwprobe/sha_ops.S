/* hwprobe/sha_ops.S — D338 (V2): one function per SHA-NI form under test (SHA256MSG1, SHA256MSG2, SHA256RNDS2, each at
   xmm,xmm and m128,xmm, legacy SSE), so the bytes the processor executes are the assembler's encoding of the line written
   here, and `sha_probe.c` refuses the run unless they are the bytes `mk_sha_rows.py` declares (read back at each
   function's `_at` label). It shares nothing with sse_ops.S, int_ops.S, bitstr_ops.S, shuf_ops.S or simda_ops.S.

   C signature: void h_X(struct hio *p), with
       struct hio { uint64_t a[2], b[2], k[2], r[2], s[2], t[2], f, fo; }   offsets 0 16 32 48 64 80 96 104, 16-aligned
   On entry to the instruction under test:
       XMM1 = a  (DEST = SRC1, all 128 bits)   XMM2 = b  (SRC2 at the register shape, all 128 bits)
       XMM0 = k  (SHA256RNDS2's IMPLICIT third operand: WK0 = k[31:0], WK1 = k[63:32]; the two message forms do not read
                  it, and every form must leave it as it was)
       RBX  = &p->b  (the m128 SRC2: 16-byte aligned, holding the same b — a legacy-SSE m128 must be, #GP otherwise)
       RFLAGS = the process's RFLAGS with its six arithmetic bits (0x8d5) replaced by f's
   ⚠️ DEST is %xmm1, NOT %xmm0: %xmm0 is SHA256RNDS2's implicit operand, so a destination there would make the
   instruction read its own destination as WK and the row could not tell the two apart.
   On exit: r = XMM1, s = XMM2, t = XMM0, fo = RFLAGS, read immediately after the instruction; the probe also re-reads
   p->b, so a write to the memory source would be seen. RBX is callee-saved and restored. */

#ifdef __APPLE__
#define SYM(x) _##x
#else
#define SYM(x) x
#endif

        .text

#define PRE                     \
        pushq %rbx;             \
        movq %rdi, %r11;        \
        movdqu 0(%r11), %xmm1;  \
        movdqu 16(%r11), %xmm2; \
        movdqu 32(%r11), %xmm0; \
        leaq 16(%r11), %rbx;    \
        pushfq;                 \
        popq %r10;              \
        andq $-0x8d6, %r10;     \
        movq 96(%r11), %rsi;    \
        andq $0x8d5, %rsi;      \
        orq %rsi, %r10;         \
        pushq %r10;             \
        popfq

#define POST                    \
        pushfq;                 \
        popq %r10;              \
        movq %r10, 104(%r11);   \
        movdqu %xmm1, 48(%r11); \
        movdqu %xmm2, 64(%r11); \
        movdqu %xmm0, 80(%r11); \
        popq %rbx;              \
        ret

#define FN(name) .globl SYM(name); SYM(name):
#define AT(name) .globl SYM(name); SYM(name):

FN(h_sha256msg1_xx)
        PRE
AT(h_sha256msg1_xx_at)
        sha256msg1 %xmm2, %xmm1             /* 0f 38 cc ca */
        POST

FN(h_sha256msg1_xm)
        PRE
AT(h_sha256msg1_xm_at)
        sha256msg1 (%rbx), %xmm1            /* 0f 38 cc 0b */
        POST

FN(h_sha256msg2_xx)
        PRE
AT(h_sha256msg2_xx_at)
        sha256msg2 %xmm2, %xmm1             /* 0f 38 cd ca */
        POST

FN(h_sha256msg2_xm)
        PRE
AT(h_sha256msg2_xm_at)
        sha256msg2 (%rbx), %xmm1            /* 0f 38 cd 0b */
        POST

/* The implicit %xmm0 is written out: GNU as and clang both accept the three-operand spelling, and it is the one that
   says what the instruction reads. */
FN(h_sha256rnds2_xx)
        PRE
AT(h_sha256rnds2_xx_at)
        sha256rnds2 %xmm0, %xmm2, %xmm1     /* 0f 38 cb ca */
        POST

FN(h_sha256rnds2_xm)
        PRE
AT(h_sha256rnds2_xm_at)
        sha256rnds2 %xmm0, (%rbx), %xmm1    /* 0f 38 cb 0b */
        POST

