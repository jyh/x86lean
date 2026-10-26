/* hwprobe/shuf_ops.S — D336 (V1b): one function per (form, imm8) of PSHUFB, PALIGNR, PINSRD, PINSRQ, PEXTRD and
   PEXTRQ (legacy SSE), so the bytes the processor executes are the assembler's encoding of the line written here, and
   `shuf_probe.c` refuses the run unless they are the bytes `mk_shuf_rows.py` declares (read back at each function's
   `_at` label). It shares nothing with the SSE (`sse_ops.S`), integer (`int_ops.S`) or bit-string paths.

   C signature: void s_X(struct sio *p), with
       struct sio { uint64_t a[2], b[2], g, f, r[2], ro, fo; }     offsets 0 16 32 40 48 64 72 (16-byte aligned)
   On entry to the instruction under test:
       XMM0 = a (the destination)        XMM1 = b (the register source)
       RBX  = &p->b (the memory source: 16-byte aligned, so a Type-4 m128 does not fault; PINSRD's m32 is its low dword,
               PINSRQ's m64 its low qword; D362: PEXTRD/Q's memory DESTINATION, read back by the probe after the call)
       RCX  = g (the GPR source of PINSRD/PINSRQ)        RAX = c3c3c3c3c3c3c3c3 (the canary; PEXTRD/Q's destination)
       RFLAGS = the process's RFLAGS with its six arithmetic bits (0x8d5) replaced by f's
   On exit: fo = RFLAGS (read immediately after the instruction), r = XMM0, ro = RAX. RBX is callee-saved and restored. */

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
        movq 32(%r11), %rcx;    \
        leaq 16(%r11), %rbx;    \
        movabsq $0xc3c3c3c3c3c3c3c3, %rax; \
        pushfq;                 \
        popq %r10;              \
        andq $-0x8d6, %r10;     \
        movq 40(%r11), %rsi;    \
        andq $0x8d5, %rsi;      \
        orq %rsi, %r10;         \
        pushq %r10;             \
        popfq

#define POST                    \
        pushfq;                 \
        popq %r10;              \
        movq %r10, 72(%r11);    \
        movdqu %xmm0, 48(%r11); \
        movq %rax, 64(%r11);    \
        popq %rbx;              \
        ret

#define FN(name) .globl SYM(name); SYM(name):

/* One function: FN, PRE, the `_at` label, the instruction under test, POST. */
#define OP(name, ...) FN(name) PRE; FN(name##_at) __VA_ARGS__; POST

OP(s_pshufb_rr, pshufb %xmm1, %xmm0)
OP(s_pshufb_rm, pshufb (%rbx), %xmm0)

OP(s_palignr_rr_i0, palignr $0, %xmm1, %xmm0)
OP(s_palignr_rr_i1, palignr $1, %xmm1, %xmm0)
OP(s_palignr_rr_i4, palignr $4, %xmm1, %xmm0)
OP(s_palignr_rr_i8, palignr $8, %xmm1, %xmm0)
OP(s_palignr_rr_i15, palignr $15, %xmm1, %xmm0)
OP(s_palignr_rr_i16, palignr $16, %xmm1, %xmm0)
OP(s_palignr_rr_i17, palignr $17, %xmm1, %xmm0)
OP(s_palignr_rr_i24, palignr $24, %xmm1, %xmm0)
OP(s_palignr_rr_i31, palignr $31, %xmm1, %xmm0)
OP(s_palignr_rr_i32, palignr $32, %xmm1, %xmm0)
OP(s_palignr_rr_i33, palignr $33, %xmm1, %xmm0)
OP(s_palignr_rr_i128, palignr $128, %xmm1, %xmm0)
OP(s_palignr_rr_i255, palignr $255, %xmm1, %xmm0)
OP(s_palignr_rm_i5, palignr $5, (%rbx), %xmm0)
OP(s_palignr_rm_i16, palignr $16, (%rbx), %xmm0)
OP(s_palignr_rm_i20, palignr $20, (%rbx), %xmm0)

OP(s_pinsrd_rr_i0, pinsrd $0, %ecx, %xmm0)
OP(s_pinsrd_rr_i1, pinsrd $1, %ecx, %xmm0)
OP(s_pinsrd_rr_i2, pinsrd $2, %ecx, %xmm0)
OP(s_pinsrd_rr_i3, pinsrd $3, %ecx, %xmm0)
OP(s_pinsrd_rr_i4, pinsrd $4, %ecx, %xmm0)
OP(s_pinsrd_rr_i7, pinsrd $7, %ecx, %xmm0)
OP(s_pinsrd_rr_i254, pinsrd $254, %ecx, %xmm0)
OP(s_pinsrd_rm_i1, pinsrd $1, (%rbx), %xmm0)
OP(s_pinsrd_rm_i6, pinsrd $6, (%rbx), %xmm0)

OP(s_pinsrq_rr_i0, pinsrq $0, %rcx, %xmm0)
OP(s_pinsrq_rr_i1, pinsrq $1, %rcx, %xmm0)
OP(s_pinsrq_rr_i2, pinsrq $2, %rcx, %xmm0)
OP(s_pinsrq_rr_i255, pinsrq $255, %rcx, %xmm0)

OP(s_pextrd_rr_i0, pextrd $0, %xmm1, %eax)
OP(s_pextrd_rr_i1, pextrd $1, %xmm1, %eax)
OP(s_pextrd_rr_i2, pextrd $2, %xmm1, %eax)
OP(s_pextrd_rr_i3, pextrd $3, %xmm1, %eax)
OP(s_pextrd_rr_i5, pextrd $5, %xmm1, %eax)
OP(s_pextrd_rr_i255, pextrd $255, %xmm1, %eax)

OP(s_pextrq_rr_i0, pextrq $0, %xmm1, %rax)
OP(s_pextrq_rr_i1, pextrq $1, %xmm1, %rax)
OP(s_pextrq_rr_i3, pextrq $3, %xmm1, %rax)
OP(s_pextrq_rr_i128, pextrq $128, %xmm1, %rax)

/* D362: the memory shapes. The stores extract from XMM0 (= a), never XMM1 (= b, the bytes already at [RBX]), so a
   dropped store cannot agree with a performed one (D358). */
OP(s_pextrd_mr_i0, pextrd $0, %xmm0, (%rbx))
OP(s_pextrd_mr_i1, pextrd $1, %xmm0, (%rbx))
OP(s_pextrd_mr_i2, pextrd $2, %xmm0, (%rbx))
OP(s_pextrd_mr_i3, pextrd $3, %xmm0, (%rbx))
OP(s_pextrd_mr_i5, pextrd $5, %xmm0, (%rbx))
OP(s_pextrd_mr_i255, pextrd $255, %xmm0, (%rbx))
OP(s_pextrq_mr_i0, pextrq $0, %xmm0, (%rbx))
OP(s_pextrq_mr_i1, pextrq $1, %xmm0, (%rbx))
OP(s_pextrq_mr_i3, pextrq $3, %xmm0, (%rbx))
OP(s_pextrq_mr_i128, pextrq $128, %xmm0, (%rbx))
OP(s_pinsrq_rm_i0, pinsrq $0, (%rbx), %xmm0)
OP(s_pinsrq_rm_i1, pinsrq $1, (%rbx), %xmm0)
OP(s_pinsrq_rm_i2, pinsrq $2, (%rbx), %xmm0)
OP(s_pinsrq_rm_i255, pinsrq $255, (%rbx), %xmm0)
