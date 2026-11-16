/* hwprobe/aes_ops.S — D342 (V4): one function per (form, imm8) under test — AESENC, AESENCLAST (legacy SSE) and
   VAESENC, VAESENCLAST, VPCLMULQDQ, VPSHUFB, VPALIGNR, VPSLLDQ, VPSRLDQ (VEX.128), register forms — so the bytes the
   processor executes are the assembler's encoding of the line written here, and `aes_probe.c` refuses the run unless
   they are the bytes `mk_aes_rows.py` declares (read back at each function's `_at` label). It shares nothing with the
   other probe paths.

   C signature: void e_X(struct eio *p), with
       struct eio { uint64_t y1[4], y2[4], y3[4], o1[4], o2[4], o3[4], f, fo; }   offsets 0 32 64 96 128 160 192 200
   On entry to the instruction under test, YMM1, YMM2 and YMM3 hold y1, y2, y3 WHOLE (all 256 bits; every upper half
   is seeded non-zero by the rows), and RFLAGS is the process's with its six arithmetic bits (0x8d5) replaced by f's.
     legacy  aesenc %xmm2, %xmm1           DEST = XMM1 (the state), SRC2 = XMM2 (the round key)
     VEX     vaesenc %xmm2, %xmm1, %xmm3   DEST = XMM3, SRC1 = XMM1 (VEX.vvvv), SRC2 = XMM2 (ModRM.rm)
     VEX     vpslldq $i, %xmm1, %xmm3      DEST = XMM3 (VEX.vvvv), SRC = XMM1 (ModRM.rm)
   On exit: o1, o2, o3 = YMM1, YMM2, YMM3 WHOLE and fo = RFLAGS, read immediately after the instruction, then
   VZEROUPPER (after the reads, so the C caller does not run with dirty upper state). */

#ifdef __APPLE__
#define SYM(x) _##x
#else
#define SYM(x) x
#endif

        .text

#define PRE                       \
        movq %rdi, %r11;          \
        vmovdqu 0(%r11), %ymm1;   \
        vmovdqu 32(%r11), %ymm2;  \
        vmovdqu 64(%r11), %ymm3;  \
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
        vmovdqu %ymm1, 96(%r11);  \
        vmovdqu %ymm2, 128(%r11); \
        vmovdqu %ymm3, 160(%r11); \
        vzeroupper;               \
        ret

#define FN(name) .globl SYM(name); SYM(name):
#define AT(name) .globl SYM(name); SYM(name):

FN(e_aesenc)
        PRE
AT(e_aesenc_at)
        aesenc %xmm2, %xmm1                 /* 66 0f 38 dc ca */
        POST

FN(e_aesenclast)
        PRE
AT(e_aesenclast_at)
        aesenclast %xmm2, %xmm1             /* 66 0f 38 dd ca */
        POST

FN(e_vaesenc)
        PRE
AT(e_vaesenc_at)
        vaesenc %xmm2, %xmm1, %xmm3         /* c4 e2 71 dc da */
        POST

FN(e_vaesenclast)
        PRE
AT(e_vaesenclast_at)
        vaesenclast %xmm2, %xmm1, %xmm3     /* c4 e2 71 dd da */
        POST

FN(e_vpshufb)
        PRE
AT(e_vpshufb_at)
        vpshufb %xmm2, %xmm1, %xmm3         /* c4 e2 71 00 da */
        POST

FN(e_vpclmulqdq_00)
        PRE
AT(e_vpclmulqdq_00_at)
        vpclmulqdq $0, %xmm2, %xmm1, %xmm3  /* c4 e3 71 44 da 00 */
        POST

FN(e_vpclmulqdq_01)
        PRE
AT(e_vpclmulqdq_01_at)
        vpclmulqdq $1, %xmm2, %xmm1, %xmm3  /* c4 e3 71 44 da 01 */
        POST

FN(e_vpclmulqdq_10)
        PRE
AT(e_vpclmulqdq_10_at)
        vpclmulqdq $16, %xmm2, %xmm1, %xmm3 /* c4 e3 71 44 da 10 */
        POST

FN(e_vpclmulqdq_11)
        PRE
AT(e_vpclmulqdq_11_at)
        vpclmulqdq $17, %xmm2, %xmm1, %xmm3 /* c4 e3 71 44 da 11 */
        POST

FN(e_vpclmulqdq_02)
        PRE
AT(e_vpclmulqdq_02_at)
        vpclmulqdq $2, %xmm2, %xmm1, %xmm3  /* c4 e3 71 44 da 02 */
        POST

FN(e_vpclmulqdq_20)
        PRE
AT(e_vpclmulqdq_20_at)
        vpclmulqdq $32, %xmm2, %xmm1, %xmm3 /* c4 e3 71 44 da 20 */
        POST

FN(e_vpclmulqdq_ee)
        PRE
AT(e_vpclmulqdq_ee_at)
        vpclmulqdq $238, %xmm2, %xmm1, %xmm3/* c4 e3 71 44 da ee */
        POST

FN(e_vpclmulqdq_ff)
        PRE
AT(e_vpclmulqdq_ff_at)
        vpclmulqdq $255, %xmm2, %xmm1, %xmm3/* c4 e3 71 44 da ff */
        POST

FN(e_vpalignr_0)
        PRE
AT(e_vpalignr_0_at)
        vpalignr $0, %xmm2, %xmm1, %xmm3    /* c4 e3 71 0f da 00 */
        POST

FN(e_vpalignr_1)
        PRE
AT(e_vpalignr_1_at)
        vpalignr $1, %xmm2, %xmm1, %xmm3    /* c4 e3 71 0f da 01 */
        POST

FN(e_vpalignr_4)
        PRE
AT(e_vpalignr_4_at)
        vpalignr $4, %xmm2, %xmm1, %xmm3    /* c4 e3 71 0f da 04 */
        POST

FN(e_vpalignr_8)
        PRE
AT(e_vpalignr_8_at)
        vpalignr $8, %xmm2, %xmm1, %xmm3    /* c4 e3 71 0f da 08 */
        POST

FN(e_vpalignr_15)
        PRE
AT(e_vpalignr_15_at)
        vpalignr $15, %xmm2, %xmm1, %xmm3   /* c4 e3 71 0f da 0f */
        POST

FN(e_vpalignr_16)
        PRE
AT(e_vpalignr_16_at)
        vpalignr $16, %xmm2, %xmm1, %xmm3   /* c4 e3 71 0f da 10 */
        POST

FN(e_vpalignr_17)
        PRE
AT(e_vpalignr_17_at)
        vpalignr $17, %xmm2, %xmm1, %xmm3   /* c4 e3 71 0f da 11 */
        POST

FN(e_vpalignr_24)
        PRE
AT(e_vpalignr_24_at)
        vpalignr $24, %xmm2, %xmm1, %xmm3   /* c4 e3 71 0f da 18 */
        POST

FN(e_vpalignr_31)
        PRE
AT(e_vpalignr_31_at)
        vpalignr $31, %xmm2, %xmm1, %xmm3   /* c4 e3 71 0f da 1f */
        POST

FN(e_vpalignr_32)
        PRE
AT(e_vpalignr_32_at)
        vpalignr $32, %xmm2, %xmm1, %xmm3   /* c4 e3 71 0f da 20 */
        POST

FN(e_vpalignr_33)
        PRE
AT(e_vpalignr_33_at)
        vpalignr $33, %xmm2, %xmm1, %xmm3   /* c4 e3 71 0f da 21 */
        POST

FN(e_vpalignr_128)
        PRE
AT(e_vpalignr_128_at)
        vpalignr $128, %xmm2, %xmm1, %xmm3  /* c4 e3 71 0f da 80 */
        POST

FN(e_vpalignr_255)
        PRE
AT(e_vpalignr_255_at)
        vpalignr $255, %xmm2, %xmm1, %xmm3  /* c4 e3 71 0f da ff */
        POST

FN(e_vpslldq_0)
        PRE
AT(e_vpslldq_0_at)
        vpslldq $0, %xmm1, %xmm3            /* c5 e1 73 f9 00 */
        POST

FN(e_vpsrldq_0)
        PRE
AT(e_vpsrldq_0_at)
        vpsrldq $0, %xmm1, %xmm3            /* c5 e1 73 d9 00 */
        POST

FN(e_vpslldq_1)
        PRE
AT(e_vpslldq_1_at)
        vpslldq $1, %xmm1, %xmm3            /* c5 e1 73 f9 01 */
        POST

FN(e_vpsrldq_1)
        PRE
AT(e_vpsrldq_1_at)
        vpsrldq $1, %xmm1, %xmm3            /* c5 e1 73 d9 01 */
        POST

FN(e_vpslldq_3)
        PRE
AT(e_vpslldq_3_at)
        vpslldq $3, %xmm1, %xmm3            /* c5 e1 73 f9 03 */
        POST

FN(e_vpsrldq_3)
        PRE
AT(e_vpsrldq_3_at)
        vpsrldq $3, %xmm1, %xmm3            /* c5 e1 73 d9 03 */
        POST

FN(e_vpslldq_7)
        PRE
AT(e_vpslldq_7_at)
        vpslldq $7, %xmm1, %xmm3            /* c5 e1 73 f9 07 */
        POST

FN(e_vpsrldq_7)
        PRE
AT(e_vpsrldq_7_at)
        vpsrldq $7, %xmm1, %xmm3            /* c5 e1 73 d9 07 */
        POST

FN(e_vpslldq_8)
        PRE
AT(e_vpslldq_8_at)
        vpslldq $8, %xmm1, %xmm3            /* c5 e1 73 f9 08 */
        POST

FN(e_vpsrldq_8)
        PRE
AT(e_vpsrldq_8_at)
        vpsrldq $8, %xmm1, %xmm3            /* c5 e1 73 d9 08 */
        POST

FN(e_vpslldq_15)
        PRE
AT(e_vpslldq_15_at)
        vpslldq $15, %xmm1, %xmm3           /* c5 e1 73 f9 0f */
        POST

FN(e_vpsrldq_15)
        PRE
AT(e_vpsrldq_15_at)
        vpsrldq $15, %xmm1, %xmm3           /* c5 e1 73 d9 0f */
        POST

FN(e_vpslldq_16)
        PRE
AT(e_vpslldq_16_at)
        vpslldq $16, %xmm1, %xmm3           /* c5 e1 73 f9 10 */
        POST

FN(e_vpsrldq_16)
        PRE
AT(e_vpsrldq_16_at)
        vpsrldq $16, %xmm1, %xmm3           /* c5 e1 73 d9 10 */
        POST

FN(e_vpslldq_17)
        PRE
AT(e_vpslldq_17_at)
        vpslldq $17, %xmm1, %xmm3           /* c5 e1 73 f9 11 */
        POST

FN(e_vpsrldq_17)
        PRE
AT(e_vpsrldq_17_at)
        vpsrldq $17, %xmm1, %xmm3           /* c5 e1 73 d9 11 */
        POST

FN(e_vpslldq_255)
        PRE
AT(e_vpslldq_255_at)
        vpslldq $255, %xmm1, %xmm3          /* c5 e1 73 f9 ff */
        POST

FN(e_vpsrldq_255)
        PRE
AT(e_vpsrldq_255_at)
        vpsrldq $255, %xmm1, %xmm3          /* c5 e1 73 d9 ff */
        POST
