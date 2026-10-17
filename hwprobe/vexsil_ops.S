/* hwprobe/vexsil_ops.S — D345 (V7): one function per (form, length, imm8) under test — the VEX.128 and VEX.256 twins
   VSHUFPS imm, VPSRAD xmm/imm, VPSRAW xmm/imm, VADDPS, VSUBPS, VMULPS, VPUNPCKLWD, VPUNPCKHWD, VPUNPCKLBW, VPACKUSWB
   and VPMOVMSKB, register forms — so the bytes the processor executes are the assembler's encoding of the line written
   here, and `vexsil_probe.c` refuses the run unless they are the bytes `mk_vexsil_rows.py` declares (read back at each
   function's `_at` label). It shares nothing with the other probe paths.

   C signature: void x_X(struct xio *p), with
       struct xio { uint64_t y1[4], y2[4], y3[4], o1[4], o2[4], o3[4], f, fo, mx, mxo, rax, raxo; }
                  offsets 0 32 64 96 128 160 192 200 208 216 224 232
   On entry to the instruction under test, YMM1, YMM2 and YMM3 hold y1, y2, y3 WHOLE (all 256 bits), MXCSR holds mx
   (the caller's MXCSR is saved on the stack and restored after the reads), RAX holds rax, and RFLAGS is the process's
   with its six arithmetic bits (0x8d5) replaced by f's.
     vaddps %ymm2, %ymm1, %ymm3        DEST = YMM3, SRC1 = YMM1 (VEX.vvvv), SRC2 = YMM2 (ModRM.rm)
     vpsrad %xmm2, %ymm1, %ymm3        DEST = YMM3, SRC = YMM1, COUNT = XMM2[63:0]
     vpsrad $i, %ymm1, %ymm3           DEST = YMM3 (VEX.vvvv), SRC = YMM1 (ModRM.rm)
     vpmovmskb %ymm1, %eax             DEST = RAX, SRC = YMM1
   (the %xmm spellings are the VEX.128 forms of the same lines). On exit: fo = RFLAGS, mxo = MXCSR, raxo = RAX and
   o1, o2, o3 = YMM1, YMM2, YMM3 WHOLE, read immediately after the instruction, then the caller's MXCSR and VZEROUPPER
   (after the reads, so the C caller does not run with dirty upper state). */

#ifdef __APPLE__
#define SYM(x) _##x
#else
#define SYM(x) x
#endif

        .text

#define PRE                       \
        movq %rdi, %r11;          \
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
        ret

#define FN(name) .globl SYM(name); SYM(name):
#define AT(name) .globl SYM(name); SYM(name):

FN(x_vshufps128_00)
        PRE
AT(x_vshufps128_00_at)
        vshufps $0x00, %xmm2, %xmm1, %xmm3  /* c5 f0 c6 da 00 */
        POST

FN(x_vshufps128_1b)
        PRE
AT(x_vshufps128_1b_at)
        vshufps $0x1b, %xmm2, %xmm1, %xmm3  /* c5 f0 c6 da 1b */
        POST

FN(x_vshufps128_4e)
        PRE
AT(x_vshufps128_4e_at)
        vshufps $0x4e, %xmm2, %xmm1, %xmm3  /* c5 f0 c6 da 4e */
        POST

FN(x_vshufps128_b1)
        PRE
AT(x_vshufps128_b1_at)
        vshufps $0xb1, %xmm2, %xmm1, %xmm3  /* c5 f0 c6 da b1 */
        POST

FN(x_vshufps128_e4)
        PRE
AT(x_vshufps128_e4_at)
        vshufps $0xe4, %xmm2, %xmm1, %xmm3  /* c5 f0 c6 da e4 */
        POST

FN(x_vshufps128_93)
        PRE
AT(x_vshufps128_93_at)
        vshufps $0x93, %xmm2, %xmm1, %xmm3  /* c5 f0 c6 da 93 */
        POST

FN(x_vshufps128_39)
        PRE
AT(x_vshufps128_39_at)
        vshufps $0x39, %xmm2, %xmm1, %xmm3  /* c5 f0 c6 da 39 */
        POST

FN(x_vshufps128_ff)
        PRE
AT(x_vshufps128_ff_at)
        vshufps $0xff, %xmm2, %xmm1, %xmm3  /* c5 f0 c6 da ff */
        POST

FN(x_vshufps128_72)
        PRE
AT(x_vshufps128_72_at)
        vshufps $0x72, %xmm2, %xmm1, %xmm3  /* c5 f0 c6 da 72 */
        POST

FN(x_vshufps128_d8)
        PRE
AT(x_vshufps128_d8_at)
        vshufps $0xd8, %xmm2, %xmm1, %xmm3  /* c5 f0 c6 da d8 */
        POST

FN(x_vshufps256_00)
        PRE
AT(x_vshufps256_00_at)
        vshufps $0x00, %ymm2, %ymm1, %ymm3  /* c5 f4 c6 da 00 */
        POST

FN(x_vshufps256_1b)
        PRE
AT(x_vshufps256_1b_at)
        vshufps $0x1b, %ymm2, %ymm1, %ymm3  /* c5 f4 c6 da 1b */
        POST

FN(x_vshufps256_4e)
        PRE
AT(x_vshufps256_4e_at)
        vshufps $0x4e, %ymm2, %ymm1, %ymm3  /* c5 f4 c6 da 4e */
        POST

FN(x_vshufps256_b1)
        PRE
AT(x_vshufps256_b1_at)
        vshufps $0xb1, %ymm2, %ymm1, %ymm3  /* c5 f4 c6 da b1 */
        POST

FN(x_vshufps256_e4)
        PRE
AT(x_vshufps256_e4_at)
        vshufps $0xe4, %ymm2, %ymm1, %ymm3  /* c5 f4 c6 da e4 */
        POST

FN(x_vshufps256_93)
        PRE
AT(x_vshufps256_93_at)
        vshufps $0x93, %ymm2, %ymm1, %ymm3  /* c5 f4 c6 da 93 */
        POST

FN(x_vshufps256_39)
        PRE
AT(x_vshufps256_39_at)
        vshufps $0x39, %ymm2, %ymm1, %ymm3  /* c5 f4 c6 da 39 */
        POST

FN(x_vshufps256_ff)
        PRE
AT(x_vshufps256_ff_at)
        vshufps $0xff, %ymm2, %ymm1, %ymm3  /* c5 f4 c6 da ff */
        POST

FN(x_vshufps256_72)
        PRE
AT(x_vshufps256_72_at)
        vshufps $0x72, %ymm2, %ymm1, %ymm3  /* c5 f4 c6 da 72 */
        POST

FN(x_vshufps256_d8)
        PRE
AT(x_vshufps256_d8_at)
        vshufps $0xd8, %ymm2, %ymm1, %ymm3  /* c5 f4 c6 da d8 */
        POST

FN(x_vpsrad128_x)
        PRE
AT(x_vpsrad128_x_at)
        vpsrad %xmm2, %xmm1, %xmm3          /* c5 f1 e2 da */
        POST

FN(x_vpsrad256_x)
        PRE
AT(x_vpsrad256_x_at)
        vpsrad %xmm2, %ymm1, %ymm3          /* c5 f5 e2 da */
        POST

FN(x_vpsrad128_i0)
        PRE
AT(x_vpsrad128_i0_at)
        vpsrad $0, %xmm1, %xmm3             /* c5 e1 72 e1 00 */
        POST

FN(x_vpsrad128_i1)
        PRE
AT(x_vpsrad128_i1_at)
        vpsrad $1, %xmm1, %xmm3             /* c5 e1 72 e1 01 */
        POST

FN(x_vpsrad128_i7)
        PRE
AT(x_vpsrad128_i7_at)
        vpsrad $7, %xmm1, %xmm3             /* c5 e1 72 e1 07 */
        POST

FN(x_vpsrad128_i15)
        PRE
AT(x_vpsrad128_i15_at)
        vpsrad $15, %xmm1, %xmm3            /* c5 e1 72 e1 0f */
        POST

FN(x_vpsrad128_i16)
        PRE
AT(x_vpsrad128_i16_at)
        vpsrad $16, %xmm1, %xmm3            /* c5 e1 72 e1 10 */
        POST

FN(x_vpsrad128_i17)
        PRE
AT(x_vpsrad128_i17_at)
        vpsrad $17, %xmm1, %xmm3            /* c5 e1 72 e1 11 */
        POST

FN(x_vpsrad128_i31)
        PRE
AT(x_vpsrad128_i31_at)
        vpsrad $31, %xmm1, %xmm3            /* c5 e1 72 e1 1f */
        POST

FN(x_vpsrad128_i32)
        PRE
AT(x_vpsrad128_i32_at)
        vpsrad $32, %xmm1, %xmm3            /* c5 e1 72 e1 20 */
        POST

FN(x_vpsrad128_i255)
        PRE
AT(x_vpsrad128_i255_at)
        vpsrad $255, %xmm1, %xmm3           /* c5 e1 72 e1 ff */
        POST

FN(x_vpsrad256_i0)
        PRE
AT(x_vpsrad256_i0_at)
        vpsrad $0, %ymm1, %ymm3             /* c5 e5 72 e1 00 */
        POST

FN(x_vpsrad256_i1)
        PRE
AT(x_vpsrad256_i1_at)
        vpsrad $1, %ymm1, %ymm3             /* c5 e5 72 e1 01 */
        POST

FN(x_vpsrad256_i7)
        PRE
AT(x_vpsrad256_i7_at)
        vpsrad $7, %ymm1, %ymm3             /* c5 e5 72 e1 07 */
        POST

FN(x_vpsrad256_i15)
        PRE
AT(x_vpsrad256_i15_at)
        vpsrad $15, %ymm1, %ymm3            /* c5 e5 72 e1 0f */
        POST

FN(x_vpsrad256_i16)
        PRE
AT(x_vpsrad256_i16_at)
        vpsrad $16, %ymm1, %ymm3            /* c5 e5 72 e1 10 */
        POST

FN(x_vpsrad256_i17)
        PRE
AT(x_vpsrad256_i17_at)
        vpsrad $17, %ymm1, %ymm3            /* c5 e5 72 e1 11 */
        POST

FN(x_vpsrad256_i31)
        PRE
AT(x_vpsrad256_i31_at)
        vpsrad $31, %ymm1, %ymm3            /* c5 e5 72 e1 1f */
        POST

FN(x_vpsrad256_i32)
        PRE
AT(x_vpsrad256_i32_at)
        vpsrad $32, %ymm1, %ymm3            /* c5 e5 72 e1 20 */
        POST

FN(x_vpsrad256_i255)
        PRE
AT(x_vpsrad256_i255_at)
        vpsrad $255, %ymm1, %ymm3           /* c5 e5 72 e1 ff */
        POST

FN(x_vpsraw128_x)
        PRE
AT(x_vpsraw128_x_at)
        vpsraw %xmm2, %xmm1, %xmm3          /* c5 f1 e1 da */
        POST

FN(x_vpsraw256_x)
        PRE
AT(x_vpsraw256_x_at)
        vpsraw %xmm2, %ymm1, %ymm3          /* c5 f5 e1 da */
        POST

FN(x_vpsraw128_i0)
        PRE
AT(x_vpsraw128_i0_at)
        vpsraw $0, %xmm1, %xmm3             /* c5 e1 71 e1 00 */
        POST

FN(x_vpsraw128_i1)
        PRE
AT(x_vpsraw128_i1_at)
        vpsraw $1, %xmm1, %xmm3             /* c5 e1 71 e1 01 */
        POST

FN(x_vpsraw128_i7)
        PRE
AT(x_vpsraw128_i7_at)
        vpsraw $7, %xmm1, %xmm3             /* c5 e1 71 e1 07 */
        POST

FN(x_vpsraw128_i15)
        PRE
AT(x_vpsraw128_i15_at)
        vpsraw $15, %xmm1, %xmm3            /* c5 e1 71 e1 0f */
        POST

FN(x_vpsraw128_i16)
        PRE
AT(x_vpsraw128_i16_at)
        vpsraw $16, %xmm1, %xmm3            /* c5 e1 71 e1 10 */
        POST

FN(x_vpsraw128_i17)
        PRE
AT(x_vpsraw128_i17_at)
        vpsraw $17, %xmm1, %xmm3            /* c5 e1 71 e1 11 */
        POST

FN(x_vpsraw128_i31)
        PRE
AT(x_vpsraw128_i31_at)
        vpsraw $31, %xmm1, %xmm3            /* c5 e1 71 e1 1f */
        POST

FN(x_vpsraw128_i32)
        PRE
AT(x_vpsraw128_i32_at)
        vpsraw $32, %xmm1, %xmm3            /* c5 e1 71 e1 20 */
        POST

FN(x_vpsraw128_i255)
        PRE
AT(x_vpsraw128_i255_at)
        vpsraw $255, %xmm1, %xmm3           /* c5 e1 71 e1 ff */
        POST

FN(x_vpsraw256_i0)
        PRE
AT(x_vpsraw256_i0_at)
        vpsraw $0, %ymm1, %ymm3             /* c5 e5 71 e1 00 */
        POST

FN(x_vpsraw256_i1)
        PRE
AT(x_vpsraw256_i1_at)
        vpsraw $1, %ymm1, %ymm3             /* c5 e5 71 e1 01 */
        POST

FN(x_vpsraw256_i7)
        PRE
AT(x_vpsraw256_i7_at)
        vpsraw $7, %ymm1, %ymm3             /* c5 e5 71 e1 07 */
        POST

FN(x_vpsraw256_i15)
        PRE
AT(x_vpsraw256_i15_at)
        vpsraw $15, %ymm1, %ymm3            /* c5 e5 71 e1 0f */
        POST

FN(x_vpsraw256_i16)
        PRE
AT(x_vpsraw256_i16_at)
        vpsraw $16, %ymm1, %ymm3            /* c5 e5 71 e1 10 */
        POST

FN(x_vpsraw256_i17)
        PRE
AT(x_vpsraw256_i17_at)
        vpsraw $17, %ymm1, %ymm3            /* c5 e5 71 e1 11 */
        POST

FN(x_vpsraw256_i31)
        PRE
AT(x_vpsraw256_i31_at)
        vpsraw $31, %ymm1, %ymm3            /* c5 e5 71 e1 1f */
        POST

FN(x_vpsraw256_i32)
        PRE
AT(x_vpsraw256_i32_at)
        vpsraw $32, %ymm1, %ymm3            /* c5 e5 71 e1 20 */
        POST

FN(x_vpsraw256_i255)
        PRE
AT(x_vpsraw256_i255_at)
        vpsraw $255, %ymm1, %ymm3           /* c5 e5 71 e1 ff */
        POST

FN(x_vaddps128)
        PRE
AT(x_vaddps128_at)
        vaddps %xmm2, %xmm1, %xmm3          /* c5 f0 58 da */
        POST

FN(x_vaddps256)
        PRE
AT(x_vaddps256_at)
        vaddps %ymm2, %ymm1, %ymm3          /* c5 f4 58 da */
        POST

FN(x_vsubps128)
        PRE
AT(x_vsubps128_at)
        vsubps %xmm2, %xmm1, %xmm3          /* c5 f0 5c da */
        POST

FN(x_vsubps256)
        PRE
AT(x_vsubps256_at)
        vsubps %ymm2, %ymm1, %ymm3          /* c5 f4 5c da */
        POST

FN(x_vmulps128)
        PRE
AT(x_vmulps128_at)
        vmulps %xmm2, %xmm1, %xmm3          /* c5 f0 59 da */
        POST

FN(x_vmulps256)
        PRE
AT(x_vmulps256_at)
        vmulps %ymm2, %ymm1, %ymm3          /* c5 f4 59 da */
        POST

FN(x_vpunpcklwd128)
        PRE
AT(x_vpunpcklwd128_at)
        vpunpcklwd %xmm2, %xmm1, %xmm3      /* c5 f1 61 da */
        POST

FN(x_vpunpcklwd256)
        PRE
AT(x_vpunpcklwd256_at)
        vpunpcklwd %ymm2, %ymm1, %ymm3      /* c5 f5 61 da */
        POST

FN(x_vpunpckhwd128)
        PRE
AT(x_vpunpckhwd128_at)
        vpunpckhwd %xmm2, %xmm1, %xmm3      /* c5 f1 69 da */
        POST

FN(x_vpunpckhwd256)
        PRE
AT(x_vpunpckhwd256_at)
        vpunpckhwd %ymm2, %ymm1, %ymm3      /* c5 f5 69 da */
        POST

FN(x_vpunpcklbw128)
        PRE
AT(x_vpunpcklbw128_at)
        vpunpcklbw %xmm2, %xmm1, %xmm3      /* c5 f1 60 da */
        POST

FN(x_vpunpcklbw256)
        PRE
AT(x_vpunpcklbw256_at)
        vpunpcklbw %ymm2, %ymm1, %ymm3      /* c5 f5 60 da */
        POST

FN(x_vpackuswb128)
        PRE
AT(x_vpackuswb128_at)
        vpackuswb %xmm2, %xmm1, %xmm3       /* c5 f1 67 da */
        POST

FN(x_vpackuswb256)
        PRE
AT(x_vpackuswb256_at)
        vpackuswb %ymm2, %ymm1, %ymm3       /* c5 f5 67 da */
        POST

FN(x_vpmovmskb128)
        PRE
AT(x_vpmovmskb128_at)
        vpmovmskb %xmm1, %eax               /* c5 f9 d7 c1 */
        POST

FN(x_vpmovmskb256)
        PRE
AT(x_vpmovmskb256_at)
        vpmovmskb %ymm1, %eax               /* c5 fd d7 c1 */
        POST
