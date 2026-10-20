/* hwprobe/vexsilb_ops.S — D348 (V8b): one function per (form, length) under test — the VEX.128 and VEX.256 twins
   VPMADDWD, VPMULHRSW, VPMADDUBSW and VPACKSSDW, register forms — so the bytes the processor executes are the assembler's
   encoding of the line written here, and `vexsilb_probe.c` refuses the run unless they are the bytes `mk_vexsilb_rows.py`
   declares (read back at each function's `_at` label). It shares nothing with the other probe paths; PRE and POST are
   `vexsil_ops.S`'s, restated.

   C signature: void x_X(struct xio *p), with
       struct xio { uint64_t y1[4], y2[4], y3[4], o1[4], o2[4], o3[4], f, fo, mx, mxo, rax, raxo; }
                  offsets 0 32 64 96 128 160 192 200 208 216 224 232
   On entry to the instruction under test, YMM1, YMM2 and YMM3 hold y1, y2, y3 WHOLE (all 256 bits), MXCSR holds mx
   (the caller's MXCSR is saved on the stack and restored after the reads), RAX holds rax, and RFLAGS is the process's
   with its six arithmetic bits (0x8d5) replaced by f's.
     vpmaddwd %ymm2, %ymm1, %ymm3      DEST = YMM3, SRC1 = YMM1 (VEX.vvvv), SRC2 = YMM2 (ModRM.rm)
   (the %xmm spellings are the VEX.128 forms of the same lines). On exit: fo = RFLAGS, mxo = MXCSR, raxo = RAX and
   o1, o2, o3 = YMM1, YMM2, YMM3 WHOLE, read immediately after the instruction, then the caller's MXCSR and VZEROUPPER. */

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

FN(x_vpmaddwd128)
        PRE
AT(x_vpmaddwd128_at)
        vpmaddwd %xmm2, %xmm1, %xmm3  /* c5 f1 f5 da */
        POST

FN(x_vpmaddwd256)
        PRE
AT(x_vpmaddwd256_at)
        vpmaddwd %ymm2, %ymm1, %ymm3  /* c5 f5 f5 da */
        POST

FN(x_vpmulhrsw128)
        PRE
AT(x_vpmulhrsw128_at)
        vpmulhrsw %xmm2, %xmm1, %xmm3  /* c4 e2 71 0b da */
        POST

FN(x_vpmulhrsw256)
        PRE
AT(x_vpmulhrsw256_at)
        vpmulhrsw %ymm2, %ymm1, %ymm3  /* c4 e2 75 0b da */
        POST

FN(x_vpmaddubsw128)
        PRE
AT(x_vpmaddubsw128_at)
        vpmaddubsw %xmm2, %xmm1, %xmm3  /* c4 e2 71 04 da */
        POST

FN(x_vpmaddubsw256)
        PRE
AT(x_vpmaddubsw256_at)
        vpmaddubsw %ymm2, %ymm1, %ymm3  /* c4 e2 75 04 da */
        POST

FN(x_vpackssdw128)
        PRE
AT(x_vpackssdw128_at)
        vpackssdw %xmm2, %xmm1, %xmm3  /* c5 f1 6b da */
        POST

FN(x_vpackssdw256)
        PRE
AT(x_vpackssdw256_at)
        vpackssdw %ymm2, %ymm1, %ymm3  /* c5 f5 6b da */
        POST
