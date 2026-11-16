/* hwprobe/vexsile_ops.S — D361 (V10): one function per (form, length[, imm8]) under test — the VEX.128 / VEX.256 MEMORY
   forms of the silicon rows: VPSHUFB and VPALIGNR (VEX.128 only), VADDPS VSUBPS VMULPS VPSRAD VPUNPCKLWD VPUNPCKHWD
   VPUNPCKLBW VPACKUSWB (both lengths) — so the bytes the processor executes are the assembler's encoding of the line
   written here, and `vexsile_probe.c` refuses the run unless they are the bytes `mk_vexsile_rows.py` declares. PRE and
   POST, the `struct xio` layout and the register roles are `vexsilc_ops.S`'s (D350), restated: DEST = YMM3, SRC1 = YMM1
   (VEX.vvvv), the memory operand `(%rbx)` with RBX = &mem[off]. VPSRAD's memory operand is its COUNT (xmm3/m128, 16
   bytes, at both lengths). The buffer is read back by the caller, which proves nothing was written. */

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

FN(x_vpshufb128_m)
        PRE
AT(x_vpshufb128_m_at)
        vpshufb (%rbx), %xmm1, %xmm3
        POST

FN(x_vpalignr128_m_i0)
        PRE
AT(x_vpalignr128_m_i0_at)
        vpalignr $0, (%rbx), %xmm1, %xmm3
        POST

FN(x_vpalignr128_m_i5)
        PRE
AT(x_vpalignr128_m_i5_at)
        vpalignr $5, (%rbx), %xmm1, %xmm3
        POST

FN(x_vpalignr128_m_i16)
        PRE
AT(x_vpalignr128_m_i16_at)
        vpalignr $16, (%rbx), %xmm1, %xmm3
        POST

FN(x_vpalignr128_m_i20)
        PRE
AT(x_vpalignr128_m_i20_at)
        vpalignr $20, (%rbx), %xmm1, %xmm3
        POST

FN(x_vpalignr128_m_i33)
        PRE
AT(x_vpalignr128_m_i33_at)
        vpalignr $33, (%rbx), %xmm1, %xmm3
        POST

FN(x_vaddps128_m)
        PRE
AT(x_vaddps128_m_at)
        vaddps (%rbx), %xmm1, %xmm3
        POST

FN(x_vaddps256_m)
        PRE
AT(x_vaddps256_m_at)
        vaddps (%rbx), %ymm1, %ymm3
        POST

FN(x_vsubps128_m)
        PRE
AT(x_vsubps128_m_at)
        vsubps (%rbx), %xmm1, %xmm3
        POST

FN(x_vsubps256_m)
        PRE
AT(x_vsubps256_m_at)
        vsubps (%rbx), %ymm1, %ymm3
        POST

FN(x_vmulps128_m)
        PRE
AT(x_vmulps128_m_at)
        vmulps (%rbx), %xmm1, %xmm3
        POST

FN(x_vmulps256_m)
        PRE
AT(x_vmulps256_m_at)
        vmulps (%rbx), %ymm1, %ymm3
        POST

FN(x_vpsrad128_m)
        PRE
AT(x_vpsrad128_m_at)
        vpsrad (%rbx), %xmm1, %xmm3
        POST

FN(x_vpsrad256_m)
        PRE
AT(x_vpsrad256_m_at)
        vpsrad (%rbx), %ymm1, %ymm3
        POST

FN(x_vpunpcklwd128_m)
        PRE
AT(x_vpunpcklwd128_m_at)
        vpunpcklwd (%rbx), %xmm1, %xmm3
        POST

FN(x_vpunpcklwd256_m)
        PRE
AT(x_vpunpcklwd256_m_at)
        vpunpcklwd (%rbx), %ymm1, %ymm3
        POST

FN(x_vpunpckhwd128_m)
        PRE
AT(x_vpunpckhwd128_m_at)
        vpunpckhwd (%rbx), %xmm1, %xmm3
        POST

FN(x_vpunpckhwd256_m)
        PRE
AT(x_vpunpckhwd256_m_at)
        vpunpckhwd (%rbx), %ymm1, %ymm3
        POST

FN(x_vpunpcklbw128_m)
        PRE
AT(x_vpunpcklbw128_m_at)
        vpunpcklbw (%rbx), %xmm1, %xmm3
        POST

FN(x_vpunpcklbw256_m)
        PRE
AT(x_vpunpcklbw256_m_at)
        vpunpcklbw (%rbx), %ymm1, %ymm3
        POST

FN(x_vpackuswb128_m)
        PRE
AT(x_vpackuswb128_m_at)
        vpackuswb (%rbx), %xmm1, %xmm3
        POST

FN(x_vpackuswb256_m)
        PRE
AT(x_vpackuswb256_m_at)
        vpackuswb (%rbx), %ymm1, %ymm3
        POST
