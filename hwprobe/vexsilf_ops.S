/* hwprobe/vexsilf_ops.S — D371: one function per VEX `vmovd`/`vmovq` form under test — r → xmm, xmm → r, m → xmm and
   xmm → m, at 32 and 64 bits, all VEX.128 — so the bytes the processor executes are the assembler's encoding of the line
   written here, and `vexsilf_probe.c` refuses the run unless they are the bytes `mk_vexsilf_rows.py` declares. PRE and
   POST, the `struct xio` layout and the register roles are `vexsile_ops.S`'s (D361), restated: DEST = YMM3 or RAX,
   SOURCE = YMM1 or RAX, the memory operand `(%rbx)` with RBX = &mem[off]. The buffer is read back by the caller and
   compared with the EXPECTED buffer, since the two store forms write it. */

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

FN(x_vmovd_gx)
        PRE
AT(x_vmovd_gx_at)
        vmovd %eax, %xmm3
        POST

FN(x_vmovq_gx)
        PRE
AT(x_vmovq_gx_at)
        vmovq %rax, %xmm3
        POST

FN(x_vmovd_xg)
        PRE
AT(x_vmovd_xg_at)
        vmovd %xmm1, %eax
        POST

FN(x_vmovq_xg)
        PRE
AT(x_vmovq_xg_at)
        vmovq %xmm1, %rax
        POST

FN(x_vmovd_ld)
        PRE
AT(x_vmovd_ld_at)
        vmovd (%rbx), %xmm3
        POST

FN(x_vmovq_ld)
        PRE
AT(x_vmovq_ld_at)
        vmovq (%rbx), %xmm3
        POST

FN(x_vmovd_st)
        PRE
AT(x_vmovd_st_at)
        vmovd %xmm1, (%rbx)
        POST

FN(x_vmovq_st)
        PRE
AT(x_vmovq_st_at)
        vmovq %xmm1, (%rbx)
        POST

