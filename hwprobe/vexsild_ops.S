/* hwprobe/vexsild_ops.S — D354 (V9b): one function per (move, length, direction) under test — the VEX.128 and VEX.256
   MEMORY forms of VMOVDQA VMOVDQU VMOVAPS VMOVUPS VMOVAPD VMOVUPD, loads and stores — so the bytes the processor executes
   are the assembler's encoding of the line written here, and `vexsild_probe.c` refuses the run unless they are the bytes
   `mk_vexsild_rows.py` declares. PRE and POST are `vexsilc_ops.S`'s, restated: RBX (callee-saved) is pushed in PRE,
   pointed at `&mem[off]`, and popped in POST.

   C signature: void x_X(struct xio *p), with
       struct xio { uint64_t y1[4], y2[4], y3[4], o1[4], o2[4], o3[4], f, fo, mx, mxo, rax, raxo, off, pad;
                    uint8_t mem[64]; }
                  offsets 0 32 64 96 128 160 192 200 208 216 224 232 240 248 256
     vmovdqa (%rbx), %ymm3       a LOAD:  DEST = YMM3, the 16/32 bytes at RBX
     vmovdqa %ymm2, (%rbx)       a STORE: the 16/32 bytes at RBX := YMM2
   (the %xmm spellings are the VEX.128 forms). ⭐ An aligned kind at a misaligned RBX raises #GP; the probe catches the
   signal around the call (sigsetjmp in the caller), so a fault leaves POST unexecuted and the caller restores MXCSR. */

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

FN(x_vmovdqa128_ld)
        PRE
AT(x_vmovdqa128_ld_at)
        vmovdqa (%rbx), %xmm3
        POST

FN(x_vmovdqa128_st)
        PRE
AT(x_vmovdqa128_st_at)
        vmovdqa %xmm2, (%rbx)
        POST

FN(x_vmovdqa256_ld)
        PRE
AT(x_vmovdqa256_ld_at)
        vmovdqa (%rbx), %ymm3
        POST

FN(x_vmovdqa256_st)
        PRE
AT(x_vmovdqa256_st_at)
        vmovdqa %ymm2, (%rbx)
        POST

FN(x_vmovdqu128_ld)
        PRE
AT(x_vmovdqu128_ld_at)
        vmovdqu (%rbx), %xmm3
        POST

FN(x_vmovdqu128_st)
        PRE
AT(x_vmovdqu128_st_at)
        vmovdqu %xmm2, (%rbx)
        POST

FN(x_vmovdqu256_ld)
        PRE
AT(x_vmovdqu256_ld_at)
        vmovdqu (%rbx), %ymm3
        POST

FN(x_vmovdqu256_st)
        PRE
AT(x_vmovdqu256_st_at)
        vmovdqu %ymm2, (%rbx)
        POST

FN(x_vmovaps128_ld)
        PRE
AT(x_vmovaps128_ld_at)
        vmovaps (%rbx), %xmm3
        POST

FN(x_vmovaps128_st)
        PRE
AT(x_vmovaps128_st_at)
        vmovaps %xmm2, (%rbx)
        POST

FN(x_vmovaps256_ld)
        PRE
AT(x_vmovaps256_ld_at)
        vmovaps (%rbx), %ymm3
        POST

FN(x_vmovaps256_st)
        PRE
AT(x_vmovaps256_st_at)
        vmovaps %ymm2, (%rbx)
        POST

FN(x_vmovups128_ld)
        PRE
AT(x_vmovups128_ld_at)
        vmovups (%rbx), %xmm3
        POST

FN(x_vmovups128_st)
        PRE
AT(x_vmovups128_st_at)
        vmovups %xmm2, (%rbx)
        POST

FN(x_vmovups256_ld)
        PRE
AT(x_vmovups256_ld_at)
        vmovups (%rbx), %ymm3
        POST

FN(x_vmovups256_st)
        PRE
AT(x_vmovups256_st_at)
        vmovups %ymm2, (%rbx)
        POST

FN(x_vmovapd128_ld)
        PRE
AT(x_vmovapd128_ld_at)
        vmovapd (%rbx), %xmm3
        POST

FN(x_vmovapd128_st)
        PRE
AT(x_vmovapd128_st_at)
        vmovapd %xmm2, (%rbx)
        POST

FN(x_vmovapd256_ld)
        PRE
AT(x_vmovapd256_ld_at)
        vmovapd (%rbx), %ymm3
        POST

FN(x_vmovapd256_st)
        PRE
AT(x_vmovapd256_st_at)
        vmovapd %ymm2, (%rbx)
        POST

FN(x_vmovupd128_ld)
        PRE
AT(x_vmovupd128_ld_at)
        vmovupd (%rbx), %xmm3
        POST

FN(x_vmovupd128_st)
        PRE
AT(x_vmovupd128_st_at)
        vmovupd %xmm2, (%rbx)
        POST

FN(x_vmovupd256_ld)
        PRE
AT(x_vmovupd256_ld_at)
        vmovupd (%rbx), %ymm3
        POST

FN(x_vmovupd256_st)
        PRE
AT(x_vmovupd256_st_at)
        vmovupd %ymm2, (%rbx)
        POST
