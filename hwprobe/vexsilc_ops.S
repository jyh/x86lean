/* hwprobe/vexsilc_ops.S — D350 (V8c): one function per (form, length) under test — VPBROADCASTD from an xmm register
   and from m32, and the VEX.128 / VEX.256 MEMORY forms of VPMADDWD, VPMULHRSW, VPMADDUBSW and VPACKSSDW — so the bytes
   the processor executes are the assembler's encoding of the line written here, and `vexsilc_probe.c` refuses the run
   unless they are the bytes `mk_vexsilc_rows.py` declares. It shares nothing with the other probe paths; PRE and POST
   are `vexsilb_ops.S`'s, restated, plus RBX: the ONE memory operand is `(%rbx)`, and RBX (callee-saved) is pushed in
   PRE, pointed at `&mem[off]`, and popped in POST.

   C signature: void x_X(struct xio *p), with
       struct xio { uint64_t y1[4], y2[4], y3[4], o1[4], o2[4], o3[4], f, fo, mx, mxo, rax, raxo, off, pad;
                    uint8_t mem[64]; }
                  offsets 0 32 64 96 128 160 192 200 208 216 224 232 240 248 256
     vpmaddwd (%rbx), %ymm1, %ymm3      DEST = YMM3, SRC1 = YMM1 (VEX.vvvv), SRC2 = the 16/32 bytes at RBX
     vpbroadcastd %xmm2, %ymm3          DEST = YMM3, SRC = XMM2's low dword
     vpbroadcastd (%rbx), %ymm3         DEST = YMM3, SRC = the 4 bytes at RBX
   (the %xmm spellings are the VEX.128 forms). On exit: fo, mxo, raxo and o1, o2, o3 as in vexsilb_ops.S; `mem` is read
   back by the caller, which proves nothing was written. */

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

FN(x_vpbroadcastd128_r)
        PRE
AT(x_vpbroadcastd128_r_at)
        vpbroadcastd %xmm2, %xmm3
        POST

FN(x_vpbroadcastd128_m)
        PRE
AT(x_vpbroadcastd128_m_at)
        vpbroadcastd (%rbx), %xmm3
        POST

FN(x_vpbroadcastd256_r)
        PRE
AT(x_vpbroadcastd256_r_at)
        vpbroadcastd %xmm2, %ymm3
        POST

FN(x_vpbroadcastd256_m)
        PRE
AT(x_vpbroadcastd256_m_at)
        vpbroadcastd (%rbx), %ymm3
        POST

FN(x_vpmaddwd128_m)
        PRE
AT(x_vpmaddwd128_m_at)
        vpmaddwd (%rbx), %xmm1, %xmm3
        POST

FN(x_vpmaddwd256_m)
        PRE
AT(x_vpmaddwd256_m_at)
        vpmaddwd (%rbx), %ymm1, %ymm3
        POST

FN(x_vpmulhrsw128_m)
        PRE
AT(x_vpmulhrsw128_m_at)
        vpmulhrsw (%rbx), %xmm1, %xmm3
        POST

FN(x_vpmulhrsw256_m)
        PRE
AT(x_vpmulhrsw256_m_at)
        vpmulhrsw (%rbx), %ymm1, %ymm3
        POST

FN(x_vpmaddubsw128_m)
        PRE
AT(x_vpmaddubsw128_m_at)
        vpmaddubsw (%rbx), %xmm1, %xmm3
        POST

FN(x_vpmaddubsw256_m)
        PRE
AT(x_vpmaddubsw256_m_at)
        vpmaddubsw (%rbx), %ymm1, %ymm3
        POST

FN(x_vpackssdw128_m)
        PRE
AT(x_vpackssdw128_m_at)
        vpackssdw (%rbx), %xmm1, %xmm3
        POST

FN(x_vpackssdw256_m)
        PRE
AT(x_vpackssdw256_m_at)
        vpackssdw (%rbx), %ymm1, %ymm3
        POST
