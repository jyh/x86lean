/* hwprobe/sse_ops.S — one function per instruction under test, so the byte pattern the
   processor executes is the one written here, never a compiler's choice for an intrinsic.

   Every function has the C signature  uint64_t p_X(uint64_t a, uint64_t b)  (SysV: a in %rdi,
   b in %rsi). `a` is loaded into %xmm0's low quadword and `b` into %xmm1's; the instruction
   runs; the result comes back in %rax. For a comparison the result is RFLAGS. */

#ifdef __APPLE__
#define SYM(x) _##x
#else
#define SYM(x) x
#endif

        .text

#define LOAD            \
        movq %rdi, %xmm0; \
        movq %rsi, %xmm1

        .globl SYM(p_cvtsi2sd)
SYM(p_cvtsi2sd):
        LOAD
        cvtsi2sd %edi, %xmm0            /* f2 0f 2a c7 : the source is a's low 32 bits */
        movq %xmm0, %rax
        ret

        .globl SYM(p_mulsd)
SYM(p_mulsd):
        LOAD
        mulsd %xmm1, %xmm0              /* f2 0f 59 c1 */
        movq %xmm0, %rax
        ret

        .globl SYM(p_mulss)
SYM(p_mulss):
        LOAD
        mulss %xmm1, %xmm0              /* f3 0f 59 c1 */
        movq %xmm0, %rax
        ret

/* B2 (D268 s8): add, sub and div, the same shape as the multiply. */
        .globl SYM(p_addsd)
SYM(p_addsd):
        LOAD
        addsd %xmm1, %xmm0              /* f2 0f 58 c1 */
        movq %xmm0, %rax
        ret

        .globl SYM(p_addss)
SYM(p_addss):
        LOAD
        addss %xmm1, %xmm0              /* f3 0f 58 c1 */
        movq %xmm0, %rax
        ret

        .globl SYM(p_subsd)
SYM(p_subsd):
        LOAD
        subsd %xmm1, %xmm0              /* f2 0f 5c c1 */
        movq %xmm0, %rax
        ret

        .globl SYM(p_subss)
SYM(p_subss):
        LOAD
        subss %xmm1, %xmm0              /* f3 0f 5c c1 */
        movq %xmm0, %rax
        ret

        .globl SYM(p_divsd)
SYM(p_divsd):
        LOAD
        divsd %xmm1, %xmm0              /* f2 0f 5e c1 */
        movq %xmm0, %rax
        ret

        .globl SYM(p_divss)
SYM(p_divss):
        LOAD
        divss %xmm1, %xmm0              /* f3 0f 5e c1 */
        movq %xmm0, %rax
        ret

        .globl SYM(p_minsd)
SYM(p_minsd):
        LOAD
        minsd %xmm1, %xmm0              /* f2 0f 5d c1 */
        movq %xmm0, %rax
        ret

        .globl SYM(p_minss)
SYM(p_minss):
        LOAD
        minss %xmm1, %xmm0              /* f3 0f 5d c1 */
        movq %xmm0, %rax
        ret

        .globl SYM(p_comisd)
SYM(p_comisd):
        LOAD
        comisd %xmm1, %xmm0             /* 66 0f 2f c1 */
        pushfq
        popq %rax
        ret

        .globl SYM(p_ucomisd)
SYM(p_ucomisd):
        LOAD
        ucomisd %xmm1, %xmm0            /* 66 0f 2e c1 */
        pushfq
        popq %rax
        ret

        .globl SYM(p_comiss)
SYM(p_comiss):
        LOAD
        comiss %xmm1, %xmm0             /* 0f 2f c1 */
        pushfq
        popq %rax
        ret

        .globl SYM(p_ucomiss)
SYM(p_ucomiss):
        LOAD
        ucomiss %xmm1, %xmm0            /* 0f 2e c1 */
        pushfq
        popq %rax
        ret

        .globl SYM(p_cvtss2sd)
SYM(p_cvtss2sd):
        LOAD
        cvtss2sd %xmm0, %xmm1           /* f3 0f 5a c8 : source is a's low 32 bits */
        movq %xmm1, %rax
        ret

        .globl SYM(p_cvtsd2ss)
SYM(p_cvtsd2ss):
        LOAD
        cvtsd2ss %xmm0, %xmm1           /* f2 0f 5a c8 : writes %xmm1's low 32 bits; 63:32 keep b's */
        movq %xmm1, %rax
        ret

        .globl SYM(p_cvttsd2si)
SYM(p_cvttsd2si):
        LOAD
        cvttsd2si %xmm0, %eax           /* f2 0f 2c c0 : 32-bit destination, zero-extended */
        ret

/* B4: the integer conversions that round under MXCSR.RC. %xmm1 is the destination, as for cvtsd2ss, so b's
   bits 63:32 are a canary the binary32 forms must leave alone. The source is %edi or %rdi, which holds a. */
/* Functions go ABOVE the GNU-stack trailer below: after it they assemble into a section an ELF linker
   discards, so the Linux leg fails to link while macOS, which has no such section, builds and passes (D274). */
        .globl SYM(p_cvtsi2ss)
SYM(p_cvtsi2ss):
        LOAD
        cvtsi2ssl %edi, %xmm1           /* f3 0f 2a cf : an int32, the low 32 bits of a */
        movq %xmm1, %rax
        ret

        .globl SYM(p_cvtsi2ssq)
SYM(p_cvtsi2ssq):
        LOAD
        cvtsi2ssq %rdi, %xmm1           /* f3 48 0f 2a cf : an int64 */
        movq %xmm1, %rax
        ret

        .globl SYM(p_cvtsi2sdq)
SYM(p_cvtsi2sdq):
        LOAD
        cvtsi2sdq %rdi, %xmm1           /* f2 48 0f 2a cf : an int64; all 64 low bits are written */
        movq %xmm1, %rax
        ret

/* B6 (D287): the square roots, into %xmm1 as cvtsd2ss is, so sqrtss must keep b's bits 63:32; and the rounding
   conversions to an integer, into %eax (zero-extended) or %rax. */
        .globl SYM(p_sqrtss)
SYM(p_sqrtss):
        LOAD
        sqrtss %xmm0, %xmm1             /* f3 0f 51 c8 */
        movq %xmm1, %rax
        ret

        .globl SYM(p_sqrtsd)
SYM(p_sqrtsd):
        LOAD
        sqrtsd %xmm0, %xmm1             /* f2 0f 51 c8 */
        movq %xmm1, %rax
        ret

        .globl SYM(p_cvtss2si)
SYM(p_cvtss2si):
        LOAD
        cvtss2si %xmm0, %eax            /* f3 0f 2d c0 : 32-bit destination, zero-extended */
        ret

        .globl SYM(p_cvtss2siq)
SYM(p_cvtss2siq):
        LOAD
        cvtss2si %xmm0, %rax            /* f3 48 0f 2d c0 */
        ret

        .globl SYM(p_cvtsd2si)
SYM(p_cvtsd2si):
        LOAD
        cvtsd2si %xmm0, %eax            /* f2 0f 2d c0 : 32-bit destination, zero-extended */
        ret

        .globl SYM(p_cvtsd2siq)
SYM(p_cvtsd2siq):
        LOAD
        cvtsd2si %xmm0, %rax            /* f2 48 0f 2d c0 */
        ret

/* B5: the PACKED arithmetic. Every lane is an operand, so the scalar LOAD (which zeroes bits 127:64) would
   compute lanes the row never declared -- and a DIVPS over zeroed lanes raises IE from 0/0 in them. So each
   function takes BOTH quadwords of each operand and returns all 128 bits of the result:
     unsigned __int128 p_X(uint64_t a_lo, uint64_t b_lo, uint64_t a_hi, uint64_t b_hi)
   (SysV: %rdi %rsi %rdx %rcx in; the 128-bit result in %rdx:%rax). The instruction under test starts at
   offset 28: four 5-byte movq and two 4-byte punpcklqdq, which probe.c checks before it runs a row. */
#define LOAD4             \
        movq %rdi, %xmm0; \
        movq %rsi, %xmm1; \
        movq %rdx, %xmm2; \
        movq %rcx, %xmm3; \
        punpcklqdq %xmm2, %xmm0; \
        punpcklqdq %xmm3, %xmm1

#define RET128            \
        movq %xmm0, %rax; \
        punpckhqdq %xmm0, %xmm0; \
        movq %xmm0, %rdx; \
        ret

        .globl SYM(p_mulps)
SYM(p_mulps):
        LOAD4
        mulps %xmm1, %xmm0              /* 0f 59 c1 */
        RET128

        .globl SYM(p_mulpd)
SYM(p_mulpd):
        LOAD4
        mulpd %xmm1, %xmm0              /* 66 0f 59 c1 */
        RET128

        .globl SYM(p_addps)
SYM(p_addps):
        LOAD4
        addps %xmm1, %xmm0              /* 0f 58 c1 */
        RET128

        .globl SYM(p_addpd)
SYM(p_addpd):
        LOAD4
        addpd %xmm1, %xmm0              /* 66 0f 58 c1 */
        RET128

        .globl SYM(p_subps)
SYM(p_subps):
        LOAD4
        subps %xmm1, %xmm0              /* 0f 5c c1 */
        RET128

        .globl SYM(p_subpd)
SYM(p_subpd):
        LOAD4
        subpd %xmm1, %xmm0              /* 66 0f 5c c1 */
        RET128

        .globl SYM(p_divps)
SYM(p_divps):
        LOAD4
        divps %xmm1, %xmm0              /* 0f 5e c1 */
        RET128

        .globl SYM(p_divpd)
SYM(p_divpd):
        LOAD4
        divpd %xmm1, %xmm0              /* 66 0f 5e c1 */
        RET128

#ifndef __APPLE__
        .section .note.GNU-stack,"",@progbits
#endif
