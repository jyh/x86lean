# A.4 as written, with E1's REPAIRED form (vir errata) and E5's (I6: SUB $24,%rsi); E2 and E3 KEPT (P5's targets).
# Constants: BUCKET_ARR = 0x3000 (disp32); ACL_BITMAP reached rip-relative at 0x2000. Code at 0 here; the Lean
# program relocates it to 0x1000 (every branch is rip-relative, so the bytes are unchanged).
        .text
router:
        cmpq    $24, %rsi
        jl      drop_truncated
        movl    0(%rdi), %eax
        cmpl    $0x4D534731, %eax
        jne     drop_unauthorized
        movl    4(%rdi), %ecx
        movl    8(%rdi), %r8d
        leaq    0x2000(%rip), %r9
        btq     %r8, 0(%r9,%rcx,8)
        jae     drop_unauthorized
        subl    $1, 0x3000(%rdx,%rcx,4)
        jl      drop_rate_limited
        leaq    24(%rdi), %rax
        subq    $24, %rsi
        jmp     emit_slice
drop_truncated:    nop
drop_unauthorized: nop
drop_rate_limited: nop
emit_slice:        nop
