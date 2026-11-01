# A.4 REPAIRED: E1 (vir errata), E2 (JB: the length compared UNSIGNED), E3 (the bucket TESTED before it is written:
# cmpl $0 / jle, then subl), E5 (I6: SUB $24,%rsi). Same constants as aswritten.s; code at 0, relocated to 0x1000.
        .text
router:
        cmpq    $24, %rsi
        jb      drop_truncated
        movl    0(%rdi), %eax
        cmpl    $0x4D534731, %eax
        jne     drop_unauthorized
        movl    4(%rdi), %ecx
        movl    8(%rdi), %r8d
        leaq    0x2000(%rip), %r9
        btq     %r8, 0(%r9,%rcx,8)
        jae     drop_unauthorized
        cmpl    $0, 0x3000(%rdx,%rcx,4)
        jle     drop_rate_limited
        subl    $1, 0x3000(%rdx,%rcx,4)
        leaq    24(%rdi), %rax
        subq    $24, %rsi
        jmp     emit_slice
drop_truncated:    nop
drop_unauthorized: nop
drop_rate_limited: nop
emit_slice:        nop
