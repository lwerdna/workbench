global	__libc_csu_init

section .text

__libc_csu_init:
    push   r15
;    lea    r15,[rip+0x2c53]
	nop

    push   r14
    mov    r14,rdx
    push   r13
    mov    r13,rsi
    push   r12
    mov    r12d,edi
    push   rbp
;    lea    rbp,[rip+0x2c44]
	nop

    push   rbx
    sub    rbp,r15
    sub    rsp,0x8
;    call   401000 <_init>
	nop

    sar    rbp,0x3
    je     .loc_401206
    xor    ebx,ebx
    nop    DWORD [rax+0x0]
.loc_4011f0:
    mov    rdx,r14
    mov    rsi,r13
    mov    edi,r12d
    call   QWORD [r15+rbx*8]
    add    rbx,0x1
    cmp    rbp,rbx
    jne    .loc_4011f0
.loc_401206:
    add    rsp,0x8
    pop    rbx
    pop    rbp
    pop    r12
    pop    r13
    pop    r14
    pop    r15
    ret
