Since [github announced support for Mermaid](https://github.blog/2022-02-14-include-diagrams-markdown-files-mermaid/), it's now possible to include many types of drawings in issues, pull requests, or anything else that is treated like github-flavored markdown and rendered, including this file.

Here's an output from [./using-miasm.py](./using-miasm.py):

```mermaid
graph TD
	block_26["792: PUSH       RBP<br>793: MOV        RBP, RSP<br>796: SUB        RSP, 0x10<br>79A: MOV        QWORD PTR [RBP + 0xFFFFFFFFFFFFFFF8], RDI<br>79E: MOV        DWORD PTR [RBP + 0xFFFFFFFFFFFFFFF4], ESI<br>7A1: MOV        EAX, DWORD PTR [RBP + 0xFFFFFFFFFFFFFFF4]<br>7A4: AND        EAX, 0x1<br>7A7: TEST       EAX, EAX<br>7A9: JZ         loc_key_32"]
	block_33["7AB: MOV        EDX, DWORD PTR [RBP + 0xFFFFFFFFFFFFFFF4]<br>7AE: MOV        EAX, EDX<br>7B0: ADD        EAX, EAX<br>7B2: ADD        EAX, EDX<br>7B4: ADD        EAX, 0x1<br>7B7: MOV        DWORD PTR [RBP + 0xFFFFFFFFFFFFFFF4], EAX<br>7BA: JMP        loc_key_34"]
	block_32["7BC: MOV        EAX, DWORD PTR [RBP + 0xFFFFFFFFFFFFFFF4]<br>7BF: MOV        EDX, EAX<br>7C1: SHR        EDX, 0x1F<br>7C4: ADD        EAX, EDX<br>7C6: SAR        EAX, 0x1<br>7C8: MOV        DWORD PTR [RBP + 0xFFFFFFFFFFFFFFF4], EAX"]
	block_36["7D2: MOV        EDX, DWORD PTR [RBP + 0xFFFFFFFFFFFFFFF4]<br>7D5: MOV        RAX, QWORD PTR [RBP + 0xFFFFFFFFFFFFFFF8]<br>7D9: MOV        RSI, RAX<br>7DC: LEA        RDI, QWORD PTR [RIP + 0x252]<br>7E3: MOV        EAX, 0x0<br>7E8: CALL       loc_key_37"]
	block_35["7ED: MOV        EAX, DWORD PTR [RBP + 0xFFFFFFFFFFFFFFF4]<br>7F0: LEAVE      <br>7F1: RET        "]
	block_34["7CB: CMP        QWORD PTR [RBP + 0xFFFFFFFFFFFFFFF8], 0x0<br>7D0: JZ         loc_key_35"]
	block_26 --> block_33
	block_26 --> block_32
	block_36 --> block_35
	block_33 --> block_34
	block_34 --> block_36
	block_34 --> block_35
	block_32 --> block_34
```

Here's an output from [./using-binja.py](./using-binja.py):

```mermaid
graph TD
	b0["00000792: push    rbp<br>00000793: mov     rbp, rsp<br>00000796: sub     rsp, 0x10<br>0000079A: mov     qword [rbp-0x8], rdi<br>0000079E: mov     dword [rbp-0xc], esi<br>000007A1: mov     eax, dword [rbp-0xc]<br>000007A4: and     eax, 0x1<br>000007A7: test    eax, eax<br>000007A9: je      0x7bc"]
	b1["000007BC: mov     eax, dword [rbp-0xc]<br>000007BF: mov     edx, eax<br>000007C1: shr     edx, 0x1f<br>000007C4: add     eax, edx<br>000007C6: sar     eax, 0x1<br>000007C8: mov     dword [rbp-0xc], eax"]
	b2["000007AB: mov     edx, dword [rbp-0xc]<br>000007AE: mov     eax, edx<br>000007B0: add     eax, eax<br>000007B2: add     eax, edx<br>000007B4: add     eax, 0x1<br>000007B7: mov     dword [rbp-0xc], eax<br>000007BA: jmp     0x7cb"]
	b3["000007ED: mov     eax, dword [rbp-0xc]<br>000007F0: leave   <br>000007F1: retn    "]
	b4["000007D2: mov     edx, dword [rbp-0xc]<br>000007D5: mov     rax, qword [rbp-0x8]<br>000007D9: mov     rsi, rax<br>000007DC: lea     rdi, [rel 0xa35]<br>000007E3: mov     eax, 0x0<br>000007E8: call    0x560"]
	b5["000007CB: cmp     qword [rbp-0x8], 0x0<br>000007D0: je      0x7ed"]
	b0 --> b1
	b0 --> b2
	b1 --> b5
	b2 --> b5
	b4 --> b3
	b5 --> b3
	b5 --> b4
```

## Notes

```
Miasm:

AsmCFG
  miasm.core.asmblock.AsmCFG
    .nodes() returns set of LocKey
    .edges() returns list of (LocKey, LocKey) tuples
    .blocks is dict_values of AsmBlock
    .getby_offset()
    .loc_key_to_block()

AsmBlock
  miasm.core.asmblock.AsmBlock
    .lines is list of instruction_x86 object

instruction\_x86
  miasm.arch.x86.arch.instruction\_x86
    .offset

LocKey
  miasm.expression.expression.LocKey
    .key is an int

Mermaid Notes:

- is not like DOT
- newlines with &lt;br&gt;
- label delimeters control vertex shape, like A[Hello] makes a box, A(Hello) makes a box with rounded corners, A{Hello} makes a diamond
```
