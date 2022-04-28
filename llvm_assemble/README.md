Sandalone disassemblers by linking with LLVM.

No modifications to LLVM like keystone does, but we lose ability to assemble at address without fill bytes.

## methodA
* assemble to an in-memory assembler file, parse out the comments
* advantage: instruction boundaries are given
* advantage: no filler from .org statements
* disadvantage: have to parse string
* disadvantage: relocation stuff is left hanging (jmp to labels won't be resolved):
```
	jmp	foo                     ## encoding: [0xeb,A]
                                        ##   fixup A - offset: 1, value: foo-1, kind: FK_PCRel_1
                                        ## <MCInst #1132 JMP_1
                                        ##  <MCOperand Expr:(foo)>>
```

## methodB
* assemble to an in-memory object file, parse the bytes
* advantage: relocation stuff is resolved
* disadvantage: no instruction boundaries
* disadvantage: file format parsing
* disadvantage: .org statement fill with bytes
