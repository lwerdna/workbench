tools/scripts/notes for BinaryNinja issue: [Inconsistency in jump table recovery depending on LDR, TBB/TBH #77](https://github.com/Vector35/arch-armv7/issues/77)

A jump table with load register instruction `LDR` used for dispatching a case produces bad case indices in HLIL:

```
00008074  void SetSemaphore(char arg1, char arg2)
00008084      uint32_t r3_2 = zx.d(arg1)
00008088      if (r3_2 u<= 8)
00008086      {
0000808e          switch (jump_table_8094[r3_2])
0000808e          {
000080bc              case 0x80b8
...
```

See [./assemble-from-scratch/using-ldr.s](./assemble-from-scratch/using-ldr.s) to reproduce.

While a jump table with table branch byte instruction `TBB` produces correct indices:

```
00008084      uint32_t r3_2 = zx.d(arg1)
00008088      if (r3_2 u<= 8)
00008086      {
0000808e          switch (r3_2)
0000808e          {
000080bc              case 0
...
```

See [./assemble-from-scratch/using-tbb.s](./assemble-from-scratch/using-tbb.s) to reproduce.

See [./unicorn-repl-scripts/](./unicorn-repl-scripts) for experiments with [../unicorn-repls](../unicorn-repls) to understand how LDR and TBB work in an emulator.
