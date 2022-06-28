# Instructions:

These are the relations that hold:

```
asm >= lifted
       lifted ? low
                low <= low_ssa
                low ? medium
                      medium <= medium_ssa
                      medium ? high
                               high <= high_ssa
```

There are always the same or greater number of assembly instructions than lifted instructions. There is no reliable relationship between lifted and low. There are always less or equal low instructions than low ssa. There is no reliable relationship between low and medium. There are always at least as many medium ssa instructions as medium. There is no consistent relationship between medium and high. There is always at least as many high ssa instructions as high.

## Explanation: asm ? lifted

I was very surprised to see the possibility less lifted instructions can exist than assembly. Here's the case from mips64:

```
sub_120050544()
120050514  3c030012   lui     $v1, 0x12
120050518  0079182d   daddu   $v1, $v1, $t9  {0x20170514}
12005051c  24020003   addiu   $v0, $zero, 3
120050520  10820010   beq     $a0, $v0, 0x20050564
120050524  6463cf1c   ??

120050528  28820004   slti    $v0, $a0, 4
12005052c  10400005   beqz    $v0, 0x20050544
120050530  24020002   addiu   $v0, $zero, 2

120050534  10820013   beq     $a0, $v0, 0x20050584
120050538  dc79b698   ld      $t9, -0x4968($v1)

12005053c  10000014   b       0x20050590
120050540  00000000   nop     
```

Lifts to:

```
120050514  $v1 = 0x120000
120050518  $v1 = $v1 + $t9
12005051c  $v0 = 3
120050520  undefined
```

Maybe the only way there can be less lifted IL than assembler is when an `undefined` or otherwise exception case interrupts the lifting process.

## Explanation: lifted ? low

Lifted can have **less** instructions than low because temporary variables can be generated:

```
004001d0  rcx = sub.q{*}(rcx, 0x20)
```

becomes:

```
004001d0  temp2.q = rcx
004001d0  rcx = rcx - 0x20
004001d0  cond:1 = temp2.q - 0x20 s>= 0
```

Lifted can have **more** instructions than low because:

```
0040011d  rax = [data_6ed590].q
00400124  rdx = [rax].q
00400127  and.q{*}(rdx, rdx)
0040012a  if (ne {!=, x87comi.f!=}) then 15 @ 0x400110 else 19 @ 0x40012c
```

reduces to:

```
0040011d  rax = [data_6ed590].q
00400124  rdx = [rax].q
0040012a  if (rdx != 0) then 8 @ 0x400110 else 12 @ 0x40012c
```

This also happens when `nop` in lifted is removed in low.

## Explanation: low ? medium

Low can have **more** instructions than medium, **contracting** during lifting, eg:

```
004000e8  rsp = rsp - 8
004000ec  call(sub_400150)
004000f1  call(sub_400960)
004000f6  rsp = rsp + 8
004000fa  <return> jump(pop)
```

lifts to:

```
004000ec  sub_400150()
004000f1  rax = sub_400960()
004000fa  return rax
```

But it can also **expand** during lifting, with the introduction of temporary variables:

```
004145d1  r8d = _bswap(r8d)
004145d4  [rsi].d = r8d
004145d7  <return> jump(pop)
```

lifts to:

```
004145d1  temp0 = _bswap(r8_1)
004145d1  int32_t r8_3 = temp0
004145d4  [arg2].d = r8_3
004145d7  return 1
```

## Explanation: medium ? high

Medium can have **more** instructions than high, **contracting** during lifting, eg:

```
004000ec  sub_400150()
004000f1  rax = sub_400960()
004000fa  return rax
```

lifts to:

```
004000ec      sub_400150()
004000fa      return sub_400960()
```

Or it can have **less** instructions:

```
00402e1b  return sub_402dc0(arg1, 0, rbx, rbp, r12, r13, r14, r15) __tailcall
```

Gets a bunch of `HLIL_VAR_DECLARE` when it is lifted:

```
00402e1b      int64_t rbx
00402e1b      int64_t rbp
00402e1b      int64_t r12
00402e1b      int64_t r13
00402e1b      int64_t r14
00402e1b      int64_t r15
00402e1b      return sub_402dc0(arg1, 0, rbx, rbp, r12, r13, r14, r15) __tailcall
```

# Blocks

```
asm <= lifted
       lifted == low
                 low == low ssa
                 low == medium
                        medium == medium ssa
                        medium ? high
                                 high == high ssa
```

## Explanation: Why there may be less ASM blocks than lifted blocks

An easy example is x86 `rep movsb` which is a single instruction that doesn't break control flow in assembler, but becomes a loop in lifted IL on the condition of `rcx` being nonzero.

## Explanation: Why medium ? high

TODO
