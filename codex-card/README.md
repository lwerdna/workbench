## Front of Card

The text has highlighted red characters: "there are eigHt FLAGs".

The initial bytes:

```
6a 03 59 48 8d 35 06 00 00 00 51 48 ad 48 93 48 ad 48 31 d8 50 e2 f6 f4 c8 1b 45 b9 33 89 f6 f4 0e 36 00 2e 05 0d 54 58 2d 09 15 28 5b 32 3d 0b 66 4c 41 47 1d 74 49 43 66 90
```

Disassemble (x86_64) to:

```
00000000  6a03               push    0x3 {i_1}
00000002  59                 pop     rcx {i_1}
00000003  488d3506000000     lea     rsi, [rel data_10]
0000000a  51                 push    rcx {i_1}
0000000b  48ad               lodsq   qword [rsi]
0000000d  4893               xchg    rbx, rax
0000000f  48ad               lodsq   qword [rsi]  {sub_0}
00000011  4831d8             xor     rax, rbx
00000014  50                 push    rax
00000015  e2f6               loop    0xd
00000017  f4                 hlt
db 0e 36 00 2e 05 0d 54 58 2d 09 15 28 5b 32 3d 0b 66 4c 41 47 1d 74 49 43 66 90
```

When emulated, that loop ends up pushing these bytes to the stack:

```
F000FFE0: 46 6C 61 67 3D 54 69 53 6B 65 74 4F 66 66 54 58  Flag=TiSketOffTX
F000FFF0: 65 53 74 61 63 6B 00 00 03 00 00 00 00 00 00 00  eStack..........
```

So the first flag is `TiSketOffTXeStack`.

The text `Y3RmQHJheXRoZW9uLmNvbQ==` base64 decoded (the trailing equals signs are the clue) to ctf@raytheon.com.

## Back of Card

The binary numbers are just base2 representation of ascii codes:

```python
nums = [0b01000110, 0b01101100, 0b01100001, 0b01100111, 0b00111101, 0b00110010, 0b01000101, 0b01011010, 0b00110000, 0b00110001, 0b00000000, 0b00000000]

print(''.join(chr(n) for n in nums))
```

Which prints `Flag=2EZ01`.

The C code is tough:

```C
void enc(char *flag, byte key)
{
  while(*flag)
  {
    *flag ^= (key=(key*13)+37);
    *(flag++) += 3;
  }
}
```

Because we don't know what the key is, but limited to one byte, we can brute force it: see [./enc.py](./enc.py) which tries all keys, and we get something human readable for key=127=0x7f:

```
for key 127: Flag=Don'tPanic
```

In other words, `enc("Don'tPanic", 0x7f)` produces the hardcoded output on the card.