# Can I load a DLL from a memory buffer instead of a file on disk?

# How?

This is where the .dll file is opened, and a section is referring to it.

```
.text:0000000076DA122C C7 44 24 28 60 00 00 00                 mov     dword ptr [rsp+178h+var_150], 60h
.text:0000000076DA1234 48 89 84 24 18 01 00 00                 mov     [rsp+178h+var_60], rax
.text:0000000076DA123C C7 84 24 08 01 00 00 30+                mov     [rsp+178h+var_70], 30h
.text:0000000076DA1247 48 89 BC 24 10 01 00 00                 mov     [rsp+178h+var_68], rdi
.text:0000000076DA124F C7 84 24 20 01 00 00 40+                mov     [rsp+178h+var_58], 40h
.text:0000000076DA125A 48 89 BC 24 28 01 00 00                 mov     [rsp+178h+var_50], rdi
.text:0000000076DA1262 48 89 BC 24 30 01 00 00                 mov     [rsp+178h+var_48], rdi
.text:0000000076DA126A C7 44 24 20 05 00 00 00                 mov     dword ptr [rsp+178h+var_158], 5
.text:0000000076DA1272 E8 C9 03 02 00                          call    ZwOpenFile
.text:0000000076DA1277 85 C0                                   test    eax, eax
.text:0000000076DA1279 0F 88 FB C0 04 00                       js      failed          ; .
.text:0000000076DA1279                                                                 ; .
.text:0000000076DA127F 48 8B 44 24 50                          mov     rax, [rsp+178h+out_handle]
.text:0000000076DA1284 45 33 C9                                xor     r9d, r9d
.text:0000000076DA1287 48 8D 4C 24 58                          lea     rcx, [rsp+178h+var_120]
.text:0000000076DA128C 48 89 44 24 30                          mov     [rsp+178h+out_handle2], rax
.text:0000000076DA1291 41 8D 51 0F                             lea     edx, [r9+0Fh]
.text:0000000076DA1295 45 33 C0                                xor     r8d, r8d
.text:0000000076DA1298 C7 44 24 28 00 00 00 01                 mov     dword ptr [rsp+178h+var_150], 1000000h
.text:0000000076DA12A0 C7 44 24 20 10 00 00 00                 mov     dword ptr [rsp+178h+var_158], 10h
.text:0000000076DA12A8 E8 03 05 02 00                          call    ZwCreateSection
.text:0000000076DA12AD 85 C0                                   test    eax, eax
.text:0000000076DA12AF 0F 88 26 C0 04 00                       js      failed2         ; .
.text:0000000076DA12AF                                                                 ; .
```

We can just hook ZwCreateSection to return a section for a pagefile backed memory containing the DLL's contents.
