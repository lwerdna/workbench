ArmV8.7A 2020-09 to 2020-12

The new spec adds 32 encodings:

```
ENC_LD1ROW_Z_P_BR_CONTIGUOUS, ENC_FMMLA_Z_ZZZ_D, ENC_SMMLA_Z_ZZZ_, ENC_FMMLA_Z_ZZZ_S, ENC_LD1ROW_Z_P_BI_U32, ENC_USDOT_Z_ZZZI_S, ENC_LD1ROD_Z_P_BI_U64, ENC_ZIP2_Z_ZZ_Q, ENC_BFMMLA_Z_ZZZ_, ENC_BFDOT_Z_ZZZ_, ENC_ZIP1_Z_ZZ_Q, ENC_UZP1_Z_ZZ_Q, ENC_BFMLALB_Z_ZZZI_, ENC_BFMLALT_Z_ZZZ_, ENC_UMMLA_Z_ZZZ_, ENC_LD1ROH_Z_P_BR_CONTIGUOUS, ENC_LD1ROB_Z_P_BR_CONTIGUOUS, ENC_LD1ROH_Z_P_BI_U16, ENC_SUDOT_Z_ZZZI_S, ENC_UZP2_Z_ZZ_Q, ENC_USDOT_Z_ZZZ_S, ENC_BFCVT_Z_P_Z_S2BF, ENC_BFCVTNT_Z_P_Z_S2BF, ENC_LD1ROD_Z_P_BR_CONTIGUOUS, ENC_TRN1_Z_ZZ_Q, ENC_BFMLALB_Z_ZZZ_, ENC_USMMLA_Z_ZZZ_, ENC_TRN2_Z_ZZ_Q, ENC_BFDOT_Z_ZZZI_, ENC_BFMLALT_Z_ZZZI_, ENC_LD1ROB_Z_P_BI_U8
```

There is now `HasMTE2()` in addition to `HasMTE()`. An encoding like `STZGM_64bulk_ldsttags` is an example needing the former and `STG_64Spost_ldsttags` needing the latter.

Examples of the new encodings follow. Without a reference disassembler, treat these as what they are: my best attempt at proper disassembly given how I read the specification:

```
// BFCVT_Z_P_Z_S2BF 01100101|opc=10|0010|opc2=10|101|Pg=xxx|Zn=xxxxx|Zd=xxxxx
// BFCVT <Zd>.H,<Pg>/M,<Zn>.S
658AB9BB bfcvt z27.h, p6/m, z13.s
658ABDD9 bfcvt z25.h, p7/m, z14.s
658AB944 bfcvt z4.h, p6/m, z10.s
658AA854 bfcvt z20.h, p2/m, z2.s
658AB803 bfcvt z3.h, p6/m, z0.s
658AAE76 bfcvt z22.h, p3/m, z19.s
658AAB20 bfcvt z0.h, p2/m, z25.s
658AA60D bfcvt z13.h, p1/m, z16.s
// BFCVTNT_Z_P_Z_S2BF 01100100|opc=10|0010|opc2=10|101|Pg=xxx|Zn=xxxxx|Zd=xxxxx
// BFCVTNT <Zd>.H,<Pg>/M,<Zn>.S
648AABAB bfcvtnt z11.h, p2/m, z29.s
648AACAB bfcvtnt z11.h, p3/m, z5.s
648AB622 bfcvtnt z2.h, p5/m, z17.s
648AA202 bfcvtnt z2.h, p0/m, z16.s
648AA021 bfcvtnt z1.h, p0/m, z1.s
648AAB67 bfcvtnt z7.h, p2/m, z27.s
648AB0E0 bfcvtnt z0.h, p4/m, z7.s
648AA72F bfcvtnt z15.h, p1/m, z25.s
// BFDOT_Z_ZZZ_ 011001000|op=1|1|Zm=xxxxx|100000|Zn=xxxxx|Zda=xxxxx
// BFDOT <Zda>.S,<Zn>.H,<Zm>.H
64698385 bfdot z5.s, z28.h, z9.h
64628006 bfdot z6.s, z0.h, z2.h
647783C3 bfdot z3.s, z30.h, z23.h
647C838F bfdot z15.s, z28.h, z28.h
646A8395 bfdot z21.s, z28.h, z10.h
646680EC bfdot z12.s, z7.h, z6.h
64638197 bfdot z23.s, z12.h, z3.h
646380D0 bfdot z16.s, z6.h, z3.h
// BFDOT_Z_ZZZI_ 011001000|op=1|1|i2=xx|Zm=xxx|010000|Zn=xxxxx|Zda=xxxxx
// BFDOT <Zda>.S,<Zn>.H,<Zm>.H[<imm>]
646641C6 bfdot z6.s, z14.h, z6.h[0]
64634326 bfdot z6.s, z25.h, z3.h[0]
64764105 bfdot z5.s, z8.h, z6.h[2]
64674374 bfdot z20.s, z27.h, z7.h[0]
64784059 bfdot z25.s, z2.h, z0.h[3]
647E43F1 bfdot z17.s, z31.h, z6.h[3]
646E40A0 bfdot z0.s, z5.h, z6.h[1]
6472416F bfdot z15.s, z11.h, z2.h[2]
// BFMLALB_Z_ZZZ_ 011001001|o2=1|1|Zm=xxxxx|10|op=0|00|T=0|Zn=xxxxx|Zda=xxxxx
// BFMLALB <Zda>.S,<Zn>.H,<Zm>.H
64F682AC bfmlalb z12.s, z21.h, z22.h
64EB8046 bfmlalb z6.s, z2.h, z11.h
64E88195 bfmlalb z21.s, z12.h, z8.h
64E0811B bfmlalb z27.s, z8.h, z0.h
64F68002 bfmlalb z2.s, z0.h, z22.h
64E38339 bfmlalb z25.s, z25.h, z3.h
64EA83D3 bfmlalb z19.s, z30.h, z10.h
64F783A2 bfmlalb z2.s, z29.h, z23.h
// BFMLALB_Z_ZZZI_ 011001001|o2=1|1|i3h=xx|Zm=xxx|01|op=0|0|i3l=x|T=0|Zn=xxxxx|Zda=xxxxx
// BFMLALB <Zda>.S,<Zn>.H,<Zm>.H[<imm>]
64E9410D bfmlalb z13.s, z8.h, z1.h[2]
64F44103 bfmlalb z3.s, z8.h, z4.h[4]
64F74893 bfmlalb z19.s, z4.h, z7.h[5]
64E4415F bfmlalb z31.s, z10.h, z4.h[0]
64ED484B bfmlalb z11.s, z2.h, z5.h[3]
64EE4014 bfmlalb z20.s, z0.h, z6.h[2]
64F64304 bfmlalb z4.s, z24.h, z6.h[4]
64FE4BE4 bfmlalb z4.s, z31.h, z6.h[7]
// BFMLALT_Z_ZZZ_ 011001001|o2=1|1|Zm=xxxxx|10|op=0|00|T=1|Zn=xxxxx|Zda=xxxxx
// BFMLALT <Zda>.S,<Zn>.H,<Zm>.H
64E68747 bfmlalt z7.s, z26.h, z6.h
64EC85D3 bfmlalt z19.s, z14.h, z12.h
64F184A3 bfmlalt z3.s, z5.h, z17.h
64F084AF bfmlalt z15.s, z5.h, z16.h
64EE8721 bfmlalt z1.s, z25.h, z14.h
64FF8410 bfmlalt z16.s, z0.h, z31.h
64E786E6 bfmlalt z6.s, z23.h, z7.h
64F28589 bfmlalt z9.s, z12.h, z18.h
// BFMLALT_Z_ZZZI_ 011001001|o2=1|1|i3h=xx|Zm=xxx|01|op=0|0|i3l=x|T=1|Zn=xxxxx|Zda=xxxxx
// BFMLALT <Zda>.S,<Zn>.H,<Zm>.H[<imm>]
64F14C19 bfmlalt z25.s, z0.h, z1.h[5]
64E54C15 bfmlalt z21.s, z0.h, z5.h[1]
64E04E74 bfmlalt z20.s, z19.h, z0.h[1]
64F7462E bfmlalt z14.s, z17.h, z7.h[4]
64E446D1 bfmlalt z17.s, z22.h, z4.h[0]
64E846A7 bfmlalt z7.s, z21.h, z0.h[2]
64FE4C36 bfmlalt z22.s, z1.h, z6.h[7]
64F24C98 bfmlalt z24.s, z4.h, z2.h[5]
// BFMMLA_Z_ZZZ_ 01100100|opc=01|1|Zm=xxxxx|111001|Zn=xxxxx|Zda=xxxxx
// BFMMLA <Zda>.S,<Zn>.H,<Zm>.H
6470E688 bfmmla z8.s, z20.h, z16.h
647BE5B4 bfmmla z20.s, z13.h, z27.h
646DE5E8 bfmmla z8.s, z15.h, z13.h
6477E473 bfmmla z19.s, z3.h, z23.h
6473E450 bfmmla z16.s, z2.h, z19.h
6472E550 bfmmla z16.s, z10.h, z18.h
6470E5E2 bfmmla z2.s, z15.h, z16.h
6471E7B3 bfmmla z19.s, z29.h, z17.h
// FMMLA_Z_ZZZ_S 01100100|opc=10|1|Zm=xxxxx|111001|Zn=xxxxx|Zda=xxxxx
// FMMLA <Zda>.S,<Zn>.S,<Zm>.S
64A7E5E7 fmmla z7.s, z15.s, z7.s
64A3E465 fmmla z5.s, z3.s, z3.s
64A9E7F1 fmmla z17.s, z31.s, z9.s
64BFE5ED fmmla z13.s, z15.s, z31.s
64BFE5DD fmmla z29.s, z14.s, z31.s
64A8E62B fmmla z11.s, z17.s, z8.s
64A7E7AA fmmla z10.s, z29.s, z7.s
64ABE607 fmmla z7.s, z16.s, z11.s
// FMMLA_Z_ZZZ_D 01100100|opc=11|1|Zm=xxxxx|111001|Zn=xxxxx|Zda=xxxxx
// FMMLA <Zda>.D,<Zn>.D,<Zm>.D
64E6E747 fmmla z7.d, z26.d, z6.d
64F5E743 fmmla z3.d, z26.d, z21.d
64F1E56A fmmla z10.d, z11.d, z17.d
64EFE4FD fmmla z29.d, z7.d, z15.d
64E6E44D fmmla z13.d, z2.d, z6.d
64E2E455 fmmla z21.d, z2.d, z2.d
64EBE59F fmmla z31.d, z12.d, z11.d
64EEE4BB fmmla z27.d, z5.d, z14.d
// LD1ROB_Z_P_BI_U8 1010010|msz=00|ssz=01|0|imm4=xxxx|001|Pg=xxx|Rn=xxxxx|Zt=xxxxx
// LD1ROB {<Zt>.B},<Pg>/Z, [<Xn|SP>{, #<imm>}]
A42F2549 ld1rob {z9.b}, p1/z, [x10, #-0x1]
A4292AF3 ld1rob {z19.b}, p2/z, [x23, #-0x7]
A422294C ld1rob {z12.b}, p2/z, [x10, #0x2]
A42F2E4B ld1rob {z11.b}, p3/z, [x18, #-0x1]
A42F3DC0 ld1rob {z0.b}, p7/z, [x14, #-0x1]
A42E3157 ld1rob {z23.b}, p4/z, [x10, #-0x2]
A42C29A2 ld1rob {z2.b}, p2/z, [x13, #-0x4]
A4212A93 ld1rob {z19.b}, p2/z, [x20, #0x1]
// LD1ROB_Z_P_BR_CONTIGUOUS 1010010|msz=00|ssz=01|Rm=xxxxx|000|Pg=xxx|Rn=xxxxx|Zt=xxxxx
// LD1ROB {<Zt>.B},<Pg>/Z, [<Xn|SP>,<Xm>]
A43713BA ld1rob {z26.b}, p4/z, [x29, x23]
A42C0ECB ld1rob {z11.b}, p3/z, [x22, x12]
A42B04B1 ld1rob {z17.b}, p1/z, [x5, x11]
A4330E95 ld1rob {z21.b}, p3/z, [x20, x19]
A42915F6 ld1rob {z22.b}, p5/z, [x15, x9]
A4291F41 ld1rob {z1.b}, p7/z, [x26, x9]
A42D08C2 ld1rob {z2.b}, p2/z, [x6, x13]
A42E0A86 ld1rob {z6.b}, p2/z, [x20, x14]
// LD1ROD_Z_P_BI_U64 1010010|msz=11|ssz=01|0|imm4=xxxx|001|Pg=xxx|Rn=xxxxx|Zt=xxxxx
// LD1ROD {<Zt>.D},<Pg>/Z, [<Xn|SP>{, #<imm>}]
A5AD395E ld1rod {z30.d}, p6/z, [x10, #-0x3]
A5AC2FB1 ld1rod {z17.d}, p3/z, [x29, #-0x4]
A5A33956 ld1rod {z22.d}, p6/z, [x10, #0x3]
A5A92328 ld1rod {z8.d}, p0/z, [x25, #-0x7]
A5A5268A ld1rod {z10.d}, p1/z, [x20, #0x5]
A5AD2B32 ld1rod {z18.d}, p2/z, [x25, #-0x3]
A5A32334 ld1rod {z20.d}, p0/z, [x25, #0x3]
A5A92031 ld1rod {z17.d}, p0/z, [x1, #-0x7]
// LD1ROD_Z_P_BR_CONTIGUOUS 1010010|msz=11|ssz=01|Rm=xxxxx|000|Pg=xxx|Rn=xxxxx|Zt=xxxxx
// LD1ROD {<Zt>.D},<Pg>/Z, [<Xn|SP>,<Xm>, LSL #3]
A5BD0A61 ld1rod {z1.d}, p2/z, [x19, x29, lsl #0x3]
A5B51BD4 ld1rod {z20.d}, p6/z, [x30, x21, lsl #0x3]
A5AE0238 ld1rod {z24.d}, p0/z, [x17, x14, lsl #0x3]
A5BA113B ld1rod {z27.d}, p4/z, [x9, x26, lsl #0x3]
A5AD0951 ld1rod {z17.d}, p2/z, [x10, x13, lsl #0x3]
A5BE08FA ld1rod {z26.d}, p2/z, [x7, x30, lsl #0x3]
A5A90BFA ld1rod {z26.d}, p2/z, [sp, x9, lsl #0x3]
A5A415CC ld1rod {z12.d}, p5/z, [x14, x4, lsl #0x3]
// LD1ROH_Z_P_BI_U16 1010010|msz=01|ssz=01|0|imm4=xxxx|001|Pg=xxx|Rn=xxxxx|Zt=xxxxx
// LD1ROH {<Zt>.H},<Pg>/Z, [<Xn|SP>{, #<imm>}]
A4AE2746 ld1roh {z6.h}, p1/z, [x26, #-0x2]
A4A935F9 ld1roh {z25.h}, p5/z, [x15, #-0x7]
A4AD2AD3 ld1roh {z19.h}, p2/z, [x22, #-0x3]
A4AC3F85 ld1roh {z5.h}, p7/z, [x28, #-0x4]
A4A22517 ld1roh {z23.h}, p1/z, [x8, #0x2]
A4A63AFC ld1roh {z28.h}, p6/z, [x23, #0x6]
A4A02C80 ld1roh {z0.h}, p3/z, [x4]
A4AB301E ld1roh {z30.h}, p4/z, [x0, #-0x5]
// LD1ROH_Z_P_BR_CONTIGUOUS 1010010|msz=01|ssz=01|Rm=xxxxx|000|Pg=xxx|Rn=xxxxx|Zt=xxxxx
// LD1ROH {<Zt>.H},<Pg>/Z, [<Xn|SP>,<Xm>, LSL #1]
A4B709AC ld1roh {z12.h}, p2/z, [x13, x23, lsl #0x1]
A4A811EE ld1roh {z14.h}, p4/z, [x15, x8, lsl #0x1]
A4A31092 ld1roh {z18.h}, p4/z, [x4, x3, lsl #0x1]
A4A7143E ld1roh {z30.h}, p5/z, [x1, x7, lsl #0x1]
A4B30C8F ld1roh {z15.h}, p3/z, [x4, x19, lsl #0x1]
A4A31B04 ld1roh {z4.h}, p6/z, [x24, x3, lsl #0x1]
A4AE175D ld1roh {z29.h}, p5/z, [x26, x14, lsl #0x1]
A4AC0CCC ld1roh {z12.h}, p3/z, [x6, x12, lsl #0x1]
// LD1ROW_Z_P_BI_U32 1010010|msz=10|ssz=01|0|imm4=xxxx|001|Pg=xxx|Rn=xxxxx|Zt=xxxxx
// LD1ROW {<Zt>.S},<Pg>/Z, [<Xn|SP>{, #<imm>}]
A5292107 ld1row {z7.s}, p0/z, [x8, #-0x7]
A52B22C7 ld1row {z7.s}, p0/z, [x22, #-0x5]
A5233105 ld1row {z5.s}, p4/z, [x8, #0x3]
A5202F61 ld1row {z1.s}, p3/z, [x27]
A526235D ld1row {z29.s}, p0/z, [x26, #0x6]
A5283D03 ld1row {z3.s}, p7/z, [x8, #-0x8]
A52B2A78 ld1row {z24.s}, p2/z, [x19, #-0x5]
A52A29C9 ld1row {z9.s}, p2/z, [x14, #-0x6]
// LD1ROW_Z_P_BR_CONTIGUOUS 1010010|msz=10|ssz=01|Rm=xxxxx|000|Pg=xxx|Rn=xxxxx|Zt=xxxxx
// LD1ROW {<Zt>.S},<Pg>/Z, [<Xn|SP>,<Xm>, LSL #2]
A53C0D39 ld1row {z25.s}, p3/z, [x9, x28, lsl #0x2]
A52B0602 ld1row {z2.s}, p1/z, [x16, x11, lsl #0x2]
A5331D72 ld1row {z18.s}, p7/z, [x11, x19, lsl #0x2]
A53E1CBD ld1row {z29.s}, p7/z, [x5, x30, lsl #0x2]
A53613C0 ld1row {z0.s}, p4/z, [x30, x22, lsl #0x2]
A5301D68 ld1row {z8.s}, p7/z, [x11, x16, lsl #0x2]
A53212F3 ld1row {z19.s}, p4/z, [x23, x18, lsl #0x2]
A53C12EC ld1row {z12.s}, p4/z, [x23, x28, lsl #0x2]
// SMMLA_Z_ZZZ_ 01000101|uns=00|0|Zm=xxxxx|100110|Zn=xxxxx|Zda=xxxxx
// SMMLA <Zda>.S,<Zn>.B,<Zm>.B
45009A56 smmla z22.s, z18.b, z0.b
45119891 smmla z17.s, z4.b, z17.b
45029B26 smmla z6.s, z25.b, z2.b
450C9B16 smmla z22.s, z24.b, z12.b
450A98C6 smmla z6.s, z6.b, z10.b
450E9B70 smmla z16.s, z27.b, z14.b
451398A9 smmla z9.s, z5.b, z19.b
450D9AD4 smmla z20.s, z22.b, z13.b
// SUDOT_Z_ZZZI_S 01000100|size=10|1|i2=xx|Zm=xxx|00011|U=1|Zn=xxxxx|Zda=xxxxx
// SUDOT <Zda>.S,<Zn>.B,<Zm>.B[<imm>]
44B41D0A sudot z10.s, z8.b, z4.b[2]
44BF1EBE sudot z30.s, z21.b, z7.b[3]
44A41CE3 sudot z3.s, z7.b, z4.b[0]
44B91E9E sudot z30.s, z20.b, z1.b[3]
44A91DB9 sudot z25.s, z13.b, z1.b[1]
44B31D3D sudot z29.s, z9.b, z3.b[2]
44B01C4D sudot z13.s, z2.b, z0.b[2]
44A71C29 sudot z9.s, z1.b, z7.b[0]
// TRN1_Z_ZZ_Q 000001011|op=0|1|Zm=xxxxx|000|11|H=0|Zn=xxxxx|Zd=xxxxx
// TRN1 <Zd>.Q,<Zn>.Q,<Zm>.Q
05BA1BB0 trn1 z16.q, z29.q, z26.q
05B218CF trn1 z15.q, z6.q, z18.q
05B4194B trn1 z11.q, z10.q, z20.q
05BB1A52 trn1 z18.q, z18.q, z27.q
05B218CB trn1 z11.q, z6.q, z18.q
05BF1B2D trn1 z13.q, z25.q, z31.q
05A81B65 trn1 z5.q, z27.q, z8.q
05AC1815 trn1 z21.q, z0.q, z12.q
// TRN2_Z_ZZ_Q 000001011|op=0|1|Zm=xxxxx|000|11|H=1|Zn=xxxxx|Zd=xxxxx
// TRN2 <Zd>.Q,<Zn>.Q,<Zm>.Q
05AE1ED6 trn2 z22.q, z22.q, z14.q
05A71F2B trn2 z11.q, z25.q, z7.q
05A21D76 trn2 z22.q, z11.q, z2.q
05B41C00 trn2 z0.q, z0.q, z20.q
05A31CD4 trn2 z20.q, z6.q, z3.q
05B91FF9 trn2 z25.q, z31.q, z25.q
05A41F89 trn2 z9.q, z28.q, z4.q
05B21C26 trn2 z6.q, z1.q, z18.q
// UMMLA_Z_ZZZ_ 01000101|uns=11|0|Zm=xxxxx|100110|Zn=xxxxx|Zda=xxxxx
// UMMLA <Zda>.S,<Zn>.B,<Zm>.B
45D99AAF ummla z15.s, z21.b, z25.b
45CA9B7F ummla z31.s, z27.b, z10.b
45C09805 ummla z5.s, z0.b, z0.b
45D8980B ummla z11.s, z0.b, z24.b
45CC9847 ummla z7.s, z2.b, z12.b
45DF9AFF ummla z31.s, z23.b, z31.b
45D19B6F ummla z15.s, z27.b, z17.b
45D39B39 ummla z25.s, z25.b, z19.b
// USDOT_Z_ZZZ_S 01000100|size=10|0|Zm=xxxxx|011110|Zn=xxxxx|Zda=xxxxx
// USDOT <Zda>.S,<Zn>.B,<Zm>.B
44867AE2 usdot z2.s, z23.b, z6.b
44897B5E usdot z30.s, z26.b, z9.b
44917B12 usdot z18.s, z24.b, z17.b
44817A62 usdot z2.s, z19.b, z1.b
44967839 usdot z25.s, z1.b, z22.b
449B7A20 usdot z0.s, z17.b, z27.b
448E7889 usdot z9.s, z4.b, z14.b
4482787F usdot z31.s, z3.b, z2.b
// USDOT_Z_ZZZI_S 01000100|size=10|1|i2=xx|Zm=xxx|00011|U=0|Zn=xxxxx|Zda=xxxxx
// USDOT <Zda>.S,<Zn>.B,<Zm>.B[<imm>]
44B5188E usdot z14.s, z4.b, z5.b[2]
44A81A4A usdot z10.s, z18.b, z0.b[1]
44AC1A61 usdot z1.s, z19.b, z4.b[1]
44BE1810 usdot z16.s, z0.b, z6.b[3]
44A318A1 usdot z1.s, z5.b, z3.b[0]
44A81B7E usdot z30.s, z27.b, z0.b[1]
44BA1B63 usdot z3.s, z27.b, z2.b[3]
44A01A17 usdot z23.s, z16.b, z0.b[0]
// USMMLA_Z_ZZZ_ 01000101|uns=10|0|Zm=xxxxx|100110|Zn=xxxxx|Zda=xxxxx
// USMMLA <Zda>.S,<Zn>.B,<Zm>.B
45969880 usmmla z0.s, z4.b, z22.b
45909A72 usmmla z18.s, z19.b, z16.b
45819B0A usmmla z10.s, z24.b, z1.b
459E98EC usmmla z12.s, z7.b, z30.b
45919A1E usmmla z30.s, z16.b, z17.b
459E9AFF usmmla z31.s, z23.b, z30.b
45849998 usmmla z24.s, z12.b, z4.b
45979A37 usmmla z23.s, z17.b, z23.b
// UZP1_Z_ZZ_Q 000001011|op=0|1|Zm=xxxxx|000|01|H=0|Zn=xxxxx|Zd=xxxxx
// UZP1 <Zd>.Q,<Zn>.Q,<Zm>.Q
05A40ABA uzp1 z26.q, z21.q, z4.q
05B50A4B uzp1 z11.q, z18.q, z21.q
05A60ADF uzp1 z31.q, z22.q, z6.q
05AE082F uzp1 z15.q, z1.q, z14.q
05A00A6F uzp1 z15.q, z19.q, z0.q
05B80808 uzp1 z8.q, z0.q, z24.q
05AF0B15 uzp1 z21.q, z24.q, z15.q
05A10B84 uzp1 z4.q, z28.q, z1.q
// UZP2_Z_ZZ_Q 000001011|op=0|1|Zm=xxxxx|000|01|H=1|Zn=xxxxx|Zd=xxxxx
// UZP2 <Zd>.Q,<Zn>.Q,<Zm>.Q
05A00C87 uzp2 z7.q, z4.q, z0.q
05BB0F10 uzp2 z16.q, z24.q, z27.q
05B50ECF uzp2 z15.q, z22.q, z21.q
05AE0F5B uzp2 z27.q, z26.q, z14.q
05BA0C6F uzp2 z15.q, z3.q, z26.q
05B80C95 uzp2 z21.q, z4.q, z24.q
05A40F9F uzp2 z31.q, z28.q, z4.q
05A00E16 uzp2 z22.q, z16.q, z0.q
// ZIP2_Z_ZZ_Q 000001011|op=0|1|Zm=xxxxx|000|00|H=1|Zn=xxxxx|Zd=xxxxx
// ZIP2 <Zd>.Q,<Zn>.Q,<Zm>.Q
05A3065F zip2 z31.q, z18.q, z3.q
05A30579 zip2 z25.q, z11.q, z3.q
05AD0425 zip2 z5.q, z1.q, z13.q
05A105AF zip2 z15.q, z13.q, z1.q
05B805D4 zip2 z20.q, z14.q, z24.q
05B50420 zip2 z0.q, z1.q, z21.q
05B00477 zip2 z23.q, z3.q, z16.q
05B10415 zip2 z21.q, z0.q, z17.q
// ZIP1_Z_ZZ_Q 000001011|op=0|1|Zm=xxxxx|000|00|H=0|Zn=xxxxx|Zd=xxxxx
// ZIP1 <Zd>.Q,<Zn>.Q,<Zm>.Q
05A900A3 zip1 z3.q, z5.q, z9.q
05A702CA zip1 z10.q, z22.q, z7.q
05BC0041 zip1 z1.q, z2.q, z28.q
05A4015F zip1 z31.q, z10.q, z4.q
05BD004A zip1 z10.q, z2.q, z29.q
05B50287 zip1 z7.q, z20.q, z21.q
05BB0279 zip1 z25.q, z19.q, z27.q
05B400F3 zip1 z19.q, z7.q, z20.q
```

relevant links:

https://developer.arm.com/architectures/cpu-architecture/a-profile/exploration-tools
