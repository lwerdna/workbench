Recall:

```
0000 eq    Z==1          equal
0001 ne    Z==0          not equal
0010 cs/hs C==1          unsigned higher or same
0011 cc/lo C==0          unsigned lower
0100 mi    N==1          negative
0101 pl    N==0          positive or zero
0110 vs    V==1          overflow
0111 vc    V==0          no overflow
1000 hi    C==1 && Z==0  unsigned higher
1001 ls    C==0 || Z==1  unsigned lower or same
1010 ge    N==V          greater or equal
1011 lt    N!=V          less than
1100 gt    Z==0 && N==V  greater than
1101 le    Z==1 || N!=V  less than or equal
1110 al    (always)
1111 ?     (never)
```

Seems we have four cases:

## Case 0: unsigned, unsigned

```
  64:	e1500001 	cmp	r0, r1
  68:	e3000000 	movw	r0, #0
  6c:	33a00001 	movcc	r0, #1     ; "cc" is also "lo" or unsigned lower
```

## Case 1: unsigned, signed

```
  80:	e1500001 	cmp	r0, r1
  84:	e3000000 	movw	r0, #0
  88:	33a00001 	movcc	r0, #1     ; "cc" is also "lo" or unsigned lower

```

## Case 2: signed, unsigned

```
  9c:	e1500001 	cmp	r0, r1
  a0:	e3000000 	movw	r0, #0
  a4:	33a00001 	movcc	r0, #1     ; "cc" is also "lo" or unsigned lower
```

## Case 3: signed, signed

```
  b8:	e1500001 	cmp	r0, r1
  bc:	e3000000 	movw	r0, #0
  c0:	b3a00001 	movlt	r0, #1	   ; "lt" is "less than" (signed)
```

## unsigned vs. a literal

```
  ; bool hmm0 = a0 < 100;
  d0:	e3500064 	cmp	r0, #100	   ; 0x64
  d4:	e3000000 	movw	r0, #0
  d8:	33a00001 	movcc	r0, #1     ; "cc" is also "lo" or unsigned lower 
```

## signed vs. a literal

```
  ; bool hmm0 = a1 < 100;
  e8:	e3500064 	cmp	r0, #100	   ; 0x64
  ec:	e3000000 	movw	r0, #0
  f0:	b3a00001 	movlt	r0, #1     ; "lt" is "less than" (signed)
```

