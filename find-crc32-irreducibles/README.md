How many irreducible degree 32 polynomials are there? **134215680** or 3.12495...%

[./search.gp](./search.gp) uses [PARI/GP](https://pari.math.u-bordeaux.fr/)

[./search.sh](./search.sh) calls the PARI/GP searcher with the search space divided into 32 pieces.

[./search.py](./search.py) uses [sympy](https://pypi.org/project/sympy/) and never got going

Fortunately I have access to a 40 core machine at work:

```
./search.sh
```

The results are:

```
range [0x00000000, 0x07FFFFFF] finished, result: 4194816/134217728 == 3.13%
range [0x08000000, 0x0FFFFFFF] finished, result: 4193280/134217728 == 3.12%
range [0x10000000, 0x17FFFFFF] finished, result: 4191744/134217728 == 3.12%
range [0x18000000, 0x1FFFFFFF] finished, result: 4195328/134217728 == 3.13%
range [0x20000000, 0x27FFFFFF] finished, result: 4193280/134217728 == 3.12%
range [0x28000000, 0x2FFFFFFF] finished, result: 4195328/134217728 == 3.13%
range [0x30000000, 0x37FFFFFF] finished, result: 4193280/134217728 == 3.12%
range [0x38000000, 0x3FFFFFFF] finished, result: 4195328/134217728 == 3.13%
range [0x40000000, 0x47FFFFFF] finished, result: 4193280/134217728 == 3.12%
range [0x48000000, 0x4FFFFFFF] finished, result: 4194304/134217728 == 3.13%
range [0x50000000, 0x57FFFFFF] finished, result: 4193280/134217728 == 3.12%
range [0x58000000, 0x5FFFFFFF] finished, result: 4194304/134217728 == 3.13%
range [0x60000000, 0x67FFFFFF] finished, result: 4195328/134217728 == 3.13%
range [0x68000000, 0x6FFFFFFF] finished, result: 4194304/134217728 == 3.13%
range [0x70000000, 0x77FFFFFF] finished, result: 4195328/134217728 == 3.13%
range [0x78000000, 0x7FFFFFFF] finished, result: 4194304/134217728 == 3.13%
range [0x80000000, 0x87FFFFFF] finished, result: 4194304/134217728 == 3.13%
range [0x88000000, 0x8FFFFFFF] finished, result: 4194240/134217728 == 3.12%
range [0x90000000, 0x97FFFFFF] finished, result: 4194368/134217728 == 3.13%
range [0x98000000, 0x9FFFFFFF] finished, result: 4194304/134217728 == 3.13%
range [0xA0000000, 0xA7FFFFFF] finished, result: 4194304/134217728 == 3.13%
range [0xA8000000, 0xAFFFFFFF] finished, result: 4194304/134217728 == 3.13%
range [0xB0000000, 0xB7FFFFFF] finished, result: 4194304/134217728 == 3.13%
range [0xB8000000, 0xBFFFFFFF] finished, result: 4194304/134217728 == 3.13%
range [0xC0000000, 0xC7FFFFFF] finished, result: 4194304/134217728 == 3.13%
range [0xC8000000, 0xCFFFFFFF] finished, result: 4194304/134217728 == 3.13%
range [0xD0000000, 0xD7FFFFFF] finished, result: 4194304/134217728 == 3.13%
range [0xD8000000, 0xDFFFFFFF] finished, result: 4194304/134217728 == 3.13%
range [0xE0000000, 0xE7FFFFFF] finished, result: 4194304/134217728 == 3.13%
range [0xE8000000, 0xEFFFFFFF] finished, result: 4194368/134217728 == 3.13%
range [0xF0000000, 0xF7FFFFFF] finished, result: 4194240/134217728 == 3.12%
range [0xF8000000, 0xFFFFFFFF] finished, result: 4194304/134217728 == 3.13%
```

Summing the columns we have:

```
4194816 + 4193280 + 4191744 + 4195328 + 4193280 + 4195328 + 4193280 + 4195328 + 4193280 + 4194304 + 4193280 + 4194304 + 4195328 + 4194304 + 4195328 + 4194304 + 4194304 + 4194240 + 4194368 + 4194304 + 4194304 + 4194304 + 4194304 + 4194304 + 4194304 + 4194304 + 4194304 + 4194304 + 4194304 + 4194368 + 4194240 + 4194304 = 134215680
```

The lowest irreducibles are:

```
0000008D: x^32 + x^7 + x^3 + x^2 + 1
000000AF: x^32 + x^7 + x^5 + x^3 + x^2 + x + 1
000000C5: x^32 + x^7 + x^6 + x^2 + 1
000000F5: x^32 + x^7 + x^6 + x^5 + x^4 + x^2 + 1
```

The highest are:

```
FFFFFFD7: x^32 + x^31 + x^30 + x^29 + x^28 + x^27 + x^26 + x^25 + x^24 + x^23 + x^22 + x^21 + x^20 + x^19 + x^18 + x^17 + x^16 + x^15 + x^14 + x^13 + x^12 + x^11 + x^10 + x^9 + x^8 + x^7 + x^6 + x^4 + x^2 + x + 1
FFFFFFDD: x^32 + x^31 + x^30 + x^29 + x^28 + x^27 + x^26 + x^25 + x^24 + x^23 + x^22 + x^21 + x^20 + x^19 + x^18 + x^17 + x^16 + x^15 + x^14 + x^13 + x^12 + x^11 + x^10 + x^9 + x^8 + x^7 + x^6 + x^4 + x^3 + x^2 + 1
FFFFFFF3: x^32 + x^31 + x^30 + x^29 + x^28 + x^27 + x^26 + x^25 + x^24 + x^23 + x^22 + x^21 + x^20 + x^19 + x^18 + x^17 + x^16 + x^15 + x^14 + x^13 + x^12 + x^11 + x^10 + x^9 + x^8 + x^7 + x^6 + x^5 + x^4 + x + 1
FFFFFFF5: x^32 + x^31 + x^30 + x^29 + x^28 + x^27 + x^26 + x^25 + x^24 + x^23 + x^22 + x^21 + x^20 + x^19 + x^18 + x^17 + x^16 + x^15 + x^14 + x^13 + x^12 + x^11 + x^10 + x^9 + x^8 + x^7 + x^6 + x^5 + x^4 + x^2 + 1
```

Related: [CRC32(32-bit buffer) is a bijective function](https://yurichev.com/news/20211224_CRC32/)
