What happens when you try to z3 solve a block cipher like [XTEA](https://en.wikipedia.org/wiki/XTEA)?

Specifically, if we supply plaintext/ciphertext pairs, could z3 solve for the key? This is known as the [Known-plaintext attack (KPA)](https://en.wikipedia.org/wiki/Known-plaintext_attack) scenario or [attack model](https://en.wikipedia.org/wiki/Attack_model).

Obviously this won't work, otherwise block ciphers wouldn't still be in use, but I wonder at what point does it not work, or what makes it not work? Would it work if the cipher were weakened to 1 cycle instead of the 32? If so, 2? 3? How many?

## Test Case

I use this instance from a set of test vectors (see [./xtea_tests.c](./xtea_tests.c)):

plaintext: 0x00112233 0x44556677
ciphertext: 0xd9a4f870, 0xba1f45d6
key: 0x00010203, 0x04050607, 0x08090A0B, 0x0C0D0E0F

This is with all 32 cycles (64 Feistel rounds).

## 1 Cycle Attack: Success

After 1 cycle (2 Feistel rounds) we have ciphertext 0x8BDC52EC, 0x3391FF02

Program [./solve1.py](./solve1.py) finds very quickly the correct key:
```
key0: 0x00010203
key3: 0x0C0D0E0F
```

Note the 2nd (key1) and 3rd (key2) are not scheduled in the first round.

## 2 Cycle Attack: semi-success

After 2 cycles (4 Feistel rounds) we expect ciphertext 0x5A055406, 0xEC8F42BD

Program [./solve2.py](./solve2.py) finds this key:

```
key0: 0xF01CC7A1
key1: 0x11CFB83B
key2: 0x43C28C0D
key3: 0x7400D76C
```

That's not right. Is z3 wrong? No:

```C
	uint32_t key_alt[4] = {0xF01CC7A1, 0x11CFB83B, 0x43C28C0D, 0x7400D76C};
	xtea_encipher_n(2, ptext, key_alt, ctext);
	printf("2cycle' ctext[0]: 0x%08X\n", ctext[0]);
	printf("2cycle' ctext[1]: 0x%08X\n", ctext[1]);
```

Which verifies. In summary we have several keys encrypting 00112233-44556677 to the second cycle output 5A055406-EC8F42BD:

```
xtea2(00112233-44556677, 00010203-04050607-08090A0B-0C0D0E0F) -> 5A055406-EC8F42BD
xtea2(00112233-44556677, F01CC7A1-11CFB83B-43C28C0D-7400D76C) -> 5A055406-EC8F42BD
xtea2(00112233-44556677, 7020C171-279403E2-95EBF595-2F3BD80F) -> 5A055406-EC8F42BD
```

If we impose that the output from the first cycle is the value from the 1 Cycle Attack, it does find the expected key:

```
key0: 0x00010203
key1: 0x04050607
key2: 0x08090A0B
key3: 0x0C0D0E0F
```

But it doesn't seem we should have to do that.

## Are these duplicate keys?

I thought at first that multiple keys could have duplicate effect. But then I realized I was narrowly focused on **this single plaintext/ciphertext pair** and concluding something about whole enciphering.

In these two simplified models of the enciphering bijection with different keys, p0 maps to c1. That's insufficient to conclude the key is a duplicate because the other mappings are different.

```mermaid
graph LR
    subgraph key0
        subgraph plaintexts
            p0
		    p1
		    p2
		    p3
        end

        subgraph ciphertexts
            c0
		    c1
		    c2
		    c3
        end
	end

    p0 --> c1
    p1 --> c2
    p2 --> c3
    p3 --> c0

    subgraph key1
        subgraph plaintexts_
            q0(p0)
		    q1(p1)
		    q2(p2)
		    q3(p3)
        end

        subgraph ciphertexts_
            d0(c0)
		    d1(c1)
		    d2(c2)
		    d3(c3)
        end
	end

    q0 --> d1
    q1 --> d3
    q2 --> d0
    q3 --> d2
```

## Can the Keyspace represent all enciphers/deciphers?

Here's another argument. Since the domain and codomain are the same (plaintexts and ciphertexts are just the 64-bit integers) we can think of enciphering as a permutation. There are `(2**64)!` possible permutations, a number I'm not sure can even be written down in base 10.

But there are "only" 2^128 possible keys: 340282366920938463463374607431768211456.

So, it's silly in hindsight to have thought there was a key for every mapping.

## 2 Cycle Attack

Instead of "helping" by supplying the output of the first cycle, let's help by supplying another plaintext/ciphertext pair:



