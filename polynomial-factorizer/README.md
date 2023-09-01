---
DATE_CREATED: 2023-03-17
TAGS: [Math]
---

Can we factor arbitrary polynomials when no special case rules apply?

Factor $x^2 - 1$:

```
$ ./factor.py 'x^2 + -1'
...
(-1x + 1)(-1x + -1)
```

Factor $x^3 + x^2 + x + 1$:

```
$ ./factor 'x^3 + x^2 + x + 1'
...
(x + 1)(x^2 + 1)
```

It works by generating a system of integer equations for a degree 1 divisor, then a degree 2 divisor, and so on to $\lfloor\frac{d}{2}\rfloor$ where $d$ is the degree of the dividend. The equations are solved by calling out to the [Z3 Theorem Prover](https://en.wikipedia.org/wiki/Z3_Theorem_Prover).
