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

## Worked Example

Suppose we want to factor $133x^6 + 214x^5 + 233x^4 + 212x^3 + 111x^2 + 46x + 11$.

We try first with a degree 1 divisor like $a_1x + a_0$, which would have cofactor $b_5x^5 + b_4x^4 + b_3x^3 + b_2x^2 + b_1x + b_0$. When we multiply it out and perform the algebra, the equations become:

$$
\begin{aligned}
a_0*b_0 = 11 \\
a_0*b_1 + a_1*b_0 = 46 \\
a_0*b_2 + a_1*b_1 = 111 \\
a_0*b_3 + a_1*b_2 = 212 \\
a_0*b_4 + a_1*b_3 = 233 \\
a_0*b_5 + a_1*b_4 = 214 \\
a_1*b_5 = 133 \\
\end{aligned}
$$

No solution.

Now we try a degree 2 divisor like $a_2x^2 + a_1x + a_0$ which would have cofactor $b_4x^4 + b_3x^3 + b_2x^2 + b_1x + b_0$ resulting in equations:

$$
\begin{aligned}
a_0*b_0 = 11 \\
a_0*b_1 + a_1*b_0 = 46 \\
a_0*b_2 + a_1*b_1 + a_2*b_0 = 111 \\
a_0*b_3 + a_1*b_2 + a_2*b_1 = 212 \\
a_0*b_4 + a_1*b_3 + a_2*b_2 = 233 \\
a_1*b_4 + a_2*b_3 = 214 \\
a_2*b_4 = 133
\end{aligned}
$$

No solution.

Now we try a degree 3 divisor like $a_3x^3 + a_2x^2 + a_1x + a_0$ which would have cofactor $b_3 x^3 + b_2 x^2 + b_1 x + b_0$ resulting in equations:

$$
\begin{aligned}
a_0*b_0 = 11 \\
a_0*b_1 + a_1*b_0 = 46 \\
a_0*b_2 + a_1*b_1 + a_2*b_0 = 111 \\
a_0*b_3 + a_1*b_2 + a_2*b_1 + a_3*b_0 = 212 \\
a_1*b_3 + a_2*b_2 + a_3*b_1 = 233 \\
a_2*b_3 + a_3*b_2 = 214 \\
a_3*b_3 = 133
\end{aligned}
$$

Which has a solution!

The solution values $a_3 = 7, a_2 = 5, a_1 = 3, a_0 = 1$ reveal factor $(7x^3 + 5x^2 + 3x + 1).$

And the solution values $b_3 = 19, b_2 = 17, b_1 = 13, b_0=11$ reveal factor $(19x^3 + 17x^2 + 13x + 11)$.

## Miscellany

[./test0.py](./test0.py) shows that z3 can bog down on relatively small systems of linear equations

[./test1.py](./test1.py) explicitly setting "linear integer arithmetic" doesn't seem to help

[./test2.py](./test2.py) constraining the values of the coefficients does help