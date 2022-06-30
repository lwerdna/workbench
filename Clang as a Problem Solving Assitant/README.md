Can clang be used as a problem solving assistant?

Spoiler: No

In [this tweet](https://twitter.com/jckarter/status/1428093469755527168) Joe Groff links to [this online compiler interface](https://gcc.godbolt.org/z/Wrfeo18of) of a [collatz conjecture](https://en.wikipedia.org/wiki/Collatz_conjecture) implementation and clang/llvm optimizes it to return true. Its optimization is so aggressive, and perhaps arrogant, it treats the conjecture as settled and returns 1. The conjecture is of course unproven, and tested only up to about 2**68, a small fraction of the `__int128_t` parameter.

But it raises an interesting question. **Could we glean insights to problems by writing solution checkers and observe clang/llvm's optimizer?** Proposed workflow:

1. write a solution checker
2. compile the solution checker with optimization
3. measure the complexity of the compiled checker (eg: [cyclomatic complexity](https://en.wikipedia.org/wiki/Cyclomatic_complexity) of the resulting CFG)
4. propose bits of the solution by hardcoding them in the solution checker, goto 2

If the complexity of the compiled checker reduces, the partial solution is correct. Iterate this process to converge on a solution.

See [./tests.c](./tests.c) for the tests cases. Result:

```
failed to optimize/simplify simple_divisibility0()
failed to optimize/simplify simple_divisibility1()
failed to optimize/simplify simple_divisibility3()
failed to optimize/simplify simple_divisibility6()
failed to optimize/simplify cleared_bits1()
failed to optimize/simplify cleared_bits2()
failed to optimize/simplify set_bits1()
failed to optimize/simplify set_bits2()
failed to optimize/simplify htpi0()
failed to optimize/simplify magic_square()
failed to optimize/simplify magic_triangle()
```
