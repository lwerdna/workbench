Can clang be used as a problem solving assistant?

TLDR: No

In [this tweet](https://twitter.com/jckarter/status/1428093469755527168) Joe Groff links to [this online compilation](https://gcc.godbolt.org/z/Wrfeo18of) of a [collatz conjecture](https://en.wikipedia.org/wiki/Collatz_conjecture) implementation and clang/llvm optimizes it to return true. That is, regardless of the input number, the sequence will eventually terminate at 1. Obviously that's a bit of a joke, since the conjecture is untested for all unsigned __int128_t.

But it raises a neat question: could we write solution checkers or searchers and outsource an optimization task to clang/llvm to help solve problems? Here's the proposed workflow:

1. write a solution checker
2. compile the solution checker with optimization
3. measure the complexity of the compiled checker (eg: [cyclomatic complexity](https://en.wikipedia.org/wiki/Cyclomatic_complexity) of the resulting CFG)
4. put parts of the solution in the solution checker, goto 2

If the complexity of the compiled checker is reduced, your partial solution is correct. Otherwise it's not. Iterate this process to converge on a solution.

Here's a quick start. All compilation is with `clang -O3 test.c -o test`.

## Test 0: Simple Inequality - SUCCESS

```C
void foo0(int a)
{
	if(a > 10) {
		printf("greater than 10\n");
	}
	else {
		printf("less than 10\n");
	}
}
```

Clang generates a conditional move to avoid branching. What if we clamp a to [0,7] with `a = a & 0b111`?

```
     100003f50  55                 push    rbp {__saved_rbp}
     100003f51  4889e5             mov     rbp, rsp {__saved_rbp}
     100003f54  488d3d4f000000     lea     rdi, [rel data_100003faa]  {"less than 10"}
     100003f5b  5d                 pop     rbp {__saved_rbp}
     100003f5c  e917000000         jmp     _put
```

It "knows" a must be less than 10.

## Test 1: Simple Divisibility Fact - FAILURE

Alright, let's try a simple mathematical truth. All numbers divisible by 4 are divisible by 2. Another way of thinking about it is all numbers with bits b0, b1 cleared have b0 cleared.

```C
void foo2(int a)
{
	if(a % 4)
		return;

	if(a % 2)
		printf("NO\n");
	else
		printf("YES\n");
}
```

It fails to see that "YES" will always be printed, generating another conditional move:

```
     100003f3c  40f6c701           test    dil, 0x1
     100003f40  488d0560000000     lea     rax, [rel data_100003fa7]
     100003f47  488d3d5d000000     lea     rdi, [rel data_100003fab]
     100003f4e  480f44f8           cmove   rdi, rax  {data_100003fa7}
     100003f52  5d                 pop     rbp {__saved_rbp}
     100003f53  e910000000         jmp     _puts
```

I wonder if clang would detect the impossibility of printing "NO" if we made an equivalent test using bits:

```C
void foo3(int a)
{
	if(a & 0b11)
		return;

	// then (a & 0b11) == 0
	//  and (a & 0b1) == 0
	if(a & 0b1)
		printf("NO\n");
	else
		printf("YES\n");
}
```

It fails to see:

```
     100003f3c  40f6c701           test    dil, 0x1
     100003f40  488d0560000000     lea     rax, [rel data_100003fa7]
     100003f47  488d3d5d000000     lea     rdi, [rel data_100003fab]
     100003f4e  480f44f8           cmove   rdi, rax  {data_100003fa7}
     100003f52  5d                 pop     rbp {__saved_rbp}
     100003f53  e910000000         jmp     _puts
```

## Test 2: Easy Theorem #1 - SUCCESS

I introduce two functions with attribute noinline: `print_yes()` and `print_no()` to try to avoid generation of conditional move. I like seeing the explicit branch.

Ok, a number added to itself is necessarily even:

```C
void foo4(int a)
{
	int b = a + a;

	if(b % 2)
		print_no();
	else
		print_yes();
}
```

And clang knows:

```
     100003f50  55                 push    rbp {__saved_rbp}
     100003f51  4889e5             mov     rbp, rsp {__saved_rbp}
     100003f54  5d                 pop     rbp {__saved_rbp}
     100003f55  e926ffffff         jmp     _print_yes
```

## Test 3: Easy Theorem #2 - SUCCESS

A number greater than 10 tripled is greater than 30, so long as it doesn't overflow:

```C
void foo5(int a)
{
	if(! (a > 10 && a < 1000000) ) // [11, 1000000)
		return;

	int b = 3*a;

	if(b <= 30)
		print_no();
	else
		print_yes();
}
```

Clang knows:

```
     100003f40  55                 push    rbp {__saved_rbp}
     100003f41  4889e5             mov     rbp, rsp {__saved_rbp}
     100003f44  83c7f5             add     edi, 0xfffffff5
     100003f47  81ff34420f00       cmp     edi, 0xf4234
     100003f4d  7706               ja      0x100003f55

     100003f4f  5d                 pop     rbp {__saved_rbp}
     100003f50  e9fbfeffff         jmp     _print_yes

     100003f55  5d                 pop     rbp {__saved_rbp}
     100003f56  c3                 retn     {__return_addr}
```

## Test 4: Harder Theorem - FAILURE

Suppose x is a real number and `x != 4`. From the book "How To Prove It 2ed" we know `(2x - 5)/(x - 4) = 3` implies `x = 7`. Provided no overflow occurs, I think this will hold for integers too:

```c
void foo6(int x)
{
	if(x < 1000000 && x != 4) {
		int a = 2*x - 5;
		int b = x - 4;

		if(a % b == 0 && a / b == 3) {
			if(x == 7) {
				print_yes();
			}
			else {
				print_no();
			}
		}
	}
}
```

Clang is unaware that printing "NO" is impossible:

```
...
     100003ee9  5d                 pop     rbp {__saved_rbp}
     100003eea  e9c1feffff         jmp     _print_yes

     100003eef  5d                 pop     rbp {__saved_rbp}
     100003ef0  c3                 retn     {__return_addr}

     100003ef1  5d                 pop     rbp {__saved_rbp}
     100003ef2  e9d9feffff         jmp     _print_no
...
```

It's something I kind of want to check. The simplest way is to loop over everything and see that no "NO" is printed:

```C
for(i=0; i<1000008; ++i)
		foo6(i);
```

Using z3, the theorem is true for reals:

```python
from z3 import *
x = Real('x')
E = Implies(And(x != 4, (2*x - 5)/(x - 4) == 3), x == 7)
prove(E)
```

It's NOT true for integers, if we're not careful:

```python
x = Int('x')
E = Implies(And(x != 4, (2*x - 5)/(x - 4) == 3), x == 7)
prove(E)
```

With counterexample `x = 6` and `(2*x - 5)/(x-4) == 3` because the real result 3.5 is integer'd to 3. But ensuring exact division:

```python
x = Int('x')
a = 2*x - 5
b = x - 4
E = Implies(And(x != 4, a%b == 0, a/b == 3), x == 7)
prove(E)
```

Is proved.

## Test 5: Magic Square - FAILURE

Let's suppose we want to solve the typical 9x9 [magic square](https://en.wikipedia.org/wiki/Magic_square). It's a 3x3 matrix where every row, column, and diagonal must sum to 15 using unique numbers {1, 2, ..., 9}. A solution is:

```
4 9 2
3 5 7
8 1 6
```

The 9 is the most troublesome number to place. To make 15, the other numbers with 9 must sum to 6. That can only be done two ways: 1, 5 and 2, 4. Thus, 9 can only be involved in two sums, so it cannot be on a corner or in the center. Here, the variables {a, b, ..., i} are the locations in the puzzle:

```
a b c
d e f
g h i
```

We insert the impossible assignment `e = 9`:

```C
void foo7(int a, int b, int c, int d, int e, int f, int g, int h, int i)
{
	e = 9;

	/* valid ranges */
	if(a < 1 || a > 9) { print_no(); return; }
	if(b < 1 || b > 9) { print_no(); return; }
	if(c < 1 || c > 9) { print_no(); return; }
	if(d < 1 || d > 9) { print_no(); return; }
	if(e < 1 || e > 9) { print_no(); return; }
	if(f < 1 || f > 9) { print_no(); return; }
	if(g < 1 || g > 9) { print_no(); return; }
	if(h < 1 || h > 9) { print_no(); return; }
	if(i < 1 || i > 9) { print_no(); return; }

	/* they must be unique */
	if(a == b || a == c || a == d || a == e || a == f || a == g || a == h || a == i) { print_no(); return; }
	if(b == c || b == d || b == e || b == f || b == g || b == h || b == i) { print_no(); return; }
	if(c == d || c == e || c == f || c == g || c == h || c == i) { print_no(); return; }
	if(d == e || d == f || d == g || d == h || d == i) { print_no(); return; }
	if(e == f || e == g || e == h || e == i) { print_no(); return; }
	if(f == g || f == h || f == i) { print_no(); return; }
	if(g == h || g == i) { print_no(); return; }
	if(h == i) { print_no(); return; }

	/* rows */
	if(a+b+c != 15) { print_no(); return; }
	if(d+e+f != 15) { print_no(); return; }
	if(g+h+i != 15) { print_no(); return; }

	/* columns */
	if(a+d+g != 15) { print_no(); return; }
	if(b+e+h != 15) { print_no(); return; }
	if(c+f+i != 15) { print_no(); return; }

	/* diagonals */
	if(a+e+i != 15) { print_no(); return; }
	if(c+e+g != 15) { print_no(); return; }

	/* success */
	print_yes();
}
```

But unfortunately clang still thinks it's possible to solve:

```
...
     100003ee9  5d                 pop     rbp {__saved_rbp}
     100003eea  e9d1fcffff         jmp     _print_yes

     100003eef  5d                 pop     rbp {__saved_rbp}
     100003ef0  e9ebfcffff         jmp     _print_no
```

## Test 6: Magic Triangle - FAILURE

A simpler version is [magic triangle](https://en.wikipedia.org/wiki/Magic_triangle_(mathematics)). Here's an order-3 instance where the three sides must sum to 9:

```
    1
   / \
  5   6
 /     \
3 - 4 - 2
```

The 6 cannot be in a corner where its involved in two sums, because the only way it can make a 9 is with a 1, 2. Thus, if we propose it's in the top corner, a smart clang would see the impossibility:

```C
void foo8(int a, int b, int c, int d, int e, int f)
{
	a = 6;

	if(a < 1 || a > 6) { print_no(); return; }
	if(b < 1 || b > 6) { print_no(); return; }
	if(c < 1 || c > 6) { print_no(); return; }
	if(d < 1 || d > 6) { print_no(); return; }
	if(e < 1 || e > 6) { print_no(); return; }
	if(f < 1 || f > 6) { print_no(); return; }

	if(a == b || a == c || a == d || a == e || a == f) { print_no(); return; }
	if(b == c || b == d || b == e || b == f) { print_no(); return; }
	if(c == d || c == e || c == f) { print_no(); return; }
	if(d == e || d == f) { print_no(); return; }
	if(e == f) { print_no(); return; }

	if(a+b+c != 9) { print_no(); return; }
	if(c+d+e != 9) { print_no(); return; }
	if(a+f+e != 9) { print_no(); return; }

	print_yes();
}
```

Yet it's still possible in optimized code for yes to print:

```
...
     100003eea  5d                 pop     rbp {__saved_rbp}
     100003eeb  e910fcffff         jmp     _print_yes

     100003ef0  5d                 pop     rbp {__saved_rbp}
     100003ef1  e92afcffff         jmp     _print_no
```
