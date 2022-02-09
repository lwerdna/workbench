How can Z3 solve magic square and variants?

## Magic Square (classic)

Let these variables represent the numbers:

```
A - B - C
| \ | / |
D - E - F
| / | \ |
G - H - I
```

Every row, column, and diagonal must sum to 15, see [./magic-square.smt2](./magic-square.smt2).

```
$ z3 ./magic-square.smt2
```

Which outputs a value for each variable:

````
2 - 7 - 6
| \ | / |
9 - 5 - 1
| / | \ |
4 - 3 - 8
````

## 324. A Star

```
;        A
;       / \
;  B - C - D - E
;   \ /     \ /
;    F       G
;   / \     / \
;  H - I - J - K
;       \ /
;        L
```

See [./324-a-star.smt2](./324-a-star.smt2).

This was very hard for me to solve by hand. A breakthrough came by first solving for odds (O) and evens (E) with each line's required even parity in mind:

```
;        E
;       / \
;  O - E - O - E
;   \ /     \ /
;    O       O
;   / \     / \
;  O - E - O - E
;       \ /
;        E
```

With this sketch available as a reference, you can disqualify number very quickly.

## 325. A Crystal

From The Moscow Puzzles, here are the variables:

```
A  ---  B  ---  C
|     /   \     |
|   D       E   |
| /   \   /   \ |
F       G       H
| \   /   \   / |
|   I       J   |
|     \   /     |
K  ---  L  ---  M 
```

Z3 solution shows 15 is not required in a corner, and repeated number is 5:

```
$ z3 ./325-crystal.smt2
```

```
11 ---  4  ---  5
|     /   \     |
|   15      6   |
| /   \   /   \ |
1       2      10
| \   /   \   / |
|   12      3   |
|     \   /     |
8  ---  7  ---  5
```

There is no solution for all numbers being distinct: [./325-crystal-distinct.smt2](./325-crystal-distinct.smt2).

There is a solution without using 15! [./325-crystal-14.smt2](./325-crystal-14.smt2)

```
10 ---  7  ---  3
|     /   \     |
|   12      2   |
| /   \   /   \ |
1       4      11
| \   /   \   / |
|   14      4   |
|     \   /     |
9  ---  5  ---  6
```

There is a solution without using 15 or 14! [./325-crystal-13.smt2](./325-crystal-13.smt2)

```
1  --- 10  ---  8
|     /   \     |
|   3       5   |
| /   \   /   \ |
7       4       5
| \   /   \   / |
|   11      13  |
|     \   /     |
12 ---  2  ---  6 
```

Though process during hand solve:

* choosing the four corners determines every other variable
* wherever 15 is placed, only (1,4) and (2,3) are possible inline with it, try A=15
* should (B,C) be (1,4) or (4,1)? if B=1, the B-D-F line is impossible to make 20, so A-B-C is (15,4,1)
* should (F,K) be (2,3) or (3,2)?
* now set and test the last corner M, values other than 9, 10, 11 are quickly ruled out

```
15 ---  4  ---  1
|     /   \     |
|   13      8   |
| /   \   /   \ |
3       2       8
| \   /   \   / |
|   10      5   |
|     \   /     |
2  ---  7  --- 11
```
* the method could be summarized as fast search with good starting point and good branch pruning

## Misc. notes

* you can convert the z3py code to smt2lib format by logging, or by the `.sexpr()` function: [./z3-to-smt.py](./z3-to-smt.py).
