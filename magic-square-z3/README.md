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

In hand solving, I mistakenly thought 15 was required to be in a corner:

```
```

