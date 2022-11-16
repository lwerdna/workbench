Minimize logic by calling out to the [Espresso heuristic logic minimizer](https://en.wikipedia.org/wiki/Espresso_heuristic_logic_minimizer).

(these results have been integrated into [curiousbits](https://github.com/lwerdna/curiousbits) library)

Strings are given in Python format.

This is not very efficient. It generates all minterms for a given expression and asks Espresso the result over a pipe.

Examples:

```
>>> espresso.minimize('A or (not A and B)')
(B or A)
```

```
>>> espresso.minimize('(A and not B) or (A and B)')
A
```

```
>>> espresso.minimize('(not A and not B and not C) or (not A and not B and C)')
((not B) and (not A))
```

```
>>> espresso.minimize('(not X and not Y and Z) or (not X and Y and Z) or (X and not Y)')
(((not X) and Z) or ((not Y) and X))
```
