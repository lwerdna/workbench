Calculate where all paths from a CFG node converge. At these points, reaching conditions can be simplified.

(these results have been integrated into [curiousbits](https://github.com/lwerdna/curiousbits) library)

https://stackoverflow.com/questions/59656961/in-a-dag-how-to-find-vertices-where-paths-converge

It's equivalent to asking "What's the most immediate post dominator?".

### Example 0

![](./assets/generated0.svg)

The path from `3` converges at `7`. The path from `8` converges at `11`. All other splits wait until node `12` to converge.

```
$ ./test.py ./generated0.graph
paths from 7 converge at 12
paths from 10 converge at 12
paths from 8 converge at 11
paths from 3 converge at 7
```

### Example 1

![](./assets/generated1.svg)

```
$ ./test.py ./generated1.graph
paths from 6 converge at 12
paths from 5 converge at 12
paths from 10 converge at 12
paths from 11 converge at 12
paths from 7 converge at 8
```

## Applied to reaching conditions

Let letters from the alphabet represent path conditions from nodes that branch.

Then the node `dst` where all paths from `src` converge can completely disregard the path condition variable `X` set at `src`.

### Example 0

![](./assets/generated0-logic.svg)

After reduction just at the converge points we get:

![](./assets/generated0-reduced-converge.svg)

After reduction at the converge points AND DESCENDANTS we get:

![](./assets/generated0-reduced.svg)

### Example 1

![](./assets/generated1-logic.svg)

After reduction just at the converge points we get:

![](./assets/generated1-reduced-converge.svg)

After reduction at the converge points AND DESCENDANTS we get:

![](./assets/generated1-reduced.svg)

