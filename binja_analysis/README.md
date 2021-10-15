Exercise some basic Binary Ninja analysis headlessly.

linear disassembly:

![](./assets/linear_disassembly.png)

red block is dominated by green blocks:

![](./assets/dominators.png)

red blocks are detected as loops:

![](./assets/loops.png)

attempt to map from disassembly to HLIL:

![](./assets/il_mapping_640x.png)

loops and nested loops mapped to graphviz clusters:

![](./assets/loop_clusters.png)

