Parse graphviz plain output and produce an SVG.

Obviously there's a `-Tsvg` option to the graphviz utilities, but this is an exercise in consuming the plain format which makes for a great intermediate representation to get layout information.

* [./example.dot](./example.dot) is an example input graph
* [./example.txt](./example.txt) is an example text format produced from `dot -y -Tplain ./example.dot`
* [./plain2svg.py](./plain2svg.py) is the program that converts the text to an svg
* [./example.svg](./example.svg) is an example output, showing the outline of vertices and the spline control points for edges:

![](./example.svg)