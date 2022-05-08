# return list for each loops
# each loop is a list of basic blocks
# eg:
# [[b0,b1,b2], [b7,b8,b9]] means two loops, the first with {b0,b1,b2}, the second with {b7,b8,b9}
def calculate_natural_loops(func):
    loops = []

    # find back edges (B -> A when A dominates B)
    # A is called "header", B is called "footer"
    #
    # WARNING:
    #   Basic_block.back_edge is a less strict "edge to ancestor" definition of back edge.
    #   We need the stricter "edge to dominator" definition for loop detection.
    back_edges = []
    for bb in func.basic_blocks:
        for edge in bb.outgoing_edges:
            if edge.target in edge.source.dominators:
                back_edges.append(edge)
                #print('back edge %s -> %s' % (bbstr(edge.source), bbstr(edge.target)))

    # reverse breadth-first search from footer to header, collecting all nodes
    for edge in back_edges:
        (header, footer) = (edge.target, edge.source)
        #print('collecting blocks for loop fenced between %s and %s:' % (bbstr(header), bbstr(footer)))
        loop_blocks = set([header, footer])
        if header != footer:
            queue = [edge.source]
            while queue:
                cur = queue.pop(0)
                loop_blocks.add(cur)
                new_batch = [e.source for e in cur.incoming_edges if (not e.source in loop_blocks)]
                #print('incoming blocks to %s: %s' % (bbstr(cur), [bbstr(x) for x in new_batch]))
                queue.extend(new_batch)
        #print(','.join([bbstr(n) for n in loop_blocks]))

        # store this loop
        loops.append(list(loop_blocks))

    return loops
