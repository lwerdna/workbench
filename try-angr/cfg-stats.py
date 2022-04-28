#!/usr/bin/env python

import os
import sys
import angr
from pprint import pprint

fpath = '../testbins/tests-macos-x64-macho'
project = angr.Project(fpath, load_options={"auto_load_libs": False})
loader = project.loader
obj = loader.main_object

# display symbols in main object
print('SYMBOLS IN MAIN OBJECT:')

# for Mach-O we have to do shit a bit manually:
pprint(list(obj.symbols))
addr2name = {s.linked_addr : s.name for s in obj.symbols}
name2addr = {s.name : s.linked_addr for s in obj.symbols}

# Generate a CFG first. In order to generate data dependence graph afterwards, you’ll have to:
# - keep all input states by specifying keep_state=True.
# - store memory, register and temporary values accesses by adding the angr.options.refs option set.
# Feel free to provide more parameters (for example, context_sensitivity_level) for CFG 
# recovery based on your needs.

# control flow graph
# cfg: angr.analyses.cfg.cfg_emulated.CFGEmulated
cfg = project.analyses.CFGEmulated(keep_state=True, 
                             state_add_options=angr.sim_options.refs, 
                             context_sensitivity_level=2
                            )

print('the cfg has %d nodes and %d edges' % (len(cfg.graph.nodes()), len(cfg.graph.edges())))

# this grabs *any* node at a given location:
entry_node = cfg.get_any_node(project.entry)

# on the other hand, this grabs all of the nodes
print("There were %d contexts for the entry block" % len(cfg.get_all_nodes(project.entry)))

# we can also look up predecessors and successors
print("Predecessors of the entry point:", entry_node.predecessors)
print("Successors of the entry point:", entry_node.successors)
print("Successors (and type of jump) of the entry point:", [ jumpkind + " to " + str(node.addr) for node,jumpkind in cfg.get_successors_and_jumpkind(entry_node) ])

# one output of the CFG analysis is the function manager, maps addr -> name
# eg: cfg.kb[0x100003b80] returns <Function sub_100003b80 (0x100003b80)>
#
#           cfg.kb: angr.knowledge_base.knowledge_base.KnowledgeBase
# cfg.kb.functions: angr.knowledge_plugins.functions.function_manager.FunctionManager (can be treated like a dict)

# dict(cfg.kb) =
#  { int : angr.knowledge_plugins.functions.function.Function,
#    ...
#  }
kb = cfg.kb
breakpoint()

#DrawGraphEnodes(cfg.graph, lookup, './cfg.png')

# control dependence graph
# cdg: angr.analyses.cdg.CDG
cdg = project.analyses.CDG(cfg)
#DrawGraphEnodes(cdg.graph, lookup, './cdg.png')

# Build the data dependence graph. It might take a while. Be patient! <DDG Analysis Result at 0x10b1df910>
# ddg: angr.analyses.ddg.DDG
ddg = project.analyses.DDG(cfg)
#DrawGraphCodeLocations(ddg.graph, lookup, './ddg.png')

# See where we wanna go... let’s go to the exit() call, which is modeled as a 
# SimProcedure.

#target_func = cfg.kb.functions.function(name="_print_2path")

# We need the CFGNode instance
breakpoint()
target_node = cfg.get_any_node(name2addr['_print_2path'])

# Let’s get a BackwardSlice out of them!
# `targets` is a list of objects, where each one is either a CodeLocation 
# object, or a tuple of CFGNode instance and a statement ID. Setting statement 
# ID to -1 means the very beginning of that CFGNode. A SimProcedure does not 
# have any statement, so you should always specify -1 for it.
bs = project.analyses.BackwardSlice(cfg, cdg=cdg, ddg=ddg, targets=[ (target_node, -1) ])

# Here is our awesome program slice!
print(bs)
