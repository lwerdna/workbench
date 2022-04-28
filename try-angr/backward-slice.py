#!/usr/bin/env python

import os
import sys
import angr
from pprint import pprint

#(Pdb) p n.instruction_addr
#*** AttributeError: 'CFGENode' object has no attribute 'instruction_addr'
#(Pdb) p n.instruction_addrs
#(4294983344, 4294983345, 4294983348, 4294983352, 4294983359, 4294983362, 4294983366)
#
# G: networkx.classes.digraph.DiGraph
def DrawGraphEnodes(G, addr2name, output):
    fpath = '/tmp/tmp.dot'
    print(f'writing {fpath}')
    with open(fpath, 'w') as fp:
        fp.write('digraph g {\n')
        fp.write('\t// nodes\n')
        for node in G.nodes:
            # node: angr.knowledge_plugins.cfg.cfg_node.CFGENode
            label = str(node)
            if func_name := addr2name.get(node.function_address, False):
                offset = node.instruction_addrs[0] - node.function_address
                label = f'{func_name}+0x{offset:x}' if offset else func_name
            fp.write(f'\t{id(node)} [label="{label}"];\n')
        fp.write('\t// edges\n')
        for (src, dst) in G.edges:
            fp.write(f'\t{id(src)} -> {id(dst)};\n')
        fp.write('}\n')
    cmd = f'dot {fpath} -Tpng -o {output}'
    print(cmd)
    os.system(cmd)

def DrawGraphCodeLocations(G, addr2name, output):
    fpath = '/tmp/tmp.dot'
    print(f'writing {fpath}')
    with open(fpath, 'w') as fp:
        fp.write('digraph g {\n')
        fp.write('\t// nodes\n')
        for node in G.nodes:
            # node: angr.knowledge_plugins.cfg.cfg_node.CFGENode
            label = addr2name.get(node.block_addr, str(node))
            fp.write(f'\t{id(node)} [label="{label}"];\n')
        fp.write('\t// edges\n')
        for (src, dst) in G.edges:
            fp.write(f'\t{id(src)} -> {id(dst)};\n')
        fp.write('}\n')
    cmd = f'dot {fpath} -Tpng -o {output}'
    print(cmd)
    os.system(cmd)

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

#           cfg.kb: angr.knowledge_base.knowledge_base.KnowledgeBase
# cfg.kb.functions: angr.knowledge_plugins.functions.function_manager.FunctionManager
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
