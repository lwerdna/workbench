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
def DrawGraphEnodes(G, lookup, output):
    fpath = '/tmp/tmp.dot'
    print(f'writing {fpath}')
    with open(fpath, 'w') as fp:
        fp.write('digraph g {\n')
        fp.write('\t// nodes\n')
        for node in G.nodes:
            # node: angr.knowledge_plugins.cfg.cfg_node.CFGENode
            label = str(node)
            if func_name := lookup.get(node.function_address, False):
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

def DrawGraphCodeLocations(G, lookup, output):
    fpath = '/tmp/tmp.dot'
    print(f'writing {fpath}')
    with open(fpath, 'w') as fp:
        fp.write('digraph g {\n')
        fp.write('\t// nodes\n')
        for node in G.nodes:
            # node: angr.knowledge_plugins.cfg.cfg_node.CFGENode
            label = lookup.get(node.block_addr, str(node))
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

# for symbol resolution name -> addr

# OPTION #1:
# obj.symbols_by_addr: dict
# pprint(obj.symbols_by_addr)
# but this is deprecated in favor of loader.find_symbol() for lookup or .symbols for enumeration

# OPTION #2:
# project.loader.find_symbol('_main')
# but this is broken for Mach-O, see: https://github.com/angr/cle/issues/194

# OPTION #3:
# obj.get_symbol('_main')
# WORKS

# for symbol resolution addr -> name
# OPTION #1:
# obj.get_symbol_by_address_fuzzy(0x100003eb0)
# doesn't work, despite _main being at this address

# for Mach-O we have to do shit a bit manually:
pprint(list(obj.symbols))
lookup = {s.linked_addr : s.name for s in obj.symbols}

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

DrawGraphEnodes(cfg.graph, lookup, './cfg.png')

# control dependence graph
# cdg: angr.analyses.cdg.CDG
cdg = project.analyses.CDG(cfg)
DrawGraphEnodes(cdg.graph, lookup, './cdg.png')

# Build the data dependence graph. It might take a while. Be patient!
# ddg: angr.analyses.ddg.DDG
ddg = project.analyses.DDG(cfg)
DrawGraphCodeLocations(ddg.graph, lookup, './ddg.png')
