#!/usr/bin/env python

import os
import sys
import angr
from pprint import pprint

from helpers import *

fpath = '../testbins/tests-macos-x64-macho'
if sys.argv[1:]:
    fpath = sys.argv[1]

project = angr.Project(fpath, load_options={"auto_load_libs": False})
loader = project.loader
obj = loader.main_object

# display symbols in main object
print('SYMBOLS IN MAIN OBJECT:')


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
