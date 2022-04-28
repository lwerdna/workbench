import os

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
            label = f'{node.instruction_addrs[0]:08X}: {label}'
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

def SymbolToAddr(symbol):
    #return symbol.linked_addr
    return symbol.rebased_addr
    #return symbol.relative_addr

# for symbol resolution name -> addr
def GetSymbolsByName(project, func_name):
    symbols = []

    loader = project.loader

    # METHOD #1: convenience function in loader (assume it visits all objects)
    try:
        sym = project.loader.find_symbol(func_name)
        if sym:
            #print('method#1 found:', sym)
            symbols.append(sym)
    except AttributeError as e:
        # but this is broken for Mach-O, see: https://github.com/angr/cle/issues/194
        # AttributeError: 'list' object has no attribute 'is_import'
        pass

    if symbols:
        return symbols

    # METHOD #2: convenience function in each object
    for obj in loader.all_objects:
        #print(f'searching in {obj}')
        syms = obj.get_symbol('_main')
        if syms:
            #print('method#2 found:', syms)
            symbols.extend(syms)

    if symbols:
        return symbols

    # METHOD #3: look for .symbols_by_name dict in each object
    # but this is deprecated in favor of loader.find_symbol() for lookup or .symbols for enumeration
    for obj in loader.all_objects:
        #print(f'searching in {obj}')

        if not hasattr(obj, 'symbols_by_name'):
            #print('doesn\'t contain .symbols_by_addr')
            continue

        if func_name in obj.symbols_by_name:
            sym = obj.symbols_by_name[func_name]
            #print('method#3 found:', sym)
            symbols.append(sym)
    
    return symbols
