#!/usr/bin/env python

import os
import sys

import helpers
import kconfiglib

def collect_menu_nodes(node):
    result = []
    result.append(node)
    if node.list: # node's children
        result.extend(collect_menu_nodes(node.list))
    if node.next: # node's siblings
        result.extend(collect_menu_nodes(node.next))
    return result

def print_menu_nodes(node, depth=0):
    indent = '  '*depth
    print('\n'.join(f'{indent}{line}' for line in menu_node_to_str(node).split('\n')))
    if node.list:
        print_menu_nodes(node.list, depth+1)
    if node.next:
        print_menu_nodes(node.next, depth)

def find_menu_node_by_sym_name_bfs(root, name):
    if root.item.__class__ is kconfiglib.Symbol:
        if root.item.name == name:
            return root

    for target in [root.next, root.list]:
        if not target:
            continue
        if subresult := find_menu_node_by_sym_name_bfs(target, name):
            return subresult

    return None

def menu_node_to_str(node):
    if node.item.__class__ is kconfiglib.Symbol:
        #                     ARM_DMA_IOMMU_ALIGNMENT
        #if node.item.name == 'ARM_DMA_IOMMU_ALIGNMENT':
        #    breakpoint()

        result = []
        result.append(f'MENU (symbol:{node.item.name})')
        if node.dep and not helpers.is_y(node.dep):
            result.append(f'  depends on: {helpers.expr_to_str(node.dep)}')
        return '\n'.join(result)

    if node.item.__class__ is kconfiglib.Choice:
        s = "MENU (choice"
        if node.item.name is not None:
            s += " " + node.item.name
        s += ')'
        return s

    if node.item is kconfiglib.MENU:
        return "MENU (menu)"

    return "MENU (comment)"

if __name__ == '__main__':
    kconf = helpers.get_kconf_object()

    #menu_nodes = collect_menu_nodes(kconf.top_node)
    mnode_arm = find_menu_node_by_sym_name_bfs(kconf.top_node, 'ARM')
    mnodes = collect_menu_nodes(mnode_arm)


    # kconfiglib is configured through the environment
    os.environ['srctree'] = helpers.get_kernel_path()
    os.environ['SRCARCH'] = 'arm'

    kconf = kconfiglib.standard_kconfig()

    #menu_nodes = collect_menu_nodes(kconf.top_node)
    mnode_arm = find_menu_node_by_sym_name_bfs(kconf.top_node, 'ARM')
    #mnodes = collect_menu_nodes(mnode_arm)

    print_menu_nodes(mnode_arm)

    breakpoint()
