#!/usr/bin/env python

import os
import sys

import helpers
import kconfiglib

def collect_menu_nodes(node):
    result = []
    result.append(node)
    if node.list:
        if type(node.list) == list:
            for child in node.list:
                result.extend(collect_menu_nodes(child))
        else:
            result.extend(collect_menu_nodes(node.list))
    if node.next:
        result.extend(collect_menu_nodes(node.next))
    return result

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

def menu_node_to_str_brief(node):
    if node.item.__class__ is kconfiglib.Symbol:
        return f'MENU (symbol:{node.item.name})'

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

	print('digraph g {')
	print(f'\t// {len(mnodes)} nodes')
	for node in mnodes:
	    label = menu_node_to_str_brief(node)
	    print(f'\t{id(node)} [label="{label}"]')
	print('\t// edges')
	for node in mnodes:
	    if node.list:
	        print(f'\t{id(node)} -> {id(node.list)} [label="child"]')
	    #if node.next:
	    #    print(f'\t{id(node)} -> {id(node.next)} [label="next"]')
	print('}')
