#!/usr/bin/env python

#!/usr/bin/env/python

import sys

from elftools.elf.elffile import ELFFile

ignore_tag_compile_unit = True

def die_info_rec(CU, die, indent_level='    '):
    """ A recursive function for showing information about a DIE and its
        children.
    """
    print(indent_level + 'DIE tag=%s' % str(die)) #die.tag)

    breakpoint()

    child_indent = indent_level + '  '
    for child in die.iter_children():
        die_info_rec(CU, child, child_indent)

def die_name(d):
    return 'die_%d' % d.offset

def die_label(d):
    #lines = str(d).splitlines()

    lines = []
    lines.append('%s size=%d' % (str(d.tag), d.size))

    for (name, attr) in d.attributes.items():
        lines.append('%s: %s val=%s offs=%s' % (name.replace('DW_AT_', ''), str(attr.form).replace('DW_FORM_', ''), str(attr.value), str(attr.offset)))

    return '\\l'.join(lines)

def process_file(filename):
    compilation_units = []
    with open(filename, 'rb') as f:
        elffile = ELFFile(f)
        if not elffile.has_dwarf_info():
            print('  file has no DWARF info')
            sys.exit(-1)
        dwarfinfo = elffile.get_dwarf_info()
        compilation_units = [cu for cu in dwarfinfo.iter_CUs()]

    CU = compilation_units[0]

    #print('  Found a compile unit at offset %s, length %s' % (
    #    CU.cu_offset, CU['unit_length']))

    dies = [d for d in CU.iter_DIEs()]

    #breakpoint()

    print('digraph G {')
    print('\trankdir="LR";')
    print('\t// nodes')
    for d in dies:
        if ignore_tag_compile_unit and d.tag == 'DW_TAG_compile_unit':
            continue
        print('\t%s [label="%s"];' % (die_name(d), die_label(d)))

    print()
    print('\t// edges')
    for src in dies:
        if ignore_tag_compile_unit and src.tag == 'DW_TAG_compile_unit':
            continue
        for dst in src.iter_children():
            print('\t%s -> %s;' % (die_name(src), die_name(dst)))
        
        # do any of the attributes refer to a die by address?
        for (name, attr) in src.attributes.items():
            if attr.form == 'DW_FORM_ref4':
                dst = CU.get_DIE_from_refaddr(attr.value)
                print('\t%s -> %s [style=dashed, color=grey];' % (die_name(src), die_name(dst)))


    print('}')
#    breakpoint()
#
#    # Start with the top DIE, the root for this CU's DIE tree
#    top_DIE = CU.get_top_DIE()
#    print('    Top DIE with tag=%s' % top_DIE.tag)
#
#    # We're interested in the filename...
#    print('    name=%s' % top_DIE.get_full_path())
#
#    # Display DIEs recursively starting with top_DIE
#    die_info_rec(CU, top_DIE)

if __name__ == '__main__':
    process_file(sys.argv[1])

