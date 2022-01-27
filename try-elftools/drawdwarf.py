#!/usr/bin/env python

import sys

from elftools.elf.elffile import ELFFile

ignore_tag_compile_unit = True

def cu_name(cu):
    die = cu.get_top_DIE()
    return die_attr(die, 'name')

def die_name(d):
    return 'die_%d' % d.offset

def die_label(d):
    #lines = str(d).splitlines()

    lines = []
    #lines.append('%s size=%d' % (str(d.tag), d.size))
    lines.append('%s' % (str(d.tag)))

    for (name, attr) in d.attributes.items():
        value = attr.value
        if type(value) == bytes:
            value = '\\"%s\\"' % value.decode()

        #lines.append('%s: %s val=%s offs=%s' % (name.replace('DW_AT_', ''), str(attr.form).replace('DW_FORM_', ''), str(attr.value), str(attr.offset)))
        lines.append('%s: %s (%s)' % (name.replace('DW_AT_', ''), str(value), str(attr.form).replace('DW_FORM_', '')))

    return '\\l'.join(lines)

def die_attr(die, name):
    if not name.startswith('DW_AT_'): # accept "name" or "DW_AT_name"
        name = 'DW_AT_' + name
    
    if not name in die.attributes:
        return None

    attr = die.attributes[name]
    value = attr.value

    if attr.form in ['DW_FORM_strp', 'DW_FORM_string']:
        if type(value) == bytes:
            value = value.decode()

    return value

# collect DIE's referenced from this die
def collect_dies(die, CUs, seen={}):
    seen.add(die)

    for dst in die.iter_children():
        if not dst in seen:
            collect_dies(dst, CUs, seen)

    for (name, attr) in die.attributes.items():
        if attr.form == 'DW_FORM_ref4':
            dst = deref(die, name, CUs)
            if not dst in seen:
                collect_dies(dst, CUs, seen)

    return seen

#  given: a die and the name of its attribute
# return: the die referenced
def deref(die, attr_name, CUs):
    assert attr_name in die.attributes
    attr = die.attributes[attr_name]
    assert attr.form == 'DW_FORM_ref4'
    for CU in CUs:
        (start, end) = (CU.cu_offset, CU.cu_offset + CU.size)
        if attr.value >= start and attr.value < end:
            return CU.get_DIE_from_refaddr(attr.value)

def process_file(filename, function_name=None):
    print('// opening file, collecting compilation units')
    CUs = []
    with open(filename, 'rb') as f:
        elffile = ELFFile(f)
        if not elffile.has_dwarf_info():
            print('  file has no DWARF info')
            sys.exit(-1)
        dwarfinfo = elffile.get_dwarf_info()
        CUs = [cu for cu in dwarfinfo.iter_CUs()]

    dies = []

    if function_name:
        print('searching for function DIEs')

        matches = []
        for CU in CUs:
            for d in CU.iter_DIEs():
                if die_attr(d, 'name') == function_name:
                    matches.append(d)

        if not matches:
            print('ERROR: couldn\'t find function ' + function_name)
        else:
            print('matches %d DIEs with function name %s' % (len(matches), function_name))

        print('// collecting dies referenced by function')
        related_dies = set()
        for die in matches:
            collect_dies(die, CUs, related_dies)

        print('matches %d related DIE:' % len(related_dies))
        for die in related_dies:
            print(die)
    else:
        print('// collecting all DIEs')
        for CU in CUs:
            #print('[0x%X, 0x%X) %s' % (CU.cu_offset, CU.cu_offset + CU.size, cu_name(CU)))
            for d in CU.iter_DIEs():
                dies.append(d)

    print('digraph G {')
    print('\trankdir="LR";')
    print('\tnode [colorscheme=pastel28];')
    print('\t// nodes')
    for d in dies:
        if ignore_tag_compile_unit and d.tag == 'DW_TAG_compile_unit':
            continue

        extra = ''
        if d.tag == 'DW_TAG_typedef':
            extra = ' color=1, style=filled'
        if d.tag == 'DW_TAG_const_type':
            extra = ' color=2, style=filled'
        if d.tag == 'DW_TAG_pointer_type':
            extra = ' color=3, style=filled'
        if d.tag == 'DW_TAG_structure_type':
            extra = ' color=4, style=filled' 
        if d.tag == 'DW_TAG_subprogram':
            extra = ' color=5, style=filled' 
        if d.tag == 'DW_TAG_formal_parameter':
            extra = ' color=6, style=filled' 
        if d.tag == 'DW_TAG_member':
            extra = ' color=7, style=filled' 
        if d.tag == 'DW_TAG_base_type':
            extra = ' color=8, style=filled' 
        print('\t%s [label="%s" shape="Mrecord"%s];' % (die_name(d), die_label(d), extra))

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
                dst = deref(src, name, CUs)
                print('\t%s -> %s [style=dashed, color=darkgray];' % (die_name(src), die_name(dst)))


    print('}')

if __name__ == '__main__':
    function = None
    if sys.argv[2:]:
        function = sys.argv[2]

    process_file(sys.argv[1], function)

