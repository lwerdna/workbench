#!/usr/bin/env python

import json

from helpers import *

g_structs_full = False # otherwise emit NTR
g_structs_full_once = False # emit full struct for top level, NTR's for remaining

# superclass DNode to add json-related features
class JNode(DNode):
    def json(self):
        global g_structs_full, g_structs_full_once

        result = None

        if self.tag == 'DW_TAG_subprogram':
            result = {
                'class': 'Function',
                'returns': self.type.json(),
                'parameters': [child.json() for child in self.children],
                'stack_adjustment': [0, 0],
                'has_variable_arguments': [False, 255],
                'calling_convention': {'arch': 'x86_64', 'name': 'sysv'},
                'can_return': [True, 255]
            }
        elif self.tag == 'DW_TAG_pointer_type':
            result = {
                'class': 'Pointer',
                'target': self.type.json(),
                'const': [False, 255],
                'volatile': [False, 255],
                'ref_type': 'PointerReferenceType',
                'width': 8
            }
        elif self.tag == 'DW_TAG_typedef':
            result = {
                'class': 'NamedTypeReference',
                'named_type_class': 'TypedefNamedTypeClass',
                'name': self.name,
                'width': self.byte_size,
                'alignment': 1,
                'type_id': '???'
            }
        elif self.tag == 'DW_TAG_structure_type':
            if g_structs_full:
                if g_structs_full_once:
                    g_structs_full = False

                last_member = self.children[-1]

                result = {
                    'class': 'Structure',
                    'packed': False,
                    'variant': 'StructStructureType',
                    'members': [m.json() for m in self.children],
                    'width': last_member.attributes['DW_AT_data_member_location'] + last_member.byte_size
                }
            else:
                result = {
                    'class': 'NamedTypeReference',
                    'named_type_class': 'StructNamedTypeClass',
                    'name': self.name,
                    'width': self.byte_size,
                    'alignment': 1,
                    'type_id': '???'
                }
        elif self.tag == 'DW_TAG_member':
            return {
                'name': self.name,
                'offset': self.attributes['DW_AT_data_member_location'],
                'type': self.type.json()
            }
        elif self.tag == 'DW_TAG_const_type':
            result = self.type.json()
            result['const'] = [True, 255]
        elif self.tag == 'DW_TAG_base_type':
            if self.name in ['char', 'int', 'unsigned int']:
                result = {
                    'class': 'Integer',
                    'width': self.byte_size,
                    'signed': [not 'unsigned' in self.encoding, 255],
                    'altname': self.name
                }
            else:
                result = 'TODO: DW_TAG_base_type.%s' % self.name
        elif self.tag == 'DW_TAG_formal_parameter':
            result = {
                'name': self.name,
                'type': self.type.json()
            }
        elif self.tag == 'DW_TAG_restrict_type':
            return self.type.json()
        else:
            result = 'TODO: %s' % self.tag

        return result

    def dot_id(self):
        return str(self.offset)

if __name__ == '__main__':
    fpath = sys.argv[1]
    task = sys.argv[2]

    start = None
    if m := re.match(r'^--structure=(.*)$', task):
        g_structs_full = True
        g_structs_full_once = True
        struct_name = m.group(1)
        start = dwarfdump_structure(fpath, struct_name, JNode)
    if m := re.match(r'^--function=(.*)$', task):
        func_name = m.group(1)
        start = dwarfdump_function(fpath, func_name, JNode)
    assert start

    pydata = start.json()

    print(json.dumps(pydata, indent=2))
    
