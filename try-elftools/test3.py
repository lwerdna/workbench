#!/usr/bin/env python

import sys, json

from elftools.elf.elffile import ELFFile

#function to read json file
def load_data_encodings():
    with open("data_encodings.json", "r") as fd:
        result = json.load(fd)
    return result

def dump_data_encodings(data):
    with open("data_encodings.json", "w") as fd:
        json.dump(data, fd)

# Opening the ELF file
#change the path to open a different file

with open(sys.argv[1], 'rb') as f:
    elffile = ELFFile(f)
    if not elffile.has_dwarf_info():
        print('file has no DWARF info')
        # get_dwarf_info returns a DWARFInfo context object, which is the
        # starting point for all DWARF-based processing in pyelftools.
    dwarfinfo = elffile.get_dwarf_info()

def make_encodings_json():
    encodings = {}
    param = {}
    for CU in dwarfinfo.iter_CUs():

   

     #used to store tags of child objects
        tags = set()

        for DIE in CU.iter_DIEs():
          
            for child in CU.iter_DIE_children(DIE):
                tags.add(child.tag)

                if child.tag == 'DW_TAG_typedef' or child.tag == "DW_TAG_base_type" or child.tag =='DW_TAG_pointer_type' or child.tag == 'DW_TAG_unspecified_type' \
                        or child.tag =="DW_TAG_array_type":
                    if 'DW_AT_name' in child.attributes and 'DW_AT_type' in child.attributes:
                        # match the name with the type and decode the name(from bytes type to string)
                        encodings[child.attributes['DW_AT_type'][2]] = child.attributes['DW_AT_name'][2].decode()

                        
                        dump_data_encodings(encodings)

                
                if child.tag == 'DW_TAG_member':
                    if 'DW_AT_name' in child.attributes and 'DW_AT_type' in child.attributes:
                        param[child.attributes['DW_AT_name'][2]] = child.attributes['DW_AT_name'][2].decode()
                        param[child.attributes['DW_AT_type'][2]] = child.attributes['DW_AT_type'][2]
                        print(param[child.attributes['DW_AT_name'][2]], param[child.attributes['DW_AT_type'][2]])


def get_var_types():
    #load data from the json file and save it in a variable
    encodings = load_data_encodings()
    #print the data from the json file
    print(encodings)
    param = {}
    for CU in dwarfinfo.iter_CUs():


        # #used to store tags of child objects
        tags = set()

        for DIE in CU.iter_DIEs():

            for child in CU.iter_DIE_children(DIE):
                tags.add(child.tag)

                # print(child)
                if child.tag == 'DW_TAG_member':
                    if 'DW_AT_name' in child.attributes and 'DW_AT_type' in child.attributes:
                        param[child.attributes['DW_AT_name'][2]] = child.attributes['DW_AT_name'][2].decode()
                        param[child.attributes['DW_AT_type'][2]] = child.attributes['DW_AT_type'][2]
                        encoding = str(param[child.attributes['DW_AT_type'][2]])
                        if encoding in encodings:
                            print(param[child.attributes['DW_AT_name'][2]],
                                  encodings[encoding])



if __name__ == '__main__':
    make_encodings_json() # update the json file
    #get_var_types()
