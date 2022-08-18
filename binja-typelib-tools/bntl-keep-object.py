#!/usr/bin/env python

# delete all but one type from the typelib

import os, sys
import binaryninja
from binaryninja import typelibrary

def create_typelib(fname, name, arch, guid, dependency_name, alternate_names,
  platform_names, named_objects, named_types):

    typelib = binaryninja.typelibrary.TypeLibrary.new(arch, name)
    typelib.guid = guid

    if alternate_names and type(alternate_names[0])==bytes:
        alternate_names = [x.decode('utf-8') for x in alternate_names]
    for an in alternate_names:
        typelib.add_alternate_name(an)

    if platform_names and type(platform_names[0])==bytes:
        platform_names = [x.decode('utf-8') for x in platform_names]
    for pn in platform_names:
        typelib.add_platform(binaryninja.Platform[pn])

    for (name, obj) in named_objects.items():
        typelib.add_named_object(name, obj)

    for (name, type_) in named_types.items():
        typelib.add_named_type(name, type_)

    typelib.finalize()
    typelib.write_to_file(fname)

if __name__ == '__main__':
    binaryninja._init_plugins()

    fpath = sys.argv[1]
    objname = sys.argv[2]
    print('keeping %s from %s' % (objname, fpath))

    # read bntl
    tl = typelibrary.TypeLibrary.load_from_file(fpath)

    named_objects = {k:v for (k,v) in tl.named_objects.items() if k == objname}

    named_types = {}

    print('named objects %d -> %d' % (len(tl.named_objects), len(named_objects)))
    print('named types %d -> %d' % (len(tl.named_types), len(named_types)))

    if len(tl.named_objects) == len(named_objects) and len(tl.named_types) == len(named_types):
        print('no change, skipping write')
        sys.exit(0)

    # write
    print('writing /tmp/tmp.bntl')
    create_typelib('/tmp/tmp.bntl', tl.name, tl.arch, tl.guid,
      tl.dependency_name, tl.alternate_names, [x.decode('utf-8') for x in tl.platform_names],
      named_objects, named_types)
    
    # copy it back
    cmd = 'cp /tmp/tmp.bntl %s' % fpath
    print(f'copying it back: {cmd}')
    os.system(cmd)
