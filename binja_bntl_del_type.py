#!/usr/bin/env python

import os, sys
import binaryninja
from binaryninja import typelibrary

import blacklist

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
    typename = sys.argv[2]
    print('removing %s from %s' % (typename, fpath))

    # read bntl
    tl = typelibrary.TypeLibrary.load_from_file(fpath)

    print('before filtering, typelib had %d named types' % len(tl.named_types))
    named_types = {key:tl.named_types[key] for key in tl.named_types if not key == typename}
    print('after filtering, typelib had %d named types' % len(named_types))

    if len(tl.named_types) == len(named_types):
        print('no change, skipping write')
        sys.exit(0)

    # write
    print('writing /tmp/tmp.bntl')
    create_typelib('/tmp/tmp.bntl', tl.name, tl.arch, tl.guid,
      tl.dependency_name, tl.alternate_names, [x.decode('utf-8') for x in tl.platform_names],
      tl.named_objects, named_types)
    
    # copy it back
    print('copying it back')
    os.system('cp /tmp/tmp.bntl %s' % fpath)
