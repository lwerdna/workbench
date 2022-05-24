#!/usr/bin/env python

import re, os, sys
import json
from helpers import *

data_funcnames = []
data_files = {}

if __name__ == '__main__':
    fnames = [f for f in os.listdir('./datas') if f.endswith('.svg')]
    fpaths = [f'./datas/{name}' for name in fnames]
     
    for fname in fnames:
        func_name = os.path.splitext(fname)[0]
        data_funcnames.append(func_name)

        # get the svg
        print(f'opening: {fname}')
        data_files[fname] = load_file('./datas/'+fname)

        # get the binja layout
        fname = fname.replace('.svg', '_binja.json')
        print(f'opening: {fname}')
        data_files[fname] = load_json('./datas/'+fname)

        # get the dot layout
        fname = fname.replace('_binja.json', '_dot.json')
        print(f'opening: {fname}')
        data_files[fname] = load_json('./datas/'+fname)

        # get the dot_ortho layout
        fname = fname.replace('_dot.json', '_dot_ortho.json')
        print(f'opening: {fname}')
        data_files[fname] = load_json('./datas/'+fname)

    # write it all
    print(f'writing: ./js/data.js')
    with open('./js/data.js', 'w') as fp:
        fp.write('funcs = ' + json.dumps(sorted(data_funcnames)))
        fp.write('\n\n')
        fp.write('files = ' + json.dumps(data_files))
    #fpath_output = fpath_input.replace('-binja.json', '-graphviz.json')
