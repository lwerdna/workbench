#!/usr/bin/env python

# test on path names, with relation (a,b) = b.startswith(a)

import sys
import random
import algorithm

items = [ \
    './lib/.DS_Store',
    './lib/clang/11.0.0/include/rtmintrin.h',
    './lib/clang/11.0.0/include/waitpkgintrin.h',
    './lib/clang/11.0.0/lib',
    './lib/clang/11.0.0/lib/wasi',
    './lib/clang/11.0.0/lib/wasi/libclang_rt.builtins-wasm32.a',
    './share',
    './share/clang',
    './share/clang/clang-format-bbedit.applescript',
    './share/clang/clang-format-diff.py',
    './share/clang/clang-format-sublime.py',
    './share/clang/clang-format.el',
    './share/clang/clang-format.py',
    './share/clang/clang-tidy-diff.py',
    './share/clang/run-clang-tidy.py',
    './share/cmake',
    './share/cmake/wasi-sdk.cmake',
    './share/misc',
    './share/misc/config.guess',
    './share/misc/config.sub',
    './share/wasi-sysroot',
    './share/wasi-sysroot/include',
    './share/wasi-sysroot/include/__struct_sockaddr_in6.h',
    './share/wasi-sysroot/include/__typedef_uid_t.h',
    './share/wasi-sysroot/include/ftw.h',
    './share/wasi-sysroot/include/semaphore.h',
    './share/wasi-sysroot/include/stdalign.h',
    './share/wasi-sysroot/include/time.h',
    './share/wasi-sysroot/include/utime.h',
    ]

if __name__ == '__main__':
    ancestor_relation = lambda a,b: b.startswith(a)
    sort_key = lambda x: x
    root = algorithm.hierarchy(items, ancestor_relation, sort_key)
    print(root)
