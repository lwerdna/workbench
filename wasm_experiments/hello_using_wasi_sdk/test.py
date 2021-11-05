#!/usr/bin/env python

# https://bytecodealliance.github.io/wasmtime-py/
# https://github.com/bytecodealliance/wasmtime-py/blob/main/examples/memory.py

import wasmtime

store = wasmtime.Store()
module = wasmtime.Module.from_file(store.engine, 'helloworld.wasm')
instance = wasmtime.Instance(store, module, [])

exports = instance.exports(store)
collatz_next = exports['add']
print("add(3,5) = %d" % add(store, 3, 5))


