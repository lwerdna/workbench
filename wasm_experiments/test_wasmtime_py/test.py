#!/usr/bin/env python

from wasmtime import Store, Module, Instance

store = Store()
module = Module.from_file(store.engine, 'foo.wasm')
instance = Instance(store, module, [])
collatz_next = instance.exports(store)['collatz_next']

print("collatz_next(5) = %d" % collatz_next(store, 5))
