#!/usr/bin/env python

# https://bytecodealliance.github.io/wasmtime-py/

import wasmtime

def print_type(foo):
    if type(foo) == wasmtime._func.Func:
        ftype = foo.type(store)
        print('%s <function>(%s)' % (ftype.results, ftype.params))
    else:
        breakpoint()

# wasmtime._store.Store
store = wasmtime.Store()

# wasmtime._module.Module
module = wasmtime.Module.from_file(store.engine, 'foo.wasm')

# wasmtime._instance.Instance
instance = wasmtime.Instance(store, module, [])

# wasmtime._instance.InstanceExports
# wasmtime._func.Func
exports = instance.exports(store)
# print this shit! exports! stuff you didn't think
collatz_next = exports['collatz_next']
return_string = exports['return_string']
#print(exports)

# wasmtime._memory.Memory
memory = exports['memory']
lp_c_ubyte = memory.data_ptr(store)

# memory.data_len(), memory.data_ptr(), memory.grow(), memory.size() memory.type()
print('linear memory is size: 0x%X' % memory.data_len(store));

print_type(collatz_next)
print_type(return_string)

print("collatz_next(5) = %d" % collatz_next(store, 5))
print("return_string() = 0x%X" % return_string(store))

str_addr = return_string(store)
buf = lp_c_ubyte[str_addr:str_addr + 256]
buf = buf[0:buf.index(0)]
print("return_string() returned: %s" % ''.join([chr(x) for x in buf]))

breakpoint()
