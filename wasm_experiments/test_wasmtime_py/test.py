#!/usr/bin/env python

# https://bytecodealliance.github.io/wasmtime-py/
# https://github.com/bytecodealliance/wasmtime-py/blob/main/examples/memory.py

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
return_animal0 = exports['return_animal0']
return_animal1 = exports['return_animal1']
return_animal2 = exports['return_animal2']
#print(exports)

# mem: wasmtime._bindings.LP_c_ubyte
def deref_string(mem, mem_len, addr):
    strlen = 0
    for strlen in range(mem_len - addr):
        if mem[addr+strlen] == 0:
            break
        strlen += 1
    else:
        raise Exception('null terminator not found')

    result = ''.join([chr(x) for x in mem[addr:addr+strlen]])

    print('read string from guest @0x%X: "%s"' % (addr, result))
    return result

#------------------------------------------------------------------------------
# EXPERIMENT: can we send and int and return an int?
#------------------------------------------------------------------------------

print("collatz_next(5) = %d" % collatz_next(store, 5))

#------------------------------------------------------------------------------
# EXPERIMENT: can guest/wasm return a string?
#------------------------------------------------------------------------------

# wasmtime._memory.Memory
# memory.data_len(), memory.data_ptr(), memory.grow(), memory.size() memory.type()
memory = exports['memory']
print('memory size in bytes: 0x%X (%d)' % (memory.data_len(store), memory.data_len(store)))
print('memory size in pages: %d' % (memory.size(store)))
print('memory type: %s' % str(memory.type(store)))

lp_c_ubyte = memory.data_ptr(store)

str_addr = return_string(store)
print("return_string(): 0x%X" % str_addr)
deref_string(lp_c_ubyte, memory.data_len(store), str_addr)

deref_string(lp_c_ubyte, memory.data_len(store), return_animal0(store))
deref_string(lp_c_ubyte, memory.data_len(store), return_animal1(store))
deref_string(lp_c_ubyte, memory.data_len(store), return_animal2(store))

#------------------------------------------------------------------------------
# EXPERIMENT: where do malloc()'d buffers in guest/wasm go?
#------------------------------------------------------------------------------

#------------------------------------------------------------------------------
# EXPERIMENT: can guest modify a host buffer?
#------------------------------------------------------------------------------


breakpoint()
