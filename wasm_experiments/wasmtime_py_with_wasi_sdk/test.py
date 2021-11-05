#!/usr/bin/env python

# https://bytecodealliance.github.io/wasmtime-py/
# https://github.com/bytecodealliance/wasmtime-py/blob/main/examples/memory.py

import wasmtime

# utility functions

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

# functions the guest/wasm is expecting to import
def proc_exit_(arg0):
    print("dummy proc_exit(0x%X)" % arg0);

def args_sizes_get_(arg0, arg1):
    print("dummy args_sizes_get(0x%X, 0x%X)" % (arg0, arg1));
    return 0;

def args_get_(arg0, arg1):
    print("dummy args_get(0x%X, 0x%X)" % (arg0, arg1));
    return 0;

store = wasmtime.Store()
module = wasmtime.Module.from_file(store.engine, 'foo.wasm')

i32 = wasmtime.ValType.i32()
proc_exit = wasmtime.Func(store, wasmtime.FuncType([i32], []), proc_exit_)
args_sizes_get = wasmtime.Func(store, wasmtime.FuncType([i32, i32], [i32]), args_sizes_get_)
args_get = wasmtime.Func(store, wasmtime.FuncType([i32, i32], [i32]), args_get_)

exports_to_guest = [proc_exit, args_sizes_get, args_get]
instance = wasmtime.Instance(store, module, exports_to_guest)

exports = instance.exports(store)

add = exports['add']
print("add(3,5) = %d" % add(store, 3, 5))

memory = exports['memory']
print('memory size in bytes: 0x%X (%d)' % (memory.data_len(store), memory.data_len(store)))
print('memory size in pages: %d' % (memory.size(store)))
print('memory type: %s' % str(memory.type(store)))
lp_c_ubyte = memory.data_ptr(store)

animal0 = exports['animal0']
deref_string(lp_c_ubyte, memory.data_len(store), animal0(store));

create_buf = exports['create_buf']
print('allocating returned address: 0x%X:' % create_buf(store))
print('allocating returned address: 0x%X:' % create_buf(store))
print('allocating returned address: 0x%X:' % create_buf(store))

addr = create_buf(store)
lp_c_ubyte[addr] = 23 # struct addends .a = 23
lp_c_ubyte[addr+1] = 0
lp_c_ubyte[addr+2] = 0
lp_c_ubyte[addr+3] = 0
lp_c_ubyte[addr+4] = 27 # struct addends .b = 27
lp_c_ubyte[addr+5] = 0
lp_c_ubyte[addr+6] = 0
lp_c_ubyte[addr+7] = 0
add_struct = exports['add_struct']
print("add({23, 27}) = %d" % add_struct(store, addr))
