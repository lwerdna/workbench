# https://lldb.llvm.org/use/python-reference.html
# https://lldb.llvm.org/python_reference/lldb-module.html

# read memory
# https://stackoverflow.com/questions/41307667/reading-n-bytes-from-a-memory-address-using-lldbs-python-api
def read_mem(process, addr, length):
    error_ref = lldb.SBError()
    result = process.ReadMemory(addr, length, error_ref)
    if error_ref.Success():
        # `memory` is a regular byte string
        pass
    else:
        print(str(error_ref))
        result = None
    # breakpoint()
    return result


    #breakpoints = [target.BreakpointCreateByName(func_name, fname_exec) for func_name in \
    #    ['main', 'dlmalloc', 'dlfree']]
    #breakpoints = [target.CreateBreakpoitnByAddress(
