"""
run this in IDA with:

sys.path.append('/path/to/this/script')
import script
import importlib
importlib.reload(script)
"""

import idc

ea = idc.find_defined(0, idc.SEARCH_DOWN)

results = []

#count = 0
while ea != idc.BADADDR:
    #count += 1
    name = idc.get_name(ea)

    if name:
        data = idc.get_bytes(ea, 16)
        results.append((ea, name, data))
        print(f'{ea:08X}, {name}, {data.hex()}')

    #if count >= 10:
    #    break

    ea = idc.find_defined(ea, idc.SEARCH_DOWN)

with open('/tmp/results.txt', 'w') as fp:
    for ea, name, data in results:
        fp.write(f'{ea:08X}, {name}, {data.hex()}\n')

