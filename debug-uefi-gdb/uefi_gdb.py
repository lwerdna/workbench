# prove that you registered the command correctly:
# (gdb) help user-defined

from LStruct import *
import gdb

efi_table_header = [
    ['signature', 8, as_string],
    ['revision', 4, as_08x],
    ['header_size', 4, as_08x],
    ['crc32', 4, as_08x],
    ['reserved', 4, as_08x]
]

efi_system_table = [
    ['header', efi_table_header],
    ['FirmwareVendor', 8, as_016x],
    ['FirmwareRevision', 4, as_08x],
    ['padding', 4, as_08x],
    ['ConsoleInHandle', 8, as_016x],
    ['ConIn', 8, as_016x],
    ['ConsoleOutputHandle', 8, as_016x],
    ['ConOut', 8, as_016x],
    ['StandardErrorHandle', 8, as_016x],
    ['StdError', 8, as_016x],
    ['RuntimeServices', 8, as_016x],
    ['BootServices', 8, as_016x],
    ['NumOfTableEntries', 8, as_16d],
    ['ConfigurationTable', 8, as_016x]
]

class DumpSystemTable(gdb.Command):
    def __init__(self):
        super(DumpSystemTable, self).__init__("dump_system_table", gdb.COMMAND_USER)

    # from_tty tells u whether run from script or command line
    def invoke(self, arg, from_tty):
        #print(f'arg: {arg}')
        if not arg:
            print('dump_system_table <address of efi_system_table>')
        addr = int(arg, 16)
        print(f'reading from 0x{addr:X}')
        inferior = gdb.inferiors()[0]

        lstruct_read(efi_system_table, inferior, addr)
        lstruct_print(efi_system_table)

DumpSystemTable()
