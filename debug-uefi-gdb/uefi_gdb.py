# (gdb) source uefi_gdb.py
#
# # prove that you registered the command correctly:
# (gdb) help user-defined

from LStruct import *
import gdb
import copy

efi_table_header = [
    ['signature', 8, as_string],
    ['revision', 4, as_08x],
    ['header_size', 4, as_08x], # includes this header
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

efi_runtime_services = [
    ['header', efi_table_header],

    # time services
    ['GetTime', 8, as_016x],
    ['SetTime', 8, as_016x],
    ['GetWakeupTime', 8, as_016x],
    ['SetWakeupTime', 8, as_016x],

    # virtual memory services
    ['SetVirtualAddressMap', 8, as_016x],
    ['ConvertPointer', 8, as_016x],

    # variable services
    ['GetVariable', 8, as_016x],
    ['GetNextVariableName', 8, as_016x],
    ['SetVariable', 8, as_016x],

    # miscellaneous services
    ['GetNextHighMonotonicCount', 8, as_016x],
    ['ResetSystem', 8, as_016x],

    # uefi 2.0 capsule services services
    ['UpdateCapsule', 8, as_016x],
    ['QueryCapsuleCapabilities', 8, as_016x],

    # misellaneous uefi 2.0 service
    ['QueryVariableInfo', 8, as_016x]
]

efi_boot_services = [
    ['header', efi_table_header],

    # task priority services
    ['RaiseTPL', 8, as_016x],
    ['RestoreTPL', 8, as_016x],

    # memory services
    ['AllocatePages', 8, as_016x],
    ['FreePages', 8, as_016x],
    ['GetMemoryMap', 8, as_016x],
    ['AllocatePool', 8, as_016x],
    ['FreePool', 8, as_016x],

    # event and timer
    ['CreateEvent', 8, as_016x],
    ['SetTimer', 8, as_016x],
    ['WaitForEvent', 8, as_016x],
    ['SignalEVent', 8, as_016x],
    ['CloseEvent', 8, as_016x],
    ['CheckEvent', 8, as_016x],

    # protocol handler
    ['InstallProtocolInterface', 8, as_016x],
    ['ReinstallProtocolInterface', 8, as_016x],
    ['UninstallProtocolInterface', 8, as_016x],
    ['HandleProtocol', 8, as_016x],
    ['Reserved', 8, as_016x],
    ['RegisterProtocolNotify', 8, as_016x],
    ['LocateHandle', 8, as_016x],
    ['LocateDevicePath', 8, as_016x],
    ['InstallConfigurationTable', 8, as_016x],

    # image services
    ['LoadImage', 8, as_016x],
    ['StartImage', 8, as_016x],
    ['Exit', 8, as_016x],
    ['UnloadImage', 8, as_016x],
    ['ExitBootServices', 8, as_016x],

    # miscellaneous services
    ['GetNextMonotonicCount', 8, as_016x],
    ['Stall', 8, as_016x],
    ['SetWatchdogTimer', 8, as_016x],

    # driversupport services
    ['ConnectController', 8, as_016x],
    ['DisconnectController', 8, as_016x],

    # open and close protocol services
    ['OpenProtocol', 8, as_016x],
    ['CloseProtocol', 8, as_016x],
    ['OpenProtocolInformation', 8, as_016x],

    # library services
    ['ProtocolsPerHandle', 8, as_016x],
    ['LocateHandleBuffer', 8, as_016x],
    ['LocateProtocol', 8, as_016x],
    ['InstallMultipleProtocolInterfaces', 8, as_016x],
    ['UninstallMultipleProtocolInterfaces', 8, as_016x],

    # crc services
    ['CalculateCrc32', 8, as_016x],

    # miscellaneous services
    ['CopyMem', 8, as_016x],
    ['SetMem', 8, as_016x],
    ['CreateEventEx', 8, as_016x]
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
        inferior = gdb.inferiors()[0]

        struct = copy.deepcopy(efi_system_table)
        print(f'reading 0x{lstruct_len(struct):X} bytes from 0x{addr:X}')
        lstruct_read(struct, inferior, addr)
        lstruct_print(struct)

class DumpTableHeader(gdb.Command):
    def __init__(self):
        super(DumpTableHeader, self).__init__("dump_table_header", gdb.COMMAND_USER)

    # from_tty tells u whether run from script or command line
    def invoke(self, arg, from_tty):
        #print(f'arg: {arg}')
        if not arg:
            print('dump_table_header <address of table>')
        addr = int(arg, 16)
        inferior = gdb.inferiors()[0]

        struct = copy.deepcopy(efi_table_header)
        print(f'reading 0x{lstruct_len(struct):X} bytes from 0x{addr:X}')
        lstruct_read(struct, inferior, addr)
        lstruct_print(struct)

class DumpRuntimeServices(gdb.Command):
    def __init__(self):
        super(DumpRuntimeServices, self).__init__("dump_runtime_services", gdb.COMMAND_USER)

    # from_tty tells u whether run from script or command line
    def invoke(self, arg, from_tty):
        #print(f'arg: {arg}')
        if not arg:
            print('dump_runtime_services <address of table>')
        addr = int(arg, 16)
        inferior = gdb.inferiors()[0]

        struct = copy.deepcopy(efi_runtime_services)
        print(f'reading 0x{lstruct_len(struct):X} bytes from 0x{addr:X}')
        lstruct_read(struct, inferior, addr)
        lstruct_print(struct)

class DumpBootServices(gdb.Command):
    def __init__(self):
        super(DumpBootServices, self).__init__("dump_boot_services", gdb.COMMAND_USER)

    # from_tty tells u whether run from script or command line
    def invoke(self, arg, from_tty):
        #print(f'arg: {arg}')
        if not arg:
            print('dump_boot_services <address of table>')
        addr = int(arg, 16)
        inferior = gdb.inferiors()[0]

        struct = copy.deepcopy(efi_boot_services)
        print(f'reading 0x{lstruct_len(struct):X} bytes from 0x{addr:X}')
        lstruct_read(struct, inferior, addr)
        lstruct_print(struct)

# instantiate the classes for the commands
DumpSystemTable()
DumpTableHeader()
DumpRuntimeServices()
DumpBootServices()
