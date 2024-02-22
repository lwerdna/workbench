class MyStruct():
    type2size = {'uint64_t':8, 'uint32_t':4}

    def __init__(self, fields):
        self.fields = fields

        # these get populated upon read()
        self.address = None
        self.values = None

    def read(self, inferior, addr):
        self.address = addr
        blob = inferior.read_memory(addr, len(self))

        self.values = []
        for type_, name in self.fields:
            # read and unpack to value
            if type_ == 'uint32_t':
                value = struct.unpack('<I', inferior.read_memory(addr, 4))[0]
            elif type_ == 'uint64_t':
                value = struct.unpack('<Q', inferior.read_memory(addr, 8))[0]
            elif isinstance(type_, MyStruct):
                type_.read(inferior, addr)
                value = type_
            else:
                assert False;
                    
            self.values.append(value)

            if isinstance(type_, MyStruct):
                addr += len(type_)
            else:
                addr += MyStruct.type2size[type_]

    def __len__(self):
        result = 0
        for t,n in self.fields:
            if isinstance(t, MyStruct):
                result += len(t)
            else:
                result += MyStruct.type2size[t]
        return result
        
    def __str_worker__(self, depth=0):
        lines = []
        indent = '  '*depth

        for i, (type_, name) in enumerate(self.fields):
            value = self.values[i]
            if type_ == 'uint32_t':
                value_str = f'0x{value:X}'
            elif type_ == 'uint64_t':
                value_str = f'0x{value:X}'
            elif isinstance(type_, MyStruct):
                value_str = type_.__str_worker__(depth+1)
            else:
                assert False;

            lines.append(f'{indent}{name} ({type_}) = {value_str}')

        return '\n'.join(lines)

    def __str__(self):
        return self.__str_worker__()

class efi_table_header(MyStruct):
    def __init__(self):
        fields = (
	        ('uint64_t', 'signature'),
	        ('uint32_t', 'revision'),
	        ('uint32_t', 'header_size'),
	        ('uint32_t', 'crc32'),
	        ('uint32_t', 'reserved')
	    )
        super().__init__(fields)

class efi_system_table(MyStruct):
    def __init__(self):
        fields = (
	        (efi_table_header(), 'header'),
	        ('uint64_t', 'FirmwareVendor'),
	        ('uint32_t', 'FirmwareRevision'),
	    )
        super().__init__(fields)

