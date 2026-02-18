import serial

REG_ADDR_REGCR = 0xD
REG_ADDR_ADDAR = 0xE

def connect(port="/dev/ttyUSB0", baud=115200):
    print('Creating Serial object...')
    ser = serial.Serial(port, baud)

    if not ser.in_waiting:
        ser.write('help\n'.encode())

    ser.timeout = 1
    ser.read_until(b'TOOL>\n')

    return ser

def set_extended_address(ser, addr):
    # set ADDAR to be an address
    value = 0
    value |= (0b00 << 14) # 00 = Address
    value |= 0b11111 # DEVAD used in DP83867
    write_reg(ser, REG_ADDR_REGCR, value)
    # assign address
    write_reg(ser, REG_ADDR_ADDAR, addr)
    # set ADDAR to be data
    value = 0
    value |= (0b01 << 14) # 01 = Data, no post increment
    value |= 0b11111 # DEVAD used in DP83867
    write_reg(ser, REG_ADDR_REGCR, value)

def read_reg(ser, addr):
    #print(f'read_reg(ser, 0x{addr:X})')
    if addr <= 15:
        ser.write(f'r 0 {addr}\n'.encode())
    else:
        set_extended_address(ser, addr)
        ser.write(f'r 0 {REG_ADDR_ADDAR}\n'.encode())

    response = ser.read_until(b'TOOL>\n')
    value, prompt = response.decode().split('\r\n')
    assert prompt == 'TOOL>'
    assert len(value) == 4
    return int(value, 16)

def write_reg(ser, addr, data):
    #print(f'write_reg(ser, 0x{addr:X}, 0x{data:X})')
    if addr <= 15:
        ser.write(f'w 0 {addr} 0x{data:04X}\n'.encode())
        response = ser.read_until(b'TOOL>\n')
    else:
        set_extended_address(ser, addr)
        cmd = f'w 0 {REG_ADDR_ADDAR} 0x{data:04X}'.encode()
        ser.write(cmd)
        response = ser.read_until(b'TOOL>\n')

def bit(value, bitnum):
    return 1 if (value & (1<<bitnum)) else 0

