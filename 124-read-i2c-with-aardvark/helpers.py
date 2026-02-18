import time

# pip install aardvark_py
from aardvark_py import *

#------------------------------------------------------------------------------
# AARDVARK HELPERS
#------------------------------------------------------------------------------

def open_aardvark():
    num, ports = aa_find_devices(16)
    if num <= 0:
        raise RuntimeError('No Aardvark adapters found')
    port = ports[0]
    #print(f'aardvark port: {port}')
    handle = aa_open(port)
    if handle < 0:
        raise RuntimeError('aa_open failed: {handle}')
    #print(f'aardvark handle: {handle}')
    return handle

def power_get(handle):
    t = aa_target_power(handle, AA_TARGET_POWER_QUERY)
    if t == AA_TARGET_POWER_NONE:
        return 'off'
    elif t == AA_TARGET_POWER_BOTH:
        return 'on'
    else:
        raise Exception('unknown power state: {t}')

def power_on(handle):
    if aa_target_power(handle, AA_TARGET_POWER_QUERY) == AA_TARGET_POWER_NONE:
        rc = aa_target_power(handle, AA_TARGET_POWER_BOTH)
        rc = aa_target_power(handle, AA_TARGET_POWER_QUERY)
        assert rc == AA_TARGET_POWER_BOTH

def power_off(handle):
    aa_target_power(handle, AA_TARGET_POWER_NONE)
    rc = aa_target_power(handle, AA_TARGET_POWER_QUERY)
    assert rc == AA_TARGET_POWER_NONE

#------------------------------------------------------------------------------
# EEPROM/PHY SHARED STUFF
#------------------------------------------------------------------------------

def general_set_addr(handle, addr, i2c_device):
    print(f'general_set_addr(handle, addr=0x{addr:X}, i2c_device=0x{i2c_device:X})')
    # try 4 times to write
    for current_try in range(1, 4+1):
        # send just 0, setting internal address to 0
        payload = array('B', [addr])
        result = aa_i2c_write(handle, i2c_device, AA_I2C_NO_FLAGS, payload)
        print(f'aa_i2c_write({payload.tobytes()}) returned {result}')
        if result == 1:
            break
        print(f'on try {current_try}/4, write of address failed...')
        time.sleep(.4)
    else:
        return False

    return True

def general_read(handle, addr, length, i2c_device):
    print(f'general_read(handle, addr=0x{addr:X}, length={length}, i2c_device=0x{i2c_device:X})')

    if not general_set_addr(handle, addr, i2c_device):
        return None

    status, data = aa_i2c_read(handle, i2c_device, AA_I2C_NO_FLAGS, length)

    if status < 0:
        print(f"fail reading data ({aa_status_string(status)})")
        return None
    
    if not data:
        print(f'ERROR (kinda): received 0 bytes')
        return None

    return data

def general_write(handle, addr, data, i2c_device):
    payload = array('B', [addr]) + data
    rc = aa_i2c_write(handle, i2c_device, AA_I2C_NO_FLAGS, payload)
    print(f'aa_i2c_write({payload.tobytes()}) returned {rc}')

#------------------------------------------------------------------------------
# PHY STUFF
#------------------------------------------------------------------------------

def set_phy_addr(handle, addr, i2c_phy_addr=(0xAC >> 1)):
    return general_set_addr(handle, addr, i2c_phy_addr)

# other side expect REG_ID, not an address
# REG_ID = 2*address since every REG_ID is 2 bytes
def read_phy(handle, addr, length, i2c_phy_addr=(0xAC >> 1)):
    return general_read(handle, addr//2, length, i2c_phy_addr)

def read_phy_reg(handle, reg_id, i2c_phy_addr=(0xAC >> 1)):
    data = general_read(handle, reg_id, 2, i2c_phy_addr)
    return (data[0]<<8)|data[1]

def write_phy_reg(handle, reg_id, value, i2c_phy_addr=(0xAC >> 1)):
    # value of 0xAABB becomes 0xAA, 0xBB
    payload = array('B', [value >> 8, value & 0xFF])
    general_write(handle, reg_id, payload, i2c_phy_addr)

def read_phy_regs(handle, i2c_phy_addr=(0xAC >> 1)):
    data = general_read(handle, 0, 32*2, i2c_phy_addr)
    data = data.tobytes()

    regs = []
    for i in range(32):
        regs.append((data[0]<<8)|data[1])
        data = data[2:]

    return regs

#------------------------------------------------------------------------------
# EEPROM STUFF
#------------------------------------------------------------------------------

def set_eeprom_addr(handle, addr, i2c_eeprom_addr=(0xA0 >> 1)):
    return general_set_addr(handle, addr, i2c_eeprom_addr)

def read_eeprom(handle, addr, length, i2c_eeprom_addr=(0xA0 >> 1)):
    return general_read(handle, addr, length, i2c_eeprom_addr)

#------------------------------------------------------------------------------
# GENERAL STUFF
#------------------------------------------------------------------------------

# https://gist.github.com/mzpqnxow/a368c6cd9fae97b87ef25f475112c84c
def hexdump(src, addr=0, length=16, sep='.'):
    FILTER = ''.join([(len(repr(chr(x))) == 3) and chr(x) or sep for x in range(256)])
    lines = []
    for c in range(0, len(src), length):
        chars = src[c: c + length]
        hex_ = ' '.join(['{:02x}'.format(x) for x in chars])
        if len(hex_) > 24:
            hex_ = '{}{}'.format(hex_[:24], hex_[24:])
        printable = ''.join(['{}'.format((x <= 127 and FILTER[x]) or sep) for x in chars])
        lines.append('{0:08x}: {1:{2}s} {3:{4}s}'.format(addr+c, hex_, length * 3, printable, length))
    return '\n'.join(lines)

