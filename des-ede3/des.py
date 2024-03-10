#!/usr/bin/env python

# https://en.wikipedia.org/wiki/Data_Encryption_Standard
# https://en.wikipedia.org/wiki/DES_supplementary_material

def get_bit(value, n):
    return 1 if value & (1 << n) else 0

def set_bit(value, n):
    return value | (1 << n)

def clear_bit(value, n):
    return value & (0xFFFFFFFFFFFFFFFF ^ (1<<n))

def apply_table(value, table):
    result = 0

    for dst, src in enumerate(table):
        if get_bit(value, src):
            result = set_bit(result, dst)
            #print(f'result: 0x{result:X}')

    return result

# initial permutation, 64 -> 64 bits
def IP(value):
    # 1-indexed, 1 is MSB
    #table = [ 58, 50, 42, 34, 26, 18, 10, 2, 60, 52, 44, 36, 28, 20, 12, 4, 62,
    #54, 46, 38, 30, 22, 14, 6, 64, 56, 48, 40, 32, 24, 16, 8, 57, 49, 41, 33,
    #25, 17, 9, 1, 59, 51, 43, 35, 27, 19, 11, 3, 61, 53, 45, 37, 29, 21, 13, 5,
    #63, 55, 47, 39, 31, 23, 15, 7 ]

    # 0-indexed, 63 is MSB
    table = [ 6, 14, 22, 30, 38, 46, 54, 62, 4, 12, 20, 28, 36, 44, 52, 60, 2,
    10, 18, 26, 34, 42, 50, 58, 0, 8, 16, 24, 32, 40, 48, 56, 7, 15, 23, 31,
    39, 47, 55, 63, 5, 13, 21, 29, 37, 45, 53, 61, 3, 11, 19, 27, 35, 43, 51,
    59, 1, 9, 17, 25, 33, 41, 49, 57]

    return apply_table(value, table)

# IP inverse, or final permutation, 64 -> 64 bits
def IP_inverse(value):
    # 1-indexed, 1 is MSB
    #table = [ 40, 8, 48, 16, 56, 24, 64, 32, 39, 7, 47, 15, 55, 23, 63, 31, 38,
    #6, 46, 14, 54, 22, 62, 30, 37, 5, 45, 13, 53, 21, 61, 29, 36, 4, 44, 12,
    #52, 20, 60, 28, 35, 3, 43, 11, 51, 19, 59, 27, 34, 2, 42, 10, 50, 18, 58,
    #26, 33, 1, 41, 9, 49, 17, 57, 25 ]

    # 0-indexed, 63 is MSB
    table = [24, 56, 16, 48, 8, 40, 0, 32, 25, 57, 17, 49, 9, 41, 1, 33, 26,
    58, 18, 50, 10, 42, 2, 34, 27, 59, 19, 51, 11, 43, 3, 35, 28, 60, 20, 52,
    12, 44, 4, 36, 29, 61, 21, 53, 13, 45, 5, 37, 30, 62, 22, 54, 14, 46, 6,
    38, 31, 63, 23, 55, 15, 47, 7, 39]

    return apply_table(value, table)

# expansion, 32 -> 48 bits
def E(value):
    #table = [32, 1, 2, 3, 4, 5, 4, 5, 6, 7, 8, 9, 8, 9, 10, 11, 12, 13, 12,
    #13, 14, 15, 16, 17, 16, 17, 18, 19, 20, 21, 20, 21, 22, 23, 24, 25, 24, 25,
    #26, 27, 28, 29, 28, 29, 30, 31, 32, 1]

    # 0-indexed, 31 is MSB
    table = [0, 31, 30, 29, 28, 27, 28, 27, 26, 25, 24, 23, 24, 23, 22, 21, 20,
    19, 20, 19, 18, 17, 16, 15, 16, 15, 14, 13, 12, 11, 12, 11, 10, 9, 8, 7, 8,
    7, 6, 5, 4, 3, 4, 3, 2, 1, 0, 31]

    return apply_table(value, table)

# permutation, 32 -> 32 bits
def P(value):
    #table = [ 16, 7, 20, 21, 29, 12, 28, 17, 1, 15, 23, 26, 5, 18, 31, 10, 2,
    #8, 24, 14, 32, 27, 3, 9, 19, 13, 30, 6, 22, 11, 4, 25]

    # 0-indexed, 31 is MSB
    table = [16, 25, 12, 11, 3, 20, 4, 15, 31, 17, 9, 6, 27, 14, 1, 22, 30, 24, 8, 18, 0, 5, 29, 23, 13, 19, 2, 26, 10, 21, 28, 7]

    return apply_table(value, table)

if __name__ == '__main__':
    foo = 0xDEADBEEF

    print('test get_bit()')
    assert get_bit(foo, 0) == 1 #F
    assert get_bit(foo, 1) == 1
    assert get_bit(foo, 2) == 1
    assert get_bit(foo, 3) == 1
    assert get_bit(foo, 4) == 0 #E
    assert get_bit(foo, 5) == 1
    assert get_bit(foo, 6) == 1
    assert get_bit(foo, 7) == 1
    assert get_bit(foo, 8) == 0 #E
    assert get_bit(foo, 9) == 1
    assert get_bit(foo, 10) == 1
    assert get_bit(foo, 11) == 1
    assert get_bit(foo, 12) == 1 #B
    assert get_bit(foo, 13) == 1
    assert get_bit(foo, 14) == 0
    assert get_bit(foo, 15) == 1

    print('test set_bit()')
    test = 0
    test = set_bit(test, 0) #F
    test = set_bit(test, 1)
    test = set_bit(test, 2)
    test = set_bit(test, 3)
    #test = set_bit(test, 4) #E
    test = set_bit(test, 5)
    test = set_bit(test, 6)
    test = set_bit(test, 7)
    #test = set_bit(test, 8) #E
    test = set_bit(test, 9)
    test = set_bit(test, 10)
    test = set_bit(test, 11)
    test = set_bit(test, 12) #B
    test = set_bit(test, 13)
    #test = set_bit(test, 14)
    test = set_bit(test, 15)
    print(f'test: {test:X}')
    assert test == 0xBEEF

    print('test clear_bit()')
    test = 0xFFFF
    test = clear_bit(test, 4)
    test = clear_bit(test, 8)
    test = clear_bit(test, 14)
    print(f'test: {test:X}')
    assert test == 0xBEEF

    print('test IP, IP_inv')
    temp0 = 0xDEADBEEFCAFEBABE
    print(f'temp0: {temp0:X}')
    temp1 = IP(temp0)
    print(f'temp1: {temp1:X}')
    temp2 = IP_inverse(temp1)
    print(f'temp2: {temp2:X}')

    print('test expansion')
    temp0 = 0xDEADBEEF
    print(f'temp0: {temp0:X}')
    temp1 = E(temp0)
    print(f'temp1: {temp1:X}')

    print('test permutation')
    temp0 = 0xDEADBEEF
    print(f'temp0: {temp0:X}')
    temp1 = P(temp0)
    print(f'temp1: {temp1:X}')

    #print('test permuted choice 1')
    #temp0 = 0xDEADBEEF
    #print(f'temp0: {temp0:X}')
    #temp1 = PC1(temp0)
    #print(f'temp1: {temp1:X}')

