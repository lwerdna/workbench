#!/usr/bin/env python

# Bool -> Bool
def NAND(A, B):
    return not (A and B)

if __name__ == '__main__':
    assert NAND(False, False)==True
    assert NAND(False, True)==True
    assert NAND(True, False)==True
    assert NAND(True, True)==False

