#!/usr/bin/env python

import math

def compound_interest(amount:float, rate:float, years:int):
    new_amount = amount * (1 + rate)**years
    return new_amount

if __name__ == '__main__':
    assert math.isclose(compound_interest(1000, 0.07, 25), 5427.43, rel_tol=.01)

