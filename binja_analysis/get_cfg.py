#!/usr/bin/env python

import fizzbuzz
from helpers import *

func = bytes_to_function(fizzbuzz.binary)
print_function_disasm(func)

