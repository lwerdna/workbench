#!/usr/bin/env python

import os, sys, re

import fizzbuzz
from helpers import *

func = bytes_to_function(fizzbuzz.binary)
print_function_disasm(func)

graph_func('control_flow_graph', func, [], [])
