import os
import inspect
from ctypes import *

print('testcomms.py plugin!')

handle = None

def acquire_handle():
    global handle
    a = inspect.getfile(inspect.currentframe())
    b = os.path.dirname(os.path.abspath(a))
    c = os.path.join(b, 'test.dylib')
    print('loading: ' + c)
    handle = CDLL(c)
    print('handle: ' + str(handle))
    assert handle

def say(int_value, str_value):
    global handle
    if handle == None:
        acquire_handle()

    str_value = str_value.encode('utf-8') + b'\x00'
    rv = handle.SayIntAndString(int_value, c_char_p(str_value))

    print(f'(PYTHON) received {rv}')

if __name__ == '__main__':
    acquire_handle()
    say(17, "17 is prime")
