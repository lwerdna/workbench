#!/usr/bin/env python

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
        tmp = super().__reduce__()

        print('__reduce__() returned:')
        if tmp[0:]:
            print('       callable: ' + str(tmp[0]))
        if tmp[1:]:
            print('           args: ' + str(tmp[1]))
        if tmp[2:]:
            print('          state: ' + str(tmp[2]))
        if tmp[3:]:
            print('          items: ' + str(tmp[3]))
        if tmp[4:]:
            print('keys and values: ' + str(tmp[4]))
        if tmp[5:]:
            print('       callable: ' + str(tmp[5]))

        # if only a callable and args was supplied, throw in a state also (to activate __setstate__() callback)
        if len(tmp) == 2:
            tmp = (tmp[0], tmp[1], 'hello')

        return tmp

    def __setstate__(self, state):
        print(f'My setstate() dunder method was called with state: {state}!')

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
