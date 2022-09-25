# represent memory with a z3 vector of bytes

import z3

from MemoryModel import MemoryModel

#------------------------------------------------------------------------------
# generate z3 array expressions (Select()/Store()) for mem accesses
#------------------------------------------------------------------------------

class MemoryArrayU8():
    # addr_width in bits
    def __init__(self, addr_width, init_mem=True):
        self.addr_width = addr_width

        if init_mem:
            self.ver = 0
            self.mem = z3.Array('mem#0', z3.BitVecSort(addr_width), z3.BitVecSort(8))
        else:
            self.ver = None
            self.mem = None

        self.conjuncts = []

    # return an expression of a memory read
    def read(self, addr, width):
        assert width in [8, 16, 32, 64]

        if width == 8:
            result = z3.Select(self.mem, addr)
        if width == 16:
            result = z3.Concat(
                z3.Select(self.mem, addr+1),
                z3.Select(self.mem, addr)
            )
        if width == 32:
            result = z3.Concat(
                z3.Select(self.mem, addr+3),
                z3.Select(self.mem, addr+2),
                z3.Select(self.mem, addr+1),
                z3.Select(self.mem, addr)
            )
        if width == 64:
            result = z3.Concat(
                z3.Select(self.mem, addr+7),
                z3.Select(self.mem, addr+6),
                z3.Select(self.mem, addr+5),
                z3.Select(self.mem, addr+4),
                z3.Select(self.mem, addr+3),
                z3.Select(self.mem, addr+2),
                z3.Select(self.mem, addr+1),
                z3.Select(self.mem, addr)
            )

        #result = z3.simplify(result)
        return result

    def write_expr(self, mem, addr, val, width):
        assert width in [8, 16, 32, 64]

        (b0,b1,b2,b3,b4,b5,b6,b7) = (0,0,0,0,0,0,0,0)

        if width == 8:
            return z3.Store(mem, addr, b0)

        b0 = z3.Extract(7, 0, val)
        b1 = z3.Extract(15, 8, val)
        if width == 16:
            return z3.Store(z3.Store(mem, addr, b0), addr+1, b1)

        b2 = z3.Extract(23, 16, val)
        b3 = z3.Extract(31, 24, val)
        if width == 32:
            return z3.Store(z3.Store(z3.Store(z3.Store(mem, addr, b0), addr+1, b1), addr+2, b2), addr+3, b3)

        b4 = z3.Extract(39, 32, val)
        b5 = z3.Extract(47, 40, val)
        b6 = z3.Extract(55, 48, val)
        b7 = z3.Extract(63, 56, val)

        return z3.Store(z3.Store(z3.Store(z3.Store(z3.Store(z3.Store(z3.Store(z3.Store(mem, addr, b0), addr+1, b1), addr+2, b2), addr+3, b3), addr+4, b4), addr+5, b5), addr+6, b6), addr+7, b7)

    # return an expression for a new version of memory with the current stores applied
    def write(self, addr, val, width):
        self.ver += 1
        mem_old = self.mem
        mem_new = z3.Array(f'mem#{self.ver}', z3.BitVecSort(self.addr_width), z3.BitVecSort(8))
        self.conjuncts.append(mem_new == self.write_expr(mem_old, addr, val, width))
        self.mem = mem_new

    def branch(self):
        result = MemoryArrayU8(self.addr_width, False)
        result.ver = self.ver + 1
        result.mem = z3.Array(f'mem#{result.ver}', z3.BitVecSort(self.addr_width), z3.BitVecSort(8))
        result.conjuncts.append(result.mem == self.mem)
        return result

