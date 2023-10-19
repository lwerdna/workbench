#------------------------------------------------------------------------------
# low level operations confined to a certain width of bits
#------------------------------------------------------------------------------

# shifts
def bitshl(a, n, regsize=32):
    return (a<<n) & (2**regsize - 1)

def bitshr(a, n, regsize=32):
    return (a>>n) & (2**regsize - 1)

# rotates 
def bitrol(r, n, regsize=32):
    n = n % regsize
    return ((r<<n) | (r>>(regsize-n))) & (2**regsize - 1)

def bitror(r, n, regsize=32):
    n = n % regsize
    return ((r>>n) | (r<<(regsize-n))) & (2**regsize - 1)

# unsigned add/sub within a register
def bitadd(a, b, regsize=32):
    return (a+b) & (2**regsize - 1)

def bitsub(a, b, regsize=32):
    return (a + (2**regsize - b)) & (2**regsize -1)
