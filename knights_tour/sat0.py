#!/usr/bin/python

# most naive encoding for knight's tour to SAT - 2013 andrewl

import re
import sys
import subprocess

# single dimension of square board
N = 5

def legalMovesFromSquare(sqr):
    row = sqr/N;
    col = sqr%N;

    rough = []
    rough.append([row+2, col-1])
    rough.append([row+2, col+1])
    rough.append([row+1, col-2])
    rough.append([row+1, col+2])
    rough.append([row-1, col-2])
    rough.append([row-1, col+2])
    rough.append([row-2, col-1])
    rough.append([row-2, col+1])

    result = []
    for pair in rough:
        if pair[0] > (N-1) or pair[0] < 0 or \
            pair[1] > (N-1) or pair[1] < 0:
            continue

        result.append(pair[0]*N + pair[1])
    
    return result

# expects a CNF input formula
# returns (dimacs, listOfVariables)
def convertToDimacs(formula):
    result = ''

    varNames = re.findall(r'[\w\d]+', formula)
    varNames = list(set(varNames))
    clauses = re.findall(r'\(.*?\)', formula)
    
    result += 'p cnf %d %d\n' % (len(varNames), len(clauses))

    for clause in clauses:
        terms = re.findall(r'/?[\w\d]+', clause)
        for term in terms:
            if term[0]=='/':
                result += '-'
                term = term[1:]
            # note that dimacs indexes variables based at 1
            result += str(varNames.index(term)+1) + ' '
        result += '0\n'

    return (result, varNames)

#  in:   formula
# out:   map from variables name to value
def PicosatPipeSolve(formula):
    (dimacs, varNames) = convertToDimacs(formula)

    print dimacs

    p = subprocess.Popen('picosat', stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    p.stdin.write(dimacs)
    p.stdin.close()

    output = p.stdout.read()
    p.stdout.close()

    print output

    if not re.match(r'^s SATISFIABLE', output):
        return None
   
    # parse out all the variables from here... 
    result = {}

    ints = re.findall(r'(-?\d+)', output)
    ints = map(lambda x: int(x), ints)
    for i in ints:
        result[ varNames[abs(i)-1] ] = int(i>0)
    
    return result

equ = ''

if sys.argv[1:]:
    N = int(sys.argv[1])
    
print "solving for a %dx%d board" % (N, N)

# generate the V_<ind>_<sqr> variables
# which represent "<sqr> is the <ind>'th move int he tour"
for sqr in range(N*N):
    # we impose:
    # V_<ind>_<sqr> -> V_<ind+1>_<sqr'> where sqr' is legal move from sqr
    for index in range(N*N-1):
        addends = ['/V_%d_%d' % (index, sqr)]
        for move in legalMovesFromSquare(sqr):
            addends.append('V_%d_%d' % (index+1, move))
        equ += '(' + '+'.join(addends) + ')\n'

# now impose that no more than one square can be the <ind>'th move
for index in range(N*N):
    # "at most one" with a product of implications V_<ind>_<sqr> -> /V_<indx>_<sqr'> 
    # where sqr' is all squares != sqr
    # "at least one" with simple or clause...
    for sqr in range(N*N-1):
        for sqr_ in range(sqr+1, N*N):
            equ += '(/V_%d_%d+/V_%d_%d)' % (index, sqr, index, sqr_)
        equ += '\n'

# finally, impose that at least one of the squares must be index 0, that one of
# the square must be index 1, etc.
for sqr in range(N*N):
    terms = map(lambda x: 'V_%d_%d' % (x, sqr), range(N*N))
    equ += '(' + '+'.join(terms) + ')\n'

print equ

result = PicosatPipeSolve(equ)

if(result == None):
    print "GAME OVER BRO"
else:
    sqrToMove = [0] * N*N

    for trueVar in filter(lambda x: result[x], result.keys()):
        m = re.match(r'V_(\d+)_(\d+)', trueVar)
        sqrToMove[int(m.group(2))] = int(m.group(1))

    print sqrToMove

    print '+--'*N + '+'
    for row in range(N):
        line = '|'
        for col in range(N):
            sqr = row*N + col

            line += '%2d|' % sqrToMove[sqr]
        print line
        print '+--'*N + '+'

