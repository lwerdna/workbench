#!/usr/bin/env python

# solve 11. Wolf, Goat, and Cabbage from Moscow Puzzles

# Let the state of the puzzle be represented by a bit vector:
# b0 - location of wolf
# b1 - location of goat
# b2 - location of cabbage
# b3 - location of man

# for each bit, 0 means side A of river, 1 means side B of river
# starting location is thus 0000
#
# illegal states are:
# 1x00 - wolf and goat are left on side A
# 0x11 - wolf and goat are left on side B
# 100x - cabbage and goat left on side A
# 011x - cabbage and goat left on side B

# crossing with an item is modelled by xor of state with a value
# ^ 0000 - nothing
# ^ 1001 - man crosses with wolf
# ^ 1010 - man crosses with goat
# ^ 1101 - man crosses with cabbage
# ^ 1000 - man crosses with nothing

# goal is to transition from state 0000 to state 1111 without hitting any illegal state

# move0_nothing  at state0, do nothing
# move0_wolf     at state0, man crosses with wolf
# move0_goat     at state0, man crosses with goat
# move0_cabbage  at state0, man crosses with cabbage
#
# and at most one of these can be true (you can only select one move)

import time
import itertools

import z3

MOVES = 10

def solution0():
    s = z3.Solver()

    state_vars = [z3.BitVec(f'state_{i}', 4) for i in range(MOVES + 1)]

    # start with everyone on side A
    s.add(state_vars[0] == z3.BitVecVal(0, 4))

    for i in range(MOVES):
        move_nothing = z3.Bool(f'move{i}_nothing')
        move_wolf = z3.Bool(f'move{i}_wolf')
        move_goat = z3.Bool(f'move{i}_goat')
        move_cabbage = z3.Bool(f'move{i}_cabbage')
        move_man = z3.Bool(f'move{i}_man')

        s.add(state_vars[i+1] == state_vars[i] ^ \
            z3.If(move_wolf, z3.BitVecVal(0b1001, 4), z3.BitVecVal(0, 4)) ^ \
            z3.If(move_goat, z3.BitVecVal(0b1010, 4), z3.BitVecVal(0, 4)) ^ \
            z3.If(move_cabbage, z3.BitVecVal(0b1100, 4), z3.BitVecVal(0, 4)) ^ \
            z3.If(move_man, z3.BitVecVal(0b1000, 4), z3.BitVecVal(0, 4))
            )

        s.add(z3.AtMost(move_nothing, move_wolf, move_goat, move_cabbage, move_man, 1))

        s.add(state_vars[i+1] != z3.BitVecVal(0b1000, 4)) # wolf and goat side A
        s.add(state_vars[i+1] != z3.BitVecVal(0b1100, 4))
        s.add(state_vars[i+1] != z3.BitVecVal(0b0011, 4)) # wolf and goat side B
        s.add(state_vars[i+1] != z3.BitVecVal(0b0111, 4))
        s.add(state_vars[i+1] != z3.BitVecVal(0b1000, 4)) # goat and cabbage side A
        s.add(state_vars[i+1] != z3.BitVecVal(0b1001, 4))
        s.add(state_vars[i+1] != z3.BitVecVal(0b0110, 4)) # goat and cabbage side B
        s.add(state_vars[i+1] != z3.BitVecVal(0b0111, 4))

    # must end with everyone on side B
    s.add(state_vars[MOVES] == z3.BitVecVal(0b1111, 4))

    return s

if __name__ == '__main__':
    # width of board in squares
    width = 10

    s = solution0()
    print(s.sexpr())

    t0 = time.time()
    assert s.check() == z3.sat
    t1 = time.time()
    m = s.model()
    t2 = time.time()

    print('check():%fs model():%fs' % (t1-t0, t2-t1))

    def piece(b):
        return 'R' if b else '-'

    name2var = {v.name(): v for v in m.decls()}
    name2val = {name: m[var] for (name, var) in name2var.items()}

    for i in range(MOVES):
        print(f'move{i}: ', end='')
        if name2val[f'move{i}_nothing']: print('nothing')
        if name2val[f'move{i}_wolf']: print('wolf')
        if name2val[f'move{i}_goat']: print('goat')
        if name2val[f'move{i}_cabbage']: print('cabbage')
        if name2val[f'move{i}_man']: print('man')
        print(f' resulting in state{i+1}:', bin(name2val[f'state_{i+1}'].as_long()))

