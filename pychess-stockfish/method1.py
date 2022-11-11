#!/usr/bin/env python

# raw communication to stockfish gets about 72 positions/sec

import os
import time
from subprocess import Popen, PIPE

import common

class Engine(object):
    def __init__(self):
        self.proc = Popen("/usr/local/bin/stockfish", stdout=PIPE, stdin=PIPE)
        self.send('uci')
        self.wait(lambda l: l=='uciok')

    def send(self, command):
        self.proc.stdin.write((command + '\n').encode('utf-8'))
        self.proc.stdin.flush()

    def wait(self, test):
        while True:
            line = self.proc.stdout.readline().decode('utf-8').strip()
            #print(f'ENGINE: {line}')
            if test(line):
                break

    def eval(self, fen):
        self.send(f'position fen {fen}')
        self.send(f'go nodes {common.NODES_ELO_2500}')
        self.wait(lambda l: l.startswith('bestmove'))

    def __del__(self):
        self.send('quit')
        self.proc.wait()

print('starting engine')
engine = Engine()

print('loading positions')
positions = common.get_positions(common.N_POSITIONS)

def eval_all():
    global positions
    for fen in positions:
        engine.eval(fen)

# simple timing, about 60 pos/sec
if 1:
    print(f'evaluating {common.N_POSITIONS} positions')
    t0 = time.perf_counter()
    eval_all()
    t1 = time.perf_counter()
    print(f'{t1-t0} seconds, or {common.N_POSITIONS/(t1-t0)} per second')

if 0:
    import cProfile
    cProfile.run('eval_all()')

