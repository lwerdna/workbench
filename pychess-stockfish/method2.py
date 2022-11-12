#!/usr/bin/env python

import os
import time
from subprocess import Popen, PIPE

import common

import chess.pgn

class Engine(object):
    def __init__(self, hash_sz=2048, threads=8):
        self.proc = Popen("/usr/local/bin/stockfish", stdout=PIPE, stdin=PIPE)
        self.send(f'setoption name Hash value {hash_sz}')
        self.send(f'setoption name Threads value {threads}')
        self.send('isready')
        self.wait(lambda l: l==b'readyok\n')

    def send(self, command):
        data = (command + '\n').encode('utf-8')
        #print(f'> {data}')
        self.proc.stdin.write(data)
        self.proc.stdin.flush()

    def wait(self, test):
        while True:
            #line = self.proc.stdout.readline().decode('utf-8').strip()
            line = self.proc.stdout.readline()
            #print(f'ENGINE: {line}')
            if test(line):
                break

    def eval(self, fen):
        self.send(f'position fen {fen}')
        self.send(f'go nodes {common.NODES_ELO_2500}')
        self.wait(lambda l: l.startswith(b'bestmove'))

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

if 0:
    print(f'evaluating {common.N_POSITIONS} positions')
    t0 = time.perf_counter()
    eval_all()
    t1 = time.perf_counter()
    print(f'{t1-t0} seconds, or {common.N_POSITIONS/(t1-t0)} per second')

if 1:
    for hash_sz in [i*1024 for i in range(1,12+1)]:
        for threads in range(1,12):
            engine = Engine(hash_sz, threads)
            t0 = time.perf_counter()
            eval_all()
            t1 = time.perf_counter()
            print(f'{hash_sz} {threads} {t1-t0}')

if 0:
    import cProfile
    cProfile.run('eval_all()')

