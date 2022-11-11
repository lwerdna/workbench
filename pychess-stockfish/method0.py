#!/usr/bin/env python

# straightforward analyze call gets only 60/sec

import os
import time

import common

import chess
import chess.pgn

print('starting engine')
engine = chess.engine.SimpleEngine.popen_uci("/usr/local/bin/stockfish")
print('loading positions')
positions = common.get_positions(common.N_POSITIONS)

def eval_all():
    global positions

    board = chess.Board()
    for fen in positions:
        board.set_fen(fen)
        #print(board)
        #result = engine.play(board, chess.engine.Limit(nodes=common.NODES_ELO_2500))
        result = engine.analyse(board, chess.engine.Limit(nodes=common.NODES_ELO_2500))
        #print(f"best move is {result['pv'][0]} with score {result['score']}")

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

engine.quit()
