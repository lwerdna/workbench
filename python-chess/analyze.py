#!/usr/bin/env python

import chess
import chess.uci
import chess.pgn

def getBestMove(board):
    eng = chess.uci.popen_engine("/usr/local/bin/stockfish")
    eng.uci()
    eng.ucinewgame()
    eng.position(board)
    result = eng.go(movetime=2000)
    return result[0]

f = open('example.pgn')
gameNode = chess.pgn.read_game(f)

i = 0;
while 1:
    move = ''
    if gameNode.parent:
        move = gameNode.san()

    board = gameNode.board()

    moveBestUci = getBestMove(board)
    moveBestSan = board.san(moveBestUci)

    print "state %d: %s (from %s, best was %s)" % (i, board.fen(), move, moveBestSan)

    if gameNode.is_end():
        break;

    gameNode = gameNode.variation(0)

