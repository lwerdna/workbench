#!/usr/bin/env python

import chess
import chess.pgn
import chess.engine

engine = None
def get_best_move(board):
    global transport, engine

    if not engine:
        engine = chess.engine.SimpleEngine.popen_uci(r'/usr/local/bin/stockfish')

    result = engine.play(board, chess.engine.Limit(time=2))    
    #breakpoint()
    return result.move

f = open('example.pgn')
game = chess.pgn.read_game(f)

# chess.Board
board = game.board()
print(board.fen())

#breakpoint()
# move in chess.pgn.Mainline
for (i,move) in enumerate(game.mainline_moves()):
    space = f'...' if i%2 else '. '

    best_move = get_best_move(board)

    print(f'{i+1}{space}{move} (stockfish recommended: {i+1}{space}{best_move})')

    board.push(move)
    print(board.fen())


    #print("state %d: %s (from %s, best was %s)" % (i, board.fen(), move, moveBestSan))

    #if game.is_end():
    #    break;


