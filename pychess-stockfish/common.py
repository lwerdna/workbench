import os

import chess
import chess.pgn

# https://www.melonimarco.it/en/2021/03/08/stockfish-and-lc0-test-at-different-number-of-nodes/
NODES_ELO_2500 = 10000

N_POSITIONS = 500

def get_positions(limit):
    # read positions
    fpath = os.path.join(os.environ['HOME'], 'Documents', 'chessdata', 'bundesliga2000.pgn')
    fp = open(fpath)

    positions = []
    keep_parsing = True
    while keep_parsing:
        game = chess.pgn.read_game(fp)
        if game == None:
            break

        board = game.board()
        for (i,move) in enumerate(game.mainline_moves()):
            board.push(move)

            # not interested in first 16 half-moves
            if i < 16:
                continue

            # not interested in boards where the best move is simply getting out of check
            if board.is_check():
                continue

            #print(board.fen())
            positions.append(board.fen())
            if len(positions) >= limit:
                keep_parsing = False
                break

    fp.close()
    return positions

