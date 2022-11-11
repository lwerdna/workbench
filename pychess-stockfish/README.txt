How do you limit the search for good moves?

python-chess provides several options:
https://python-chess.readthedocs.io/en/latest/engine.html#chess.engine.Limit
* Search exactly time seconds.
* Search depth ply only.
* Search only a limited number of nodes.
* Search for a mate in mate moves.
* Number of moves to the next time control. If this is not set, but white_clock and black_clock are, then it is sudden death.

Going lower, UCI has several parameters for its go command, among them:
go depth
go nodes
go movetime

Then there are DIY options outside of the search command. You can just stream the feedback from an ongoing search, and decide when to stop. Like if the depth or seldepth or some time has passed.

There are built in ways to do so:

engine.play(board, chess.engine.Limit(time=0.1))
info = engine.analyse(board, chess.engine.Limit(time=0.1))

RESOURCES

Marcus Buffet who shared his experience optimizing calls to Stockfish with Rust and the uciengine create:
https://mbuffett.com/posts/generating_chess_puzzles/
Marco Meloni who shared his research mapping the number of nodes Stockfish searches with ELO performance:
https://www.melonimarco.it/en/2021/03/08/stockfish-and-lc0-test-at-different-number-of-nodes/
