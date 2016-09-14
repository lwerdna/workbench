function engineGame(fen) {
	/* chess game state (chess.js) */
 	var game = new Chess(fen);

	/*************************************************************************/
	/* chess engine */
	/*************************************************************************/
    var engine = new Worker('./js/stockfish.js');
    engine.postMessage('uci');

    engine.onmessage = function(event) {
        var line = event.data;
        if(line == 'uciok') {
			console.log("engine replied 'uciok'");
        } else if(line == 'readyok') {
			console.log("engine replied 'readyok'");
        } else {
            var match = line.match(/^bestmove ([a-h][1-8])([a-h][1-8])([qrbk])?/);
            if(match) {
				console.log("engine has a move! " + line);
                game.move({from: match[1], to: match[2], promotion: match[3]});
				board.position(game.fen());
				engine.postMessage('stop');
            }
        }
    };

	/*************************************************************************/
	/* chessboard stuff (the GUI display) */
	/*************************************************************************/
    var cb_chessBoardOnDragStart = function(source, piece, position, orientation) {
        if(game.game_over()) {
        	return false;
        }
    };

    var cb_chessBoardOnDrop = function(source, target) {
        // update the game while checking if move is legal
        var move = game.move({
            from: source,
            to: target,
            promotion: 'q' // NOTE: always promote to a pawn for example simplicity
        });

		console.log("move attempt: " + source + ' -> ' + target);

        // illegal move
        if (move === null) {
			console.log("illegal!");
			return 'snapback';
		}

		console.log("move accepted");

        // update board
		console.log("updating board position: " + game.fen());
		board.position(game.fen());
		// update engine	
		if(game.game_over()) {
			console.log("game over!");
		}
		else {
			console.log("launching engine!");
			engine.postMessage('position fen '+game.fen());
			engine.postMessage('go movetime 2000')
		}
    };

    var cb_chessBoardOnSnapEnd = function() {
        board.position(game.fen());
    };

    var chessBoardCfg = {
        draggable: true,
        position: fen,
        onDragStart: cb_chessBoardOnDragStart,
        onDrop: cb_chessBoardOnDrop,
        onSnapEnd: cb_chessBoardOnSnapEnd
    };

    var board = new ChessBoard('board', chessBoardCfg);
}
