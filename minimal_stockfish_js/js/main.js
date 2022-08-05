// this is a javascript MODULE
// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Guide/Modules

export const name = 'main'

import {Chessboard, COLOR, INPUT_EVENT_TYPE} from "./cm-chessboard/Chessboard.js"

export function CreateGameDiv(fen, title)
{
	let h2 = document.createElement('h2');
	h2.innerText = title;
	document.body.append(h2)

	let div = document.createElement('div');
	div.style.width = '400px';
	div.style.height = '400px';
	document.body.append(div)

	/* set up chessboard */
    var chessboard = new Chessboard(div, {position: fen})

	/* set up game state, attach to UI board */
	let game = new Chess(fen);
	chessboard.game = game;

	chessboard.enableMoveInput((event) => {
    	switch (event.type) {
	        case INPUT_EVENT_TYPE.moveStart:
	            //console.log(`moveStart: ${event.square}`)
	            // return `true`, if input is accepted/valid, `false` aborts the interaction, the piece will not move
	            return true
	        case INPUT_EVENT_TYPE.moveDone:
	        	return handle_move_done(event.chessboard, event.squareFrom, event.squareTo);
	        case INPUT_EVENT_TYPE.moveCanceled:
	            console.log(`moveCanceled`);
	    }
	});
}

function handle_move_done(board, source, target)
{
 	let game = board.game;

	console.log(`handle_move_done("${game.fen()}", "${source}-${target})"`);

    // update the game while checking if move is legal
    var move = game.move({from: source, to: target, promotion: 'q'});

	// illegal move
	if (move === null) {
		console.log("illegal!");
		return false
	}

	/* update UI board to new game state */
	console.log('output fen: ' + game.fen());
	console.log("move accepted");

	if(game.game_over()) {
		console.log("game over!");
		return true;
	}

	/* how will the engine reply? */
    let engine = new Worker('./js/stockfish.js');
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
				board.setPosition(game.fen(), true);
				engine.postMessage('stop');
            }
        }
    };

	/* */

	console.log("launching engine!");
	engine.postMessage('position fen '+game.fen());
	engine.postMessage('go movetime 2000')

	return true;
}

