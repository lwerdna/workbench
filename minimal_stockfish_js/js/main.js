// this is a javascript MODULE
// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Guide/Modules

export const name = 'main'

import {Chessboard, COLOR, INPUT_EVENT_TYPE} from "./cm-chessboard/Chessboard.js"

export function CreateGame(fen, title, elem_id)
{
	/*
	let h2 = document.createElement('h2');
	h2.innerText = title;
	document.body.append(h2)
	*/

	/*
	let div = document.createElement('div');
	div.style.width = '400px';
	div.style.height = '400px';
	document.body.append(div)
	*/

	/* set up chessboard */
	console.log(`element id is: ${elem_id}`)
	let elem = document.getElementById(elem_id);
    let chessboard = new Chessboard(elem, {position: fen});

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

/* convert long algebraic like "e2e4" to short algebraic notation like "Bxf7+" */
function lan_to_san(game, line)
{
	let sans = []

	/* save game state */
	let fen = game.fen();

	for (const lan of line.split(' '))
	{
		/* eg: "e2e4" */
		let src = lan.substr(0, 2);
		let dst = lan.substr(2, 4);
    	let move = game.move({from: src, to: dst, promotion: 'q'});

		if (move === null)
		{
			console.log(`ERROR: Stockfish returned illegal move: ${lan}`);
			return null
		}

		sans.push(move.san);
	}


	/* restore game state */
	game.load(fen);

	/* done */
	return sans.join(' ');
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
    //engine.postMessage('setoption name MultiPV value 3');
    engine.postMessage('uci');

    engine.onmessage = function(event) {
        let line = event.data;
        if(line == 'uciok') {
			console.log("engine replied 'uciok'");
        } else if(line == 'readyok') {
			console.log("engine replied 'readyok'");
        } else {
            console.log('line: ' + line);
            var match = line.match(/^bestmove ([a-h][1-8])([a-h][1-8])([qrbk])?/);
            if(match) {
				console.log("engine has a move! " + line);
                game.move({from: match[1], to: match[2], promotion: match[3]});
				board.setPosition(game.fen(), true);
				engine.postMessage('stop');
            }

			// eg: 
            var match = line.match(/^info depth \d+ seldepth \d+ score cp (\d+) nodes \d+ nps \d+ time \d+ multipv \d+ pv (.*)/);
            if(match) {
            	console.log("engine has new line! " + line);
	            let [_, score, moves] = match
	            score = parseInt(score) * .01
	            score = Math.round((score + Number.EPSILON) * 100) / 100

	            //console.log("parsed out: " + moves);
	            let san = lan_to_san(game, moves);
	            //console.log('san: ' + san);
	            document.getElementById('board0_line0').value = `${score} ${san}`
	        }
        }
    };

	/* */

	console.log("launching engine!");
	engine.postMessage('position fen '+game.fen());
	engine.postMessage('go movetime 2000')

	return true;
}

