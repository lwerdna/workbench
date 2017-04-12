var g_input
var g_output
var g_canvas

/******************************************************************************
 * debug
 *****************************************************************************/
var g_DEBUG = 1

function debug(msg) {
    if(g_DEBUG) {
        console.log(msg)
    }
}

/******************************************************************************
 * HELPERS
 *****************************************************************************/
function dataFromElem(elem)
{
	var strings = elem.innerHTML.split("\n")
	return strings.map(parseFloat)
}

function dataToElem(data, elem)
{
	var dataStr = ''

	for(var i=0; i<data.length; ++i) {
		dataStr += data[i];

		if(i != data.length-1) {
			dataStr += '\n';
		}
	}

	elem.innerText = dataStr
}

/******************************************************************************
 * SERVICE ROUTINES
 *****************************************************************************/

function doSampling() {
	var values = dataFromElem(g_input);

	var weight = document.getElementById('weight').value
	var sampSize = document.getElementById('sampSize').value

	/* sanity check */
	if(sampSize > values.length) {
		alert("ERROR: you can't sample " + sampSize + 
			" values from a pool of " + values.length)
		return;
	}

	/* create ticket intervals for all values */
	var cur = 0
	var pool = []
	for(var i=0; i<values.length; ++i) {
		var value = values[i]
		var intervStart = cur
		var intervEnd
		if(weight == 'fair')
			intervEnd = intervStart+1
		else
		if(weight == 'medium')
			intervEnd = intervStart + (1 + .10*value)
		else
		if(weight == 'mut')
			intervEnd = intervStart + value

		record = [value, intervStart, intervEnd]
		pool.push(record)

		cur = intervEnd
	}

	/* draw winners */
	winners = []
	losers = []
	while(pool.length) {
		var ticket = Math.random() * pool[pool.length-1][2]

		/* find winner */
		var winIdx = -1
		var minIdx = 0
		var maxIdx = pool.length-1

		while(minIdx <= maxIdx) {
			var curIdx = Math.floor((minIdx + maxIdx)/2)
			var left = pool[curIdx][1]
			var right = pool[curIdx][2]
			
			if(ticket < left) {
				maxIdx = curIdx - 1;
			}
			else
			if(ticket >= right) {
				minIdx = curIdx + 1;
			}
			else {
				winIdx = curIdx
				break
			}
		}

		if(winIdx == -1) {
			alert("MAJOR ERROR! BLAME DEVELOPER!")
		}

		if(winners.length < sampSize)
			winners.push(pool[winIdx][0])
		else
			losers.push(pool[winIdx][0])

		/* collapse all indices following the winner */
		var curEnd = pool[winIdx][1]
		for(var j=winIdx+1; j<pool.length; ++j) {
			var length = pool[j][2] - pool[j][1]
			pool[j][1] = curEnd
			pool[j][2] = curEnd + length;
			curEnd = pool[j][2]
		}

		/* delete winner from pool */
		pool.splice(winIdx, 1)
	}

	/* use winners list to update output text */
	dataToElem(winners, g_output);

	/* draw this shit */
	var maxValue = Math.max(Math.max.apply(null, winners), Math.max.apply(null, losers))
	var scaler = 100 / maxValue

	g_canvas.width = Math.max(640, winners.length + losers.length)
	
	var ctx = g_canvas.getContext("2d");

	ctx.beginPath()
	ctx.rect(0, 0, g_canvas.width, g_canvas.height)
	ctx.fillStyle = "black"
	ctx.fill()

	ctx.strokeStyle="#00FF00"
	for(var i=0; i<winners.length; ++i) {
		ctx.beginPath()
		ctx.moveTo(i, 100)
		var height = scaler * winners[i]
		ctx.lineTo(i, 100-height)
		ctx.stroke()
	}

	ctx.strokeStyle="#FF0000"
	for(var i=0; i<losers.length; ++i) {
		ctx.beginPath()
		ctx.moveTo(winners.length + i, 100)
		var height = scaler * losers[i]
		ctx.lineTo(winners.length + i, 100-height)
		ctx.stroke()
	}
}

function logicInit() {
	/* set globals */
	g_input = document.getElementById('input')
	g_output = document.getElementById('output')
	g_canvas = document.getElementById('mycanvas')

	/* load up initial data */
	dataToElem(g_seedData, g_input);

	/* done */
	debug("shellInit() finished")
}


