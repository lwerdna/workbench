var ctx
var width, height
var depth = 3

var numBack = 150
var numMid = 100
var numFront = 50

var stars

var ticker = 0

var elemFps

/* for the RequestAnimation method, browser will call us 60fps

	for the SetInterval method, we can set a frequency (in ms) where
	0 is maximum frequency and depends on how fast our function returns */
var animMethod = 'SetInterval'
var updateInterval = 10
//var animMethod = 'RequestAnimation'

/****[ star settings ]********************************************************/

var depth2color = [[255,255,255],	// depth 0, brightest
				[128,128,128],	// depth 1, medium
				[96,96,96]]		// depth 2, dim

var depth2speed = [8,4,2]

/*	INPUT:	n
	OUTPUT:	[0,n-1]	*/
function randRange(n)
{
	return Math.floor(Math.random()*n)
}

function randomStar(x,y,z)
{
	if(x == undefined) x = randRange(width)
	if(y == undefined) y = randRange(height)
	if(z == undefined) z = randRange(depth)
	console.log('returning star ' + x + ',' + y + ',' + z)
	return [x,y,z]
}

function initStarsArray()
{
	console.log('initializing ' + numBack + ' and ' + numMid + ' and ' + numFront)
	stars = []
	for(var i=0; i<numBack; ++i)
		stars.push(randomStar(undefined, undefined, 2))
	for(var i=0; i<numMid; ++i)
		stars.push(randomStar(undefined, undefined, 1))
	for(var i=0; i<numFront; ++i) {
		console.log('YEEHAW')
		stars.push(randomStar(undefined, undefined, 0))
	}
}

/****[ fps stuff ]************************************************************/

var fpsElem
var t0, frameCnt, fps
var fpsFont = "12px Arial"
var fpsTxtX=32, fpsTxtY=32

function initFps()
{
	t0 = performance.now()
	frameCnt = 0
	fps = 0

	ctx.font = fpsFont
}

function fpsUpdate()
{
	frameCnt += 1

	var t1 = performance.now()
	if(t1-t0 > 1000) {
		fps = frameCnt / ((t1-t0)/1000.0)
		fpsElem.innerText = Math.round(fps)
		t0 = t1;
		frameCnt = 0;
	}
}

/****[ draw ]******************************************************************/

/* INPUT:
	data	Uint8ClampedArray
	x,y		coordinates
	rgb		3-array with r,g,b values
*/
function setPixelRgb(data, x, y, rgb)
{
	var idx = 4*(y*width + x)
	data[idx] = rgb[0]
	data[idx+1] = rgb[1]
	data[idx+2] = rgb[2]
	data[idx+3] = 0xFF
}

/* if the animation method is requestAnimationFrame(), this first parameter is
	a DOMHighRestTimeStamp */
function update(dhrts)
{
	/* ImageData object */
	var imgdata = ctx.getImageData(0, 0, width, height)
	/* Uint8ClampedArray */
	var data = imgdata.data;

	for(var i=0; i<stars.length; ++i) {
		[x,y,z] = stars[i]

		//console.log('star[' + i + '] = (' + x + ',' + y + ',' + z + ')')

		/* erase old star */
		setPixelRgb(data, Math.round(x), Math.round(y), [0,0,0])

		/* new position */
		/* had options:
			1) store only the start point, then calculate draw point from trig(start)
			2) store current point, update it in steps from trig(velocity), after round
			3) store current point, update it in steps from trig(velocity), keep float (use round before draw)
		*/
		x = x + depth2speed[z] * Math.sin((ticker/1000)*2*Math.PI)
		y = y + depth2speed[z] * Math.sin((ticker/700)*2*Math.PI)

		if(x < 0) {
			[x,y,z] = randomStar(width-1,undefined,z)
		} else if(x >= width) {
			[x,y,z] = randomStar(0,undefined,z)
		} else if(y < 0) {
			[x,y,z] = randomStar(undefined,height-1,z)
		} else if(y >= height) {
			[x,y,z] = randomStar(undefined,0,z)
		}

		stars[i] = [x,y,z]

		/* draw it */
		setPixelRgb(data, Math.round(x), Math.round(y), depth2color[z])
	}
	
	fpsUpdate()

	ticker++;
	ctx.putImageData(imgdata, 0, 0)

	if(animMethod == 'RequestAnimation') {
		window.requestAnimationFrame(update)
	}
}

/****[ gui stuff ]*************************************************************/

function cbKey(event) {
	/* event.keycode is ascii of key, eg 0x41
		event.key is ascii representation, eg 'A' */

	var key = event.key
	//console.log('cbKey got key: ' + key)
	if(!key) return;
}

function cbBackSlider() {
	document.getElementById("starsBackText").innerText = "stars back: " + this.value
	numBack = this.value
	ctx.clearRect(0,0,width,height)
	initStarsArray()	
}

function cbMidSlider() {
	document.getElementById("starsMidText").innerText = "stars mid: " + this.value
	numMid = this.value
	ctx.clearRect(0,0,width,height)
	initStarsArray()	
}

function cbFrontSlider() {
	document.getElementById("starsFrontText").innerText = "stars front: " + this.value
	numFront = this.value
	ctx.clearRect(0,0,width,height)
	initStarsArray()	
}


/****[ main ]******************************************************************/

function main()
{
	/* set up key listener */
	window.onkeyup = cbKey

	var elem
	elem = document.getElementById("starsBackSlider")
	elem.oninput = cbBackSlider
	numBack = elem.value
	elem = document.getElementById("starsMidSlider")
	elem.oninput = cbMidSlider
	numMid = elem.value
	elem = document.getElementById("starsFrontSlider")
	elem.oninput = cbFrontSlider
	numFront = elem.value

	fpsElem = document.getElementById("fps")
	var canvas = document.getElementById("myCanvas")
	
	/*	"2d"				returns CanvasRenderingContext2D
		"webgl" 			returns WebGLRenderingContext
		"webgl2"			returns WebGL2RenderingContext
		"bitmaprenderer"	returns ImageBitmapRenderingContext	*/
	ctx = canvas.getContext("2d", {alpha: false});
	width = canvas.width
	height = canvas.height

	initStarsArray()
	initFps()

	/* go! */
	/* setTimeout() for one-shot, time in ms */

	if(animMethod == 'RequestAnimation') {
		window.requestAnimationFrame(update)
	}
	else
	if(animMethod == 'SetInterval') {
		setInterval(update, updateInterval);
	}
}
