var canvas
var ctx
var width, height
var firespace

var lastMouseY
var lastMouseX

/* for the RequestAnimation method, browser will call us 60fps

	for the SetInterval method, we can set a frequency (in ms) where
	0 is maximum frequency and depends on how fast our function returns */
var animMethod = 'SetInterval'
var updateInterval = 10
//var animMethod = 'RequestAnimation'

/****[ fire settings ]********************************************************/

var divisor = 4.01

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

function distance(x0,y0,x1,y1)
{
	return Math.sqrt((x0-x1)**2 + (y0-y1)**2)
}

/* thanks https://www.hanshq.net/fire.html */
/* Jare's original FirePal. */
var palette = [
[0,0,0], [0,4,4], [0,16,20], [0,28,36], [0,32,44], [0,36,48], [60,24,32],
[100,16,16], [132,12,12], [160,8,8], [192,8,8], [220,4,4], [252,0,0],
[252,0,0], [252,12,0], [252,28,0], [252,40,0], [252,52,0], [252,64,0],
[252,80,0], [252,92,0], [252,104,0], [252,116,0], [252,132,0], [252,144,0],
[252,156,0], [252,156,0], [252,160,0], [252,160,0], [252,164,0], [252,168,0],
[252,168,0], [252,172,0], [252,176,0], [252,176,0], [252,180,0], [252,180,0],
[252,184,0], [252,188,0], [252,188,0], [252,192,0], [252,196,0], [252,196,0],
[252,200,0], [252,204,0], [252,204,0], [252,208,0], [252,212,0], [252,212,0],
[252,216,0], [252,220,0], [252,220,0], [252,224,0], [252,228,0], [252,228,0],
[252,232,0], [252,232,0], [252,236,0], [252,240,0], [252,240,0], [252,244,0],
[252,248,0], [252,248,0], [252,252,0],
/* Followed by "white heat". */
[252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252],
[252,252,252], [252,252,252], [252,252,252], [252,252,252], [252,252,252]
]

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

/* INPUT:
	data	Uint8ClampedArray
	x,y		coordinates
	color	[0,255] palette index
*/
function setPixelPal(data, x, y, color)
{
	firespace[y*width + x] = color
	setPixelRgb(data, x, y, palette[color])
}

function getPixelPal(data, x, y)
{
	if(x >= width || x < 0 || y >= height || y < 0)
		return 0;
	return firespace[y*width + x]
}

/* if the animation method is requestAnimationFrame(), this first parameter is
	a DOMHighRestTimeStamp */
var ticker = 0

function update(dhrts)
{
	/* ImageData object */
	var imgdata = ctx.getImageData(0, 0, width, height)
	/* Uint8ClampedArray */
	var data = imgdata.data;

	/* random palette entries across the bottom */
	for(var x=0; x<width; ++x) {
		var color = Math.floor(Math.random()*256)
		setPixelPal(data, x, height-1, color)
	}

	/* CA for next cell */
	for(var y=0; y<height-1; ++y) {
		for(var x=0; x<width; ++x) {
			var sum = 0
			sum += getPixelPal(data, x-1, y+1)
			sum += getPixelPal(data, x, y+1)
			sum += getPixelPal(data, x+1, y+1)
			sum += getPixelPal(data, x, y+2)

			var divisor_ = divisor

			/* if the "firefinger" is nearby, decrease divisor (increase heat!) */
			if(lastMouseX && lastMouseY) {
				var dist = distance(x,y,lastMouseX,lastMouseY)
				if(dist < 16) {
					divisor_ *= .75 
				}
			}

			sum = Math.floor(sum/divisor_)

			if(sum > 255)
				sum = 255

			setPixelPal(data, x, y, sum)
		}
	}

	ctx.putImageData(imgdata, 0, 0)

	ticker += 1

	fpsUpdate()
}

/****[ gui stuff ]*************************************************************/

function cbKey(event) {
	/* event.keycode is ascii of key, eg 0x41
		event.key is ascii representation, eg 'A' */

	var key = event.key
	//console.log('cbKey got key: ' + key)
	if(!key) return;
}

function cbDivisorSlider() {
	divisor = this.value / 1000

	document.getElementById("divisorSliderText").innerText = "divisor: " + divisor
	ctx.clearRect(0,0,width,height)
}

function cbDownCanvas(event) {
	var rect = canvas.getBoundingClientRect()
	var canvX = event.clientX - rect.left
	var canvY = event.clientY - rect.top
	lastMouseX = canvX
	lastMouseY = canvY
	//console.log('you pressed button: ' + event.button)
}

/****[ main ]******************************************************************/

function main()
{
	/* set up key listener */
	window.onkeyup = cbKey

	var elem
	elem = document.getElementById("divisorSlider")
	elem.oninput = cbDivisorSlider
	divisor = elem.value / 1000.0
	console.log('initial divisor: ' + divisor)

	fpsElem = document.getElementById("fps")
	canvas = document.getElementById("myCanvas")
	
	/*	"2d"				returns CanvasRenderingContext2D
		"webgl" 			returns WebGLRenderingContext
		"webgl2"			returns WebGL2RenderingContext
		"bitmaprenderer"	returns ImageBitmapRenderingContext	*/
	ctx = canvas.getContext("2d", {alpha: false});
	width = canvas.width
	height = canvas.height

	canvas.addEventListener('mousemove', cbDownCanvas)

	firespace = new Array(width*height)
	firespace.fill(0)

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
