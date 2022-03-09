var canvas
var ctx
var width, height
var firespace

var lastMouseY
var lastMouseX

/*
	0 == use SetInterval, we can set a frequency (in ms) (0 == max)
	1 == use RequestAnimationFrame(), attempted frequency is 60fps */
var animMethod = 1
var updateInterval = 1
//var animMethod = 'RequestAnimation'

var divisor = 4.01

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

	if(animMethod == 0) {
		/* do nothing, SetInterval() has us called ASAP */
	} else if(animMethod == 1) {
		/* must reschedule ourselves */
		window.requestAnimationFrame(update)
	}	
}

/****[ gui stuff ]*************************************************************/

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

function handleFile(e) {
	var fileObj = document.getElementById('inpFile').files[0]

	//console.log('reading file ' + fname)

	var img = new Image();
	/* when image source set, write in the canvas */
	img.onload = function() {
		/* get palette canvas, resize to picture */
		var palElem = document.getElementById('palette')
		palElem.width = img.width
		palElem.height = img.height

		/* draw image to palette canvas */
		var palCtx = palElem.getContext("2d")
		palCtx.drawImage(img, 0, 0, palElem.width, palElem.height)

		/* collect colors from palette canvas */
		var palPix = palCtx.getImageData(0, 0, palElem.width, palElem.height).data
		var colors = []
	
		var lastR = palPix[0]
		var lastG = palPix[1]
		var lastB = palPix[2]
	
		for(var x=0; x<palElem.width; ++x) {
			var r = palPix[4*x + 0]	
			var g = palPix[4*x + 1]	
			var b = palPix[4*x + 2]	
	
			if(r!=lastR || g!=lastG || b!=lastB) {
				colors.push([r,g,b])
				lastR = r
				lastG = g
				lastB = b
			}
		}
		console.log(palette)

		/* write to palette array */
		palette = colors
		while(palette.length < 256)
			palette.push(palette[palette.length-1])
		console.log(palette)
	}
	
	var reader = new FileReader()
	reader.onloadend = function() {
		img.src = reader.result		/* when reader is done, set image source */
	}
	reader.readAsDataURL(fileObj)
}

function onAnimMethChg(event) {
	var method0 = document.getElementById('method0').checked
	var method1 = document.getElementById('method1').checked

	if(method0 && animMethod != 0) {
		console.log('changing to animation method 0 (setInterval())')
		animMethod = 0
		setInterval(update, updateInterval);
	}
	else if(method1 && animMethod != 1) {
		console.log('changing to animation method 1 (requestAnimationFrame())')
		clearInterval(update)
		animMethod = 1
		requestAnimationFrame(update)
	}
}

/****[ main ]******************************************************************/

function main()
{
	var elem
	elem = document.getElementById("divisorSlider")
	elem.oninput = cbDivisorSlider
	divisor = elem.value / 1000.0
	console.log('initial divisor: ' + divisor)

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
	if(animMethod == 0) {
		setInterval(update, updateInterval);
	}
	else
	if(animMethod == 1) {
		window.requestAnimationFrame(update)
	}
}
