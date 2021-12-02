var ctx
var width, height

var front
var mid
var back

function randomSpot()
{
	return [Math.floor(Math.random()*width),
		Math.floor(Math.random()*height)]
}

function randomSpotRight()
{
	return [width-1, Math.floor(Math.random()*height)]
}

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

function update()
{
	/* ImageData object */
	var imgdata = ctx.getImageData(0, 0, width, height)
	/* Uint8ClampedArray */
	var data = imgdata.data;

	for(var i=0; i<front.length; ++i) {
		position = front[i]
		setPixelRgb(data, position[0], position[1], [0,0,0])

		front[i][0] -= 4 
		if(front[i][0] < 0)
			front[i] = randomSpotRight()
		
		setPixelRgb(data, position[0], position[1], [255,255,255])
	}

	for(var i=0; i<mid.length; ++i) {
		position = mid[i]
		setPixelRgb(data, position[0], position[1], [0,0,0])

		mid[i][0] -= 2 
		if(mid[i][0] < 0)
			mid[i] = randomSpotRight()
		
		setPixelRgb(data, position[0], position[1], [128,128,128])
	}

	for(var i=0; i<back.length; ++i) {
		position = back[i]
		setPixelRgb(data, position[0], position[1], [0,0,0])

		back[i][0] -= 1 
		if(back[i][0] < 0)
			back[i] = randomSpotRight()
		
		setPixelRgb(data, position[0], position[1], [96,96,96])
	}

	ctx.putImageData(imgdata, 0, 0)
}

function main()
{
	var canvas = document.getElementById("myCanvas");
	
	/*	"2d"				returns CanvasRenderingContext2D
		"webgl" 			returns WebGLRenderingContext
		"webgl2"			returns WebGL2RenderingContext
		"bitmaprenderer"	returns ImageBitmapRenderingContext	*/
	ctx = canvas.getContext("2d", {alpha: false});

	width = canvas.width
	height = canvas.height

	front = new Array(100)
	for(var i=0; i<front.length; ++i)
		front[i] = randomSpot()
	
	mid = new Array(70)
	for(var i=0; i<mid.length; ++i)
		mid[i] = randomSpot()

	back = new Array(4000)
	for(var i=0; i<back.length; ++i)
		back[i] = randomSpot()

	/* setTimeout() for one-shot, time in ms */
	setInterval(update, 10);
}
