var ctx
var width, height
var x, y
var radius = 50
var vect = [4, 4]

function update()
{
	ctx.clearRect(0, 0, width, height)

	ctx.beginPath();
	ctx.arc(x, y, radius, 0, 2*Math.PI);
	ctx.fillStyle = "#0095DD"
	ctx.fill();
	ctx.closePath();

	ctx.fillStyle = "#FF0000"
	ctx.fillText('('+x+','+y+')', x+radius, y-radius);

	x += vect[0]
	y += vect[1]

	if(x < (0+radius))
		vect[0] = 4;
	if(x >= (640-radius))
		vect[0] = -4;
	if(y < (0+radius))
		vect[1] = 4;
	if(y >= (480-radius))
		vect[1] = -4;
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

	x = radius;
	y = radius;

	/* setTimeout() for one-shot, time in ms */
	setInterval(update, 10);
}
