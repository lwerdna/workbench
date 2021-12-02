var ctx
var width, height

var palSpace

var t0 = performance.now()
var fcnt = 0
var fps = 0

var tick = 0

var palette = [ [253,2,0], [254,6,0], [254,12,0], [254,19,0],
[254,24,1], [254,30,2], [254,38,1], [254,43,0], [254,48,0], [254,53,0],
[255,59,0], [254,65,0], [254,72,0], [253,78,0], [253,84,3], [253,89,2],
[255,96,4], [254,100,2], [254,107,3], [254,114,1], [254,119,1], [254,126,0],
[253,132,0], [253,137,0], [255,142,2], [255,147,2], [254,153,1], [254,160,2],
[254,165,0], [254,172,0], [254,179,0], [253,183,0], [254,189,0], [255,195,0],
[255,202,2], [255,209,2], [253,214,0], [253,221,0], [252,228,0], [254,234,0],
[254,239,0], [254,244,0], [254,250,1], [251,253,2], [247,254,1], [241,254,0],
[234,254,0], [229,255,0], [224,253,2], [217,254,1], [212,253,0], [204,254,0],
[199,255,0], [192,255,0], [187,254,0], [181,254,0], [174,254,0], [169,255,0],
[164,253,1], [157,254,0], [151,254,1], [143,255,0], [138,254,0], [132,255,0],
[127,254,1], [121,254,1], [114,253,0], [108,254,0], [103,254,0], [95,255,0],
[90,254,0], [84,254,0], [80,254,1], [74,254,0], [69,252,1], [62,253,0],
[57,254,1], [50,254,0], [44,254,0], [38,253,0], [33,254,0], [27,254,0],
[20,254,0], [13,253,0], [8,253,0], [3,254,1], [0,255,5], [0,255,8], [0,255,17],
[0,255,23], [1,253,28], [0,254,36], [1,254,42], [1,254,49], [0,255,50],
[0,255,57], [0,255,63], [0,254,68], [0,254,74], [0,254,80], [0,254,88],
[0,254,94], [0,253,102], [0,254,106], [1,254,111], [0,254,114], [0,254,122],
[1,254,129], [1,254,137], [1,253,142], [1,254,148], [0,254,152], [0,254,158],
[0,254,162], [0,253,170], [1,253,176], [0,254,182], [0,253,188], [0,253,196],
[0,253,199], [1,254,207], [0,254,210], [0,255,218], [0,254,224], [0,254,230],
[0,254,236], [0,255,244], [0,254,248], [1,254,252], [0,249,253], [0,242,254],
[0,236,254], [1,229,255], [0,223,255], [0,216,255], [0,211,254], [0,205,254],
[0,200,252], [0,195,253], [0,188,252], [0,182,255], [0,175,255], [0,168,255],
[1,164,255], [0,159,253], [0,154,252], [0,147,251], [0,142,252], [1,134,255],
[1,129,255], [1,122,255], [1,117,254], [0,112,253], [0,107,252], [0,101,253],
[0,95,252], [1,88,255], [0,82,254], [0,75,255], [1,71,255], [0,65,255],
[0,60,255], [0,52,252], [0,46,253], [1,40,255], [2,34,255], [2,26,255],
[0,20,255], [0,15,255], [0,10,255], [0,4,253], [2,1,252], [9,0,253],
[13,0,255], [20,0,255], [23,0,254], [31,0,252], [36,1,253], [44,1,255],
[50,0,255], [56,0,255], [61,0,254], [70,0,255], [73,0,255], [80,0,255],
[83,0,252], [90,0,253], [96,0,252], [103,0,255], [110,0,255], [116,0,254],
[120,0,254], [129,0,253], [132,0,252], [140,1,254], [145,0,255], [151,0,255],
[156,0,254], [165,0,255], [169,0,253], [174,0,255], [178,1,253], [186,1,255],
[192,1,254], [197,0,255], [204,0,255], [210,0,255], [215,1,255], [221,0,254],
[226,1,255], [234,0,255], [241,1,255], [246,1,255], [251,0,253], [254,0,249],
[255,0,244], [254,0,239], [253,0,231], [253,1,226], [252,1,218], [253,0,212],
[252,1,205], [255,0,204], [254,0,197], [255,0,190], [254,0,184], [254,1,179],
[253,1,172], [253,1,166], [252,1,158], [254,1,154], [253,1,148], [255,0,143],
[255,0,138], [255,0,134], [254,0,125], [254,0,119], [254,0,114], [253,0,107],
[253,1,102], [254,0,97], [254,0,90], [253,0,85], [253,1,78], [254,0,72],
[253,0,64], [253,0,59], [253,0,54], [255,0,47], [255,0,42], [255,0,37],
[255,0,30], [255,0,24], [255,0,16], [255,0,11], [255,0,8] ]

function setPixelRgb(data, x, y, rgb) {
	var idx = 4*(y*width + x)
	data[idx] = rgb[0]
	data[idx+1] = rgb[1]
	data[idx+2] = rgb[2]
	data[idx+3] = 0xFF
}

function setPixelPal(data, x, y, color) {
	setPixelRgb(data, x, y, palette[(color+tick)%256])
}

function draw()
{
	var imgdata = ctx.getImageData(0, 0, width, height)
	var data = imgdata.data;

	for(var y=0; y<height-1; ++y) {
		for(var x=0; x<width; ++x) {
			setPixelPal(data, x, y, palSpace[y][x])
		}
	}

	ctx.putImageData(imgdata, 0, 0)
	fcnt += 1
	tick += 1

	var t1 = performance.now()
	if(t1-t0 > 1000) {
		fps = fcnt / ((t1-t0)/1000.0)
		console.log('fps: ' + fps)
		t0 = t1;
		fcnt = 0;
	}

	requestAnimationFrame(draw)
}

function main()
{
	var canvas = document.getElementById("myCanvas");
	
	ctx = canvas.getContext("2d", {alpha: false});

	width = canvas.width
	height = canvas.height

	/* allocate plasma */
	palSpace = new Array(height)
	for(var i=0; i<height; ++i) {
		palSpace[i] = new Array(width)
		palSpace[i].fill(0)
	}

	for(var y=0; y<height; ++y) {
		for(var x=0; x<width; ++x) {
			/* these three functions are from http://lodev.org/cgtutor/plasma.html */
			if(0) {
				var pidx =	128 + (127 * Math.sin(x / 16.0)) +
					128 + (127 * Math.sin(y / 16.0))
				palSpace[y][x] = Math.round(pidx/2)
			}

			if(0) {
				var pidx = 128.0 + (128.0 * Math.sin(x / 16.0)) +
							128.0 + (128.0 * Math.sin(y / 8.0)) + 
							128.0 + (128.0 * Math.sin((x + y) / 16.0)) +
							128.0 + (128.0 * Math.sin(Math.sqrt((x * x + y * y)) / 8.0))
				palSpace[y][x] = Math.round(pidx/4)
			}
   
			if(1) {
				var pidx = 128.0 + (128.0 * Math.sin(x / 16.0))
							+ 128.0 + (128.0 * Math.sin(y / 32.0))
							+ 128.0 + (128.0 * Math.sin(Math.sqrt(((x - width / 2.0)* (x - width / 2.0) + (y - height / 2.0) * (y - height / 2.0))) / 8.0))
							+ 128.0 + (128.0 * Math.sin(Math.sqrt((x * x + y * y)) / 8.0))
				palSpace[y][x] = Math.round(pidx/4)
			}
		}
	}

	/* setTimeout() for one-shot, time in ms */
	requestAnimationFrame(draw)
}
