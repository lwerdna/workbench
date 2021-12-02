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

/****[ color conversions ]*****************************************************/

/**
 * Converts an RGB color value to HSL. Conversion formula
 * adapted from http://en.wikipedia.org/wiki/HSL_color_space.
 * Assumes r, g, and b are contained in the set [0, 255] and
 * returns h, s, and l in the set [0, 1].
 *
 * @param	 Number	r			 The red color value
 * @param	 Number	g			 The green color value
 * @param	 Number	b			 The blue color value
 * @return	Array				 The HSL representation
 */
function rgbToHsl(r, g, b) {
	r /= 255, g /= 255, b /= 255;

	var max = Math.max(r, g, b), min = Math.min(r, g, b);
	var h, s, l = (max + min) / 2;

	if (max == min) {
		h = s = 0; // achromatic
	} else {
		var d = max - min;
		s = l > 0.5 ? d / (2 - max - min) : d / (max + min);

		switch (max) {
			case r: h = (g - b) / d + (g < b ? 6 : 0); break;
			case g: h = (b - r) / d + 2; break;
			case b: h = (r - g) / d + 4; break;
		}

		h /= 6;
	}

	return [ h, s, l ];
}

/**
 * Converts an HSL color value to RGB. Conversion formula
 * adapted from http://en.wikipedia.org/wiki/HSL_color_space.
 * Assumes h, s, and l are contained in the set [0, 1] and
 * returns r, g, and b in the set [0, 255].
 *
 * @param	 Number	h			 The hue
 * @param	 Number	s			 The saturation
 * @param	 Number	l			 The lightness
 * @return	Array					 The RGB representation
 */
function hslToRgb(h, s, l) {
	var r, g, b;

	if (s == 0) {
		r = g = b = l; // achromatic
	} else {
		function hue2rgb(p, q, t) {
			if (t < 0) t += 1;
			if (t > 1) t -= 1;
			if (t < 1/6) return p + (q - p) * 6 * t;
			if (t < 1/2) return q;
			if (t < 2/3) return p + (q - p) * (2/3 - t) * 6;
			return p;
		}

		var q = l < 0.5 ? l * (1 + s) : l + s - l * s;
		var p = 2 * l - q;

		r = hue2rgb(p, q, h + 1/3);
		g = hue2rgb(p, q, h);
		b = hue2rgb(p, q, h - 1/3);
	}

	return [ r * 255, g * 255, b * 255 ];
}

/**
 * Converts an RGB color value to HSV. Conversion formula
 * adapted from http://en.wikipedia.org/wiki/HSV_color_space.
 * Assumes r, g, and b are contained in the set [0, 255] and
 * returns h, s, and v in the set [0, 1].
 *
 * @param	 Number	r			 The red color value
 * @param	 Number	g			 The green color value
 * @param	 Number	b			 The blue color value
 * @return	Array					 The HSV representation
 */
function rgbToHsv(r, g, b) {
	r /= 255, g /= 255, b /= 255;

	var max = Math.max(r, g, b), min = Math.min(r, g, b);
	var h, s, v = max;

	var d = max - min;
	s = max == 0 ? 0 : d / max;

	if (max == min) {
		h = 0; // achromatic
	} else {
		switch (max) {
			case r: h = (g - b) / d + (g < b ? 6 : 0); break;
			case g: h = (b - r) / d + 2; break;
			case b: h = (r - g) / d + 4; break;
		}

		h /= 6;
	}

	return [ h, s, v ];
}

/**
 * Converts an HSV color value to RGB. Conversion formula
 * adapted from http://en.wikipedia.org/wiki/HSV_color_space.
 * Assumes h, s, and v are contained in the set [0, 1] and
 * returns r, g, and b in the set [0, 255].
 *
 * @param	 Number	h			 The hue
 * @param	 Number	s			 The saturation
 * @param	 Number	v			 The value
 * @return	Array					 The RGB representation
 */
function hsvToRgb(h, s, v) {
	var r, g, b;

	var i = Math.floor(h * 6);
	var f = h * 6 - i;
	var p = v * (1 - s);
	var q = v * (1 - f * s);
	var t = v * (1 - (1 - f) * s);

	switch (i % 6) {
		case 0: r = v, g = t, b = p; break;
		case 1: r = q, g = v, b = p; break;
		case 2: r = p, g = v, b = t; break;
		case 3: r = p, g = q, b = v; break;
		case 4: r = t, g = p, b = v; break;
		case 5: r = v, g = p, b = q; break;
	}

	return [ r * 255, g * 255, b * 255 ];
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

function rgbStrToList(str) {
	var r = parseInt(str.substr(1,2),16)
	var g = parseInt(str.substr(3,2),16)
	var b = parseInt(str.substr(5,2),16)
	return [r,g,b]
}

function onColor0Change() {
	var descr = ''

	var elem = document.getElementById("color0")
	var rgbstr = elem.value
	descr += rgbstr

	var [r,g,b] = rgbStrToList(rgbstr)
	descr = (' RGB=('+r+','+g+','+b+')')
	var [h,s,l] = rgbToHsl(r,g,b)
	descr += (' HSL=('+Math.round(h*360)+'&deg;,'+Math.round(s*100)+'%,'+Math.round(l*100)+'%)')
	var [h,s,v] = rgbToHsv(r,g,b)
	descr += (' HSV/HSB=('+Math.round(h*360)+'&deg;,'+Math.round(s*100)+'%,'+Math.round(v*100)+'%)')

	elem = document.getElementById('color0txt')
	elem.innerHTML = descr
}

function canvasGraph(canvId, data, maxY)
{
	let can = document.getElementById(canvId)
	let w = can.width
	let h = can.height
	let ctx = can.getContext("2d")

	let xStep = hGraph.width / data.length
	let yStep = hGraph.height / maxY

	ctx.fillStyle = "#D0D0D0"
	ctx.fillRect(0, 0, w, h)
	ctx.strokeStyle = "#000000"
	ctx.beginPath()
	var first = true
	for(var i=0; i<data.length; ++i) {
		var x = i*xStep
		var y = h - data[i]*yStep
		if(first) {
			ctx.beginPath(x,y)
			first = false
		}
		else {
			ctx.lineTo(x,y)
		}
	}
	ctx.stroke()
}

function drawGraphs() {
	var pix = ctx.getImageData(0, 0, canvas.width, canvas.height).data;

	var colors = []

	var lastR = pix[0]
	var lastG = pix[1]
	var lastB = pix[2]
	colors.push([lastR,lastG,lastB])

	for(var x=0; x<canvas.width; ++x) {
		var r = pix[4*x + 0]	
		var g = pix[4*x + 1]	
		var b = pix[4*x + 2]	

		if(r!=lastR || g!=lastG || b!=lastB) {
			colors.push([r,g,b])
			lastR = r
			lastG = g
			lastB = b
		}
	}

	//console.log('unique colors:')
	//for(var i=0; i<colors.length; ++i) {
	//	[r,g,b] = colors[i]	
	//	console.log('color '+i+' ('+r+','+g+','+b+')')
	//}

	/* drop those colors into the code area */
	var celem = document.getElementById('code')
	var code = ''
	code += 'var palette = [ /* ' + colors.length + ' entries */\n'
	for(var i=0; i<colors.length; ++i) {
		code += '[' + colors[i][0] + ',' + colors[i][1] + ',' + colors[i][2] + '], '
	}
	code += '\n]\n'
	celem.innerText = code

	var dataH=[], dataS=[], dataL=[]

	for(var i=0; i<colors.length; ++i) {
		var [r,g,b] = colors[i]
		var [h,s,l] = rgbToHsl(r,g,b)
		dataH.push(h * 360)
		dataS.push(s * 100)
		dataL.push(l * 100)
	}

	console.log(dataH)

	canvasGraph('hGraph', dataH, 360)
	canvasGraph('sGraph', dataS, 100)
	canvasGraph('lGraph', dataL, 100)
}

function handleFile(e) {
	var fileObj = document.getElementById('inpFile').files[0]
	//console.log('reading file ' + fname)

	var img = new Image();
	/* when image source set, write in the canvas */
	img.onload = function() {
		canvas.width = img.width
		canvas.height = img.height
		document.getElementById("hGraph").width = img.width
		document.getElementById("sGraph").width = img.width
		document.getElementById("lGraph").width = img.width
		ctx.drawImage(img, 0, 0, ctx.canvas.width, ctx.canvas.height)
		drawGraphs()
	}
	
	var reader = new FileReader()
	reader.onloadend = function() {
		img.src = reader.result		/* when reader is done, set image source */
	}
	reader.readAsDataURL(fileObj)
}

/****[ main ]******************************************************************/

function main()
{
	/* set up key listener */
	window.onkeyup = cbKey

	var elem
	elem = document.getElementById("color0")
	console.log(elem)

	canvas = document.getElementById("preview");
	ctx = canvas.getContext("2d");

}
