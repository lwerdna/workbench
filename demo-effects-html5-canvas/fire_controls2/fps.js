var fpsElem /* expected to be some element where we can set .innerText */
var fpsT0, frameCnt, fps
var fpsFont = "12px Arial"
var fpsTxtX=32, fpsTxtY=32

function initFps()
{
	fpsElem = document.getElementById("fps")

	fpsT0 = performance.now()
	frameCnt = 0
	fps = 0

	ctx.font = fpsFont
}

function fpsUpdate()
{
	frameCnt += 1

	var T1 = performance.now()
	if(T1-fpsT0 > 1000) {
		fps = frameCnt / ((T1-fpsT0)/1000.0)
		fpsElem.innerText = Math.round(fps)
		fpsT0 = T1;
		frameCnt = 0;
	}
}
