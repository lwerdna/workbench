var svg_doc;
var C;
var xspeed = 3;
var yspeed = 3;

// evt is an SVGLoad
// https://developer.mozilla.org/en-US/docs/Web/API/SVGElement/load_event
function startup(evt)
{
	// evt.target is an object representing the svg itself "<svg..."
	svg_doc = evt.target
	C = svg_doc.getElementById("C") /* circle */

	window.requestAnimationFrame(animateStep);
}

function animateStep(timestamp) 
{
	cx = parseInt(C.getAttribute('cx')) + xspeed;
	cy = parseInt(C.getAttribute('cy')) + yspeed;
	r = parseInt(C.getAttribute('r'));

	C.setAttributeNS(null, 'cx', cx);
	C.setAttributeNS(null, 'cy', cy);

	w = parseInt(svg_doc.getAttribute("width"))
	h = parseInt(svg_doc.getAttribute("height"))

	if (cx+r >= w || cx-r <= 0)
		xspeed *= -1;
	if (cy+r >= h || cy-r <= 0)
		yspeed *= -1;

	window.requestAnimationFrame(animateStep);
}
