var svg_doc;
var hlines=8
var vlines=10

// evt is an SVGLoad
// https://developer.mozilla.org/en-US/docs/Web/API/SVGElement/load_event
function startup(evt)
{
	// evt.target is an object representing the svg itself "<svg..."
	svg_doc = evt.target
	V = document.getElementById("V") /* vertical line */
	H = document.getElementById("H") /* horizontal line */
	C = document.getElementById("C") /* circle */
	drawlines(hlines, vlines)
}

function drawlines(hoz,vrt)
{
	var B = svg_doc.getBBox()
	var w = B.width
	var h = B.height
	for (var i=0; i<=hoz; i++)
	{
		var HC = H.cloneNode(false)
		HC.setAttributeNS(null,"y1",i*h/hoz)
		HC.setAttributeNS(null,"y2",i*h/hoz)
		svg_doc.appendChild(HC)
	}
	for (var i=0; i<=vrt; i++)
	{
		var VC = V.cloneNode(false)
		VC.setAttributeNS(null,"x1",i*w/vrt)
		VC.setAttributeNS(null,"x2",i*w/vrt)
		svg_doc.appendChild(VC)
	}
	for (var i=0; i <= hoz; i++)
	{
		for (var j=0; j<=vrt; j++)
		{
			var CC = C.cloneNode(false)
			CC.setAttributeNS(null,"cx",j*w/vrt)
			CC.setAttributeNS(null,"cy",i*h/hoz)
			CC.setAttributeNS(null,"id",j+":"+i)
			svg_doc.appendChild(CC)
		}
	}
}

function change(event)
{
	// svg_elem is likely the "<circle id="3:6" r="10" stro..."
	var svg_elem = event.target
	if (svg_elem.getAttribute("fill") == "red")
		svg_elem.setAttributeNS(null, "fill", "white")
	else
		svg_elem.setAttributeNS(null, "fill", "red")
}
