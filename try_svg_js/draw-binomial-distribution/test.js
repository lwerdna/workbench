var slider;
var svg_object;
var p_output;
var xml_doc;
var tspans;
var rects;

function body_loaded()
{
}

function binary(x, width)
{
	var result = ''
	for(var i=0; i<width; ++i)
		result = ((x>>i)&1) + result;
	return result;
}

function svg_loaded()
{
	svg_object = document.getElementById('svg-object');
	xml_doc = svg_object.contentDocument;

	tspans = new Array(8)
	rects = new Array(8)

	for(var i=0; i<8; i++)
	{
		/* get tspan i */
		text = xml_doc.getElementById("text_" + binary(i, 3));
		console.assert(text.nodeName == "text");
		tspan = text.children[0]
		console.assert(tspan.nodeName == "tspan");
		tspans[i] = tspan;

		/* get rect i */
		rect = xml_doc.getElementById("rect_" + binary(i, 3));
		console.assert(rect.nodeName == "rect");
		rects[i] = rect;
	}
	
	/* set up slider */
	slider = document.getElementById("p");
	slider.oninput = slider_changed;

	p_output = document.getElementById('p_output');

	/* initial value */
	document.getElementById("p").value=.5;
	slider_changed();
}

/* probability of events (where bits represent success/failure) with success probability p */
function probability(events, p)
{
	var result = 1;
	for (var i=0; i<events.length; ++i)
	{
		if(events[i] == '0')
			result *= (1-p);
		else
			result *= p;
	}
	return result;
}

function slider_changed(evt)
{
	p = slider.value;
	p_output.textContent = "p: " + p

	for (var i=0; i<8; ++i)
	{
		p_path = probability(binary(i, 3), p);
		tspans[i].textContent = p_path.toFixed(3);
		rects[i].setAttributeNS(null, "height", 16*p_path);
	}
}

 


