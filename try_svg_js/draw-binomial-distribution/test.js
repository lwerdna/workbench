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
	return Array.from(new Array(width), (value, index) => (x>>index)&1);
}

function binary_string(x, width)
{
	return binary(x, width).map(k => k.toString()).join("")
}

function set_text(name, value)
{
	text = xml_doc.getElementById(name);
	console.assert(text.nodeName == "text");
	tspan = text.children[0];
	console.assert(tspan.nodeName == "tspan");
	tspan.textContent = value;
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
		text = xml_doc.getElementById("text_" + binary_string(i, 3));
		console.assert(text.nodeName == "text");
		tspan = text.children[0]
		console.assert(tspan.nodeName == "tspan");
		tspans[i] = tspan;

		/* get rect i */
		rect = xml_doc.getElementById("rect_" + binary_string(i, 3));
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
		if(events[i])
			result *= p;
		else
			result *= (1-p);
	}
	return result;
}

function slider_changed(evt)
{
	p = slider.value;
	p_output.textContent = "p: " + p

	for (var i=0; i<2; ++i)
	{
		set_text('text_'+i, probability(binary(i, 1), p).toFixed(3));
	}

	for (var i=0; i<4; ++i)
	{
		set_text('text_'+binary_string(i, 2), probability(binary(i, 2), p).toFixed(3));
	}

	for (var i=0; i<8; ++i)
	{
		p_path = probability(binary(i, 3), p);
		tspans[i].textContent = p_path.toFixed(3);
		rects[i].setAttributeNS(null, "height", 16*p_path);
	}
}

 


