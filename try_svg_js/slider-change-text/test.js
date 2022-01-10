var slider;
var svg_object;
var xml_doc;
var tspan;

function body_loaded()
{
	slider = document.getElementById("myRange");
	slider.oninput = slider_changed;
}

function svg_loaded()
{
	svg_object = document.getElementById('svg-object');
	xml_doc = svg_object.contentDocument;

	text = xml_doc.getElementById("text87");
	console.assert(text.nodeName == "text");

	tspan = text.children[0]
	console.assert(tspan.nodeName == "tspan");
}

function slider_changed(evt)
{
	console.log(this.value);
	tspan.textContent = this.value;	
}

 


