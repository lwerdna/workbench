var slider;
var svg_object;
var xml_doc;

function body_loaded()
{
	slider = document.getElementById("myRange");
	slider.oninput = slider_changed;
}

function svg_loaded()
{
	svg_object = document.getElementById('svg-object');
	xml_doc = svg_object.contentDocument;
	xml_doc.getElementById("text_001").textContent = "test"; // text disappears! WTF?
}

function slider_changed(evt)
{
	console.log(this.value);
	
}

 


