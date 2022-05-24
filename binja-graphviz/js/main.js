function expand_svg(width, height) {
	console.log(`resizing svg to ${width},${height}`)

	let e_svg = document.getElementsByTagName('svg')[0]
	e_svg.attributes.width.value = Math.max(e_svg.attributes.width.value, width);
	e_svg.attributes.height.value = Math.max(e_svg.attributes.height.value, height);
}

function transition_out_edges(except) {
	// fade out arrowheads
    d3.selectAll('.arrow')
	  .transition()
	  .style('stroke', 'rgb(42, 42, 42)')
	  .style('fill', 'rgb(42, 42, 42)')

	// fade out edges, remove
	for (const c of ['.edge-binja', '.edge-dot']) {
		if(c == except)
			continue

		d3.selectAll(c)
		  //.transition()
		  .style('stroke', 'rgb(42, 42, 42)')
		  .remove()
    }
}

function show_graphviz(graph) {
	let func_name = e_function_names.value;
	let graph_binja = files[func_name + '_binja.json']

	expand_svg(graph['width'], graph['height']);

	//selection = d3.selectAll('.bb');
	//selection.each(function(d, i) {
	//	console.log(this);
	//});
	//expand_svg(graph['width'], graph['height']);
	
    transition_out_edges('.edge-dot');

	function rebuild_edges() {
		/* draw graphviz edges */
		d3.select('#functiongraph0')
		  .selectAll('.edge-dot')
		  .data(graph['edges'])
		  .join('path')
		  .attr('class', function(d, i) {
		  	return 'edge-dot ' + d['type'];
		  })
		  .attr('d', function(d, i) {
		  	let points = d['points']
		  	let result = `M ${points[0]},${points[1]}`;
		  	result += ' C'
		  	for(let i=2; i<points.length; i+=2)
		  		result += `${points[i]},${points[i+1]} `;
			return result;
		  })
		  .attr('marker-end', function(d, i) {
			return 'url(#arrow-' + d['type'] + ')';
		  })
		  .style('stroke', 'rgb(42, 42, 42)')
		  .transition()
		  .style('stroke', null)		  

	    d3.selectAll('.arrow')
		  .style('stroke', 'rgb(42, 42, 42)')
		  .style('fill', 'rgb(42, 42, 42)')
		  .transition()
		  .style('stroke', null)
		  .style('fill', null)
	}

	/* move, scale the blocks */
	d3.selectAll('.bb')
		.data(graph['blocks'])
		.join('g')
		.transition()
		.attr('transform', function(d, i) {
	    	let [x,y,w,h] = d['rect']
	    	let [bx,by,bw,bh] = graph_binja['blocks'][i]['rect']
	    	//console.log('transforming: ', this);
	    	result = `translate(${x-bx}, ${y-by})`
	    	//console.log(result)
			return result
		})

	d3.selectAll('.bb rect')
		.data(graph['blocks'])
		.join('rect')
		.transition()
		.attr('width', function(d, i) {
			return graph['blocks'][i]['rect'][2];
		})
		.attr('height', function(d, i) {
			return graph['blocks'][i]['rect'][3];
		})
		.on('end', rebuild_edges);

}

function show_dot() {
	let func_name = e_function_names.value;
	let graph = files[func_name + '_dot.json']
	show_graphviz(graph)
}

function show_dot_ortho() {
	let func_name = e_function_names.value;
	let graph = files[func_name + '_dot_ortho.json']
	show_graphviz(graph)
}

function show_binja() {
	let func_name = e_function_names.value;
	let graph = files[func_name + '_binja.json']

	expand_svg(graph['width'], graph['height']);

    transition_out_edges('.edge-binja')

	// rebuild edges <polyline>
	function rebuild_edges() {
		d3.select('#functiongraph0')
		  .selectAll('.edge-binja')
		  .data(graph['edges'])
		  .join('polyline')
		  .attr('class', function(d,i) {
		    if(d.type=='TrueBranch') return 'edge-binja TrueBranch';
		    if(d.type=='FalseBranch') return 'edge-binja FalseBranch';
		    if(d.type=='UnconditionalBranch') return 'edge-binja UnconditionalBranch';
		  })
		  .attr('points', function(d,i) {
	        let points = d['points'];
		    let result = '';
		    for(let i=0; i<points.length; i+=2)
		        result += `${points[i]},${points[i+1]} `
		    return result
		  })
		  .attr('marker-end', function(d,i) {
		    if(d.type=='TrueBranch') return 'url(#arrow-TrueBranch)';
		    if(d.type=='FalseBranch') return 'url(#arrow-FalseBranch)';
		    if(d.type=='UnconditionalBranch') return 'url(#arrow-UnconditionalBranch)';
		  })
		  .style('stroke', 'rgb(42, 42, 42)')
		  .transition()
		  .style('stroke', null)

	    d3.selectAll('.arrow')
		  .style('stroke', 'rgb(42, 42, 42)')
		  .style('fill', 'rgb(42, 42, 42)')
		  .transition()
		  .style('stroke', null)
		  .style('fill', null)
	}

	// remove transformation (returning to original SVG positions)
	d3.selectAll('.bb')
	  .transition()
	  .attr('transform', '')
	  .on('end', rebuild_edges)
}

function load_function() {
	let func_name = e_function_names.value;
	console.log(`load_function(${func_name})`);

	e_svg_container = document.getElementById('svg-container');
	e_svg_container.innerHTML = files[func_name + '.svg'];
}

document.getElementById('button0').addEventListener('click', show_binja);
document.getElementById('button1').addEventListener('click', show_dot);
document.getElementById('button2').addEventListener('click', show_dot_ortho);

let e_function_names = document.getElementById('function_names')
for (const fn of funcs) {
	let option = document.createElement('option');
	option.value = fn;
	option.text = fn;
	e_function_names.add(option);
}
e_function_names.addEventListener('change', load_function);
load_function();
