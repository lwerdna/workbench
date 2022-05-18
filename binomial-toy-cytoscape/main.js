const WIDTH = 500;
const HEIGHT = 500;
const RED = [255, 0, 0];

const graph_style = [ // the stylesheet for the graph
	{
		// https://js.cytoscape.org/#style/labels
		selector: 'node',
		style:
		{
			'border-color': 'black',
			'border-style': 'solid',
			'border-width': 1,
			'background-color': '#C0C0C0',
			'line-color': 'black',
			'label': 'data(label)',
			'text-halign': 'center',
			'text-valign': 'center',
			'shape': 'round-rectangle'
		}
	},
	{
		selector: 'edge',
		style:
		{
	  	  'width': 3,
	  	  'line-color': '#ccc',
	  	  'target-arrow-color': '#ccc',
	  	  'target-arrow-shape': 'triangle',
	  	  'curve-style': 'bezier',
	  	  'label': 'data(label)'
		}
	}
]

/* globals */
let cy;
let info = document.getElementById('info');

function setPixelRgb(data, x, y, rgb)
{
	var idx = 4*(y*WIDTH + x)
	data[idx] = rgb[0]
	data[idx+1] = rgb[1]
	data[idx+2] = rgb[2]
	data[idx+3] = 0xFF
}

function rand_int(n)
{
	let zero_to_one = Math.random(); // [0, 1) in R
	let zero_to_n = zero_to_one * n; // [0, n) in R
	let zero_to_n_int = Math.floor(zero_to_n); // [0, n) in Z
	return zero_to_n_int;
}

function round_to(n, decimal_places)
{
	let factor = 10**decimal_places;
	return Math.round((n + Number.EPSILON) * factor) / factor;
}

//-----------------------------------------------------------------------------
// binary tree stuff
//-----------------------------------------------------------------------------
function bintree_gen_re(id, remaining)
{
	let result = {id: id};

	if(remaining)
	{
	    result.left = bintree_gen_re(id+'0', remaining-1);
	    result.right = bintree_gen_re(id+'1', remaining-1);
	}

	return result;
}

function bintree_gen(depth)
{
	let result = {id: 'root'};

	if(depth > 0)
	{
	    result.left = bintree_gen_re('0', depth-1);
	    result.right = bintree_gen_re('1', depth-1);
	}

	return result;
}

function bintree_get_ids(root)
{
	let result = [root.id];

	if(root.left != undefined)
	{
		result.push(...bintree_get_ids(root.left));
		result.push(...bintree_get_ids(root.right));
	}

	return result;
}

function bintree_get_edges(root)
{
	let result = [];

	if(root.left != undefined)
	{
		// add my edges to children
		result.push({src:root.id, dst:root.left.id, label:'F'});
		result.push({src:root.id, dst:root.right.id, label:'S'});
		// add childrens edges
		result.push(...bintree_get_edges(root.left));
		result.push(...bintree_get_edges(root.right));
	}

	return result;
}

//-----------------------------------------------------------------------------
// 
//-----------------------------------------------------------------------------

// '01101' -> p**3 * (1-p)**2
function p_bits(bits, p)
{
	let result = bits.split('').map(x => x==1 ? p : (1-p)).reduce((x,y)=>x*y, 1);
	result = round_to(result, 4);
	return result;
}

function gen_elements(n_trials, p_trial)
{
	let result = { nodes: [], edges: [] };

	let tree = bintree_gen(n_trials);

	let ids = bintree_get_ids(tree);
	for(const id of ids)
	{
		let label = id;
		if(label != 'root')
			label = p_bits(label, p_trial)

		result.nodes.push({ data: { id:id, label:label }});
	}

	let edges = bintree_get_edges(tree);
	for(const edge of edges)
	{
		result.edges.push({ data:
			{
				source: edge.src,
				target: edge.dst,
				label: edge.label
			}
		});
	}

	return result;
}

function update()
{
	let n_trials = document.getElementById('n_trials').value;
	let p_trial = document.getElementById('p_trial').value;

	if(cy != undefined)
		cy.destroy();
	
	cy = cytoscape({
  		container: document.getElementById('cy'), // container to render in
  		elements: gen_elements(n_trials, p_trial),
		style: graph_style,
  		layout: {
	    	name: 'dagre'
  		}
	});
}

document.getElementById('n_trials').addEventListener('input', update);
document.getElementById('p_trial').addEventListener('input', update);

update()
