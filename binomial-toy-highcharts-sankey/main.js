const data_keys = ['from', 'to', 'weight'];
const data_data = [
	["root", "0", .5],
	["root", "1", .5],
	["0", "00", .25],
	["0", "01", .25],
  	["1", "10", .25],
	["1", "11", .25],
];

const chart = Highcharts.chart("container", {
  chart: {
        animation: false
  },
  title: {
    text: "Binomial Distribution"
  },
  accessibility: {
    point: {
      valueDescriptionFormat:
        "{index}. {point.from} to {point.to}, {point.weight}."
    }
  },
  series: [
    {
      keys: data_keys,
      data: data_data,
      type: "sankey",
    }
  ],
  accessibility: {
     enabled: false
  }
});

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

// '01101' -> p**3 * (1-p)**2
function p_bits(bits, p) {
	let result = bits.split('').map(x => x==1 ? p : (1-p)).reduce((x,y)=>x*y, 1);
	result = result;
	return result;
}

function update() {
    n_trials = elem_n_trials.value;
    p_trial = elem_p_trial.value;
    console.log(`update() with n_trials=${n_trials}, p_trial=${p_trial}`);  

	tree = bintree_gen(n_trials);

	// turn tree into this format:
	// [
	//  [ from:str, to:str, weight:float ],
	//  ...
	// ]
	let data = [];
	let edges = bintree_get_edges(tree);
	for(const edge of edges) {
		data.push( [edge.src, edge.dst, p_bits(edge.dst, p_trial)]);
	}

	console.log(data);

	chart.series[0].update(
      {
        keys: data_keys,
        data: data,
        type: "sankey",
      }
    );
}

let elem_n_trials = document.getElementById('n_trials');
let elem_p_trial = document.getElementById('p_trial');
elem_n_trials.addEventListener('input', update);
elem_p_trial.addEventListener('input', update)
