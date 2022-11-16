let chart;

/* generate data like:
      [
        {id: '0', value:.5, name:'0'},
        {id: '1', value:.5, name:'1'},

        {id: '00', value:.25, name:'00', parent:'0'},
        {id: '01', value:.25, name:'01', parent:'0'},
        {id: '10', value:.25, name:'10', parent:'1'},
        {id: '11', value:.25, name:'11', parent:'1'},

        {id: '000', value:.125, name:'000', parent:'00'},
        {id: '001', value:.125, name:'001', parent:'00'},
        {id: '010', value:.125, name:'010', parent:'01'},
        {id: '011', value:.125, name:'011', parent:'01'},
        {id: '100', value:.125, name:'100', parent:'10'},
        {id: '101', value:.125, name:'101', parent:'10'},
        {id: '110', value:.125, name:'110', parent:'11'},
        {id: '111', value:.125, name:'111', parent:'11'}
      ]
*/
function generate_re(base, p_current, p, remaining) {
	if(!remaining)
		return []

	let result = [
		{id:base+'0', value:p_current*(1-p), name:base+'0', parent:base},
		{id:base+'1', value:p_current*p, name:base+'1', parent:base}
	]
	
	result.push(...generate_re(base+'0', p_current*(1-p), p, remaining-1));
	result.push(...generate_re(base+'1', p_current*p, p, remaining-1));

	return result;
}

function generate(base, p_current, p, remaining) {
	result = generate_re(base, p_current, p, remaining);

	result.sort(function (a, b) {
	    if(a.id.length == b.id.length)
	        return a.id < b.id ? -1 : 1;
	    return a.id.length < b.id.length ? -1 : 1;
	})

	let colors = [
		'#377EB8', '#4DAF4A', '#984EA3', '#999999',
		'#A65628', '#E41A1C', '#F781BF', '#FF7F00'
	];

	if(result.length == 2) {
		for(let i=0; i<2; ++i)
			result[i].color = colors[i];
	}
	else
	if(result.length == 6) {
		for(let i=0; i<4; ++i)
			result[2+i].color = colors[i];
	}
	else
	if(result.length >= 12) {
		for(let i=0; i<8; ++i)
			result[6+i].color = colors[i];
	}

	return result;
}

function update() {
    n_trials = elem_n_trials.value;
    p_trial = elem_p_trial.value;

	data = generate('', 1, p_trial, n_trials);
	//console.log(data);

	chart.series[0].setData(data);
	//chart.series[0].updateData(data);
}

let elem_n_trials = document.getElementById('n_trials');
let elem_p_trial = document.getElementById('p_trial');
elem_n_trials.addEventListener('input', update);
elem_p_trial.addEventListener('input', update);

// generate initial chart
data = generate('', 1, elem_p_trial.value, elem_n_trials.value);
chart = Highcharts.chart("container", {
  title: {
    text: null,
  },

  series: [
    {
      type: "treemap",
      layoutAlgorithm: 'squarified',
      allowDrillToNode: false,    
      name: 'My Treemap',
      data: data,
    }
  ]
});


