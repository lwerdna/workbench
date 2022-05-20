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
function generate(base, p_current, p, remaining) {
	if(!remaining)
		return []

	let result = [
		{id:base+'0', value:p_current*(1-p), name:base+'0', parent:base},
		{id:base+'1', value:p_current*p, name:base+'1', parent:base}
	]
	
	result.push(...generate(base+'0', p_current*(1-p), p, remaining-1));
	result.push(...generate(base+'1', p_current*p, p, remaining-1));

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


