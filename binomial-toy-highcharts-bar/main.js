const chart = Highcharts.chart("container", {
  chart: {
    type: 'bar'
  },
  title: {
    text: 'Binomial Distribution'
  },
  xAxis: {
    categories: ['00', '01', '10', '11'],
    title: {
      text: null
    }
  },
  yAxis: {
    min: 0,
    max: 1,
    title: {
      text: 'probability',
      align: 'high'
    },
    labels: {
      overflow: 'justify'
    }
  },
  plotOptions: {
    bar: {
      dataLabels: {
        enabled: true
      }
    }
  },
  series: [
    {
      name: 'success/failure sequence',
      data: [.25, .25, .25, .25]
    }
  ]
});

function round_to(n, decimal_places)
{
	let factor = 10**decimal_places;
	return Math.round((n + Number.EPSILON) * factor) / factor;
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

	let cats = [];
	let data = [];
	for(let i=0; i<(2**n_trials); ++i) {
		bitstr = i.toString(2);
		bitstr = '0'.repeat(n_trials - bitstr.length) + bitstr;
		cats.push(bitstr);

		data.push(round_to(p_bits(bitstr, p_trial), 2));
	}

	console.log('cats:');
	console.log(cats);
	console.log('data:');
	console.log(data);

	chart.xAxis[0].setCategories(cats);
	chart.series[0].setData(data);
	//chart.series[0].updateData(data);
}

let elem_n_trials = document.getElementById('n_trials');
let elem_p_trial = document.getElementById('p_trial');
elem_n_trials.addEventListener('input', update);
elem_p_trial.addEventListener('input', update)
