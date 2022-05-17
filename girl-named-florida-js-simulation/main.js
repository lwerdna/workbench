const boy_boy = 0
const boy_girl = 1
const girl_boy = 2
const girl_girl = 3

function setPixelRgb(data, x, y, rgb)
{
	var idx = 4*(y*640 + x)
	data[idx] = rgb[0]
	data[idx+1] = rgb[1]
	data[idx+2] = rgb[2]
	data[idx+3] = 0xFF
}

function rand_int(n)
{
	let zero_to_one = Math.random(); // [0, 1) in R
	let zero_to_n = zero_to_one * n; // [0, n) in R
	let zero_to_n_int  = Math.floor(zero_to_n); // [0, n) in Z
	return zero_to_n_int;
}

function bernoulli_trial(p)
{
	return Math.random() < p;
}

function run_experiment(p_florida)
{
	gg_counts = [0, 0, 0, 0];
	names_counts = [0, 0, 0, 0];

	for(let x=0; x<640; x++)
	{
		for(let y=0; y<480; y++)
		{
			// 0 == boy boy
			// 1 == boy girl
			// 2 == girl boy
			// 3 == girl girl
			genders = rand_int(4);

			let has_girl_named_florida = false;
			switch(genders)
			{
				case boy_girl:
				case girl_boy:
					has_girl_named_florida = bernoulli_trial(p_florida)
					break;
				case 3:
					has_girl_named_florida = bernoulli_trial(p_florida) || bernoulli_trial(p_florida)
			}

			gg_counts[genders] += 1;

			if(has_girl_named_florida)
			{
				names_counts[genders] += 1;
				genders += 10;
			}

			population[x][y] = genders;
		}
	}
}

function draw()
{
	let color_lookup = [
		[0xbd, 0xe0, 0xfe], // boy boy
		[0xcd, 0xb4, 0xdb], // boy girl
		[0xcd, 0xb4, 0xdb], // girl boy
		[0xff, 0xc8, 0xdd] // girl girl
	]

	let imgData = context2d.getImageData(0, 0, 640, 480);
	let data = imgData.data;

	for(let x=0; x<640; x++)
	{
		for(let y=0; y<480; y++)
		{
			genders = population[x][y];

			let color = genders < 10 ? color_lookup[genders] : [255, 0, 0];
			setPixelRgb(data, x, y, color);
		}
	}
	
	context2d.putImageData(imgData, 0, 0);
}

/* html elements */
let canvas = document.getElementById('draw_area');
let context2d = canvas.getContext('2d');
let slider = document.getElementById('slider');
let slider_value = document.getElementById('slider-value');
let info = document.getElementById('info');

/* experiment results */
let population = Array(640);
for(let i=0; i<640; i++)
	population[i] = Array(480);
let gg_counts;
let names_counts;

function update()
{
	let p_florida = document.getElementById('slider').valueAsNumber;
	run_experiment(p_florida);
	draw();

	slider_value.innerHTML = p_florida;
	document.getElementById('boy-boy-value').innerHTML = `${gg_counts[0]}  (${(100*gg_counts[0]/(640*480)).toPrecision(4)}%)`;
	document.getElementById('boy-girl-value').innerHTML = 
	  `${gg_counts[1]}  (${(100*gg_counts[1]/(640*480)).toPrecision(4)}%), ${names_counts[1]} have <span style="background-color:red">a girl named Florida</span>`;
	document.getElementById('girl-boy-value').innerHTML =
	  `${gg_counts[2]}  (${(100*gg_counts[2]/(640*480)).toPrecision(4)}%), ${names_counts[2]} have <span style="background-color:red">a girl named Florida</span>`;
	document.getElementById('girl-girl-value').innerHTML =
	  `${gg_counts[3]}  (${(100*gg_counts[3]/(640*480)).toPrecision(4)}%), ${names_counts[3]} have <span style="background-color:red">a girl named Florida</span>`;
    info.innerHTML = `<b>Probability girl-girl given a girl named Florida is ${names_counts[3]}/(${names_counts[1]}+${names_counts[2]}+${names_counts[3]}) = ${(100*names_counts[3] / (names_counts[1] + names_counts[2] + names_counts[3])).toPrecision(4)}%</b>`
}

slider.addEventListener('input', update);

update();
