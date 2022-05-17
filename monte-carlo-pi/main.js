const WIDTH = 500;
const HEIGHT = 500;
const N_POINTS= 100000;
const RED = [255, 0, 0];

/* html elements */
let canvas = document.getElementById('draw_area');
let context2d = canvas.getContext('2d');
let slider = document.getElementById('slider');
let slider_value = document.getElementById('slider-value');
let info = document.getElementById('info');

/* experiment results */
let points = Array(N_POINTS);
let within = Array(N_POINTS);

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

function run_experiment()
{
	within[0] = 0;

	for(let i=0; i<N_POINTS; ++i)
	{
		// generate, store point
		let x = rand_int(WIDTH);
		let y = rand_int(HEIGHT);
		points[i] = [x, y];

		// is within circle?
		r = Math.sqrt((x-(WIDTH/2))**2 + (y-(WIDTH/2))**2);

		within[i] = within[(i==0) ? 0 : i-1];
		if(r < (WIDTH/2))
			within[i] += 1;
	}
}

function draw(n_points)
{
	// clear the drawing
	context2d.clearRect(0, 0, WIDTH, HEIGHT);

	// draw the circle
	context2d.strokeStyle = 'black';
	context2d.beginPath();
	context2d.arc((WIDTH/2), (WIDTH/2), (WIDTH/2), 0, 2*Math.PI);
	context2d.stroke();

	// draw the points
	let imgData = context2d.getImageData(0, 0, WIDTH, HEIGHT);
	let data = imgData.data;

	for(let i=0; i<n_points; ++i)
	{
		[x,y] = points[i];
		setPixelRgb(data, x, y, RED);
	}
	
	context2d.putImageData(imgData, 0, 0);
}

function update()
{
	// get number of points to display
	let num_points = document.getElementById('slider').valueAsNumber;

	// draw it
	draw(num_points);

	// calculate pi
	let inside = within[num_points-1];
	let pi = 4 * inside / num_points;
	let error = Math.abs(Math.PI - pi) / Math.PI

	// report results
	info.innerHTML = '';
	info.innerHTML += `number of points: ${num_points}<br>`
	info.innerHTML += `inside/total = ${inside}/${num_points} = ${round_to(inside/num_points, 4)}<br>`;
	info.innerHTML += `pi = ${round_to(pi, 8)} (${round_to(100*error, 4)}% error)`;
}

slider.addEventListener('input', update);

run_experiment();
update();
