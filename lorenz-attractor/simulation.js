/*
 canvas coords are x,y with origin at top-left of canvas and top-left of sprites
 real coords are x,y with origin at bottom-left of canvas
 */
const canvas = document.getElementById("myCanvas");
const context = canvas.getContext("2d");

context.font = '14px sans-serif';

const elem_position = document.getElementById('position');
const elem_velocity = document.getElementById('velocity');
const elem_acceleration = document.getElementById('acceleration');

// ----------------------------------------------------------------------------
// LANDER STATE
// ----------------------------------------------------------------------------

let x = 0
let y = 1
let z = 1.5
let dt = .01
let rho = 28
let sigma = 10
let beta = 8/3

// ----------------------------------------------------------------------------
// FPS
// ----------------------------------------------------------------------------

let frames = 60;
let fps = 60;
function callback_1sec()
{
	fps = frames;
	frames = 0;
	window.setTimeout(callback_1sec, 1000);
}

function map(x, y)
{
	let x_canvas = (x + 21) * canvas.width / 42
	let y_canvas = (-y + 30) * canvas.height / 60
	return [x_canvas, y_canvas]
}

// ----------------------------------------------------------------------------
// UPDATE
// ----------------------------------------------------------------------------

function update()
{
	coords_start = map(x, y)

	/* update state */
    x += sigma * (y-x) * dt
    y += (x * (rho - z) - y) * dt
    z += (x * y - beta*z) * dt
    //console.log(`x,y,z = ${x},${y},${z}`)

	coords_end = map(x, y)

	/* DRAW: FPS */
	context.fillStyle = "white";
	context.fillText(`fps: ${fps}`, 0, 12);
	context.stroke();
	/* DRAW: point */
	context.beginPath();
	context.fillStyle = "white";
	context.moveTo(coords_start[0], coords_start[1]);
	context.lineTo(coords_end[0], coords_end[1]);
	context.fillStyle = "red";
	context.strokeStyle = "#ffffff"
	context.stroke();
	//context.fillRect(coords_start[0], coords_start[1], 1, 1);
	//context.fillRect(coords_end[0], coords_end[1], 1, 1);
	
	/* update */
	frames += 1;
	window.requestAnimationFrame(update);
}

// main()
/* background */
context.fillStyle = "black";
context.fillRect(0, 0, canvas.width, canvas.height);
/* set for pixel */
context.fillStyle = "rgba(255,0,0)";


callback_1sec();

window.onload = update();

