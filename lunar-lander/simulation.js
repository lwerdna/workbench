const canvas = document.getElementById("myCanvas");
const context = canvas.getContext("2d");

context.font = '14px sans-serif';

const elem_velocity = document.getElementById('velocity');
const elem_acceleration = document.getElementById('acceleration');

// ----------------------------------------------------------------------------
// LOAD IMAGES
// ----------------------------------------------------------------------------

function load_image(path)
{
	let result = new Image();
	result.src = path;
	return result;
}

const lander_width = 20;
const lander_height = 24;
const lander0 = load_image('assets/lander0.png')
const lander1 = load_image('assets/lander1.png')
const lander2 = load_image('assets/lander2.png')
let lander_pic = lander0;

//const clickSound = new Audio('assets/click.mp3');
//const pointSound = new Audio('assets/point.mp3');

// ----------------------------------------------------------------------------
// LANDER STATE
// ----------------------------------------------------------------------------

let x = (canvas.width / 2) - (lander_width / 2);
let y = canvas.height / 2;

let velocity = 0;
let accel_gravity = 9.8; /* m/s per second */
let accel_thrust = 0;

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

// ----------------------------------------------------------------------------
// FPS
// ----------------------------------------------------------------------------

function update()
{
	/* update state */

	/* apply acceleration to velocity */
	let acceleration = accel_gravity/fps + accel_thrust/fps;

	if (Math.abs(acceleration) > 10)
	{
		debugger;
	}

	velocity = velocity + acceleration;

	/* apply velocity to position */
	y += velocity;

	let ground = canvas.height - lander_height;
	if (y >= ground)
	{
		y = ground;
		velocity = 0;
	}

	elem_velocity.textContent = Math.round((velocity + Number.EPSILON) * 10000) / 10000;
	elem_acceleration.textContent = Math.round((acceleration + Number.EPSILON) * 10000) / 10000;
	
	//console.log(`x=${x} y=${y}`);

	/* background */
	context.fillStyle = "black";
	context.fillRect(0, 0, canvas.width, canvas.height);
	/* lander */
	context.drawImage(lander_pic, x, y);
	/* fps */
	context.fillStyle = "white";
	context.fillText(`fps: ${fps}`, 0, 12);
	
	/* update */
	frames += 1;
	window.requestAnimationFrame(update);
}

function handleKeyDown(e)
{
	if (e.code == "ArrowUp")
	{
		accel_thrust = -30;
		lander_pic = lander2;
		//console.log(`accel_thrust = ${accel_thrust}`);
	}

	//console.log(`${e.code}`);
}

function handleKeyUp(e)
{
	if (e.code == "ArrowUp")
	{
		accel_thrust = 0;
		lander_pic = lander0;
		//console.log(`accel_thrust = ${accel_thrust}`);
	}

	//console.log(`${e.code}`);
}

// main()
window.addEventListener("keydown", handleKeyDown);
window.addEventListener("keyup", handleKeyUp);

callback_1sec();

window.onload = update();

