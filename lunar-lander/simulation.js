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

let pid_controller = null;

let pg_position = null;
let pg_velocity = null;
let pg_acceleration = null;
let pg_erro = null;

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

let x = (100 / 2) - (lander_width / 2);
let y = canvas.height / 2;

let velocity = 0;
let accel_gravity = -9.8; /* m/s per second */
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
// Graphers
// ----------------------------------------------------------------------------

class PixelGrapher
{
	constructor(canvas_ctx, x, y, range_min, range_max, color)
	{
		this.canvas_ctx = canvas_ctx;
		this.x = x;
		this.y = y;
		this.range_min = range_min;
		this.range_max = range_max;
		this.width = 100;
		this.height = 100;
		this.color = color;

		this.history = [];
		for (var i=0; i<this.width; ++i)
			this.history.push(0);
	}

	add_data(y)
	{
		this.history.copyWithin(0, 1);
		this.history[this.width-1] = y;
	}

	update()
	{
		this.canvas_ctx.lineWidth = 1;
		this.canvas_ctx.beginPath();

		for (var i=0; i<this.history.length; i++)
		{
			var y = this.history[i];
			if (false)
				if (y < this.range_min || y > this.range_max)
					continue;
			else
			{
				y = max(y, this.range_min);
				y = min(y, this.range_max);
			}
			
			var px_height = (y-this.range_min)/(this.range_max-this.range_min) * this.height;

			this.canvas_ctx.moveTo(this.x+i, this.y+this.height);
			this.canvas_ctx.lineTo(this.x+i, this.y+this.height - px_height);
		}

		this.canvas_ctx.strokeStyle = this.color;
		this.canvas_ctx.stroke();
	}
}

// ----------------------------------------------------------------------------
// PID
// ----------------------------------------------------------------------------

class Pid
{
	constructor(setpoint)
	{
		this.setpoint = setpoint;

		this.history = [];
		for (var i=0; i<30; i++)
			this.history.push(0);

		this.gain_p = 1/3;
		this.gain_i = 1/3;
		this.gain_d = 1/3;
	}

	inform(measurement)
	{
		var error = measurement - this.setpoint;

		this.history.copyWithin(0, 1);
		this.history[this.history.length-1] = error;
	}

	query(dt)
	{
		var n = this.history.length;

		/* proportional is just the last error */
		proportional = this.history[n-1];

		/* integral is the mass from the history */
		integral = this.history.map((x) => dt*x).reduce((a, b) => a + b, 0);

		/* derivative is estimated by taking the slope of last two measures */
		derivative = (this.history[n-1] - this.history[n-2]) / dt;

		/*  */
		return this.gain_p * proportional + this.gain_i * integral + this.gain_d * derivative;
	}
}

// ----------------------------------------------------------------------------
// UPDATE
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

	/* hit ground? */
	if (y < 0)
	{
		y = 0;
		velocity = 0;
	}

	/* inform pid contoller */
	pid_controller.inform(y);

	/* inform pixel graphers */
	pg_acceleration.add_data(acceleration);
	pg_velocity.add_data(velocity);
	pg_position.add_data(y);
	//console.log(pid_controller.history[pid_controller.history.length-1]);
	pg_error.add_data(pid_controller.history[pid_controller.history.length-1]);

	elem_position.textContent = Math.round((y + Number.EPSILON) * 10000) / 10000;
	elem_velocity.textContent = Math.round((velocity + Number.EPSILON) * 10000) / 10000;
	elem_acceleration.textContent = Math.round((acceleration + Number.EPSILON) * 10000) / 10000;
	
	//console.log(`x=${x} y=${y}`);

	/* background */
	context.fillStyle = "black";
	context.fillRect(0, 0, canvas.width, canvas.height);
	/* lander */

	/* convert y (position) to y_canvas (canvas coords) */
	let y_canvas = canvas.height - y - lander_height

	/* DRAW: FPS */
	context.fillStyle = "white";
	context.fillText(`fps: ${fps}`, 0, 12);
	/* DRAW: line */
	context.strokeStyle = "white";
	context.moveTo(0, canvas.height/2);
	context.lineTo(100, canvas.height/2);
	context.stroke();
	/* DRAW: lander */
	context.drawImage(lander_pic, x, y_canvas);
	/* DRAW: velocity graph */
	pg_position.update();
	pg_velocity.update();
	pg_acceleration.update();
	pg_error.update();
	
	/* update */
	frames += 1;
	window.requestAnimationFrame(update);
}

function handleKeyDown(e)
{
	if (e.code == "ArrowUp")
	{
		accel_thrust = 30;
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
pg_position = new PixelGrapher(context, 100, 0, -1, 700, 'red');
pg_velocity = new PixelGrapher(context, 100, 100, -10, 10, 'green');
pg_acceleration = new PixelGrapher(context, 100, 200, -.5, .5, 'blue');
pg_error = new PixelGrapher(context, 100, 300, -200, 200, 'cyan');

pid_controller = new Pid(200);

callback_1sec();

window.onload = update();

