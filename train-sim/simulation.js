const canvas = document.getElementById("myCanvas");
const context = canvas.getContext("2d");

function load_image(path)
{
	let result = new Image();
	result.src = path;
	return result;
}

const tiles = load_image('assets/tiles.png')
const track_ns = load_image('assets/track-NS.png')
const track_ew = load_image('assets/track-EW.png')
const track_ne = load_image('assets/track-NE.png')
const track_nw = load_image('assets/track-NW.png')
const track_se = load_image('assets/track-SE.png')
const track_sw = load_image('assets/track-SW.png')
const station = load_image('assets/station.png')
const track_point_n = load_image('assets/track-point-N.png')
const track_point_e = load_image('assets/track-point-E.png')
const track_point_s = load_image('assets/track-point-S.png')
const track_point_w = load_image('assets/track-point-W.png')
const clickSound = new Audio('assets/click.mp3');
const pointSound = new Audio('assets/point.mp3');

const grid = [
'┌--------------S---------------------┐', 
'|..............|.....................|', 
'|...┌----------S.....................|', 
'|...|..........|.....................|', 
'|...|..........|.....................|', 
'|...S----------E-----------E---------U', 
'|...|......................|.........|', 
'|...|......................|.........|', 
'|...S----------E-----------S.........|', 
'|...|..........|...........|.........|', 
'|...|..........|...........|.........|', 
'└---E----------E-----------R---------┘'];

for(var i=0; i<grid.length; i++)
	grid[i] = grid[i].split('')

const roundTime = 500;
const carCount = 3;
const trainSpriteOffset = 4;
const tileSize = 16;
let cars = [];
let grid2 = [];
let counter, mode, targetStation, points;

function reset()
{
	mode = 'play';
	counter = 0;

	/* initialize cars */
	for (let n = 0; n < carCount; n++)
	{
		cars[n] = {
			x: (20 + n) * tileSize,
			y: 0,
			xSpeed: -1,
			ySpeed: 0
		};
	}
	points = 0;
}

/*****************************************************************************/
/* car helpers */
/*****************************************************************************/

function is_vertical(car) { return car.xSpeed == 0; }
function is_horizontal(car) { return car.ySpeed == 0; }

function turn_E(car)
{
	car.ySpeed = 0;
	car.xSpeed = 1;
}

function turn_W(car)
{
	car.ySpeed = 0;
	car.xSpeed = -1;
}

function turn_N(car)
{
	car.ySpeed = -1;
	car.xSpeed = 0;
}

function turn_S(car)
{
	car.ySpeed = 1;
	car.xSpeed = 0;
}

function draw_tile(grid_x, grid_y, image)
{
	context.drawImage(image,
		0, 0, tileSize, tileSize,
		grid_x*tileSize, grid_y*tileSize, tileSize, tileSize);
}

function animate()
{
	if (mode == 'play')
	{
		/* draw background image */
		context.clearRect(0, 0, canvas.width, canvas.height);

		/* draw tracks */
		map_height = grid.length;
		map_width = grid[0].length;
		for(var y=0; y<map_height; y++) {
			for(var x=0; x<map_width; x++) {
				switch(grid[y][x]) {
					case '-': draw_tile(x, y, track_ew); break;
					case '|': draw_tile(x, y, track_ns); break;
					case '0':
					case '1':
					case '2':
					case '3':
					case '4':
					case '5':
					case '6':
					case '7':
					case '8':
					case '9': draw_tile(x, y, station); break;
					case 'E': draw_tile(x, y, track_point_e); break;
					case 'S': draw_tile(x, y, track_point_s); break;
					case 'N': draw_tile(x, y, track_point_n); break;
					case 'W': draw_tile(x, y, track_point_w); break;
					case '┐': draw_tile(x, y, track_sw); break;
					case '└': draw_tile(x, y, track_ne); break;
					case '┘': draw_tile(x, y, track_nw); break;
					case '┌': draw_tile(x, y, track_se); break;
				}
			}
		}

		/* draw each car */
		cars.forEach((car,index)=>{
			context.drawImage(tiles, (index + trainSpriteOffset) * tileSize, 1 * tileSize, tileSize, tileSize, car.x, car.y, tileSize, tileSize);
		}
		);

		/* move each car */
		cars.forEach((car,index)=>{
			let gridX = car.x / tileSize;
			let gridY = car.y / tileSize;
			if (gridX == Math.floor(gridX) && gridY == Math.floor(gridY))
			{
				let tileValue = grid[gridY][gridX];
				//console.log(`car ${index} sees tile ${tileValue}`);
				switch (tileValue)
				{
					case '┐':
						if(is_vertical(car)) turn_W(car)
						else turn_S(car)
						break;						
					case '└':
						if(is_vertical(car)) turn_E(car)
						else turn_N(car)
						break;						
					case '┘':
						if(is_vertical(car)) turn_W(car)
						else turn_N(car)
						break;					
					case '┌':
						if(is_vertical(car)) turn_E(car)
						else turn_S(car)
						break;
					case 'N': turn_N(car); break;
					case 'E': turn_E(car); break;
					case 'S': turn_S(car); break;
					case 'W': turn_W(car); break;
				}
//				if (index > 0 && tileValue > 'A' && tileValue < 'Z')
//				{
//					car.xSpeed = cars[index - 1].xSpeed;
//					car.ySpeed = cars[index - 1].ySpeed;
//				}
			}

			/* update position */
			car.x += car.xSpeed;
			car.y += car.ySpeed;
		}
		);
		counter++;
		let timeLeft = Math.floor(roundTime - counter / 10);
		context.fillText('Time left: ' + timeLeft, 290, 125);
		context.fillText(points, 460, 70);
		if (timeLeft == 0)
		{
			mode = 'gameOver';
			context.fillText('GAME OVER! Click to restart.', 230, 110);
		}
	}
	window.requestAnimationFrame(animate);
}

window.onpointerdown = function(event)
{
	if (mode == 'play')
	{
		let x = Math.floor(event.offsetX / tileSize);
		let y = Math.floor(event.offsetY / tileSize);
		console.log(`click canvas (${event.offsetX}, ${event.offsetY}) -> grid (${x}, ${y}) tile ${grid[y][x]}`)
		switch(grid[y][x])
		{
			case 'N': grid[y][x] = 'E'; break;
			case 'E': grid[y][x] = 'S'; break;
			case 'S': grid[y][x] = 'W'; break;
			case 'W': grid[y][x] = 'N'; break;
		}
		//clickSound.play();
	} else
		reset();
	event.preventDefault();
}
;

grid.forEach((r,index)=>{
		grid2[index] = Array.from(r);
	}
	);

context.fillStyle = 'green';
context.font = '14px sans-serif';

reset();
window.onload = animate();

