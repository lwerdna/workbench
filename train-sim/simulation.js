const canvas = document.getElementById("myCanvas");
const context = canvas.getContext("2d");
const img = new Image();
img.src = "background.jpg";
const tiles = new Image();
tiles.src = "tiles.png";
const clickSound = new Audio('click.mp3');
const pointSound = new Audio('point.mp3');

const grid = [
'D______________L_______7_____________L', 
'0..............|.....................|', 
'|...D__________D.....................|', 
'|...|..........|.....................|', 
'|...|..........1.....................|', 
'|...D__6_______R___________R_________U', 
'|...|......................4.........|', 
'|...|......................|.........|', 
'|...D__________R___________U.........|', 
'|...|..........|...........|.........|', 
'|...2..........3...........|.........5', 
'R___R__________R___________R_________U'];
const buttons = [
	{	x: 15,	y: 0,	value: "D" },
	{	x: 15,	y: 2,	value: "L" },
	{	x: 4,	y: 5,	value: "R" },
	{	x: 4,	y: 8,	value: "R" },
	{	x: 15,	y: 8,	value: "D" },
	{	x: 27,	y: 11,	value: "U" }];
const roundTime = 500;
const carCount = 3;
const trainSpriteOffset = 4;
const stations = ['Ducktropolis', 'Ducks Landing', 'Duck City', 'Duckville', 'Duckburg', 'Ducktown', 'Duck Valley', 'Duck Corners'];
const tileSize = 16;
let cars = [];
let grid2 = [];
let counter, mode, targetStation, points;

function newTarget()
{
	targetStation = Math.floor(Math.random() * stations.length);
}

function reset()
{
	mode = 'play';
	counter = 0;
	for (let n = 0; n < carCount; n++)
	{
		cars[n] = {
			x: (20 + n) * tileSize,
			y: 0,
			xSpeed: -1,
			ySpeed: 0,
			spriteRow: 0
		};
	}
	points = 0;
	newTarget();
}

function animate()
{
	if (mode == 'play')
	{
		/* draw background image */
		context.drawImage(img, 0, 0);
		//context.clearRect(0, 0, canvas.width, canvas.height);

		/* draw buttons */
		buttons.forEach((button)=>{
			let offset;
			switch (grid2[button.y][button.x])
			{
				case 'U':
					offset = 0;
					break;
				case 'D':
					offset = 1;
					break;
				case 'R':
					offset = 2;
					break;
				case 'L':
					offset = 3;
					break;
			}

			context.drawImage(tiles,
				offset * tileSize,		/* source x */
				0,						/* source y */
				tileSize,				/* source width */
				tileSize,				/* source height */
				button.x * tileSize,	/* destination x */
				button.y * tileSize,	/* destination y */
				tileSize,				/* destination width */
				tileSize				/* destination height */
			);
		}
		);

		/* draw each car */
		cars.forEach((car,index)=>{
			context.drawImage(tiles, (index + trainSpriteOffset) * tileSize, car.spriteRow * tileSize, tileSize, tileSize, car.x, car.y, tileSize, tileSize);
		}
		);

		/* move each car */
		cars.forEach((car,index)=>{
			let gridX = car.x / tileSize;
			let gridY = car.y / tileSize;
			if (gridX == Math.floor(gridX) && gridY == Math.floor(gridY))
			{
				let tileValue = grid2[gridY][gridX];
				if (index == 0 && tileValue == targetStation)
				{
					pointSound.play();
					points++;
					newTarget();
				}
				switch (tileValue)
				{
					case 'L':
						car.xSpeed = -1;
						car.ySpeed = 0;
						car.spriteRow = 0;
						break;
					case 'R':
						car.xSpeed = 1;
						car.ySpeed = 0;
						car.spriteRow = 1;
						break;
					case 'U':
						car.xSpeed = 0;
						car.ySpeed = -1;
						car.spriteRow = 2;
						break;
					case 'D':
						car.xSpeed = 0;
						car.ySpeed = 1;
						car.spriteRow = 3;
						break;
				}
				if (index > 0 && tileValue > 'A' && tileValue < 'Z')
				{
					car.xSpeed = cars[index - 1].xSpeed;
					car.ySpeed = cars[index - 1].ySpeed;
					car.spriteRow = cars[0].spriteRow;
				}
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
		context.fillText(stations[targetStation], 460, 50);
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
		let x1 = Math.floor(event.offsetX);
		let y1 = Math.floor(event.offsetY);
		buttons.forEach((button)=>{
			let x2 = button.x * tileSize + tileSize / 2;
			let y2 = button.y * tileSize + tileSize / 2;
			let distance = Math.sqrt(Math.pow((x1 - x2), 2) + Math.pow((y1 - y2), 2));
			if (distance <= tileSize)
			{
				let x = button.x;
				let y = button.y;
				let temp = grid2[y][x];
				grid2[y][x] = button.value;
				button.value = temp;
				clickSound.play();
			}
		}
		);
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

