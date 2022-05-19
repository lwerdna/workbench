/* html elements */
let door0 = document.getElementById('door0');
let door1 = document.getElementById('door1');
let door2 = document.getElementById('door2');
let doors = [door0, door1, door2];
let info = document.getElementById('info');

/* game state */
let game_state;
let first_choice; // {1,2,3}
let door_revealed;
let door_prize; // {1,2,3}

/* record keeping */
let wins_stay = 0;
let games_stay = 0;
let wins_switch = 0;
let games_switch = 0;
let games_played = 0;

function sleep(duration)
{
    let now = new Date().getTime();
    while(new Date().getTime() < now + duration)
    {
    	/* Do nothing */
    }
}

function rand_int(n)
{
	let zero_to_one = Math.random(); // [0, 1) in R
	let zero_to_n = zero_to_one * n; // [0, n) in R
	let zero_to_n_int = Math.floor(zero_to_n); // [0, n) in Z
	return zero_to_n_int;
}

function rand_select(array)
{
	return array[rand_int(array.length)];
}

function round_to(n, decimal_places)
{
	let factor = 10**decimal_places;
	return Math.round((n + Number.EPSILON) * factor) / factor;
}

function update()
{
	info.innerHTML = `
	    games played: ${games_played}<br>
	    win/loss when staying: ${wins_stay}/${games_stay} (${round_to(100*wins_stay/games_stay, 2)}%)<br>
	    win/loss when switching: ${wins_switch}/${games_switch} (${round_to(100*wins_switch/games_switch, 2)}%)<br>
    `
}

function door_close(i)
{
	console.log(`closing door ${i}`);
	doors[i].innerHTML = '';

	for (const color of ['#FFFFFF', '#F0F0F0', '#E0E0E0', '#C0C0C0'])
	{
		doors[i].style.backgroundColor = color;
		//sleep(50);
	}
	
	doors[i].removeAttribute('style')
	doors[i].innerHTML = '?'
}

function door_reveal(i, play_sound)
{
	console.log(`revealing door ${i}`);
	doors[i].innerHTML = '';

	for (const color of ['#C0C0C0', '#E0E0E0', '#F0F0F0', '#FFFFFF'])
	{
		doors[i].style.backgroundColor = color;
		//sleep(50);
	}

	if(i == door_prize)
	{
		doors[i].innerHTML = '<img src="res/car.jpg">';
		if(play_sound)
			(new Audio('./res/car.mp3')).play();
	}
	else
	{
		doors[i].innerHTML = '<img src="res/goat.jpg">';
		if(play_sound)
			(new Audio('./res/goat.mp3')).play();
	}
}

function game_reset()
{
	first_choice = undefined;
	game_state = 0;

	// close the doors
	door_close(0);
	door_close(1);
	door_close(2);

	// place prize
	door_prize = rand_int(3); // {0,1,2}
	console.log(`prize is behind door ${door_prize}`);
}

function door_select(i)
{
	console.log(`selecting door ${i}`);

	// use attribute .style to set inline styles
	for (const j of [0,1,2])
		doors[j].style.borderColor = (j==i) ? 'red' : 'black';
}

function onclick_door(choice)
{
	door_elems = 
	console.log(`you clicked door: ${choice}`);

	if(game_state == 0)
	{
		// save first choice
		first_choice = choice;
		door_select(choice);

		// open another door
		candidates = [0,1,2].filter(d => d!=choice && d!=door_prize);
		i = rand_select(candidates)
		door_reveal(i, true)
		door_revealed = i;

		game_state = 1;
	}
	else
	if(game_state == 1)
	{
		if(choice == door_revealed)
			return;

		door_select(choice);

		// reveal selected door
		door_reveal(choice, true);

		// reveal remaining door
		candidates = [0,1,2].filter(d => d!=choice && d!=door_revealed);
		door_reveal(candidates[0], false);

		// won? update stats
		won = choice == door_prize;

		if(choice == first_choice)
		{
		    wins_stay += won;
		    games_stay += 1;
		}
		else
		{
			wins_switch += won;
			games_switch += 1;
		}

		games_played += 1;

		game_state = 2;
	}
	else
	if(game_state == 2)
	{
		game_reset();
	}

	update();
}

door0.addEventListener('click', function() { onclick_door(0); });
door1.addEventListener('click', function() { onclick_door(1); });
door2.addEventListener('click', function() { onclick_door(2); });

game_reset();
update();
