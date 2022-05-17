let case1 = `
<p>Case 1/5</p>

<p>
The test is <b>sound</b> because the test never returns positive when the condition is negative.
It is <b>incomplete</b> because returns negative when the condition is positive.
</p>

<p>
Positive results are <b>trustworthy/honest</b>, since there are none.
Negative results are <b>untrustworthy/dishonest</b>.
</p>

<p>
The test's result is <b>sufficient</b>: T → D, because the implication will never be violated as T is never true.
The test is <b>not necessary</b> because it is never the case T ← D (or equivalently: /T ← /D).
</p>

<p>
It is <b>0% sensitive</b> since it never detects the condition.
It is <b>100% specific</b> since it always detects the absense of the condition.
</p>

<p>
The test <b>underreports</b>.
</p>

<p>
Example: a coin with "negative" written on both sides.
</p>
`

let case2 = `
<p>Case 2/5</p>

<p>
The test is <b>sound</b> because the test returns positive only for true positives.
The test is <b>incomplete</b> because not all true positives are detected.
</p>

<p>
Positive results are <b>trustworthy/honest</b>.
Negative results are <b>untrustworthy/dishonest</b>.
</p>

<p>
The test's result is <b>sufficient</b>: T → D.
The test is <b>not necessary</b> because it is not always true T ← D or equivalently /T ← /D.
</p>

<p>
The test <b>underreports</b>.
</p>

<p>
The test is a logical <b>"if"</b> for the condition.
The test is not a logical "only if" for the condition. The lone red dot shows its possible to have the condition without a positive test.
</p>

<p>
It <b>partially sensitive</b> since it returns positive for only some true positive cases.
It is <b>100% specific</b> since it returns negative for all true negative cases.
</p>

<p>
The test <b>underreports</b>.
</p>

<p>
Example: A medical test for a disease that's not sensitive enough. False negatives exist.
</p>

<p>
Example: A data recovery service claiming, with proof, they can recover your hard drive's data (reporting positive) is a sound test your data is recoverable. But it is incomplete, because if they say they are unable to perform recovery (reporting negative), you cannot rule out recoverability. Perhaps a more advanced service could recover it.
</p>
`

let case3 = `
<p>Case 3/5</p>

<p>
The test is <b>sound</b> because the test returns positive only for true positives.
It is <b>complete</b> because all true positives are detected.
It is <b>correct</b> because it is sound and complete.
</p>

<p>
Positive and negative results are <b>trustworthy/honest</b>.
</p>

<p>
The test is <b>sufficient</b> and <b>necessary</b>: T ↔ D
</p>

<p>
The test is a logical <b>"if"</b> and <b>"only if"</b> for the condition.
</p>

<p>
It is <b>100% sensitive</b>, returning true for all positive cases.
It is <b>100% specific</b>, returning false for all negative cases.
</p>

<p>
The test <b>overreports</b>.
</p>

<p>
Example: A medical test for a disease that perfectly distinguishes subjects into true positives and true negatives.
</p>

<p>
Example: Testing if a number is even by checking if its rightmost digit in decimal representation is in the set {0,2,4,5,8}.
</p>
`

let case4 = `
<p>Case 4/5</p>

<p>
The test is <b>unsound</b>. It may return positive for true negatives.
The test is <b>complete</b> because all true positives are detected.
</p>

<p>
Positive results are <b>untrustworthy/dishonest</b>.
Negative results are <b>trustworthy/honest</b>, since there are none.
</p>

<p>
The test's result is <b>insufficient</b> for condition D.
The test is <b>necessary</b> because T ← D (or equivalently: /T ← /D) is true.
</p>

<p>
The test is not a logical <b>"if"</b>.
It is an <b>"only if"</b> for the condition.
</p>

<p>
It is <b>100% sensitive</b>, returning true for all positive cases.
It is <b>not</b> 100% specific, as it returns a false positive.
</p>

<p>
The test <b>overreports</b>.
</p>

<p>
Example: A medical test for a disease that's too sensitive, reporting some false positives.
</p>

<p>
Example: Probabilistic primality tests like Miller-Rabin. False positives are known as pseudoprimes.
</p>
`

let case5 = `
<p>Case 5/5</p>

<p>
It is <b>unsound</b> because it may return positive for a true negative.
It is <b>complete</b> all true positives cause the test to return positive.
</p>

<p>
Positive results are <b>untrustworthy/dishonest</b>.
Negative results are <b>trustworthy/honest</b>, since there are none.
</p>

<p>
The test's result is <b>insufficient</b> for condition D.
The test is <b>necessary</b> you cannot have the condition without a positive test.
</p>

<p>
The test is not a logical <b>"if"</b>.
It is an <b>"only if"</b> for the condition.
</p>

<p>It is <b>not</b> sensitive since it never detects the condition.</p>
<p>It is <b>100% specific</b> since it always detects the absense of the condition.</p>

<p>
Example: a coin with "positive" written on both sides.
</p>
`

function draw(percent)
{
	context2d.clearRect(0, 0, 640, 120);

	// draw 4 equally spaced balls
	context2d.fillStyle = 'red';
	context2d.strokeStyle = 'black';

	context2d.beginPath();
	context2d.arc(80, 60, 30, 0, 2*Math.PI);
	context2d.fill();
	context2d.stroke();

	context2d.beginPath();
	context2d.arc(80+160, 60, 30, 0, 2*Math.PI);
	context2d.fill();
	context2d.stroke();

	context2d.fillStyle = 'grey';

	context2d.beginPath();
	context2d.arc(80+2*160, 60, 30, 0, 2*Math.PI);
	context2d.fill();
	context2d.stroke();

	context2d.beginPath();
	context2d.arc(80+3*160, 60, 30, 0, 2*Math.PI);
	context2d.fill();
	context2d.stroke();

	context2d.beginPath();
	context2d.rect(0, 0, 640*(percent/100), 120);
	context2d.stroke();
}

let canvas = document.getElementById('draw_area');
let context2d = canvas.getContext('2d');
let slider = document.getElementById('slider');
let info = document.getElementById('info');

function update()
{
	draw(slider.value);

	if(slider.value >= 93)
		info.innerHTML = case5;
	else if(slider.value >= 68)
		info.innerHTML = case4;
	else if(slider.value >= 43)
		info.innerHTML = case3;
	else if(slider.value >= 18)
		info.innerHTML = case2;
	else
		info.innerHTML = case1;
	
	//console.log(`update(${slider.value})`);
}

slider.addEventListener('input', update);

update();
