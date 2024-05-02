//       list of events here: https://developer.mozilla.org/en-US/docs/Web/Events
// mouse events for elements: https://developer.mozilla.org/en-US/docs/Web/API/Element#mouse_events
//                            https://developer.mozilla.org/en-US/docs/Web/API/GlobalEventHandlers/oninput

/* <button id="button0">Click Me</button> */
document.getElementById('button0').addEventListener('click', callback)

document.getElementById('slider').addEventListener('input', update);

/*
  <p>
    Number of trials:
    <input type="range" min="1" max="8" value="2" id="n_trials"
           oninput="document.getElementById('e000').innerHTML = this.value;" />
    <span id="e000">2</span>
  </p>
*/

/* invoke browser debugger programmatically */
debugger;

/* loop over arrays */
for (var i = 0; i < xs.length; i++) { console.log(xs[i]); }
xs.forEach((x, i) => console.log(x));
for (const x of xs) { console.log(x); }

/* template strings (like Python's format strings) */
console.log(`MyVar has value: ${MyVar}`);

function myFunction(p1, p2) {
  return p1 * p2;
}

/* remember we have:
 * SYNCHRONOUS (blocking)
 * ASYNCHRONOUS (via callbacks) eg: XMLHttpRequest()
 * ASYNCHRONOUS (via promises) eg: fetch()
 * and a promise is just a returned object upon which you can set callbacks with .then()
 */
const promise = fetch(url);
console.log(promise); /* will say "pending" */
promise.then((response) => {
  console.log(`Received response: ${response.status}`);
});
console.log("Started request…");

/* and .then() itself returns a promise, which will be completed with the result of the
 * function passed to it, so chaining looks like this: 
 * https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Asynchronous/Promises */
const promise = fetch(url);
promise
  .then((response) => response.json())
  .then((data) => {
    console.log(data[0].name);
  });


