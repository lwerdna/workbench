// https://www.d3indepth.com/selections/
// https://www.d3indepth.com/datajoins/
//
let cities = [
  { name: 'London', population: 8674000},
  { name: 'New York', population: 8406000},
  { name: 'Sydney', population: 4293000},
  { name: 'Paris', population: 2244000},
  { name: 'Beijing', population: 11510000}
];

// once you have a selection, you probably wanna call something like:
// .style(), .attr(), .text() and .each()
function update() {
	console.log('update() executing');

	for(let i=0; i<cities.length; i++) {
		cities[i].population *= (Math.random()+.5);
	}

    // Join cities to rect elements and modify height, width and position
    d3.select('.bars')
      .selectAll('rect')
      .data(cities)
      .join('rect')
      .transition() /* OH BABY! THIS IS HUGE */
      .attr('height', 19)
      .attr('width', function(d) {
        let scaleFactor = 0.00004;
        return d.population * scaleFactor;
      })
      .attr('x', 70)
      .attr('y', function(d, i) {
        return i * 20 + 30;
      })
    
    // Join cities to text elements and modify content and position
    d3.select('.labels')
      .selectAll('text')
      .data(cities)
      .join('text')
      .attr('x', 66)
      .attr('y', function(d, i) {
        return i * 20 + 13 + 30;
      })
      .text(function(d) {
        return d.name;
      })
      .attr('style', 'border: 1px solid red');
}

update();

// vanilla JS way:
//document.getElementById('button0').addEventListener('click', update)
// d3 way:
d3.select('#button0').on('click', update);
