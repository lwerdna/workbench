// https://www.d3indepth.com/selections/
// https://www.d3indepth.com/datajoins/
//
var circle_radii = [70, 40, 50, 90, 60];
var square_coords = [[35,10], [55,20], [95,30], [90,40], [60,50]];

/* Evidently you can select circles and rects that don't exist, and they will spawn into existence!

   select() selects the first matching element
   selectAll() selects all matching elements

   both take selector strings: https://www.w3schools.com/cssref/css_selectors.asp

*/

/*
 * d3.select(container)
  .selectAll(element-type)
  .data(array)
  .join(element-type);
*/

function update() {
	d3.select('.chart')
	  .selectAll('circle') // element-type
	  .data(circle_radii) // array
	  .join('circle') // element-type - this is where elems are added/removed
	  .attr('cx', function(d, i) { /* d is the joined data, or "datum"
	                                  i is the index of the element within the selection */
    		return i * 100 + 40;
		  })
  	  .attr('cy', 50)
	  .attr('r', function(d) { /* THIS FUNCTION IS CALLED FOR EACH ELEMENT IN THE SELECTION! */
	    return 10 + Math.random() * 40;
	  })
	.style('fill', 'orange');

	d3.select('.chart')
	  .selectAll('rect')
	  .data(square_coords)
	  .join('rect')
	  .attr('x', function(d, i) { /* d is the joined data, or "datum"
	                                  i is the index of the element within the selection */
    		return d[0] + Math.random() * 100;
		  })
  	  .attr('y', function(d, i) {
            return d[1];
  	  	})
	  .attr('width', 50)
	  .attr('height', 100)
	  .style('fill', 'green');
}

document.getElementById('button0').addEventListener('click', update)
