// https://www.d3indepth.com/selections/
// https://www.d3indepth.com/datajoins/
//
let coords = [
    {name:'c1', x:70, y:10},
    {name:'c2', x:110, y:40},
    {name:'c3', x:290, y:30},
    {name:'c4', x:390, y:80},
    {name:'c5', x:520, y:50}
];

function update() {
	d3.select('.chart')
	  .selectAll('circle') // element-type
	  .data(coords, function(d) {
	    return d.name;
	  })
	  .join('circle') // element-type - this is where elems are added/removed
	  .transition()
	  .attr('cx', function(d, i) { /* d is datum, i is index */
    		return d.x;
		  })
  	  .attr('cy', function(d, i) {
  	        return d.y;
  	      })
	  .attr('r', function(d) {
	    return 50;
	  })
	  .style('fill', 'orange');
}

update();

function hehe() {
    coords[0].x += 40;
    coords[1].y += 40;
    coords[2].x += 80;
    coords[3].y += 80;
    coords[4].x += 140;
    update();
}

document.getElementById('button0').addEventListener('click', hehe)
