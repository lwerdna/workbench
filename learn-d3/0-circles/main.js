// https://www.d3indepth.com/selections/

var myData = [70, 40, 50, 90, 60];

/* Evidently you can select circles that don't exist, and they will spawn into existence!

   select() selects the first matching element
   selectAll() selects all matching elements

   both take selector strings: https://www.w3schools.com/cssref/css_selectors.asp

*/
d3.select('.chart')
  .selectAll('circle')
  .data(myData)
  .join('circle')
  .attr('cx', function(d, i) {
    return i * 100 + 40;
  })
  .attr('cy', 50)
  .attr('r', function(d) {
    return 0.5 * d;
  })
  .style('fill', 'orange');
