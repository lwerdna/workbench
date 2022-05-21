// https://www.d3indepth.com/selections/
// https://www.d3indepth.com/datajoins/
//

var letters = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';
var i = 25;

function update() {
    console.log('update() called!');

    if(i < 0)
        return;
    let data = letters.slice(i).split('');
    i--;

    d3.select('#content')
        .selectAll('div')
        //.data(data)
        .data(data, function(d) { return d; }) /* by default the key of each datum is the index
                                                  in the data array - by comparing keys of the data
                                                  before and after, d3 can make transition

                                                  we now make the key the data itself, so d3 knows what
                                                  was there before */
        .join('div')
        .transition()
        .style('left', function(d, i) {
            return i * 32 + 'px';
        })
        .text(function(d) {
            return d;
        });
}

d3.select('#button0').on('click', update);

