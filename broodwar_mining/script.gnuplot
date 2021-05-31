set term png
set output "./mining.png"
set xlabel "workers"
set ylabel "minerals per minute"
set key off
plot "mining.dat" using 1:3 with linespoints
