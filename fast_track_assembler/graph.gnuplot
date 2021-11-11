set term png
set output "/tmp/quick.png"
set logscale y
set style fill solid border -1
set boxwidth .9 relative
set key noautotitle
set key title "offspring needed by instruction quantity"
set yrange [.1:10000000]
set grid xtics lt 0 lw 1 lc rgb "#c0c0c0"
set grid ytics lt 0 lw 1 lc rgb "#c0c0c0"
$data << EOD
25 409251
50 588036
75 1827
100 755
125 65
150 41
175 9
200 8
225 5
250 1
275 1
300 0
325 0
350 0
375 0
400 0
425 0
450 1
EOD
plot 'data.txt' with boxes lc rgb"gray", \
	'' using 1:2:2 with labels rotate by 90 center offset 0,2 notitle
