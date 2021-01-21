roughness: roughness.dat dissonance.dat

# then:
# $ gnuplot
# gnuplot> plot 'roughness.dat'
roughness.dat: go.py
	./go.py roughness > roughness.dat

dissonance.dat: go.py
	./go.py dissonance > dissonance.dat
