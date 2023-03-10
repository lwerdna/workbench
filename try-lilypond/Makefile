all: test.pdf test.midi

test.pdf: test.ly
	lilypond --output=test test.ly

test.midi: test-midi.ly
	lilypond --output=test test-midi.ly

test-midi.ly: test.ly
	./add-midi.py test.ly > test-midi.ly

clean:
	rm -f *-midi.ly *.pdf *.midi
