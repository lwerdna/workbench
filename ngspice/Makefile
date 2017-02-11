# else make considers files created in the middle of chains of implicit rules
.SECONDARY:

all: rtl-inverter.png

# pattern rules
# ($@ and $< are `automatic variables` for the target and source file)

%: %.png

%.png: %.plt %.data
	gnuplot $<

%.plt %.data: %.raw
	./raw2plot.py $<

%.raw: %.cir
	SPICE_ASCIIRAWFILE=1 ngspice -b -r $@ $<

all: rtl-inverter.raw

clean:
	rm *.raw *.plt *.dat *.png
