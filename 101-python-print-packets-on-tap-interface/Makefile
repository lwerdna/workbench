all: tap2stdout stdin2hex

tap2stdout: tap2stdout.c
	gcc tap2stdout.c -o tap2stdout

stdin2hex: stdin2hex.c
	gcc stdin2hex.c -o stdin2hex

clean:
	rm -rf tap2stdout stdin2hex __pycache__
