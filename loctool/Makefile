all: loctool-sh4 loctool-ppc

loctool-sh4: loctool.c
	gcc -DTARGET_SH4 loctool.c -o loctool-sh4 -lopcodes -lbfd -liberty -lz

loctool-ppc: loctool.c
	gcc -DTARGET_PPC loctool.c -o loctool-ppc -lopcodes -lbfd -liberty -lz

clean:
	rm -f ./loctool-sh4
	rm -f ./loctool-ppc

install:
	rm -f ~/bin/loctool-sh4
	ln -s `pwd`/loctool-sh4 ~/bin/loctool-sh4
	rm -f ~/bin/loctool-ppc
	ln -s `pwd`/loctool-ppc ~/bin/loctool-ppc

