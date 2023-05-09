all: lena.macho64

lena.jpg: ../testbins/lena.jpg
	# resize to 128 pixel width
	convert -resize 128 ../testbins/lena.jpg ./lena.jpg
	# convert to black and white
	convert lena.jpg -monochrome lena.jpg
	#convert lena.jpg -remap pattern:gray50 lena.jpg

lena.asm: lena.jpg
	./img2binja.py ./lena.jpg > ./lena.asm

lena.macho64: lena.asm
	nasm -f macho64 lena.asm -o lena.macho64
	#gcc lena.macho64 -o lena.macho64

lena.elf: lena.asm
	nasm -f elf lena.asm -o lena.elf

clean:
	rm -f lena.elf lena.asm lena.jpg lena.macho64
