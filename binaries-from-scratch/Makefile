all: sample-elf32 sample-elf64

sample-elf32:
	./gen-elf32.py code.bin data.bin 400000 sample-elf32

sample-elf64:
	./gen-elf64.py code.bin data.bin 400000 sample-elf64

clean:
	rm -rf __pycache__ sample-elf32 sample-elf64
