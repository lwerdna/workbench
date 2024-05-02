all: sample.bin

sample.bin: sample.elf
	arm-linux-gnueabihf-objcopy --dump-section .text=./sample.bin sample.elf

sample.elf: sample.s
	arm-linux-gnueabihf-as ./sample.s -o sample.elf

clean:
	rm -rf sample.elf sample.bin
