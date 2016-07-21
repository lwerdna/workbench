FLAGS_COMPILE = $(shell llvm-config --cxxflags) -fno-rtti
FLAGS_LINK = $(shell llvm-config --libs --ldflags)

FLAGS_LINK += -lz
#FLAGS_LINK += -ltinfo
FLAGS_LINK += -lncurses

all: asm_x86

asm_x86: asm_x86.cpp
	g++ $(FLAGS_COMPILE) asm_x86.cpp $(FLAGS_LINK) -o asm_x86

clean:
	rm asm_x86

