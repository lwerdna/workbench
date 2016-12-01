FLAGS_COMPILE = $(shell llvm-config --cxxflags)
FLAGS_LINK = $(shell llvm-config --libs --ldflags)

FLAGS_LINK += -lz
#FLAGS_LINK += -ltinfo
FLAGS_LINK += -lncurses

all: disasm_thumb disasm_amd64 disasm_len

disasm_thumb: disasm_thumb.cpp
	g++ $(FLAGS_COMPILE) disasm_thumb.cpp $(FLAGS_LINK) -o disasm_thumb

#disasm_len: disasm_len.cpp
#	g++ $(FLAGS_COMPILE) disasm_len.cpp $(FLAGS_LINK) -o disasm_len

disasm_amd64: disasm_amd64.cpp
	g++ $(FLAGS_COMPILE) disasm_amd64.cpp $(FLAGS_LINK) -o disasm_amd64

clean:
	rm *.o disasm_thumb disasm_amd64 2>/dev/null
