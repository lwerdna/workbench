FLAGS_COMPILE = $(shell $$LLVM_PATH_BIN/llvm-config --cxxflags)
FLAGS_LINK = $(shell $$LLVM_PATH_BIN/llvm-config --libs --ldflags)

FLAGS_LINK += -lz
#FLAGS_LINK += -ltinfo
FLAGS_LINK += -lncurses

all: disasm_thumb disasm_amd64

disasm_thumb: disasm_thumb.cpp
	g++ $(FLAGS_COMPILE) disasm_thumb.cpp $(FLAGS_LINK) -o disasm_thumb

disasm_amd64: disasm_amd64.cpp
	g++ $(FLAGS_COMPILE) disasm_amd64.cpp $(FLAGS_LINK) -o disasm_amd64
