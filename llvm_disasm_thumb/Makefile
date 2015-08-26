FLAGS_COMPILE = $(shell $$LLVM_PATH_BIN/llvm-config --cxxflags)
FLAGS_LINK = $(shell $$LLVM_PATH_BIN/llvm-config --libs --ldflags)

FLAGS_LINK += -lz
#FLAGS_LINK += -ltinfo
FLAGS_LINK += -lncurses

test: test.cpp
	g++ $(FLAGS_COMPILE) test.cpp $(FLAGS_LINK) -o test
