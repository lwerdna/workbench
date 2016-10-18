FLAGS_COMPILE = $(shell llvm-config --cxxflags) -fno-rtti
FLAGS_LINK = $(shell llvm-config --libs --ldflags)
#FLAGS_LINK = -L/usr/local/lib -Wl,-search_paths_first -Wl,-headerpad_max_install_names \
#	-lLLVMSupport \
#    -lLLVMMC -lLLVMMCParser -lLLVMMCDisassembler \
#    -lLLVMAsmParser -lLLVMAsmPrinter \
#    -lLLVMX86AsmParser -lLLVMX86CodeGen -lLLVMX86Disassembler -lLLVMX86Utils \
#    -lLLVMX86AsmPrinter -lLLVMX86Desc -lLLVMX86Info

FLAGS_LINK += -lz
#FLAGS_LINK += -ltinfo
FLAGS_LINK += -lncurses

all: methodA methodB

methodA: methodA.cpp
	g++ $(FLAGS_COMPILE) methodA.cpp $(FLAGS_LINK) -o methodA

methodB: methodB.cpp
	g++ $(FLAGS_COMPILE) methodB.cpp $(FLAGS_LINK) -o methodB

clean:
	rm methodA

