FLAGS_COMPILE = -O0 -g $(shell llvm-config --cxxflags) -fno-rtti
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

#all: methodA methodB methodC
all: methodC

methodA: methodA.cpp
	g++ $(FLAGS_COMPILE) methodA.cpp help.cpp $(FLAGS_LINK) -o methodA

methodB: methodB.cpp
	g++ $(FLAGS_COMPILE) methodB.cpp help.cpp $(FLAGS_LINK) -o methodB

methodC: methodC.cpp help.cpp
	g++ $(FLAGS_COMPILE) methodC.cpp help.cpp $(FLAGS_LINK) -o methodC

clean:
	rm -rf methodA methodB methodC

