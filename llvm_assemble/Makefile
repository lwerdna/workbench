FLAGS_COMPILE = $(shell llvm-config --cxxflags) -fno-rtti
FLAGS_LINK = $(shell llvm-config --libs --ldflags)
FLAGS_LINK = -L/usr/local/lib -Wl,-search_paths_first -Wl,-headerpad_max_install_names \
	-lLLVMSupport \
    -lLLVMMC -lLLVMMCParser -lLLVMMCDisassembler \
    -lLLVMAsmParser -lLLVMAsmPrinter \
    -lLLVMX86AsmParser -lLLVMX86CodeGen -lLLVMX86Disassembler -lLLVMX86Utils \
    -lLLVMX86AsmPrinter -lLLVMX86Desc -lLLVMX86Info

FLAGS_LINK += -lz
#FLAGS_LINK += -ltinfo
FLAGS_LINK += -lncurses

all: asm_x86

asm_x86: asm_x86.cpp
	g++ $(FLAGS_COMPILE) asm_x86.cpp $(FLAGS_LINK) -o asm_x86

clean:
	rm asm_x86

