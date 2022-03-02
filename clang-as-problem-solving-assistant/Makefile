LIBCLANG = $(HOME)/libclang/12.0.0/bin

all: tests tests-O0.ll tests-O3.ll tests-O0-opt-pass.ll tests-O3-opt-pass.ll

tests: tests.c
	clang -DINCLUDE_STDIO=1 -O3 tests.c -o tests

# -S to clang means "Only run preprocess and compilation steps"
tests-O0.ll: tests.c
	$(LIBCLANG)/clang -O0 -S -emit-llvm tests.c -o tests-O0.ll

tests-O3.ll: tests.c
	$(LIBCLANG)/clang -O3 -S -emit-llvm tests.c -o tests-O3.ll

# -S Write output as LLVM assembly
# -adce aggressive dead code elimination
#       https://llvm.org/docs/Passes.html#introduction
tests-O0-opt-pass.ll: tests-O0.ll
	$(LIBCLANG)/opt -S tests-O0.ll -adce > tests-O0-opt-pass.ll

tests-O3-opt-pass.ll: tests-O3.ll
	$(LIBCLANG)/opt -S tests-O3.ll -adce > tests-O3-opt-pass.ll

graph:
	$(LIBCLANG)/opt tests-O3.ll -dot-cfg -cfg-func-name=_foo7

clean:
	rm -f *.ll
