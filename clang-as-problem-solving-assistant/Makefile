LIBCLANG = $(HOME)/libclang/12.0.0/bin

all: test test-O0.ll test-O3.ll test-O0-opt-pass.ll test-O3-opt-pass.ll

test: test.c
	clang -DINCLUDE_STDIO=1 -O3 test.c -o test

# -S to clang means "Only run preprocess and compilation steps"
test-O0.ll: test.c
	$(LIBCLANG)/clang -O0 -S -emit-llvm test.c -o test-O0.ll

test-O3.ll: test.c
	$(LIBCLANG)/clang -O3 -S -emit-llvm test.c -o test-O3.ll

# -S Write output as LLVM assembly
# -adce aggressive dead code elimination
#       https://llvm.org/docs/Passes.html#introduction
test-O0-opt-pass.ll: test-O0.ll
	$(LIBCLANG)/opt -S test-O0.ll -adce > test-O0-opt-pass.ll

test-O3-opt-pass.ll: test-O3.ll
	$(LIBCLANG)/opt -S test-O3.ll -adce > test-O3-opt-pass.ll

graph:
	$(LIBCLANG)/opt test-O3.ll -dot-cfg -cfg-func-name=_foo7

clean:
	rm -f *.ll
