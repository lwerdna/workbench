.PHONY: all clean

all: stage1.so injected.dll

stage1.so: stage1.c
	gcc stage1.c -ldl -shared -o stage1.so

injected.dll: injected.cs
	mono-csc -target:library injected.cs -out:injected.dll

clean:
	rm -f *.so *.dll
