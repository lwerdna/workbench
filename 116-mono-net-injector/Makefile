.PHONY: all clean install

all: stage1.so Injected.dll

stage1.so: stage1.c
	gcc stage1.c -ldl -shared -fPIC -o stage1.so

Injected.dll: Injected.cs
	mono-csc -target:library Injected.cs -out:Injected.dll

install-link:
	ln -s $(PWD)/inject.py $(HOME)/.local/bin/inject.py
	ln -s $(PWD)/stage1.so $(HOME)/.local/bin/stage1.so

install:
	cp inject.py $(HOME)/.local/bin
	cp stage1.so $(HOME)/.local/bin

uninstall:
	rm -f $(HOME)/.local/bin/inject.py
	rm -f $(HOME)/.local/bin/stage1.so

clean:
	rm -f *.so *.dll
