.PHONY: all

all: hello-mono.exe hello-mono-square.exe

square-mono.dll: Bar.cs
	mono-csc -target:library Bar.cs -out:square-mono.dll

hello-mono.exe: Foo.cs Bar.cs
	mono-csc Foo.cs Bar.cs -out:hello-mono.exe

hello-mono-square.exe: Foo.cs square-mono.dll
	mono-csc Foo.cs -reference:square-mono.dll -out:hello-mono-square.exe

clean:
	rm -f *.exe *.dll
