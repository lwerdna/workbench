.PHONY: all clean

all: create-objects.exe load-assembly.exe

create-objects.exe: create-objects.cs
	mono-csc create-objects.cs -out:create-objects.exe

load-assembly.exe: load-assembly.cs
	mono-csc load-assembly.cs -reference:create-objects.exe -out:load-assembly.exe

clean:
	rm -rf *.exe
