.PHONY: all clean

all: create-objects.exe load-assembly.exe ref-loaded-assembly.exe ref-loaded-assembly-injected.exe injectee.exe Injected.dll

Injected.dll: Injected.cs
	mono-csc -target:library Injected.cs -out:Injected.dll

injectee.exe: injectee.cs
	mono-csc injectee.cs -out:injectee.exe

create-objects.exe: create-objects.cs
	mono-csc create-objects.cs -out:create-objects.exe

load-assembly.exe: load-assembly.cs
	mono-csc load-assembly.cs -reference:create-objects.exe -out:load-assembly.exe

ref-loaded-assembly.exe: ref-loaded-assembly.cs
	mono-csc ref-loaded-assembly.cs -reference:create-objects.exe -out:ref-loaded-assembly.exe

ref-loaded-assembly-injected.exe: ref-loaded-assembly-injected.cs
	mono-csc -target:library ref-loaded-assembly-injected.cs -out:ref-loaded-assembly-injected.dll

clean:
	rm -rf *.exe *.dll
