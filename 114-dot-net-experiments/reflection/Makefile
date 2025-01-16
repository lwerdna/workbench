.PHONY: all clean

all: create-objects.exe load-assembly.exe ref-loaded-assembly.exe injectee.exe injector.exe Injected.dll

Injected.dll: Injected.cs
	mono-csc -target:library Injected.cs -out:Injected.dll

injectee.exe: injectee.cs
	mono-csc injectee.cs -out:injectee.exe

injector.exe: injector.cs MInject.dll
	mono-csc injector.cs -reference:MInject.dll -out:injector.exe

create-objects.exe: create-objects.cs
	mono-csc create-objects.cs -out:create-objects.exe

load-assembly.exe: load-assembly.cs
	mono-csc load-assembly.cs -reference:create-objects.exe -out:load-assembly.exe

ref-loaded-assembly.exe: ref-loaded-assembly.cs
	mono-csc ref-loaded-assembly.cs -reference:create-objects.exe -out:ref-loaded-assembly.exe

clean:
	rm -rf *.exe *.dll
