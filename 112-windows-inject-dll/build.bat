cl helloworld.c /Fo:helloworld.obj
link helloworld.obj /DYNAMICBASE /HIGHENTROPYVA /OUT:helloworld.exe

cl mydll.c /c /Fo:mydll.obj
link mydll.obj legacy_stdio_definitions.lib /DLL /OUT:mydll.dll

cl /c /Od /Zi attack.c /Fo:attack.obj
link attack.obj advapi32.lib /DEBUG:FULL /OUT:attack.exe

