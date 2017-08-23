cl libfake.c /c
link libfake.obj /DLL

cl /Od /Zi hello.c kernel32.lib
