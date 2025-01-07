`mono-csc` comes from the mono-devel package, `sudo apt install mono-devel`

Compiler informs Foo.cs of Bar at compile time:
  mono-csc Foo.cs Bar.cs -out:test.exe

Compiler links against Bar.dll:
  mono-csc -target:library Bar.cs -out:Foo.dll
  mono-csc Foo.cs -reference:Bar.dll -out:test.exe

Run with:
  mono test.exe

Get extra debugging info with:
  MONO_LOG_LEVEL="debug" MONO_LOG_MASK="asm,dll" mono test.exe

Convention seems to be for CamelCase filenames for classes, and directory names
for namespaces.

References:
  https://stackoverflow.com/questions/4070542/how-to-include-multiple-source-files-in-c-sharp
