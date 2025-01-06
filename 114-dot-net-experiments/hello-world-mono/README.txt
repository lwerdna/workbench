`mono-csc` comes from the mono-devel package

Compiler informs Foo.cs of Bar at compile time:
  mono-csc Foo.cs Bar.cs -out:test.exe
  mono test.exe

Compiler links against Bar.dll:
  mono-csc -target:library Bar.cs -out:Foo.dll

Convention seems to be for CamelCase filenames for classes, and directory names
for namespaces.
