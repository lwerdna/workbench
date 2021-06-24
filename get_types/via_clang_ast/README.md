Can clang's AST dump feature be used to parse types from headers?

```
clang -cc1 ./go.c -ast-dump
clang -Xclang -ast-dump -fsyntax-only foo.h
```
