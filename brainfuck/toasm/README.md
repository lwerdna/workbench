How:

```
./translate.py ../helloworld.bf > test.s
nasm -f macho64 test.s -o test.o
ld -L /Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib -lSystem test.o -o test
./test
```

See ./helloworld.s for example output.
