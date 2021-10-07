How:

```
./translate.py ../helloworld.bf > test.s
nasm -f macho64 test.s -o test.o
ld -L /Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib -lSystem test.o -o test
./test
```

See ./helloworld.s for example output.

translate.py now does some simple optimizations and the original is preserved as translate_simple.py

99bob.s is 46k optimized, 91k unoptimized
99bob.s is 3300 lines optimized, 8100 lines unoptimized
