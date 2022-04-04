Attempt to generate an executable that imports and calls every C-like function from the Windows SDK.

Results in >25k imports in an executable weighing just over 1 megabyte for the SDK I used (10.0.17134.0).

Instructions:

Adjust `PATH` variable in generate.py to point to your SDK. Then:

```
$ python generate.py C > test.c
$ python generate.py make > build.bat
$ build.bat
```
