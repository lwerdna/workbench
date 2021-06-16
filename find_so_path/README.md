Get path of shared object in memory, code from answer at:

https://stackoverflow.com/questions/43409167/find-location-of-loaded-shared-library-from-in-that-shared-library

Run in current directory `./test`.

Then mkdir one/two/three and mv libso.so to ./one/two/three and retest:

MacOS:

```
DYLD_LIBRARY_PATH=./one/two/three ./test
```

linux:


```
LD_LIBRARY_PATH=./one/two/three ./test
```


