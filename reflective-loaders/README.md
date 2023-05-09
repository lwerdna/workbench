By "reflective loader" I mean code that can load a shared object stored as a byte array.

That stands in contrast to the usual loader functions (dlopen(), etc.) that required the shared object stored as a file.

They all work by hooking some functions in the usual loader logic. The simplest is probably the FreeBSD one which makes open() check for sentinel value, and returns a handle to some shared memory that holds the object's bytes.

Originally written around 2018-07-15.