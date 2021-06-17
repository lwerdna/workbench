Compile against Binary Ninja with pure C.

The binaryninjacore.h file included in the API isn't fully C compatible because an internal tool that parses it to generate python bindings can't handle typedefs.

Use ./patch.py to generate bnc.h (adding typedefs) and include it instead of binaryninjacore.h.

See ./go.c for example.

Build with `make`.

Run with something like `DYLD_LIBRARY_PATH=$BN_INSTALL_DIR/Contents/MacOS/ ./go`
