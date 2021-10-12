Compile against Binary Ninja with pure C.

The binaryninjacore.h file included in the API isn't fully C compatible because an internal tool that parses it to generate python bindings can't handle typedefs.

Use ./patch.py to generate bnc.h (adding typedefs) and include it instead of binaryninjacore.h.

You can test this yourself within Binary Ninja `bv.platform.parse_types_from_source_file('/path/to/binaryninjacore.h')` fails while `bv.platform.parse_types_from_source_file('/path/to/bnc.h')` succeeds.

How to use it? See ./go.c for example.

Build with `make`.

Run with something like `DYLD_LIBRARY_PATH=$BN_INSTALL_DIR/Contents/MacOS/ ./go`

### 2021-10-12 Update

In C++ after `enum BNLogLevel;` you can use `BNLogLevel` as a type anywhere, like binaryninjacore.h does, eg:

```
BINARYNINJACOREAPI void BNLogToStdout(BNLogLevel minimumLevel);
```

But in C you cannot do this, you must continue to preface it with “enum”, as in enum BNLogLevel so the above declaration of BNLogToStdout doesn’t compile in C.

Same thing applies to structs.

Also binaryninjacore.h has these includes:

```
#include <cstdint>
#include <cstddef>
#include <cstdlib>
```