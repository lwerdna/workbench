### What's the TLDR on type libraries?

They're collections of type information (structs, enums, function types, etc.)

The information is contained in two key-value stores:

1. named types: key is the type name, value is the type
2. named objects: key is external symbol name, value is the type

I recommend you reference [1][1] and [2][2] while reading the FAQ.

### What's a named type vs. just a type?

Some variable definitions have type information, but don't produce a type name useful for future definitions, examples:

* `enum {A=1,B=2} foo;` foo has type with no type name (it does have a variable name)
* `struct {int A; int B;} bar;` bar has type with no type name

In C, enum and struct definitions can create a new type name as a byproduct of a definition by using a "tag name":

* `enum MyEnum {A=1,B=2} foo;` foo has type named MyEnum
* `struct MyStruct {int A; int B;} bar;` bar has type named MyStruct

In the second set of examples, the types are named, and that name could be used to declare other variables, like `enum MyEnum bar2;` and `struct MyStruct bar2`.

Functions' types are not named. The function name is considered the name of a function _object_, and the function's type is anonymous.

In summary:

```C
typedef int foo; // type:int, name:foo

// structs, without and with a "tag name"
struct {int A; int B;} foo; // type:struct{int A, intB;}, name:<anonymous>
struct MyStruct {int A; int B;} foo; // type:struct{int A, intB;}, name:MyStruct

// enumerations, without and with a "tag name"
enum {A=1,B=2} foo; // type:enum{A=1,B=2}, name:<anonymous>
enum MyEnum {A=1,B=2} foo; // type:enum{A=1,B=2}, name:MyEnum

// functions
int main(int ac, char **av); // type int ()(int, char **), name:<anonymous>
typedef int (MyFunc)(int ac, char **av); // type int ()(int, char **), name:MyFunc
```

### What's the difference between a named type and a named object?

A named type is a type with a name that can identify it. Like `Color` is the name of type `enum {RED=0, ORANGE=1, YELLOW=2, ...}`.

A named object is the name of an external/imported symbol for which the typelibrary has type information. Like `MessageBoxA` is the name of a function whose type is `int ()(HWND, LPCSTR, LPCSTR, UINT)`.

### How can I manually load a type library?

```python
>>> bv.add_type_library(TypeLibrary.load_from_file('test.bntl'))
```

### How can I manually load a type object?

```python
>>> bv.import_library_object('_MySuperComputation')
<type: int32_t (int32_t, int32_t, char*)>
```

While this succeeds, the type of `_MySuperComputation` will not change. It is only changed if the named type object information is available when the imports are being processed at binary load time.

TODO

### Why doesn't the type view show function types I've set?

Because they're anonymous, and the type view only shows named types.

A function with prototype `int sum(int a, int b);` means there's a function object named sum with type `int ()(int, int)`, but no name for that type in the named types key/value store:

```python
>>> bv.functions[0].function_type
<type: uint64_t (int32_t arg1, int32_t arg2)>
>>> bv.functions[0].function_type.registered_name == None
True
```

### Why doesn't the types view show the types imported from type libraries?

Because the type libraries added to a binary view only makes their type information _available_ for use. The types view will show a type from a type library only after it is used (on demand).

Try this experiment:

* note `bv.type_libraries`, `bv.types`
* add type library with `bv.add_type_library(TypeLibrary.load_from_file('test.bntl'))`
* note `bv.type_libraries` is extended, but `bv.types` is unchanged!
* note `bv.get_type_by_name('Rectangle')` returns nothing
* set the type of some data to `struct Rectangle`
* `bv.types` is extended, and the types view shows `struct Rectangle` in the auto types

### What's a named type reference?

It's a way to refer to a type by name, without having its declaration immediately available.

For example, examine this struct from [1][1]:

```C
struct Rectangle2 {
  int width;
  int height;
  struct Point center;
}
```

We don't know at this moment what a `struct Point` is. Maybe we've already added it. Maybe we'll add it later. Maybe it's in another type library. But we want to add a Rectangle now. So we leave the center field as a reference to the named type `struct Point`.

Load the resulting test.bntl in your binary and try to set some data to type `struct Rectangle2` and you'll be met with this message:

```
TypeLibrary: failed to import type 'Point'; referenced but not present in library 'libtest.so.1`
```

Makes sense! Now go to types view and define `struct Point { int x; int y; }` and try again, success!

```
100001000  struct rectangle_unresolved data_100001000 = 
100001000  {
100001000      int32_t width = 0x5f0100
100001004      int32_t height = 0x5f030005
100001008      struct Point center = 
100001008      {
100001008          int32_t x = 0x655f686d
10000100c          int32_t y = 0x75636578
100001010      }
100001008  }
```

You should repeat the experiment using `struct Rectangle` and see that you're allowed to create variables with type containing _pointers_ to unresolved type references.

### When do named objects get used?

When a binary is loaded and its external symbols is processed, the symbol names are searched against the named objects from type libraries. If there is a match, it obeys the type from the type library. Upon success, you'll see a message like:

`type library test.bntl found hit for _DoSuperComputation`

At this moment, there is no built in functionality to apply named objects to an existing Binary Ninja database.

### How do I find what type of type a type object is? How many are there?

I've seen "types of types", "sorts of types", "kinds of types", "classes of types" used to differentiate the varieties of possible types, and there are probably more. Binja uses "class", example:

```python
>>> type_obj.type_class
<TypeClass.FunctionTypeClass: 8>
```

In `api/python/enums.py` we can see Binja currently thinks of types falling into 13 classes: Void, Bool, Integer, Float, Structure, Enumeration, Pointer, Array, Function, VarArgs, Value, NamedTypeReference, WideCharType.

Compare to LLDB, which also uses the term "class", and currently has 19 of them: Array, BlockPointer, Builtin, Class, ComplexFloat, ComplexInteger, Enumeration, Function, MemberPointer, ObjCObject, ObjCInterface, ObjCObjectPointer, Pointer, Reference, Struct, Typedef, Union, Vector, Other.

Compare to GDB, which uses the term "type code" and has 25 of them.

### Where are function parameter names stored?

While technically not part of the type, having names of function parameters is very useful and can thus be optionally stored in a type.

Function types (types with `.type_class == FunctionTypeClass`) have a `.parameters` attribute, a list of `FunctionParameter` objects. When those objects have `.name==''` you get the bare bones function types like  `int ()(int, char **)`. When those objects have their `.name` populated you get the more meaningful `int ()(int argc, char **argv)`.

### How are typed represented?

By a hierarchy of objects from api/python/types.py referencing one another. The "glue" object is binaryninja.types.Type and depending on the complexity of the type it represents (stored in its `.type_class` attribute), could have an attribute with more information. For instance, if the binaryninja.types.Type has `.type_class == FunctionTypeClass` then its `.parameters` attribute is a list of binaryninja.types.FunctionParameter. See [2][2].

As an example, here is the hierarchical representation of type `struct Rectangle` from [1][1]:

```
typelib.named_types["Rectangle"] =
----------------------------------
Type class=Structure
  Structure
    StructureMember "width"
      Type class=Integer width=4
    StructureMember "height"
      Type class=Integer width=4
    StructureMember "center"
      Type class=Pointer
        Type class=NamedTypeReference
          NamedTypeReference <named type: struct Point>
```

Here is the representation of type `int ()(int, int)` named `MyFunctionType` in [1][1]:

```
Type class=Function
  Type class=Integer width=4 // .return_value
  FunctionParameter ""
    Type class=Integer width=4 // .parameters[0]
  FunctionParameter ""
    Type class=Integer width=4 // .parameters[1]
  FunctionParameter ""
    Type class=Integer width=4 // .parameters[2]
```

### How does Binja decide when to use a typelibrary file?

Binja reads the ELF's .dynstr section for the requested name. It kind of behaves like the dynamic linker in this regard.

This requested name _should_ be a soname, like "libfoo.so.1" but could be a linkname like "libfoo.so". See [3][3].

Binja's logic for determining a match is straightforward:

```python
typelibname.removesuffix('.bntl') == requestedname or requestedname in alternativenames
```

Therefore, without any alternative names, libc.so.bntl will not be loaded by Binja if an ELF requests libc.so.6.

We recommend and follow the following convention. Type libraries should be named for the filename from which they were generated with the phrase ".bntl" added. When the source library contains additional minor and release number, like libfoo.so.1.2.3 Binja would not load the resulting type library libfoo.so.1.2.3.bntl for an ELF requesting soname libfoo.so.1. Therefore the alternative names list should include the most specific version numbers, incrementally stripped down to the soname, and finally a linkname for good measure.

Example:

libfoo.so.1.2.3 is used to generated libfoo.so.1.2.3.bntl

Alternative names list should have:

```
libfoo.so.1.2.3 <-- includes version, minor, release (most specific)
libfoo.so.1.2   <-- includes version, minor (less specific)
libfoo.so.1     <-- includes version (soname)
libfoo.so       <-- linkname
```

### References and Notes

1. [https://github.com/Vector35/binaryninja-api/blob/dev/python/examples/typelib_create.py](https://github.com/Vector35/binaryninja-api/blob/dev/python/examples/typelib_create.py)
[1]: https://github.com/Vector35/binaryninja-api/blob/dev/python/examples/typelib_create.py "typelib_create.py"

2. [https://github.com/Vector35/binaryninja-api/blob/dev/python/examples/typelib_dump.py](https://github.com/Vector35/binaryninja-api/blob/dev/python/examples/typelib_dump.py)
[2]: https://github.com/Vector35/binaryninja-api/blob/dev/python/examples/typelib_dump.py "typelib_dump.py"

3. The ldconfig tool is responsible for creating symlinks from soname to realnames, like /usr/lib/libfoo.so.1 -> /usr/lib/libfoo.so.1.0. At library installation time, a symlink from linkname to soname may have been created, like /usr/lib/liboo.so -> /usr/lib/libfoo.so.1. See [https://tldp.org/HOWTO/Program-Library-HOWTO/shared-libraries.html](https://tldp.org/HOWTO/Program-Library-HOWTO/shared-libraries.html).
