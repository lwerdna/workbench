Welcome to my collection of BinaryNinja questions. I also recommend you look through Jordan's snippets at: https://gist.github.com/psifertex/6fbc7532f536775194edd26290892ef7

Now for the questions!

## How do I open a file?

**Quick answer:** `binaryninja.open_view(path)`

Actual opening is done in class BinaryViewType's methods. When the module binaryninja has a convenience wrapper, it is recommended you use it. 

The following graph shows the convenience functions in red:

![](./assets/binja-open-functions.svg)

You can view the source of module binaryninja in `api/python/__init__.py` and see some examples. You can view class BinaryViewType in `api/python/binaryview.py`.

The `open_view()` allows you to use python's context manager `with` keyword to get a runtime context:

```python
from binaryninja import *
with open_view("/bin/ls") as bv:
    print(len(list(bv.functions)))
```

But it's not required:

```python
bv = open_view('/bin/ls')
```

But be sure to `bv.file.close()` to cleanup properly.

## How can I set a function boundary?

**Quick answer:** You can set function starts, but you can't set the end of a function because Binja doesn't conceptualize functions that way.

Mostly you can't, you must rely on analysis. Analysis performs actions like making functions at call destinations and potentially ending functions at returns.

Through the UI, you can set new function starts (right click, "Make Function at This Address").

If the current function start is manually made (and not automatically made by being the destination of a call), you might move it by undefining the function and making the function at the new address.

See [How does Binja think of function boundaries?](#how-does-binja-think-of-function-boundaries).

## How do I get the end of a function?

**Quick answer**: you can't, because Binja doesn't think of functions like that

Binja does not have a strict view of a functions start and end boundaries. See [How does Binja think of function boundaries?](#how-does-binja-think-of-function-boundaries)

If you want the address after the final byte which comprises the function, use `max(bb.end for bb in func.basic_blocks)`.

see binaryninja-api discussion: <https://github.com/Vector35/binaryninja-api/discussions/2189>

## How can I test for blocks that return?

**Quick answer:** by testing if its last instruction lifts to an LLIL_RET:

```python
def does_block_return(bb):
    bb._buildStartCache()
    last_addr = bb._instStarts[-1]
    llils = bb.function.get_llils_at(last_addr)
    if not llils or len(llils) != 1:
        return False
    return llils[0].instr.operation == LowLevelILOperation.LLIL_RET
```

## How does Binja think of functions?

**Quick answer**: as a directed [graph](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)) of [basic blocks](https://en.wikipedia.org/wiki/Basic_block) where one block is specified as the entry.

Note:

* there is no requirement the blocks be contiguous
* there is no requirement a block be solely owned (it may exist in multiple functions), see: [How can one address appear in two functions?](#how-can-one-address-appear-in-two-functions)

## How does Binja think of function boundaries?

**Quick answer**: as the union of all [start, end) of every basic block from the function.

See: [How does Binja think of functions?](#how-does-binja-think-of-functions)

In the python API, you might notice `binaryninja.function.Function` has `.start` but not `.end` or `.len` or `.length`. It does have `.total_bytes` which cannot be set and is the sum of the sizes of all its basic blocks.

Unlike some RE tools, Binja does not bound a function by a start and end address. Here are some reasons:

1. functions can have multiple return points
2. function return could be located at not its greatest address
3. A straightforward [start, end] might capture non-function code

The first two could be handled by a policy of "function end should be the greatest address containing bytes of the function". So when there are multiple return points, function end is the address after the final (greatest address) return. When a return is not at the function's greatest address, return the address of the instruction that is at the greatest address.

The third objection is carries some weight IMO. Here I purposely place function `int my_sub(int a, b)` within the lowest and highest addresses of `int my_add(int a, int b)`:

```asm
my_add:
	mov		rax, rdx
	jmp		my_add_continued

my_sub:
	mov		rax, rdx
	sub		rax, rsi
	ret

my_add_continued:
	add		rax, rsi
	ret
```

Binja disassembles:

```
00000000  int64_t my_add(int64_t, int64_t arg2, int64_t arg3)
00000000  4889d0             mov     rax, rdx
00000003  eb07               jmp     my_add_continued

00000005  int64_t my_sub(int64_t, int64_t arg2, int64_t arg3)
00000005  4889d0             mov     rax, rdx
00000008  4829f0             sub     rax, rsi
0000000b  c3                 retn     {__return_addr}

{ Continuation of function my_add }
0000000c  4801f0             add     rax, rsi
0000000f  c3                 retn     {__return_addr}
```

If we say `my_add()` starts at 0 and ends at 0x10 that would mistakenly include bytes of `my_sub()`.

## How can one address appear in two functions?

**Quick answer**: because the two functions' graphs of blocks can share

See: [How does Binja think of functions?](#how-does-binja-think-of-functions)

Here's a simple example:

```asm
my_add:
	mov		rax, rdx
	add		rax, rsi
	jmp		done

my_sub:
	mov		rax, rdx
	sub		rax, rsi
	jmp		done

done:
	ret
```

Each function has two blocks/vertices in its graph. The second block is shared:

```mermaid
graph TD
  b0["my_add:<br>00000000: mov rax, rdx<br>00000003: add rax, rsi<br>000000006: jmp done"]
  b1["my_sub:<br>00000008: mov rax, rdx<br>0000000b: sub rax, rsi<br>0000000e: jmp done"]
  b2["00000010: retn"]
  b0 --> b2
  b1 --> b2
```

In the python console:
```
>>> [f.name for f in bv.get_functions_containing(0x10)]
['my_sub', 'my_add']
```

## How can I programmatically disassemble some bytes?

**Quick answer:** See the example code below for the `ret` instruction in 64-bit arm:

```python
import binaryninja
data = b'\xc0\x03\x5f\xd6'
arch = binaryninja.Architecture['aarch64']
tokens, length = arch.get_instruction_text(data, 0) or ('', 0)
if length > 0:
    print(data.hex() + ': ' + ' '.join([t.text for t in tokens]))
```

It prints:

```
c0035fd6: ret
```

## How can I programmatically lift some bytes?

```python
import binaryninja
data = b'\x48\xc7\xc0\xad\xde\x00\x00' # mov rax, 0xDEAD
platform = binaryninja.Platform['linux-x86_64']
bview = binaryninja.binaryview.BinaryView.new(data)
bview.add_function(0, plat=platform)
print(bview.functions[0].low_level_il[0])
```

Prints:

```
rax = 0xdead
```

## How can I programmatically access the feature map?

**Quick answer:** See the example code below.

There's no API to access the result of the feature map (the image data) but you can access everything the feature map widget uses to draw the image in order to draw it yourself.

See [./code/feature-map.py](./code/feature-map.py) for an example using PIL to produce a .png:

![](./assets/feature-map.png)

## How can I programmatically access pseudo-C?

**Quick answer:** By using a LinearViewObject. See the example code below.

There's currently no convenient API to just say "give me some pseudo-C of a function" or "give me some pseudo-C at an address". But there's a kind of hackish way to go about it using a LinearViewObject.

See: [./code/access-pseudoc.py](./code/access-pseudoc.py)

And by matching addresses, you can get a coarse mapping between, say, HLIL and corresponding pseudo-C:

```
// HLIL: void* r8 = arg1
1000039d7      void* r8 = arg1;
// HLIL: void* rdx = *(arg2 + 0x60)
1000039da      void* rdx = *(int64_t*)((char*)arg2 + 0x60);
// HLIL: void* rdi = *(arg1 + 0x60)
1000039de      void* rdi = *(int64_t*)((char*)arg1 + 0x60);
// HLIL: int64_t rcx = *(rdi + 0x30)
1000039e2      int64_t rcx = *(int64_t*)((char*)rdi + 0x30);
// HLIL: int64_t rax = 1
1000039e6      int64_t rax = 1;
// HLIL: int64_t temp0 = *(rdx + 0x30)
1000039eb      int64_t temp0 = *(int64_t*)((char*)rdx + 0x30);
1000039eb      bool cond:0 = temp0 >= rcx;
1000039eb      {
// ...
```

## Does the index of a block indicate the order of execution of the blocks?

**Quick answer:** No.

Counterexamples are easy to find with the following script:

```python
bv = binaryninja.open_view(sys.argv[1])
for func in bv.functions:
    print(f'analyzing function {func}')
    bbs = list(func.basic_blocks)
    for (i, bb) in enumerate(bbs):
        left = set(bb.strict_dominators)
        right = set(bbs[i+1:])
        both = left.intersection(right)
        if both:
            print(f'blocks {both} execute before, but appear after {bb}')
            sys.exit(-1)
```

That is, there are blocks that appear later in an enumeration that dominate blocks that appear earlier. For example, from busybox-x64 there's function `sub_400350()`:

![](./assets/topo-order-counterexample.png)

You can do it manually, however. See: [get-blocks-topological-order.py](./code/get-blocks-topological-order.py)

## What Are Intrinsics?

There are a few ways this term is used, but they all involve the concept of the compiler possessing and using knowledge of the implementation of some function instead of referring to it.

**CASE 1:** A C programmer remains at a high level and the low level details happen behind the scenes.

For example, compiling a call to `memset()` or `memcpy()` can:

* **extrinsic:** generate a call to a symbol that gets linked against an implementation in some library
* **intrinsic:** inline a highly optimized implementation

Note the programmer intended merely to clear or copy memory.

**CASE 2:** A C programmer wants a special low level implementation.

Functions are sometimes exposed intentionally to generate specialized instructions. For example, the [ARM instrinsics](https://developer.arm.com/architectures/instruction-sets/intrinsics) have functions like `vaddq_s16()` to generate the advanced SIMD form of the instruction `ADD`.

Note the programmer knew they were working with advanced SIMD and the int16x8_t datatype.

**CASE 3:** An architecture writer cannot fully model an instruction, but still wants to convey to Binary Ninja what operands are read and written.

For example, consider the A64 instruction `autda` which authenticates a data address using a key. There's no way to model that in Binja's IL. But it does read and write some registers, so the writer:

* creates some identifier for the instrinsic, like `ARM_INTRIN_AUTDA`
* informs Binja of its presence by returning it in `GetAllIntrinsics()`
* informs Binja of how it should be presented by having `GetIntrinsicName()` return something like `"__autda"` which will be `__autda(arg)` in decompiler view
* informs Binja that it writes two 8-byte registers (`<Xd>`, `<Xn|SP>`) via `GetIntrinsicOutputs()`
* informs Binja that it reads an 8-byte register (`<Xd>`) via `GetIntrinsicInputs()`

**CASE 4:** An Architecture writer could fully model an instruction, but thinks the analyst might benefit more from seeing a human readable name.

For example the A64 instruction `clz` counts the leading zeros of an input register, and writes the result to an output register. There's no single IL instruction to do this, but it could be synthesized with a loop or some fancy bit masking. Instead, the A64 architecture currently lifts this as an intrinsic, naming one input and one output 8-byte register, and decompiling to `_CountLeadingZeros(arg)`.

**CASE 5:** An architecture writer knows certain instructions were generated by case #2 intrinsics, and wants the decompiler to display what the programmer likely wrote.

## What's the definition of .back_edge and how does it differ from the academic definition?

The usual definition of back edges given in academic texts for finding "natural loops" has two requirements:

1. edge goes from descendent to ancestor (as defined by a breadth first traveral of the CFG)
2. ancestor dominates descendent (ancestor necessarily executes prior to descendent)

The BinaryNinja only captures property 1. If you'd like to add property 2, you can say `edge.back_edge and edge.target in edge.source.dominators`.

## How do I access high level IL in AST form?

The UI presents HLIL only in control flow graph form. You can use `hlil_function.root` to get at the AST. See [hlil-ast.py](./code/hlil-ast.py) for how to generate trees like this:

![](./assets/hlil-cfg.svg)

## How do the version numbers work?

There are three numbers separated by dots: major, minor, and build.

```
>>> import binaryninja
>>> binaryninja.core_version()
'3.1.3469'
```

On newer version of the API you have also the update channel from which BinaryNinja came, like "test", "dev", etc.

```
>>> binaryninja.core_version_info()
CoreVersionInfo(major=3, minor=1, build=3729, channel='dev')
```

The build field holds the **universal build number**, which increments every time a new build is released, and is independent of the other version numbers, the update channel (dev, stable, etc.) and the license type (personal, commercial). So version 3.1.3469 is the 3469'th build our build machines have ever built and made available for customers. And build 3469 is at the same commit for demo, personal, and commercial.

If BinaryNinja is built from source on a developer machine, it has no build number and the channel is set to "Local":

```
>>> binaryninja.core_version_info()
CoreVersionInfo(major=3, minor=1, build=0, channel='Local')
```

There's also a confusing hash that is called a **build id** (not a build number), for example:

```
Version 3.5.4526 Personal, Build ID ec37d737
```

This is the last git commit hash to BinaryNinja core repo (not the API repo!) before this release, and is typically tagged, for example:

```
commit ec37d73742bbd3b8e93bdfda4fc4983bd4de6f86 (tag: v3.5.4526-stable, origin/test_fix_analysis_hang)
```

## What's the difference between "auto" and "user"? Why do some functions have "\_user\_" in their name?

"Auto" refers to actions performed by BinaryNinja's auto analysis. Most of these can be recomputed quickly and so their result is not stored in saved databases.

"User" refers to actions the performed by the user, like `create_user_var()`, `set_user_type()`. They are stored in the database so they can be displayed.
