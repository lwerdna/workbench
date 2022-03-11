Deobfuscate common x86/x64 push+ret obfuscation using a Binary Ninja script and a Binary Ninja architecture hook.

This project is inspired by the question: <https://github.com/Vector35/binaryninja-api/discussions/2539>.

Create a test binary with push/ret obfuscation:

* [./generate.py](./generate.py) - used in creating the obfuscated test binary
* [./linux32](./linux32) - source for the 32-bit linux ELF obfuscated test binary
* [./macos64](./macos64) - source for the 64-bit macos macho obfuscated test binary

Undo the push/ret obfuscation:

* [./solution_script/deobfuscate.py](./solution_script/deobfuscate.py) - method using straightforward binja script
* [./solution_arch_hook/deobfuscate.py](./solution_arch_hook/deobfuscate.py) - method using binja architecture hook

The basic idea of an architecture hook is that you can override the methods in an architecture plugin with your own. This example overrides `get_instruction_text()` and `get_instruction_info()` to produce custom disassembly text and inform Binja the call+ret should be treated as an unconditional branch.
