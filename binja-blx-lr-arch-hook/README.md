This project is inspired from the question: <https://github.com/Vector35/binaryninja-api/discussions/2977>.

Distilled: Is `blx lr` a call, or is it a return?

Prior to this question, Binja considered it as a call and gave no special treatment to the destination address being the link register. Here's how to override that behavior with a plugin.

Open [./test.bin](./test.bin) with architecture armv7, no linear sweep, start procedure at 0. See `blx lr` at 0x458.

The basic idea of an architecture hook is that you can override the methods in an architecture plugin with your own. This example overrides `get_instruction_info()` and `get_instruction_low_level_il()`.

