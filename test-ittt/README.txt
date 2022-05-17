Does an ITTT impose the condition on the instructions even if the instructions do not have the condition flag set?

Hypothesis: Yes, the condition flag on the IT-block instructions are just a convenience for viewers of disassembly.

https://github.com/Vector35/arch-armv7/issues/64

Answer: THERE ARE NO CONDITION FLAGS IN THUMB ENCODINGS! That's why the IT block was made. When you see conditional suffixes on instructions, like the "lt" in "blt" from tools like objdump, it's because that tool is IT block aware, not because the blt actually has a condition code.
