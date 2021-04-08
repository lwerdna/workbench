demo code for these old style relocations

https://github.com/Vector35/binaryninja-api/issues/1610

```
meme commented on Apr 24, 2020

In seemingly really, really old linker configurations, the MachO produced will use the local relocation table for relocations which is stored in the __LINKEDIT segment (which is referenced in the DYNSYM MachO load command).

Additionally it appears that when .dylibs contain the local relocation section they will also report themselves as non-PIE which is as far as I can tell INCORRECT because they can observably be relocated by the macOS linker using the local relocations section.

As well, Binary Ninja should type these relocations and display them in the linear view.
```

