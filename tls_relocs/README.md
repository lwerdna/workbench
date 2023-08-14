---
typora-copy-images-to: ./assets
---

Build some examples of relocations:

```
R_ARM_TLS_DTPMOD3
R_ARM_TLS_DTPOFF3
R_386_TLS_DTPMOD3
R_386_TLS_DTPOFF3
```

For resolving these issues:

https://github.com/Vector35/arch-x86/issues/19
https://github.com/Vector35/arch-armv7/issues/50

```
$ readelf.py --relocs ./libaaa.so
Relocation section '.rel.dyn' at offset 0x498 contains 12 entries:
 Offset     Info    Type            Sym.Value  Sym. Name
...
00011034  00001811 R_ARM_TLS_DTPMOD3 00000000 var0
00011038  00001812 R_ARM_TLS_DTPOFF3 00000000 var0
```

`R_ARM_TLS_DTPMOD3` makes the dynamic linker find the module ID (`l_tls_modid`) for the shared object at runtime and place it at 00011034. Relevant code from an X64 linker:

```C
  case R_X86_64_DTPMOD64:
    /* Get the information from the link map returned by the
       resolve function.  */
    if (sym_map != NULL)
      *reloc_addr = sym_map->l_tls_modid;
    break;
```

`R_ARM_TLS_DTPOFF3` makes the dynamic linker calculate var0's offset within its module's TLS block and write it to 00011038. Relevant code from an X64 linker:

```C
  case R_X86_64_DTPOFF64:
    /* During relocation all TLS symbols are defined and used.
       Therefore the offset is already correct.  */
    if (sym != NULL)
      {
        value = sym->st_value + reloc->r_addend;
        *reloc_addr = value;
      }
    break;
```

## GOT entry

```C
/* Type used for the representation of TLS information in the GOT.  */
typedef struct dl_tls_index
{
  uint64_t ti_module;
  uint64_t ti_offset;
} tls_index;
```

```
$ readelf.py -x .got ./libaaa.so
 Hex dump of section '.got':
  Note: This section has relocations against it, but these have NOT been applied to this dump.
  0x00011000 200f0100 00000000 00000000 1c050000  ...............
  0x00011010 1c050000 1c050000 00000000 04000000 ................
  0x00011020 00000000 00000000 00000000 00000000 ................
  0x00011030 00000000 00000000 00000000 00000000 ................
```

## TLS Notes

Two types of TLS:

* ordinary, explicit

  * functions `pthread_key_create()`, `pthread_setspecific()`, `pthread_getspecific()`

  * 2d hashmap: `tls_map[tid][key]`, where `tid` is thread ID, and `key` is the hash map key to a particular thread local variable.

* implicit

  * declared in source
    ```C
    __thread int main_tls_var;
    int main() {
    	return main_tls_var;
    }
    ```
    
  * disassembles as `mov %fs:0xfffffffffffffffc,%eax`
  
  * because `fs` segment register is assigned to thread context (or gs on some other systems) it is same as `*(int *)(thread_context_ptr + 4)`
  
  * the kernel assigns `fs` at context switch

This "thread context" is a general word that describes a data structure to manage a thread and its local storage (TLS) and umbrellas various implementations:

* thread control block (TCB) in Linux and glibc
* thread information block (TIB) or thread environment block (TEB) in Windows

Who and when the thread context is set up depends on:

* static vs. dynamic executables
* main thread (spawned by kernel) vs. threads that follow

The initial executable has module id 1. Subsequently loaded modules get 2, 3, ...

The module id is the first key into the 2d dynamic thread vector (DTV) array. The pointer entry from there has the offset member added to it to arrive at the variable:

```C
var = *(dtv[module].pointer + offset);
```

## Related

Best reference on the subject: https://chao-tic.github.io/blog/2018/12/25/tls
