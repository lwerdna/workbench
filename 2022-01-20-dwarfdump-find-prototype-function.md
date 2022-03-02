---
TITLE: use dwarfdump to find prototype of function
TAGS: []
---

Get the DIE for function `__copy_grp()`:

```
$ dwarfdump ./libc_x86_64.so.6 --name=__copy_grp
```

There will be multiple DIEs probably. Choose the one for 'DW\_TAG\_subpgrogram' (DWARF term for function):

```
0x002a24e2: DW_TAG_subprogram
              DW_AT_external	(true)
              DW_AT_name	("__copy_grp")
              DW_AT_decl_file	("./grp/grp-merge.c")
              DW_AT_decl_line	(39)
              DW_AT_decl_column	(0x01)
              DW_AT_linkage_name	("__GI___copy_grp")
              DW_AT_prototyped	(true)
              DW_AT_type	(0x002a1e63 "int")
              DW_AT_low_pc	(0x00000000000c9440)
              DW_AT_high_pc	(0x00000000000c9642)
              DW_AT_frame_base	(DW_OP_call_frame_cfa)
              DW_AT_GNU_all_call_sites	(true)
              DW_AT_sibling	(0x002a2710)
```

The DW\_AT\_type gives the return type "int". Note the address `0x002a24e2`. Now show this DIE with all its children, looking for formal parameters.

```
$ dwarfdump ./libc_x86_64.so.6 --debug-info=0x002a24e2 --show-children
```

Pruned output:

```
0x002a2508:   DW_TAG_formal_parameter
                DW_AT_name	("srcgrp")
                DW_AT_type	(0x002a2290 "const group")

0x002a251c:   DW_TAG_formal_parameter
                DW_AT_name	("buflen")
                DW_AT_type	(0x002a1e7d "const size_t")

0x002a2530:   DW_TAG_formal_parameter
                DW_AT_name	("destgrp")
                DW_AT_type	(0x002a24dc "group*")

0x002a2544:   DW_TAG_formal_parameter
                DW_AT_name	("destbuf")
                DW_AT_type	(0x002a1e56 "char*")

0x002a2558:   DW_TAG_formal_parameter
                DW_AT_name	("endptr")
                DW_AT_type	(0x002a2295 "char**")
```

Resulting in prototype `int __copy_grp(const group srcgrp, const size_t buflen, group* destgrp, char* destbuf, char** endptr);`


