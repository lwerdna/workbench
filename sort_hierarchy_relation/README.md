Sort items into a hierarchy given an arbitrary "is ancestor of" relation.

### Example: strings with relation "a starts b"

```
root
  a
    aardvark
    ant
      anteater
      antelope
```

### Example: A64 strings with relation "a starts b"

```
    ...
    sve_int_brkp
    sve_int_cmp_0
    sve_int_cmp_1
    sve_int_count
      sve_int_count_r
        sve_int_count_r_sat
      sve_int_count_v
        sve_int_count_v_sat
      sve_int_countvlv0
      sve_int_countvlv1
    sve_int_cterm
    sve_int_dup_fpimm
      sve_int_dup_fpimm_pred
    sve_int_dup_imm
      sve_int_dup_imm_pred
    ...
```

### Example: path names with relation "a starts b"

```
root
  ./lib/.DS_Store
  ./lib/clang/11.0.0/include/rtmintrin.h
  ./lib/clang/11.0.0/include/waitpkgintrin.h
  ./lib/clang/11.0.0/lib
    ./lib/clang/11.0.0/lib/wasi
      ./lib/clang/11.0.0/lib/wasi/libclang_rt.builtins-wasm32.a
  ./share
    ./share/clang
      ./share/clang/clang-format-bbedit.applescript
      ./share/clang/clang-format-diff.py
```

### Example: family tree with relation "a is ancestor of b"

Warning: multiple inheritance not supported

```
root
  catherine
    charles1
      claudia
      james1
    fay
  charles2
  george1
    sam
    sophia
      elizabeth
      paul
  james2
```

### Example: sets with relation "a is superset of b"

```
root
  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
    {3, 4, 5, 6, 7}
      {6, 7}
      {4, 5, 6}
        {4, 5}
          {5}
    {8, 9, 10, 7}
      {8}
      {9, 10}
    {1, 2}
```

### Example: intervals with relation "a envelopes b"

```
  ...
  [0x189A,0x19A6) section ".shstrtab" contents
  [0x20E8,0x2128) elf64_shdr ".symtab" SYMTAB
    [0x20E8,0x20EC) sh_name=0x1
    [0x20EC,0x20F0) sh_type=0x2 (SYMTAB)
    [0x20F0,0x20F8) sh_flags=0x0 (0)
    [0x20F8,0x2100) sh_addr=0x0
    [0x2100,0x2108) sh_offset=0x1068
    [0x2108,0x2110) sh_size=0x630
    [0x2110,0x2114) sh_link=0x1E
    [0x2114,0x2118) sh_info=0x2F
    [0x2118,0x2120) sh_addralign=0x8
    [0x2120,0x2128) sh_entsize=0x18
  [0x1068,0x1698) section ".symtab" contents
    [0x1068,0x1080) Elf64_Sym ""
      [0x1068,0x106C) st_name=0x0 ""
      [0x106C,0x106D) st_info bind:0(LOCAL) type:0(NOTYPE)
      [0x106D,0x106E) st_other=0x0
      [0x106E,0x1070) st_shndx=0x0
      [0x1070,0x1078) st_value=0x0
      [0x1078,0x1080) st_size=0x0
  ...
```

What about multiple inheritance? The algorithm stops after it finds the FIRST insertion point. Should it keep going? See test\_family.py.

I think the multiple inheritance problem should build a graph instead of a hierarchy/tree and is equivalent to having a list of "is downstream of" facts and building a directed graph from it.