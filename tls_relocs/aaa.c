__thread int var0 = 0x29a;
/*
 This results in two entries at 0x11034 at GOT+34:

Relocations:

 Offset     Info    Type            Sym.Value  Sym. Name
00011034  00001811 R_ARM_TLS_DTPMOD3 00000000 var0
00011038  00001812 R_ARM_TLS_DTPOFF3 00000000 var0

Both target 0x11034 (GOT+34) where they'll form a `struct tls_index`
whose address will be passed to __tls_get_addr()

.dynsym symbols:
   Num:    Value  Size Type    Bind   Vis      Ndx Name
    24: 00000000     4 TLS     GLOBAL DEFAULT   14 var0
.symtab symbols:
   Num:    Value  Size Type    Bind   Vis      Ndx Name
    97: 00000000     4 TLS     GLOBAL DEFAULT   14 var0

The .GOT after relocation will have:
11034: <module number> (0 in IDA)
11038: <offset> (IDA populates this with a pointer to var0)
*/

/*
Will get the address of the:
struct tls_index
{
	uint32_t module;
	uint32_t index;
}
at 0x11034 and call __tls_get_addr() then return the dereferenced result:
*/
int value(void) { return var0; }
/* Same as above, but won't dereference. */
int *address(void) { return &var0;	}

static __thread int var1 = 0x29b;
/*
Relocations: (notice no symbol name or value)

 Offset     Info    Type            Sym.Value  Sym. Name
00011018  00000011 R_ARM_TLS_DTPMOD3

.dynsym symbols:
  (none)
.symtab symbols:
   Num:    Value  Size Type    Bind   Vis      Ndx Name
    57: 00000004     4 TLS     LOCAL  DEFAULT   14 var1

The .GOT after relocation will have:
11018: <module number> (0 in IDA)
1101C: 4 (compiled in)
*/

/* However, the exact same methods as above are used. The .index member is
 statically populated with 4 */
int value_static() { return var1; }
int *address_static() { return &var1; }

/*
Relocations:

 Offset     Info    Type            Sym.Value  Sym. Name
0001102c  00000711 R_ARM_TLS_DTPMOD3 00000000 var2
00011030  00000712 R_ARM_TLS_DTPOFF3 00000000 var2

.dynsym symbols:
   Num:    Value  Size Type    Bind   Vis      Ndx Name
     7: 00000000     0 TLS     GLOBAL DEFAULT  UND var2
.symtab symbols:
   Num:    Value  Size Type    Bind   Vis      Ndx Name
    90: 00000000     0 TLS     GLOBAL DEFAULT  UND var2

The .GOT after relocation will have:
1102C: <module number> (0 in IDA)
11030: 0x11240, address of a made up variable in extern
*/
extern __thread int var2;
int value_extern() { return var2; }
int *address_extern() { return &var2; }
