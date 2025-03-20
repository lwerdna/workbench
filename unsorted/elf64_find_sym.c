#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include <inttypes.h>

#include <elf.h>

#define MAX_STRTAB_ENTRY_LEN 64 // includes null byte
void get_string(FILE *fp, int strtab_offs, int strtab_idx, char *result)
{
	char buf[MAX_STRTAB_ENTRY_LEN] = {0};

	int pos = ftell(fp);

	fseek(fp, strtab_offs + strtab_idx, SEEK_SET);
	fread(buf, MAX_STRTAB_ENTRY_LEN, 1, fp);

	memset(result, '\0', MAX_STRTAB_ENTRY_LEN);
	strncpy(result, buf, MAX_STRTAB_ENTRY_LEN-1);

	fseek(fp, pos, SEEK_SET);
}

int main(int ac, char **av)
{
	int rc = 0;
	char *path = av[1];

	FILE *fp = fopen(path, "rb");

	// get important bits from elf64 header
	Elf64_Ehdr ehdr;
	fread(&ehdr, sizeof(Elf64_Ehdr), 1, fp);

	// get the string table, containing section names
	Elf64_Shdr strtab = {0};
	fseek(fp, ehdr.e_shoff + ehdr.e_shstrndx*sizeof(Elf64_Shdr), SEEK_SET);
	fread(&strtab, sizeof(Elf64_Shdr), 1, fp);
	printf("strtab.sh_offset: 0x%lx\n", strtab.sh_offset);

	// find .dynstr and .dynsym sections
	Elf64_Shdr dynstr = {0};
	Elf64_Shdr dynsym = {0};
	fseek(fp, ehdr.e_shoff, SEEK_SET);
	for (int i=0; i<ehdr.e_shnum; ++i) {
		Elf64_Shdr shdr;
		fread(&shdr, sizeof(Elf64_Shdr), 1, fp);

		char name[MAX_STRTAB_ENTRY_LEN];
		get_string(fp, strtab.sh_offset, shdr.sh_name, name);
		//printf("section %d/%d has sh_name=0x%x, name=\"%s\"\n", i+1, ehdr.e_shnum, shdr.sh_name, name);

		if (!strcmp(name, ".dynstr"))
			memcpy(&dynstr, &shdr, sizeof(Elf64_Shdr));
		else if (!strcmp(name, ".dynsym"))
			memcpy(&dynsym, &shdr, sizeof(Elf64_Shdr));
	}

	if (!(dynstr.sh_name && dynsym.sh_name)) {
		printf("ERROR: couldn't locate .dynstr and .dynsym\n");
		goto cleanup;
	}

	// seek symbols
	Elf64_Sym __libc_dlopen_mode = {0};
	Elf64_Sym __libc_dlclose = {0};
	int num_syms = dynsym.sh_size / sizeof(Elf64_Sym);
	fseek(fp, dynsym.sh_offset, SEEK_SET);
	for (int i=0; i<num_syms; ++i) {
		Elf64_Sym sym;
		fread(&sym, sizeof(Elf64_Sym), 1, fp);

		char name[MAX_STRTAB_ENTRY_LEN];
		get_string(fp, dynstr.sh_offset, sym.st_name, name);

		printf("symbol %d/%d has st_name=0x%x, name=\"%s\"\n", i+1, num_syms, sym.st_name, name);
		
		if (!strcmp(name, "__libc_dlopen_mode"))
			memcpy(&__libc_dlopen_mode, &sym, sizeof(Elf64_Sym));
		else if (!strcmp(name, "__libc_dlclose"))
			memcpy(&__libc_dlclose, &sym, sizeof(Elf64_Sym));
	}

	if (!(__libc_dlopen_mode.st_name && __libc_dlclose.st_name)) {
		printf("ERROR: couldn't locate __libc_dlopen_mode or __libc_dlclose\n");
		goto cleanup;
	}

	printf("__libc_dlopen_mode.st_value=0x%lx\n", __libc_dlopen_mode.st_value);
	printf("__libc_dlclose.st_value=0x%lx\n", __libc_dlclose.st_value);

	rc = 0;

	cleanup:
	return rc;
}
