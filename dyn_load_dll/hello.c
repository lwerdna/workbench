#include <stdio.h>

#include <windows.h>

#include "libfake.h"

/* locations and signatures to the things we patch */
#define OFFS_ZWCLOSE 0x51400
#define SIG_ZWCLOSE "\x4c\x8b\xd1\xb8\x0c\x00\x00\x00\x0f\x05\xc3"
#define OFFS_ZWOPENFILE 0x51640
#define SIG_ZWOPENFILE "\x4c\x8b\xd1\xb8\x30\x00\x00\x00\x0f\x05\xc3"
#define OFFS_ZWCREATESECTION 0x517b0
#define SIG_ZWCREATESECTION "\x4c\x8b\xd1\xb8\x47\x00\x00\x00\x0f\x05\xc3\x0f\x1f\x44\x00\x00"
#define OFFS_HOTSPOT 0x31272
#define SIG_HOTSPOT	"\xe8\xc9\x03\x02\x00\x85\xc0\x0f\x88\xfb\xc0\x04\x00\x48\x8b\x44"

/* globals */
unsigned char *pNtDll = NULL;

/* various patches */
unsigned char ret_zero[] = {
	0xb8, 0x00, 0x00, 0x00, 0x00,
	0xc3
};
unsigned char hook_x64[] = {
	0xff, 0x35, 0x01, 0x00, 0x00, 0x00,
	0xc3,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
};

/* detour functions */
NTSTATUS detour_ZwOpenFile(
	PHANDLE access,
	ACCESS_MASK DesiredAccess,
	void *ObjectAttributes /* POBJECT_ATTRIBUTES ObjectAttributes */,
	void *IoStatusBlock /* PIO_STATUS_BLOCK IoStatusBlock */,
	ULONG ShareAccess,
	ULONG OpenOptions
)
{
	printf("I'm in detour_ZwOpenFile()!\n");
	return 0; /* STATUS_SUCCESS */
}

NTSTATUS detour_ZwCreateSection(
	PHANDLE            SectionHandle /* out */,
	ACCESS_MASK        DesiredAccess,
	void *ObjectAttributes /* POBJECT_ATTRIBUTES ObjectAttributes */,
	PLARGE_INTEGER     MaximumSize,
	ULONG              SectionPageProtection,
	ULONG              AllocationAttributes,
	HANDLE             FileHandle
)
{
	HANDLE hFile;
	HANDLE hMapFile;

	printf("I'm in detour_ZwCreateSection()!\n");
	printf("        SectionHandle: %p\n", SectionHandle);
	printf("        DesiredAccess: 0x%X\n", DesiredAccess);
	printf("     ObjectAttributes: %p\n", ObjectAttributes);
	printf("          MaximumSize: %p\n", MaximumSize);
	printf("SectionPageProtection: 0x%X\n", SectionPageProtection);
	printf(" AllocationAttributes: 0x%X\n", AllocationAttributes);
	printf("           FileHandle: %p\n", FileHandle);

	/* unpatch (so we only execute once) */
	memcpy(pNtDll+OFFS_ZWCREATESECTION, SIG_ZWCREATESECTION, 15);

	hFile = CreateFile(
		"libfake2.dll",
		GENERIC_READ|GENERIC_WRITE /* dwDesiredAccess */,
		FILE_SHARE_READ|FILE_SHARE_WRITE /* dwShareMode */,
		NULL /* lpSecurityAttributes */,
		OPEN_EXISTING /* dwCreationDisposition */,
		FILE_ATTRIBUTE_NORMAL /* dwFlagsAndAttributes */,
		NULL /* hTemplateFile */
	);
	if(hFile == INVALID_HANDLE_VALUE) {
		printf("ERROR: CreateFile()\n");
		goto cleanup;
	}

	hMapFile = CreateFileMapping(
		hFile /* INVALID_HANDLE_VALUE */, 
		NULL, 
		PAGE_READWRITE | SEC_IMAGE,
		0,
		0,
		NULL
	);
	if(!hMapFile) {
		printf("ERROR: CreateFileMapping\n");
		goto cleanup;
	}

	*SectionHandle = hMapFile;

	cleanup:
	return 0 /* STATUS_SUCCESS */;
}

/* main :) */
int main(int ac, char **av)
{
	int rc=-1, i;
	int (*foo)(void);
	HANDLE hDll;
	LPCTSTR pBuf;
	DWORD oldProtect;

	printf("Hello, world!\n");

	pNtDll = (void *)LoadLibrary("ntdll.dll");
	if(!pNtDll) {
		printf("ERROR: LoadLibrary()\n");
		goto cleanup;
	}

	printf("found ntdll at: %p\n", pNtDll);

	/* hook ZwOpen() */
	//VirtualProtect(pNtDll+OFFS_ZWOPEN, 64, PAGE_EXECUTE_READWRITE, &oldProtect);
	//*(unsigned long long *)(hook_x64+7) = (unsigned __int64) detour_ZwOpenFile;
	//memcpy(pNtDll+OFFS_ZWOPEN, hook_x64, 15);

	/* shortcut ZwClose() */
	//VirtualProtect(pNtDll+OFFS_ZWCLOSE, 64, PAGE_EXECUTE_READWRITE, &oldProtect);
	//memcpy(pNtDll+OFFS_ZWCLOSE, ret_zero, 6);

	/* shortcut ZwCreateSection() */
	VirtualProtect(pNtDll+OFFS_ZWCREATESECTION, 64, PAGE_EXECUTE_READWRITE, &oldProtect);
	*(unsigned long long *)(hook_x64+7) = (unsigned __int64) detour_ZwCreateSection;
	memcpy(pNtDll+OFFS_ZWCREATESECTION, hook_x64, 15);

	/* drop-down Hotspot */
	//VirtualProtect(pNtDll+OFFS_HOTSPOT, 64, PAGE_EXECUTE_READWRITE, &oldProtect);
	//memset(pNtDll+OFFS_HOTSPOT+13, 0x90, 0x36);

	printf("hooks done!\n");

	hDll = LoadLibrary("libfake.dll");
	if(!hDll) {
		printf("ERROR: LoadLibrary()\n");
		goto cleanup;
	}

	printf("yeehaw\n");

	foo = (void *)GetProcAddress(hDll, "foo");
	if(!foo) {
		printf("ERROR: GetProcAddress()\n");
		goto cleanup;
	}

	printf("foo() returns: %d\n", foo());

	cleanup:
	return 0;
}
