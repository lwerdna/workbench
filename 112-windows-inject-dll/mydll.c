#include <windows.h>

#define _NO_CRT_STDIO_INLINE 1

//#define DBGPRINTF(...) { char tmp[1024]; sprintf(tmp, __VA_ARGS__); OutputDebugStringA(tmp); }
#define DBGPRINTF(...) { char tmp[1024]; sprintf(tmp, __VA_ARGS__); printf(tmp); }

BOOL WINAPI DllMain(
	HINSTANCE const instance,
	DWORD const reason,
	LPVOID const reserved)
{
	switch (reason) {
		case DLL_PROCESS_ATTACH:
			DBGPRINTF("mydll: DLL_PROCESS_ATTACH\n");
			break;
		case DLL_THREAD_ATTACH:
			DBGPRINTF("mydll: DLL_THREAD_ATTACH\n");
			break;
		case DLL_THREAD_DETACH:
			DBGPRINTF("mydll: DLL_THREAD_DETACH\n");
			break;
		case DLL_PROCESS_DETACH:
			DBGPRINTF("mydll: DLL_PROCESS_DETACH\n");
			break;
		default:
			DBGPRINTF("mydll: unknown reason! %d\n", reason);
	}

	return 0;
}
