#include <stdio.h>

#include <Windows.h>

int main(int ac, char **av)
{
	DWORD pid = GetCurrentProcessId();
	HANDLE hThis = GetModuleHandleA(0);
	HANDLE hKernel32 = GetModuleHandleA("kernel32");

	for(int i=0; i<10000; ++i)
	{
		printf("PID=%d hKernel32=0x%p hThis=0x%p\n", pid, hKernel32, hThis);
		Sleep(1000);
	}

	return 0;
}
