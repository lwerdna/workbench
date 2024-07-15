#include <stdio.h>

#include <Windows.h>

#define TARGET "helloworld.exe"

// how do we set privileges?
// 1) look up its luid
// 2) populate a token privileges structure
// 3) call AdjustTokenPrivileges
BOOL SetPrivilege(HANDLE hToken, char *privName, BOOL enablePrivilege)
{
	TOKEN_PRIVILEGES tp;
	LUID luid;

	// resolve privilege name to a LUID
	if (!LookupPrivilegeValue(NULL, privName, &luid)) {
		printf("ERROR: LookupPrivilege\n");
		return FALSE;
	}

	tp.PrivilegeCount = 1;
	tp.Privileges[0].Luid = luid;
	if (enablePrivilege)
		tp.Privileges[0].Attributes = SE_PRIVILEGE_ENABLED;
	else
		tp.Privileges[0].Attributes = 0;

	if (!AdjustTokenPrivileges(hToken, FALSE, &tp, sizeof(TOKEN_PRIVILEGES), (PTOKEN_PRIVILEGES) NULL, (PDWORD) NULL)) {
		printf("ERROR: AdjustTokenPrivileges()\n");
		DWORD error = GetLastError();
		printf("GetLastError() returns %d or 0x%08X\n", error, error);
		return FALSE;
	}

	printf("SetPrivilege() succeeded!\n");
	return TRUE;
}

int get_victim_pid(char *targetProcName)
{
	int result = 0;

	DWORD pids[4096];
	DWORD cbNeeded, cProcesses;

	if (!K32EnumProcesses(pids, sizeof(pids), &cbNeeded))
		goto cleanup;

	cProcesses = cbNeeded / sizeof(DWORD);
	for (int i=0; i<cProcesses; i++) {
		int pid = pids[i];
		HANDLE hProcess = OpenProcess(PROCESS_QUERY_INFORMATION, FALSE, pid);
		if (hProcess == NULL) {
			printf("Couldn't OpenProcess() on pid=%d\n", pid);
			continue;
		}

		char fileName[1024];
		if (K32GetModuleFileNameExA(hProcess, NULL, fileName, 1024) == 0)
			continue;

		int j = strlen(fileName)-1;
		while (j >= 0 && fileName[j] != '\\')
			j--;
		j += 1;

		printf("pid=%d filename=%s\n", pid, fileName+j);

		if (strcmp(fileName+j, targetProcName) == 0) {
			result = pid;
			break;
		}
	}

	cleanup:
	return result;
}

int main(int ac, char **av)
{
	BOOL bRet;

	HANDLE processHandle = NULL;
	int pid = 0;

	char username[1024];
	int cb = sizeof(username);
	bRet = GetUserNameA(username, &cb);
	if (!bRet) {
		printf("ERROR: GetUserNameA()\n");
	}
	else
	{
		printf("username: %s\n", username);
	}

	HANDLE hToken;
	bRet = OpenProcessToken(GetCurrentProcess(), TOKEN_ADJUST_PRIVILEGES, &hToken);
	if (!bRet) {
		printf("ERROR: OpenProcessToken()\n");
		return -1;
	}

	printf("current process token: 0x%p\n", hToken);

	if (SetPrivilege(hToken, "SeDebugPrivilege", TRUE) == FALSE) {
		printf("ERROR: SetPrivilege()\n");
		return -1;
	}

	if (ac > 1) {
		pid = atoi(av[1]);
	} else {
		pid = get_victim_pid(TARGET);
	}

	if (pid == 0) {
		printf("ERROR: couldn't resolve pid of %s\n", TARGET);
		goto cleanup;
	}

	printf("found process %s as pid=%d\n", TARGET, pid);

	processHandle = OpenProcess(PROCESS_ALL_ACCESS, FALSE, pid);
	if (processHandle == NULL) {
		printf("ERROR: OpenProcess()\n");
		goto cleanup;
	}

	printf("success! handle is 0x%p\n", (PVOID)processHandle);

	// We need to copy the name of the dll to load into the memory space of the target process.
	char *dllName = "mydll.dll";
	PVOID remoteBuffer = VirtualAllocEx(processHandle, NULL, strlen(dllName)+1, MEM_COMMIT, PAGE_READWRITE);
	if (remoteBuffer == NULL)
		goto cleanup;

	printf("remote memory is at 0x%p\n", remoteBuffer);

	bRet = WriteProcessMemory(processHandle, remoteBuffer, (LPVOID)dllName, strlen(dllName)+1, NULL);
	if (!bRet)
		goto cleanup;

	// Here we're getting the module handle for kernel32. We're also assuming (and testing seems to
	// bear this out) that since kernel32 is a shared module, the module handle is portable across
	// processes
	HANDLE hKernel32 = GetModuleHandleA("kernel32");
	printf("hKernel32: 0x%p\n", hKernel32);

	printf("Testing that the target has at least an MZ header at this address...\n");
	unsigned char buf[1024];
	bRet = ReadProcessMemory(processHandle, hKernel32, buf, 8, NULL);
	if (!bRet)
		goto cleanup;

	if (buf[0] != 'M' || buf[1] != 'Z') {
		printf("MZ header not found!!\n");
		goto cleanup;
	}

	FARPROC addrLoadLibrary = GetProcAddress(hKernel32, "LoadLibraryA");

	printf("kernel32!LoadLibraryA: 0x%p\n", addrLoadLibrary);

	bRet = ReadProcessMemory(processHandle, addrLoadLibrary, buf, 16, NULL);
	if (!bRet)
		goto cleanup;

	printf("Testing that the target has at least sane LoadLibraryA bytes...\n");
	//if (buf[0] != 0x48 || buf[7] != 0xCC || buf[8] != 0xCC || buf[9] != 0xCC || buf[10] != 0xCC || buf[11] != 0xCC || buf[12] != 0xCC || buf[13] != 0xCC || buf[14] != 0xCC || buf[15] != 0xCC) {
	if (buf[7] != 0xCC || buf[8] != 0xCC || buf[9] != 0xCC || buf[10] != 0xCC || buf[11] != 0xCC || buf[12] != 0xCC || buf[13] != 0xCC || buf[14] != 0xCC || buf[15] != 0xCC) {
		printf("%02X %02X %02X %02X %02X %02X %02X %02X\n", buf[0], buf[1], buf[2], buf[3], buf[4], buf[5], buf[6], buf[7]);
		printf("ERROR: doesnt actually look like LoadLibrary\n");
		goto cleanup;
	}

	HANDLE hThread = CreateRemoteThread(processHandle, NULL, 0, (LPTHREAD_START_ROUTINE)addrLoadLibrary, remoteBuffer, 0, NULL);
	if (hThread == NULL) {
		printf("ERROR: CreateRemoteThread()\n");
		goto cleanup;
	}

	printf("So far so good!\n");

	cleanup:

	if (processHandle != NULL)
		CloseHandle(processHandle);

	return 0;
}
