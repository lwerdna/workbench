#define _CRT_SECURE_NO_WARNINGS
#define NOMINMAX

#include <inttypes.h>

#include <string>

#include "binaryninjaapi.h"

using namespace std;
using namespace BinaryNinja;

#if defined(_MSC_VER)
#define snprintf _snprintf
#endif

extern "C"
{
	BN_DECLARE_CORE_ABI_VERSION
}

extern "C" int SayIntAndString(int foo, char *bar)
{
	LogInfo("c++/LogInfo(): foo=%d bar=%s", foo, bar);
	return 234;
}

extern "C" BINARYNINJAPLUGIN bool CorePluginInit()
{
	printf("printf(): TEST plugin loaded!\n");
	return true;
}

