#include <stdio.h>
#include <dlfcn.h>

void test()
{
 	Dl_info info;
 	if (dladdr(test, &info))
 	{
    	printf("Loaded from path = %s\n", info.dli_fname);
 	}
}
