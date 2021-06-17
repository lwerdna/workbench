#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

// generated with patch.py
#include "bnc.h"

int main(int ac, char **av)
{
	int rc = -1;
	unsigned int i;
	BNArchitecture *arch;
	const char *data = "\x48\x89\xe5";
	size_t data_n = 3;
	BNInstructionTextToken *itt = NULL;
	size_t token_n;
	const char *path_bundled_plugins;
	char BN_INSTALL_DIR[1024] = {'\0'};

	path_bundled_plugins = BNGetBundledPluginDirectory();
	printf("BNGetBundledPluginDirectory() returns: %s\n", path_bundled_plugins);
	if(!getenv("BN_INSTALL_DIR")) goto cleanup;
	strncpy(BN_INSTALL_DIR, getenv("BN_INSTALL_DIR"), 1024-1);
	path_bundled_plugins = BN_INSTALL_DIR;
	printf("using bundled plugin path: %s\n", path_bundled_plugins);
	BNSetBundledPluginDirectory(path_bundled_plugins);
	BNInitPlugins(true);

	arch = BNGetArchitectureByName("x86_64");
	if(!arch) goto cleanup;

	BNGetInstructionText(arch, (const uint8_t *)data, 0, &data_n, &itt, &token_n);

	for(i=0; i<token_n; ++i)
		printf("%s", itt[i].text);
	printf("\n");

	cleanup:
	if(itt)
		BNFreeInstructionText(itt, token_n);
	BNShutdown();
	return rc;
}


