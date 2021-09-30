/*
Q: How can you print all functions in C++
A: see below

this is cribbed from the llil_parser.cpp example in the API

g++ -std=c++11 -I$BN_API_PATH test3.cpp $BN_LIBBINARYNINJAAPI $BN_LIBBINARYNINJACORE -o test3
install_name_tool -change @rpath/libbinaryninjacore.1.dylib $BN_LIBBINARYNINJACORE ./test3
*/

#include "binaryninjaapi.h"

#include <stdio.h>

#include <string>
#include <cinttypes> // for PRIx64
using namespace std;
using namespace BinaryNinja;

// <BINJA_CPP_BOILERPLATE>

/* find the bundled plugins directory by finding the address of a function to
 * get the address of libbinaryninjacore to get its directory and append
 * "plugins" */
#ifndef _WIN32
#include <libgen.h>
#include <dlfcn.h>
static string GetPluginsDirectory()
{
	Dl_info info;
	if (!dladdr((void *)BNGetBundledPluginDirectory, &info))
		return NULL;

	stringstream ss;
	ss << dirname((char *)info.dli_fname) << "/plugins/";
	return ss.str();
}
#else
static string GetPluginsDirectory()
{
	return "C:\\Program Files\\Vector35\\BinaryNinja\\plugins\\";
}
#endif

/* C++ analog of python binaryninja.open_view() */
Ref<BinaryView> open_view(char *fpath)
{
	Ref<BinaryView> bv = NULL;
	Ref<BinaryData> bd = new BinaryData(new FileMetadata(), fpath);
	if(!bd) {
		printf("ERROR: couldn't get a new BinaryData() on %s\n", fpath);
		goto cleanup;
	}
	for (auto type : BinaryViewType::GetViewTypes()) {
		if (type->IsTypeValidForData(bd) && type->GetName() != "Raw") {
			bv = type->Create(bd);
			if(!bv) {
				printf("ERROR: couldn't Create() a binary view from the type\n");
				goto cleanup;
			}
			break;
		}
	}

	cleanup:
	return bv;
}

// </BINJA_CPP_BOILERPLATE>

int main(int ac, char **av)
{
	int rc = -1;
	string plugins_dir;
	Ref<BinaryView> bv;
	
	if(ac < 2) { printf("supply file\n"); goto cleanup; }

	plugins_dir = GetPluginsDirectory();
	printf("GetPluginsDirectory(): %s\n", plugins_dir.c_str());
	SetBundledPluginDirectory(plugins_dir);
	InitPlugins();

	bv = open_view(av[1]);
	if(!bv) { printf("couldn't open file\n"); goto cleanup; }
	bv->UpdateAnalysisAndWait();	

	for (auto& func : bv->GetAnalysisFunctionList())
	{
		// Get the name of the function and display it
		Ref<Symbol> sym = func->GetSymbol();
		if (sym)
			printf("Function %s:\n", sym->GetFullName().c_str());
		else
			printf("Function at 0x%" PRIx64 ":\n", func->GetStart());
	}

	cleanup:
	return rc;
}
