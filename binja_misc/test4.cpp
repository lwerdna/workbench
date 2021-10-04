/*
Q: How can you print the linear disassembly view to stdout?
A:

build:
$ g++ -g -O0 -std=c++11 -I$BN_API_PATH test4.cpp $BN_LIBBINARYNINJAAPI $BN_LIBBINARYNINJACORE -o test4
$ install_name_tool -change @rpath/libbinaryninjacore.1.dylib $BN_LIBBINARYNINJACORE ./test4
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

	if(bv)
		bv->UpdateAnalysisAndWait();

	cleanup:
	return bv;
}

void binja_init(void)
{
	string plugins_dir = GetPluginsDirectory();
	//printf("GetPluginsDirectory(): %s\n", plugins_dir.c_str());
	SetBundledPluginDirectory(plugins_dir);
	InitPlugins();
}

// </BINJA_CPP_BOILERPLATE>

int main(int ac, char **av)
{
	Ref<BinaryView> bv;
	
	if(ac < 2) { printf("ERROR: supply file\n"); return -1; }

	binja_init();
	bv = open_view(av[1]);
	if(!bv) { printf("ERROR: opening file\n"); return -1; }

	Ref<DisassemblySettings> settings = new DisassemblySettings();
	settings->SetOption(ShowAddress, true);
	settings->SetOption(ShowOpcode, true);
	settings->SetOption(ExpandLongOpcode, true);
	settings->SetOption(ShowVariablesAtTopOfGraph, true);
	settings->SetOption(ShowVariableTypesWhenAssigned, true);
	settings->SetOption(ShowCallParameterNames, true);
	settings->SetOption(ShowRegisterHighlight, true);
	settings->SetOption(ShowFunctionAddress, true);
	settings->SetOption(ShowFunctionHeader, true);

	/* what type of linear view object?
	 * CreateLiftedIL()
	 * CreateLowLevelIL()
	 * CreateMediumLevelIL()
	 * etc. */
	Ref<LinearViewObject> lvo = LinearViewObject::CreateDisassembly(bv, settings);
	if(!lvo) { printf("ERROR: creating linear view object\n"); return -1; }

	Ref<LinearViewCursor> lvc = new LinearViewCursor(lvo);
	if(!lvc) { printf("ERROR: creating cursor\n"); return -1; }
	
	while(lvc->IsValid()) {
		vector<LinearDisassemblyLine> lines = lvc->GetLines();
		for(const auto& line : lines) {
			for(const auto& token : line.contents.tokens){
				/* no tags/emojis */
				if(token.type == TagToken)
					continue;

				printf("%s", token.text.c_str());
			}
			printf("\n");
		}

		lvc->Next();
	}

	/* reference counted objects auto-deleted if reference count to zero at scope exit */
	//delete lvc;
	//delete lvo;
	//delete settings;

	printf("OK!\n");
	return 0;
}
