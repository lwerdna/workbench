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

	/* what type of linear view object?
	 * CreateLiftedIL()
	 * CreateLowLevelIL()
	 * CreateMediumLevelIL()
	 * etc. */
	Ref<LinearViewObject> lvo = LinearViewObject::CreateDisassembly(bv, new DisassemblySettings());
	if(!lvo) { printf("ERROR: creating linear view object\n"); return -1; }

	Ref<LinearViewCursor> lvc = new LinearViewCursor(lvo);
	if(!lvc) { printf("ERROR: creating cursor\n"); return -1; }
	
//	for(int i=0; 1; ++i) {
//		printf("before:%d after:%d valid:%d\n", lvc->IsBeforeBegin(), lvc->IsAfterEnd(), lvc->IsValid());
//		bool tmp = lvc->Next();
//		printf("%d lvc->Next(): %d\n", i, tmp);
//		if(!tmp) break;
//	}
//	printf("before:%d after:%d valid:%d\n", lvc->IsBeforeBegin(), lvc->IsAfterEnd(), lvc->IsValid());
//
//	lvc->Previous();
	vector<LinearDisassemblyLine> lines = lvc->GetLines();
	for(const auto& line : lines) {
		for(const auto& token : line.contents.tokens){
			printf("%s\n", token.text.c_str());
		}
	}
	//if(!lvc) { printf("ERROR: creating linear view cursor\n"); return -1; }
	//vector<LinearDisassemblyLine> lines = lvc->GetLines();
//	for(int i=0; i<lines.size(); ++i) {
//		LinearDisassemblyLine ldl = lines[i];
//		DisassemblyTextLine dtl = ldl.contents;
//		std::vector<InstructionTextToken> &tokens = dtl.tokens;
//		for(int j=0; j<tokens.size(); ++j) {
//			InstructionTextToken itt = dtl.tokens[j];
//			printf("%s", itt.text.c_str());
//		}
//	}

	printf("OK!\n");
	return 0;
}
