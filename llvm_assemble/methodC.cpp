/* from binaryninja */

#define _SILENCE_CXX17_ITERATOR_BASE_CLASS_DEPRECATION_WARNING

/* c++ includes */
#include <map>
#include <string>
#include <vector>
using namespace std;

/* local include */
#include "help.h"

#define LLVM_SVCS_DIALECT_UNSPEC 0
#define LLVM_SVCS_DIALECT_ATT 1
#define LLVM_SVCS_DIALECT_INTEL 2

#define LLVM_SVCS_CM_DEFAULT 0
#define LLVM_SVCS_CM_SMALL   1
#define LLVM_SVCS_CM_KERNEL  2
#define LLVM_SVCS_CM_MEDIUM  3
#define LLVM_SVCS_CM_LARGE   4

#define LLVM_SVCS_RM_STATIC 0
#define LLVM_SVCS_RM_PIC 1
#define LLVM_SVCS_RM_DYNAMIC_NO_PIC 2


/* llvm includes */
/* note that at least in 4.0.0 and onward, much gets moved to llvm/MC/MCParser/ */

#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif

#ifdef __GNUC__
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#endif

#ifdef WIN32
#pragma warning(disable: 4100)
#pragma warning(disable: 4141)
#pragma warning(disable: 4146)
#pragma warning(disable: 4244)
#pragma warning(disable: 4267)
#pragma warning(disable: 4624)
#endif

#include <llvm/MC/MCAsmBackend.h>
#include <llvm/MC/MCAsmInfo.h>
#include <llvm/MC/MCContext.h>
#include <llvm/MC/MCDisassembler/MCDisassembler.h>
#include <llvm/MC/MCInstPrinter.h>
#include <llvm/MC/MCInstrInfo.h>
#include <llvm/MC/MCObjectFileInfo.h>
#include <llvm/MC/MCObjectWriter.h>
#include <llvm/MC/MCRegisterInfo.h>
#include <llvm/MC/MCSectionMachO.h>
#include <llvm/MC/MCStreamer.h>
#include <llvm/MC/MCSubtargetInfo.h>
#include <llvm/MC/MCParser/MCTargetAsmParser.h>
#include <llvm/MC/MCTargetOptions.h>
#include <llvm/MC/MCCodeEmitter.h>
#include <llvm/MC/MCParser/AsmLexer.h>

#include <llvm/Support/CommandLine.h>
#include <llvm/Support/Compression.h>
#include <llvm/Support/FileUtilities.h>
#include <llvm/Support/FormattedStream.h>
#include <llvm/Support/Host.h> // for getDefaultTargetTriple();
#include <llvm/Support/ManagedStatic.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/PrettyStackTrace.h>
#include <llvm/Support/Signals.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/MC/TargetRegistry.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Support/ToolOutputFile.h>

#include <llvm-c/Disassembler.h>

#ifdef __GNUC__
#pragma GCC diagnostic pop
#endif
#ifdef __clang__
#pragma clang diagnostic pop
#endif

#define DIALECT_ATT 0
#define DIALECT_INTEL 1

using namespace llvm;


/*****************************************************************************/
/* MISCELLANY */
/*****************************************************************************/

void BNLlvmServicesInit(void)
{
	llvm::InitializeAllTargetInfos();
	llvm::InitializeAllTargetMCs();
	llvm::InitializeAllAsmParsers();
	llvm::InitializeAllDisassemblers();
}

/* map LLVM services reloc mode to LLVM reloc mode
	(so API users don't have to include LLVM headers) */
static Reloc::Model map_reloc_mode(int relocMode)
{
	/* SEE: NOT the values in include/llvm-c/TargetMachine.h
		but llvm/Support/CodeGen.h */
	switch(relocMode) {
		case LLVM_SVCS_RM_STATIC: return Reloc::Static;
		case LLVM_SVCS_RM_PIC: return Reloc::PIC_;
		case LLVM_SVCS_RM_DYNAMIC_NO_PIC: return Reloc::DynamicNoPIC;
		default: return Reloc::Static;
	}
}

static uint32_t bswap32(uint32_t x)
{
	return ((x&0xFF)<<24) |
		((x&0xFF00)<<8) |
		((x&0xFF0000)>>8) |
		((x&0xFF000000)>>24);
}

static uint64_t bswap64(uint64_t x)
{
	return ((x&0xFF)<<56) |
		((x&0xFF00)<<40) |
		((x&0xFF0000)<<24) |
		((x&0xFF000000)<<8) |
		((x&0xFF00000000)>>8) |
		((x&0xFF0000000000)>>24) |
		((x&0xFF000000000000)>>40) |
		((x&0xFF00000000000000)>>56);
}

static uint32_t fetch32(char *data, bool swap=false)
{
	uint32_t tmp = *(uint32_t *)data;
	if(swap) tmp = bswap32(tmp);
	return tmp;
}

//static uint64_t fetch64(char *data, bool swap=false)
//{
//	uint64_t tmp = *(uint64_t *)data;
//	if(swap) tmp = bswap64(tmp);
//	return tmp;
//}

static void set32(char *addr, uint32_t val, bool swap=false)
{
	if(swap) val = bswap32(val);
	*(uint32_t *)addr = val;
}

//static void set64(char *addr, uint64_t val, bool swap=false)
//{
//	if(swap) val = bswap64(val);
//	*(uint64_t *)addr = val;
//}

/*****************************************************************************/
/* ASSEMBLE RELATED FUNCTIONS */
/*****************************************************************************/

static int obj_output_to_bytes(char *data, string &result)
{
	int rc = -1;

	uint64_t codeOffset=0, codeSize = 0;

	/* it's assumed that in all ELF files, the .text section is third, usually
		the layout is NULL, .strtab, .text, ... */

	/* Mach-O */
	if(*(uint32_t *)data == 0xFEEDFACF) {
		unsigned int idx = 0;
		idx += 0x20; /* skip mach_header_64 to first command */
		idx += 0x48; /* advance into segment_command_64 to first section */
		idx += 0x28; /* advance into section_64 to size */
		uint64_t scn_size = *(uint64_t *)(data + idx);
		idx += 0x8; /* advance into section_64 to offset */
		uint64_t scn_offset = *(uint64_t *)(data + idx);
		codeOffset = scn_offset;
		codeSize = scn_size;
	}
	/* 32-bit ELF */
	else if(0==memcmp(data, "\x7F" "ELF\x01\x01\x01\x00", 8) || /* little endian */
	  0==memcmp(data, "\x7F" "ELF\x01\x02\x01\x00", 8)) { /* big endian */

		bool s = data[5] != 0x01;

		/* possibilities:
			- four sections: NULL, .strtab, .text, .symtab
			- five sections: NULL, .strtab, .text, .rel.text, .symtab */
		uint32_t e_shoff = fetch32(data + 0x20, s);
		uint16_t e_shnum = *(uint16_t *)(data + 0x30);
		uint32_t txt_offs = fetch32(data + e_shoff + 2*0x28 + 0x10, s); /* second shdr */
		uint32_t txt_size = fetch32(data + e_shoff + 2*0x28 + 0x14, s); /* second shdr */
		codeOffset = txt_offs;
		codeSize = txt_size;

		if(e_shnum == 5) {
			/* we have relocations, uh oh */
			uint32_t rel_offs = fetch32(data + e_shoff + 3*0x28 + 0x10, s);
			uint32_t rel_size = fetch32(data + e_shoff + 3*0x28 + 0x14, s);
			uint32_t sym_offs = fetch32(data + e_shoff + 4*0x28 + 0x10, s);
			uint32_t sym_size = fetch32(data + e_shoff + 4*0x28 + 0x14, s);
			/* parse relocations */
			for(uint32_t i=0; i<rel_size; i+=8) {
				uint32_t d_val = fetch32(data + rel_offs + i, s);
				uint32_t d_ptr = fetch32(data + rel_offs + i + 4, s);
				/* if R_ARM_CALL */
				if((d_ptr & 0xFF) == 0x1C) {
					uint8_t sym_idx = (d_ptr & 0xFF00) >> 8;
					if(sym_idx >= (sym_size / 16)) continue;
					uint32_t st_value = fetch32(data + sym_offs + 16*sym_idx + 4, s);
					/* at d_val we should find a bl/blx (0xEB/0xFA) */
					uint32_t instr = fetch32(data + txt_offs + d_val, s);
					/* remember pc bias of +8 and this is 4-byte instr count */
					int32_t displ = (st_value - (d_val + 8)) / 4;
					/* modify the instr operand: 3 byte displacement */
					instr = (instr & 0xFF000000) | (displ & 0xFFFFFF);
					set32(data + txt_offs + d_val, instr, s);
				}
			}
		}
	}
	/* 64-bit ELF */
	else if(0==memcmp(data, "\x7F" "ELF\x02\x01\x01\x00", 8)) {
		/* assume text is third section (eg: NULL, .strtab, .text) */
		uint64_t e_shoff = *(uint64_t *)(data + 0x28);
		uint64_t sh_offset = *(uint64_t *)(data + e_shoff + 2*0x40 + 0x18); /* second shdr */
		uint64_t sh_size = *(uint64_t *)(data + e_shoff + 2*0x40 + 0x20); /* second shdr */
		codeOffset = sh_offset;
		codeSize = sh_size;
	}
	/* 64-bit ELF (big-end) */
	else if(0==memcmp(data, "\x7F" "ELF\x02\x02\x01\x00", 8)) {
		/* assume text is third section (eg: NULL, .strtab, .text) */
		uint64_t e_shoff = bswap64(*(uint64_t *)(data + 0x28));
		uint64_t sh_offset = bswap64(*(uint64_t *)(data + e_shoff + 2*0x40 + 0x18)); /* second shdr */
		uint64_t sh_size = bswap64(*(uint64_t *)(data + e_shoff + 2*0x40 + 0x20)); /* second shdr */
		codeOffset = sh_offset;
		codeSize = sh_size;
	}
	else {
		//printf("ERROR: couldn't identify type of output file\n");
		goto cleanup;
	}

	result.assign(reinterpret_cast<char const *>(data+codeOffset), codeSize);

	rc = 0;
	cleanup:
	return rc;
}

/* source manager diagnostics handler
	(instead of printing to stderr) */
/* we set LLVM's callback to this to fill in the error string when possible */
static void diag_cb(const SMDiagnostic &diag, void *param)
{
	if(!param) return;

	string *strErr = (string *)param;

	switch(diag.getKind()) {
		case SourceMgr::DK_Warning:
		case SourceMgr::DK_Error:
		{
			//string fileName = diag.getFilename().str();
			string message = diag.getMessage().str();
			// diag.getLineNo()
			*strErr += "line " + to_string(diag.getLineNo()) + ": " + message + "\n";
		}
			break;

		case SourceMgr::DK_Note:
		default:
			break;
	}
}

static int invoke_llvm_parsers(const Target *TheTarget, SourceMgr *SrcMgr, MCContext &context,
	MCStreamer &Str, MCAsmInfo &MAI, MCSubtargetInfo &STI, MCInstrInfo &MCII,
	MCTargetOptions &MCOptions, int dialect)
{
	int rc = -1;

	/* create a vanilla (non-target) AsmParser (lib/MC/MCParser/AsmParser.cpp) */
	std::unique_ptr<MCAsmParser> Parser(createMCAsmParser(*SrcMgr, context, Str, MAI));

	/* set the dialect (otherwise it defaults to assemblerInfo's dialect) */
	switch(dialect) {
		case LLVM_SVCS_DIALECT_UNSPEC:
			break;
		case LLVM_SVCS_DIALECT_ATT:
			Parser->setAssemblerDialect(DIALECT_ATT);
			break;
		case LLVM_SVCS_DIALECT_INTEL:
			Parser->setAssemblerDialect(DIALECT_INTEL);
			break;
	}

	/* TARGET asm parser */
	std::unique_ptr<MCTargetAsmParser> TAP(TheTarget->createMCAsmParser(STI, *Parser, MCII, MCOptions));

	if (!TAP) {
		//printf("ERROR: createMCAsmParser() (does target support assembly parsing?)\n");
		goto cleanup;
	}

	Parser->setTargetParser(*TAP);

	// AsmParser::Run in lib/MC/MCParser/AsmParser.cpp
	/* first param is NoInitialTextSection
		by supplying false -> YES initial text section and obviate ".text" in asm source */
	rc = Parser->Run(false);

	cleanup:
	return rc;
}

int BNLlvmServicesAssemble(
	/* in parameters */
	const char *srcText, 		/* eg: "mov r0, r0" */
	int dialect, 				/* eg: LLVM_SVCS_DIALECT_ATT */
	const char *triplet, 		/* eg: x86_64-thumb-linux-gnu */
	int codeModel,				/* LLVM_SVCS_CM_JIT, LLVM_SVCS_CM_SMALL, etc. */
	int relocMode, 				/* LLVM_SVCS_RM_STATIC, etc. */

	/* out parameters */
	char **outBytes, int *outBytesLen,
	char **err, int *errLen)
{
	(void)codeModel;
	(void)errLen;
	int rc = -1;

	*outBytes = NULL;
	*outBytesLen = 0;

	*err = NULL;
	*errLen = 0;

	/* output for asm->obj */
	SmallString<1024> smallString;
	raw_svector_ostream rsvo(smallString);

	/* source code vars */
	std::string strSrc(srcText);
	std::unique_ptr<MemoryBuffer> mbSrc;

	string instrBytes;
	string strErr;

	/*************************************************************************/
	/* the triple and the target */
	/*************************************************************************/

	// see /lib/Support/Triple.cpp for the details
	std::string machSpec(triplet);
	machSpec = Triple::normalize(machSpec);
	Triple TheTriple(machSpec);

	/* get the target specific parser
		if arch is blank, the triple is consulted */
	const Target *target = TargetRegistry::lookupTarget(/*arch*/"", TheTriple, strErr);
	if (!target) {
		strErr = "TargetRegistry::lookupTarget() failed\n" + strErr;
		return -1;
	}

	//printf("machine spec: %s\n", machSpec.c_str());
	//printf("Target.getName(): %s\n", target->getName());
	//printf("Target.getShortDescription(): %s\n", target->getShortDescription());

	/* target opts */
	MCTargetOptions targetOpts;
	targetOpts.MCUseDwarfDirectory = false;
	/* how is this different than the last field of the triplet? */
	//targetOpts.ABIName = abi;

	/* from the target we get almost everything */
	std::unique_ptr<MCRegisterInfo> regInfo(target->createMCRegInfo(machSpec));
	std::unique_ptr<MCAsmInfo> asmInfo(target->createMCAsmInfo(*regInfo, machSpec, MCTargetOptions()));
	std::unique_ptr<MCInstrInfo> instrInfo(target->createMCInstrInfo()); /* describes target instruction set */
	std::unique_ptr<MCSubtargetInfo> subTargetInfo(target->createMCSubtargetInfo(machSpec, "", "")); /* subtarget instr set */
	/* fixups, relaxations, objs, elfs */
	std::unique_ptr<MCAsmBackend> asmBackend(target->createMCAsmBackend(*subTargetInfo, *regInfo, targetOpts));

	/*************************************************************************/
	/* source code manager */
	/*************************************************************************/

	// llvm::SourceMgr (include/llvm/Support/SourceMgr.h) that holds assembler source
	// has vector of llvm::SrcBuffer encaps (Support/MemoryBuffer.h) and vector of include dirs
	SourceMgr srcMgr;
	mbSrc = MemoryBuffer::getMemBuffer(strSrc);
	srcMgr.AddNewSourceBuffer(std::move(mbSrc), SMLoc());
	srcMgr.setDiagHandler(diag_cb, (void *)&strErr);

	/*************************************************************************/
	/* MC context, object file, code emitter, target options */
	/*************************************************************************/

	// MC/MCObjectFileInfo.h describes common object file formats
	MCObjectFileInfo objFileInfo;

	/* MC/MCContext.h */
	MCContext context(TheTriple, asmInfo.get(), regInfo.get(), subTargetInfo.get(), &srcMgr);

	/* yes, this is circular (MCContext requiring MCObjectFileInfo and visa
		versa, and is marked "FIXME" in llvm-mc.cpp */

	/* also see initMachOMCObjectFileInfo(), initELFMCObjectFileInfo(),
		initCOFFMCObjectFileInfo() ... will ask TT.getObjectFormat() if not
		specified */
	objFileInfo.initMCObjectFileInfo(context, /* LargeCodeModel */ false);
	context.setObjectFileInfo(&objFileInfo);

	/* code emitter llvm/MC/MCCodeEmitter.h
		has encodeInstruction() which maps MCInstr -> bytes

		target returns with X86MCCodeEmitter, ARMMCCodeEmitter, etc.
	*/
	std::unique_ptr<MCCodeEmitter> codeEmitter(target->createMCCodeEmitter(*instrInfo, *regInfo, context));

	/*************************************************************************/
	/* assemble to object */
	/*************************************************************************/

	std::unique_ptr<MCObjectWriter> objWriter(asmBackend->createObjectWriter(rsvo));
	std::unique_ptr<MCStreamer> streamer(target->createMCObjectStreamer(
		TheTriple,
		context,
		std::move(asmBackend),  /* (fixups, relaxation, objs and elfs) */
		std::move(objWriter),
		std::move(codeEmitter),
		*subTargetInfo,
		true, /* relax all fixups */
		true, /* incremental linker compatible */
		false /* DWARFMustBeAtTheEnd */
	));

	if(invoke_llvm_parsers(target, &srcMgr, context, *streamer, *asmInfo,
	  *subTargetInfo, *instrInfo, targetOpts, dialect))
	{

		if(strErr.empty())
			strErr = "invoking llvm parsers\n";

		goto cleanup;
	}

	/* dump to file for debugging */
	if(0)
	{
		FILE *fp;
		fp = fopen("out.bin", "wb");
		fwrite(smallString.data(), 1, smallString.size(), fp);
		fclose(fp);
	}

	if(obj_output_to_bytes(smallString.data(), instrBytes))
	{
		if(strErr.empty())
			strErr = "parsing bytes from LLVM obj\n";

		goto cleanup;
	}

	*outBytes = new char[instrBytes.size()];
	if(!outBytes)
	{
		strErr = "allocating memory for bytes\n";
		goto cleanup;
	}

	memcpy(*outBytes, instrBytes.c_str(), instrBytes.size());
	*outBytesLen = instrBytes.size();

	rc = 0;
	cleanup:
	if(strErr.size()) {
		//*err = BNAllocString(strErr.c_str());
		//*errLen = strErr.size();
	}
	return rc;
}


void BNLlvmServicesAssembleFree(char *outBytes, char *err)
{
	if(outBytes) {
		delete[] outBytes;
	}

	if(err) {
		//BNFreeString(err);
	}
}

/*****************************************************************************/
/* DISASSEMBLE related functions */
/*****************************************************************************/

/* a dummy function for the disasm context, else aarch64 crashes on
	FF 43 00 D1

	see llvm-c/Disassembler.h
*/
const char *
symbol_lookup_cb(void *DisInfo, uint64_t ReferenceValue, uint64_t *ReferenceType,
	uint64_t ReferencePC, const char **ReferenceName)
{
	(void)DisInfo;
	(void)ReferenceValue;
	(void)ReferenceType;
	(void)ReferencePC;
	(void)ReferenceName;

#if 0
	const char *strRefType = "unknown";

	switch(*ReferenceType) {
		/* No input reference type or no output reference type. */
		case LLVMDisassembler_ReferenceType_InOut_None:
			strRefType = "none"; break;
		/* The input reference is from a branch instruction. */
		case LLVMDisassembler_ReferenceType_In_Branch:
			strRefType = "branch"; break;
		/* The input reference is from a PC relative load instruction. */
		case LLVMDisassembler_ReferenceType_In_PCrel_Load:
			strRefType = "pcref_load"; break;

		/* The input reference is from an ARM64::ADRP instruction. */
		case LLVMDisassembler_ReferenceType_In_ARM64_ADRP:
			strRefType = "arm64_adrp"; break;
		/* The input reference is from an ARM64::ADDXri instruction. */
		case LLVMDisassembler_ReferenceType_In_ARM64_ADDXri:
			strRefType = "arm64_addxri"; break;
		/* The input reference is from an ARM64::LDRXui instruction. */
		case LLVMDisassembler_ReferenceType_In_ARM64_LDRXui:
			strRefType = "arm64_ldrxui"; break;
		/* The input reference is from an ARM64::LDRXl instruction. */
		case LLVMDisassembler_ReferenceType_In_ARM64_LDRXl:
			strRefType = "arm64_ldrxl"; break;
		/* The input reference is from an ARM64::ADR instruction. */
		case LLVMDisassembler_ReferenceType_In_ARM64_ADR:
			strRefType = "arm64_adr"; break;
	}
#endif

	//printf("%s(refval:%llx reftype:%s)\n", __func__, ReferenceValue,
	//	strRefType);

	*ReferenceType = LLVMDisassembler_ReferenceType_InOut_None;
	return NULL;
}

int disasm_single(
	/* in parameters */
	uint8_t *src, int src_len,
	uint64_t addr,
	/* out parameters */
	string &result, int &instrLen,
	/* internal */
	LLVMDisasmContextRef context)
{
	int rc = -1;

	char buf[1024] = {0};

	instrLen = LLVMDisasmInstruction(
		context, /* disasm context */
		src, /* source data */
		src_len, /* length of source data */
		addr, /* address */
		buf, /* output buf */
		sizeof(buf) /* size of output buf */
	);

	if(instrLen <= 0)
	{
		//printf("%04X: undefined?\n", offs);
		goto cleanup;
	}

	result = buf;

	rc = 0;
	cleanup:
	return rc;
}

/* disassemble a single instruction from the start of an input buffer */
int BNLlvmServicesDisassembleSingle(
	/* in parameters */
	const char *triplet,
	uint8_t *src, int src_len,
	uint64_t addr,
	/* out parameters */
	string &result, int &instrLen)
{
	int rc = -1;
	LLVMDisasmContextRef context = NULL;

	/* see /lib/MC/MCDisassembler/Disassembler.h */
	context = LLVMCreateDisasm (
		triplet, /* triple */
		NULL, /* void *DisInfo */
		0, /* TagType */
		NULL, /* LLVMOpInfoCallback GetOpInfo */
		symbol_lookup_cb /* LLVMSymbolLookupCallback SymbolLookUp */
	);

	if(context == NULL) {
		//printf("ERROR: LLVMCreateDisasm()\n");
		goto cleanup;
	}

	if(0 != disasm_single(src, src_len, addr, result, instrLen, context))
	{
		//printf("ERROR: disasm_single()\n");
		goto cleanup;
	}

	rc = 0;
	cleanup:
	if(context) {
		LLVMDisasmDispose(context);
		context = NULL;
	}
	return rc;
}

int BNLlvmServicesDisassembleLengths(
	/* in parameters */
	const char *triplet,
	uint8_t *src, int src_len,
	uint64_t addr,
	/* out parameters */
	vector<int> &lengths)
{
	int rc = -1;
	int length;
	string result;
	LLVMDisasmContextRef context = NULL;

	/* see /lib/MC/MCDisassembler/Disassembler.h */
	context = LLVMCreateDisasm (
		triplet, /* triple */
		NULL, /* void *DisInfo */
		0, /* TagType */
		NULL, /* LLVMOpInfoCallback GetOpInfo */
		symbol_lookup_cb /* LLVMSymbolLookupCallback SymbolLookUp */
	);

	if(!context)
	{
		//printf("ERROR: LLVMCreateDisasm()\n");
		goto cleanup;
	}

	lengths.clear();
	for(int i=0; i<src_len; )
	{
		if(disasm_single(src+i, src_len-i, addr+i, result, length, context))
		{
			if(0)
			{
				//printf("ERROR: disasm_single()\n");
				goto cleanup;
			}
			else
			{
				/* make it best effort */
				break;
			}
		}

		//printf("%s(): %s has length %d\n", __func__, result.c_str(), length);

		lengths.push_back(length);
		i += length;
	}

	rc = 0;
	cleanup:
	if(context) {
		LLVMDisasmDispose(context);
		context = NULL;
	}
	return rc;
}

int main(int ac, char **av)
{
	char *output;
	int out_len = 0;
	char *error = NULL;
	int err_len = 0;

	int rc;

	rc = BNLlvmServicesAssemble(
		"mov x0, x0",
		LLVM_SVCS_DIALECT_UNSPEC, 
		"aarch64-none-none",
		LLVM_SVCS_CM_DEFAULT, /* code model */
		LLVM_SVCS_RM_STATIC, /* reloc model */
		&output, &out_len,
		&error, &err_len
	);

	if(rc || err_len) {
		printf("ERROR %d: %s\n", rc, error);
		return -1;
	}

	dump_bytes((uint8_t *)output, out_len, 0);
	return 0;
}
