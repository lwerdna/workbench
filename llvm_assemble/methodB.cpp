#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#include <string>

#include "llvm/MC/MCAsmBackend.h"
#include "llvm/MC/MCAsmInfo.h"
#include "llvm/MC/MCContext.h"
#include "llvm/MC/MCInstPrinter.h"
#include "llvm/MC/MCInstrInfo.h"
#include "llvm/MC/MCObjectFileInfo.h"
#include "llvm/MC/MCParser/AsmLexer.h"
#include "llvm/MC/MCParser/MCTargetAsmParser.h"
#include "llvm/MC/MCRegisterInfo.h"
#include "llvm/MC/MCSectionMachO.h"
#include "llvm/MC/MCStreamer.h"
#include "llvm/MC/MCSubtargetInfo.h"
#include "llvm/MC/MCTargetOptionsCommandFlags.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Compression.h"
#include "llvm/Support/FileUtilities.h"
#include "llvm/Support/FormattedStream.h"

#include "llvm/Support/Host.h" // for getDefaultTargetTriple();

#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/ToolOutputFile.h"

#include "help.h"

// globals
std::string ArchName;

int AssembleInput(
    const Target *TheTarget,
    SourceMgr &SrcMgr, 
    MCContext &Ctx, 
    MCStreamer &Str,
    MCAsmInfo &MAI, 
    MCSubtargetInfo &STI,
    MCInstrInfo &MCII, 
    MCTargetOptions &MCOptions
) {
  std::unique_ptr<MCAsmParser> Parser(createMCAsmParser(SrcMgr, Ctx, Str, MAI));
  std::unique_ptr<MCTargetAsmParser> TAP(TheTarget->createMCAsmParser(STI, *Parser, MCII, MCOptions));

  if (!TAP) {
    errs() << ": error: this target does not support assembly parsing.\n";
    return 1;
  }

  Parser->setTargetParser(*TAP);

  // AsmParser::Run in lib/MC/MCParser/AsmParser.cpp
  /* first param is NoInitialTextSection
		by supplying false -> YES initial text section (we don't have to do .text) */
  int Res = Parser->Run(false);

  return Res;
}

int main(int ac, char **av)
{
    SourceMgr SrcMgr;

    //LLVMInitializeX86TargetInfo();
    llvm::InitializeAllTargetInfos();
    //LLVMInitializeX86AsmParser();
    llvm::InitializeAllTargetMCs();
    //LLVMInitializeX86TargetMC();
    llvm::InitializeAllAsmParsers();
    //LLVMInitializeX86AsmParser();
    llvm::InitializeAllDisassemblers();
    //LLVMInitializeX86Disassembler();

    // arg0:
    // llvm::Target encapsulating the "x86_64-apple-darwin14.5.0" information 

    // see /lib/Support/Triple.cpp for the details
    //spec = llvm::sys::getDefaultTargetTriple();
    //std::string machSpec = "x86_64-apple-windows"; // will produce a COFF
    //std::string machSpec = "x86_64-apple-darwin14.5.0"; // will produce a Mach-O
    std::string machSpec = "arm-none-none-eabi"; //
    //std::string machSpec = "x86_64-apple-darwin";
    //std::string machSpec = "x86_64-thumb-linux-gnu";
    //std::string machSpec = "x86_64-unknown-linux-gnu";
    printf("machine spec: %s\n", machSpec.c_str());
    machSpec = Triple::normalize(machSpec);
    printf("machine spec (normalized): %s\n", machSpec.c_str());
    Triple TheTriple(machSpec);

    // Get the target specific parser.
    std::string Error;
    const Target *TheTarget = TargetRegistry::lookupTarget(/*arch*/"", TheTriple, Error);
    if (!TheTarget) {
        errs() << Error;
        return -1;
    }

    machSpec = TheTriple.getTriple();
    printf("machine spec (returned): %s\n", machSpec.c_str());
    
    printf("Target.getName(): %s\n", TheTarget->getName());
    printf("Target.getShortDescription(): %s\n", TheTarget->getShortDescription());

    /* from the target we get almost everything */
    std::unique_ptr<MCRegisterInfo> MRI(TheTarget->createMCRegInfo(machSpec));
    std::unique_ptr<MCAsmInfo> MAI(TheTarget->createMCAsmInfo(*MRI, machSpec));
    std::unique_ptr<MCInstrInfo> MCII(TheTarget->createMCInstrInfo()); /* describes target instruction set */
    MCSubtargetInfo *STI = TheTarget->createMCSubtargetInfo(machSpec, "", ""); /* subtarget instr set */
    MCAsmBackend *MAB = TheTarget->createMCAsmBackend(*MRI, machSpec, /* specific CPU */ "");

    // arg0:
    // llvm::SourceMgr (Support/SourceMgr.h) that holds assembler source
    // has vector of llvm::SrcBuffer encaps (Support/MemoryBuffer.h) and vector of include dirs
    //std::string asmSrc = ".org 0x100, 0xAA\nfoo:\nxor %eax, %ebx\npush %rbp\njmp foo\nrdtsc\n";
	//std::string asmSrc = ".text\n" "ldr pc, data_foo\n" "\n" "data_foo:\n" "    .int 0x8\n" "\n" "loop:\n" "b loop\n";
	//std::string asmSrc = ".text\n" "mov r2, r1\n";
	std::string asmSrc = ".text\n" "ldr pc, data_foo\n" "data_foo:\n" ".int 0x8\n" "loop:\n" "b loop\n";

    std::unique_ptr<MemoryBuffer> memBuf = MemoryBuffer::getMemBuffer(asmSrc);
    SrcMgr.AddNewSourceBuffer(std::move(memBuf), SMLoc());

    // arg1: the machine code context
    MCObjectFileInfo MOFI;
    MCContext Ctx(MAI.get(), MRI.get(), &MOFI, &SrcMgr);
    MOFI.InitMCObjectFileInfo(TheTriple, Reloc::Default, CodeModel::Default, Ctx);

    // this is the assembler interface
    // -methods per .s statements (emit bytes, handle directive, etc.)
    // -remembers current section
    // -implementations that write a .s, or .o in various formats
    //
    //   1. the output stream ... a formatted_raw_ostream wraps a raw_ostream to provide
    //   tracking of line and column position for padding and shit
    //
    //   but raw_ostream is abstract and is implemented by raw_fd_ostream, raw_string_ostream, etc.

	/* output stream:
		raw_svector_ostream is a raw_pwrite_stream is a raw_ostream
		since a SmallString is SmallVector (svector) we can use this and 
		retrieve bytes later with its .data() method */
	SmallString<1024> smallString;
    raw_svector_ostream rso(smallString);

    /* code emitter needs 1) instruction set info 2) register info */
    MCCodeEmitter *CE = TheTarget->createMCCodeEmitter(*MCII, *MRI, Ctx);

    MCStreamer *as = TheTarget->createMCObjectStreamer(
		TheTriple, /* Triple */	
        Ctx, /* the MCContext */
        *MAB,  /* the AsmBackend, (fixups, relaxation, objs and elfs) */
        rso, /* output stream raw_pwrite_stream */
        CE, /* code emitter */
		*STI, /* subtarget info */
		true, /* relax all fixups */
		true, /* incremental linker compatible */ 
        false /* DWARFMustBeAtTheEnd */
    );

    std::string abi = "none";
    MCTargetOptions toptions;
    toptions.MCUseDwarfDirectory = false;
    toptions.ABIName = abi;

    printf("trying to assemble, let's go..\n");
    AssembleInput(TheTarget, SrcMgr, Ctx, *as, *MAI, *STI,
        *MCII, toptions);
	printf("done with AssembleInput()\n");

	/* dump to file for debugging */
	FILE *fp;
	fp = fopen("out.bin", "wb");
	fwrite(smallString.data(), 1, smallString.size(), fp);
	fclose(fp);

	//int n = smallString.size();
	int codeOffset=0, codeSize = 0;
	char *data = smallString.data();
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
	else if(0==memcmp(data, "\x7F" "ELF\x01\x01\x01\x00", 8)) {
		/* assume four sections: NULL, .strtab, .text, .symtab */
		uint32_t e_shoff = *(uint32_t *)(data + 0x20);
		uint32_t sh_offset = *(uint32_t *)(data + e_shoff + 2*0x28 + 0x10); /* second shdr */
		uint32_t sh_size = *(uint32_t *)(data + e_shoff + 2*0x28 + 0x14); /* second shdr */
		codeOffset = sh_offset;
		codeSize = sh_size;
	}
	else {
		printf("ERROR: couldn't identify type of output file\n");
	}
	
	dump_bytes((unsigned char *)data + codeOffset, codeSize, 0);

    return 0;
}
