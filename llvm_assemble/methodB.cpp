#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#include <string>
using namespace std;

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
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/ToolOutputFile.h"

using namespace llvm;

#include "help.h"

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
  unique_ptr<MCAsmParser> Parser(createMCAsmParser(SrcMgr, Ctx, Str, MAI));
  unique_ptr<MCTargetAsmParser> TAP(TheTarget->createMCAsmParser(STI, *Parser, MCII, MCOptions));

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
    //string machSpec = "x86_64-apple-windows"; // will produce a COFF
    //string machSpec = "x86_64-apple-darwin14.5.0"; // will produce a Mach-O
    string machSpec = "arm-none-none-eabi"; //
    //string machSpec = "x86_64-apple-darwin";
    //string machSpec = "x86_64-thumb-linux-gnu";
    //string machSpec = "x86_64-unknown-linux-gnu";
    printf("machine spec: %s\n", machSpec.c_str());
    machSpec = Triple::normalize(machSpec);
    printf("machine spec (normalized): %s\n", machSpec.c_str());
    Triple TheTriple(machSpec);

    // Get the target specific parser.
    string errStr;
    const Target *TheTarget = TargetRegistry::lookupTarget(/*arch*/"", TheTriple, errStr);
    if (!TheTarget) {
        errs() << errStr;
        return -1;
    }

    machSpec = TheTriple.getTriple();
    printf("machine spec (returned): %s\n", machSpec.c_str());
    
    printf("Target.getName(): %s\n", TheTarget->getName());
    printf("Target.getShortDescription(): %s\n", TheTarget->getShortDescription());

    /* from the target we get almost everything */
    unique_ptr<MCRegisterInfo> MRI(TheTarget->createMCRegInfo(machSpec));
    unique_ptr<MCAsmInfo> MAI(TheTarget->createMCAsmInfo(*MRI, machSpec, MCTargetOptions()));
    unique_ptr<MCInstrInfo> MCII(TheTarget->createMCInstrInfo()); /* describes target instruction set */
    MCSubtargetInfo *STI = TheTarget->createMCSubtargetInfo(machSpec, "", ""); /* subtarget instr set */
    MCAsmBackend *MAB = TheTarget->createMCAsmBackend(*MRI, machSpec, /* specific CPU */ "");

    // arg0:
    // llvm::SourceMgr (Support/SourceMgr.h) that holds assembler source
    // has vector of llvm::SrcBuffer encaps (Support/MemoryBuffer.h) and vector of include dirs
    //string asmSrc = ".org 0x100, 0xAA\nfoo:\nxor %eax, %ebx\npush %rbp\njmp foo\nrdtsc\n";
	//string asmSrc = ".text\n" "ldr pc, data_foo\n" "\n" "data_foo:\n" "    .int 0x8\n" "\n" "loop:\n" "b loop\n";
	//string asmSrc = ".text\n" "mov r2, r1\n";
	//string asmSrc = ".text\n" "ldr pc, data_foo\n" "data_foo:\n" ".int 0x8\n" "loop:\n" "b loop\n";

	string asmSrc;
	if(readTextFileToString("arm.s", asmSrc, errStr)) {
		errs() << errStr;
		return -1;
	}
	printf("assembling:\n%s\n", asmSrc.c_str());

    unique_ptr<MemoryBuffer> memBuf = MemoryBuffer::getMemBuffer(asmSrc);
    SrcMgr.AddNewSourceBuffer(move(memBuf), SMLoc());

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
		false, /* relax all fixups */
		false, /* incremental linker compatible */ 
        false /* DWARFMustBeAtTheEnd */
    );

    string abi = "none";
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
	/* ELF, 32-bit, little-end */
	else if(0==memcmp(data, "\x7F" "ELF\x01\x01\x01\x00", 8)) {
		/* possibilities:
			- four sections: NULL, .strtab, .text, .symtab 
			- five sections: NULL, .strtab, .text, .rel.text, .symtab */
		uint32_t e_shoff = *(uint32_t *)(data + 0x20);
		uint16_t e_shnum = *(uint16_t *)(data + 0x30);
		uint32_t txt_offs = *(uint32_t *)(data + e_shoff + 2*0x28 + 0x10); /* second shdr */
		uint32_t txt_size = *(uint32_t *)(data + e_shoff + 2*0x28 + 0x14); /* second shdr */
		codeOffset = txt_offs;
		codeSize = txt_size;

		if(e_shnum == 5) {
			/* we have relocations, uh oh */
			uint32_t rel_offs = *(uint32_t *)(data + e_shoff + 3*0x28 + 0x10);
			uint32_t rel_size = *(uint32_t *)(data + e_shoff + 3*0x28 + 0x14);
			uint32_t sym_offs = *(uint32_t *)(data + e_shoff + 4*0x28 + 0x10);
			uint32_t sym_size = *(uint32_t *)(data + e_shoff + 4*0x28 + 0x14);
			/* parse relocations */
			for(uint32_t i=0; i<rel_size; i+=8) {
				uint32_t d_val = *(uint32_t *)(data + rel_offs + i);
				uint32_t d_ptr = *(uint32_t *)(data + rel_offs + i + 4);
				/* if R_ARM_CALL */
				if((d_ptr & 0xFF) == 0x1C) {
					uint8_t sym_idx = (d_ptr & 0xFF00) >> 8;
					if(sym_idx >= (sym_size / 16)) continue;
					uint32_t st_value = *(uint32_t *)(data + sym_offs + 16*sym_idx + 4);
					/* at d_val we should find a bl/blx (0xEB/0xFA) */
					uint32_t instr = *(uint32_t *)(data + txt_offs + d_val);
					/* remember pc bias of +8 and this is 4-byte instr count */
					int32_t displ = (st_value - (d_val + 8)) / 4;
					/* modify the instr operand: 3 byte displacement */
					instr = (instr & 0xFF000000) | (displ & 0xFFFFFF);
					*(uint32_t *)(data + txt_offs + d_val) = instr;
				}
			}
		}
	}
	else {
		printf("ERROR: couldn't identify type of output file\n");
	}
	
	dump_bytes((unsigned char *)data + codeOffset, codeSize, 0);

    return 0;
}
