#include <stdio.h>
#include <stdlib.h>

#include <string>

#include "llvm/MC/MCAsmBackend.h"
#include "llvm/MC/MCAsmInfo.h"
#include "llvm/MC/MCContext.h"
#include "llvm/MC/MCInstPrinter.h"
#include "llvm/MC/MCInstrInfo.h"
#include "llvm/MC/MCObjectFileInfo.h"
#include "llvm/MC/MCParser/AsmLexer.h"
#include "llvm/MC/MCTargetAsmParser.h"
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

// globals
std::string TripleName; // eg: x86_64-apple-darwin14.5.0
std::string ArchName;
Triple TheTriple;

const Target *
GetTarget(const char *ProgName) {
    // Figure out the target triple.
    if (TripleName.empty())
        TripleName = llvm::sys::getDefaultTargetTriple();
    TheTriple = Triple(Triple::normalize(TripleName));

    // Get the target specific parser.
    std::string Error;
    const Target *TheTarget = TargetRegistry::lookupTarget(ArchName, TheTriple,
            Error);
    if (!TheTarget) {
        errs() << ProgName << ": " << Error;
        return nullptr;
    }

    // Update the triple name and return the found target.
    TripleName = TheTriple.getTriple();
    return TheTarget;
}

int AssembleInput(
    const char *ProgName,
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
    errs() << ProgName
           << ": error: this target does not support assembly parsing.\n";
    return 1;
  }

  Parser->setTargetParser(*TAP);

  int Res = Parser->Run(true);

  return Res;
}

int main(int ac, char **av)
{
    const Target *TheTarget;
    SourceMgr SrcMgr;

    LLVMInitializeAllTargetInfos();
    LLVMInitializeAllTargetMCs();
    LLVMInitializeAllDisassemblers();

    // arg0:
    // llvm::Target encapsulating the "x86_64-apple-darwin14.5.0" information 
    TheTarget = GetTarget(av[0]);
    if (!TheTarget) {
        return -1;
    }
    printf("Got target: %s\n", TripleName.c_str()); // eg: x86_64-apple-darwin14.5.0
    printf("Got arch: %s\n", ArchName.c_str());

    // arg1:
    // llvm::SourceMgr (Support/SourceMgr.h) that holds assembler source
    // has vector of llvm::SrcBuffer encaps (Support/MemoryBuffer.h) and vector of include dirs
    std::string asmSrc = "push ebp";
    std::unique_ptr<MemoryBuffer> memBuf = MemoryBuffer::getMemBuffer(asmSrc);
    SrcMgr.AddNewSourceBuffer(std::move(memBuf), SMLoc());

    // arg2: the machine code context
    std::unique_ptr<MCRegisterInfo> MRI(TheTarget->createMCRegInfo(TripleName));
    std::unique_ptr<MCAsmInfo> MAI(TheTarget->createMCAsmInfo(*MRI, TripleName));
    MCObjectFileInfo MOFI;
    MCContext Ctx(MAI.get(), MRI.get(), &MOFI, &SrcMgr);
    MOFI.InitMCObjectFileInfo(TheTriple, Reloc::Default, CodeModel::Default, Ctx);

    // arg3: the streamer
    //
    // this is the assembler interface
    // -methods per .s statements (emit bytes, handle directive, etc.)
    // -remembers current section
    // -implementations that write a .s, or .o in various formats
    //
    //   1. the output stream ... a formatted_raw_ostream wraps a raw_ostream to provide
    //   tracking of line and column position for padding and shit
    //
    //   but raw_ostream is abstract and is implemented by raw_fd_ostream, raw_string_ostream, etc.
    std::string strOutput;
    raw_string_ostream rso(strOutput);
    formatted_raw_ostream fro(rso);
    std::unique_ptr<::formatted_raw_ostream> pfro(&fro);

    MCInstrInfo *MCII = TheTarget->createMCInstrInfo(); /* describes target instruction set */
    /* code emitter needs 1) instruction set info 2) register info */
    MCCodeEmitter *CE = TheTarget->createMCCodeEmitter(*MCII, *MRI, Ctx);
    MCAsmBackend *MAB = TheTarget->createMCAsmBackend(*MRI, TripleName, /* specific CPU */ "");
    MCStreamer *mcs = TheTarget->createAsmStreamer(
        Ctx, /* the MC context */
        std::move(pfro), /* output stream (type: std::unique_ptr<formatted_raw_ostream> from Support/FormattedStream.h) */
        true, /* isVerboseAsm */
        false, /* useDwarfDirectory */
        NULL, /* if given, the instruction printer to use (else, MCInstr representation is used) */
        CE, /* if given, a code emitter used to show instruction encoding inline with the asm */
        MAB,  /* the AsmBackend, (fixups, relaxation, objs and elfs) */
        true /* ShowInst (show encoding) */
    );

    //AssembleInput(av[0], TheTarget, SrcMgr, Ctx, *Str, *MAI, *STI,
    //    *MCII, MCOptions);

    return 0;
}
