#define _CRT_SECURE_NO_WARNINGS
#define NOMINMAX

#include <signal.h>

#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <mutex>
#include <string>
#include <tuple>
#include <unordered_map>

#include "binaryninjaapi.h"
#include "lowlevelilinstruction.h"
#include "mediumlevelilinstruction.h"

using namespace BinaryNinja;
using namespace std;

#if defined(_MSC_VER)
#define snprintf _snprintf
#endif


BN_DECLARE_CORE_ABI_VERSION

extern "C" void hook_core_function_advancedSelector(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_advancedSelector()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_advancedSelector()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_processAnalysisSkip(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_processAnalysisSkip()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_processAnalysisSkip()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_basicAnalysis(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_basicAnalysis()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_basicAnalysis()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_modeSelector(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_modeSelector()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_modeSelector()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_advancedAnalysis(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_advancedAnalysis()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_advancedAnalysis()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_generateMediumLevelIL(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_generateMediumLevelIL()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_generateMediumLevelIL()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_runFunctionRecognizers(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_runFunctionRecognizers()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_runFunctionRecognizers()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_update(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_update()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_update()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_fullAnalysis(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_fullAnalysis()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_fullAnalysis()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_analyzeIndirectBranches(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_analyzeIndirectBranches()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_analyzeIndirectBranches()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_translateTailCalls(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_translateTailCalls()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_translateTailCalls()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_generateLiftedIL(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_generateLiftedIL()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_generateLiftedIL()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_processConstantPointerReferences(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_processConstantPointerReferences()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_processConstantPointerReferences()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_analyzeCallsites(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_analyzeCallsites()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_analyzeCallsites()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_controlFlowAnalysis(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_controlFlowAnalysis()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_controlFlowAnalysis()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_analyzeCallTypes(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_analyzeCallTypes()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_analyzeCallTypes()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_checkForReturnWithBasicBlocksOnly(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_checkForReturnWithBasicBlocksOnly()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_checkForReturnWithBasicBlocksOnly()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_propagateAnalysis(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_propagateAnalysis()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_propagateAnalysis()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_analyzeTailCalls(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_analyzeTailCalls()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_analyzeTailCalls()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_analyzeDataVariables(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_analyzeDataVariables()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_analyzeDataVariables()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_analyzeConstantReferences(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_analyzeConstantReferences()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_analyzeConstantReferences()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_defaultAnalysis(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_defaultAnalysis()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_defaultAnalysis()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_commitAnalysisData(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_commitAnalysisData()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_commitAnalysisData()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_module_freeAllUnusedAdvancedAnalysisData(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function) {
		printf("0x%" PRIx64 " hook_core_module_freeAllUnusedAdvancedAnalysisData()\n", function->GetStart());
	} else {
		printf("???????? hook_core_module_freeAllUnusedAdvancedAnalysisData()\n");
		//return;
	}
		
	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc) {
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
	}
}

extern "C" void hook_core_function_concurrent_advancedAnalysis(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_concurrent_advancedAnalysis()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_concurrent_advancedAnalysis()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_resetIndirectBranchesOnFullUpdate(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_resetIndirectBranchesOnFullUpdate()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_resetIndirectBranchesOnFullUpdate()\n");
		//return;
	}

	printf("you know it\n");

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedIL();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_analyzeStackVariableReferences(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_analyzeStackVariableReferences()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_analyzeStackVariableReferences()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_analyzeCachedIndirectStructureReferences(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_analyzeCachedIndirectStructureReferences()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_analyzeCachedIndirectStructureReferences()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_finishUpdate(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_finishUpdate()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_finishUpdate()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_findStringReferences(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_findStringReferences()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_findStringReferences()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_analyzeStackAdjustment(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_analyzeStackAdjustment()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_analyzeStackAdjustment()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_runCompletionCallbacks(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_runCompletionCallbacks()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_runCompletionCallbacks()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_generateHighLevelIL(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_generateHighLevelIL()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_generateHighLevelIL()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_analyzeAndExpandFlags(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_analyzeAndExpandFlags()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_analyzeAndExpandFlags()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_checkForPureFunction(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_checkForPureFunction()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_checkForPureFunction()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_analyzeHLILTypeReferences(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_analyzeHLILTypeReferences()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_analyzeHLILTypeReferences()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_intermediateAnalysis(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_intermediateAnalysis()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_intermediateAnalysis()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_basicBlockAnalysis(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_basicBlockAnalysis()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_basicBlockAnalysis()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_analyzeMLILTypeReferences(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_analyzeMLILTypeReferences()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_analyzeMLILTypeReferences()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_processCompletionState(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_processCompletionState()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_processCompletionState()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_checkForReturn(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_checkForReturn()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_checkForReturn()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" void hook_core_function_analyzeSystemCalls(Ref<AnalysisContext> analysisContext)
{
	Ref<Function> function = analysisContext->GetFunction();
	if(function)
		printf("0x%" PRIx64 " hook_core_function_analyzeSystemCalls()\n", function->GetStart());
	else {
		printf("???????? hook_core_function_analyzeSystemCalls()\n");
		//return;
	}

	Ref<LowLevelILFunction> liftedFunc = function->GetLiftedILIfAvailable();
	if(liftedFunc)
		printf("Lifted IL instruction count is: %zu\n", liftedFunc->GetInstructionCount());
}

extern "C" BINARYNINJAPLUGIN bool CorePluginInit()
{
	printf("WFHook CorePluginInit()\n");
	bool rc = false;

	Ref<Workflow> wf = Workflow::Instance()->Clone("WFHookWorkflow");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.generateLiftedIL", &hook_core_function_generateLiftedIL));
	wf->Insert("core.function.generateLiftedIL", "extension.WFHook.core.function.generateLiftedIL");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.analyzeDataVariables", &hook_core_function_analyzeDataVariables));
	wf->Insert("core.function.analyzeDataVariables", "extension.WFHook.core.function.analyzeDataVariables");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.checkForPureFunction", &hook_core_function_checkForPureFunction));
	wf->Insert("core.function.checkForPureFunction", "extension.WFHook.core.function.checkForPureFunction");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.advancedAnalysis", &hook_core_function_advancedAnalysis));
	wf->Insert("core.function.advancedAnalysis", "extension.WFHook.core.function.advancedAnalysis");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.analyzeAndExpandFlags", &hook_core_function_analyzeAndExpandFlags));
	wf->Insert("core.function.analyzeAndExpandFlags", "extension.WFHook.core.function.analyzeAndExpandFlags");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.analyzeConstantReferences", &hook_core_function_analyzeConstantReferences));
	wf->Insert("core.function.analyzeConstantReferences", "extension.WFHook.core.function.analyzeConstantReferences");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.analyzeStackVariableReferences", &hook_core_function_analyzeStackVariableReferences));
	wf->Insert("core.function.analyzeStackVariableReferences", "extension.WFHook.core.function.analyzeStackVariableReferences");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.processConstantPointerReferences", &hook_core_function_processConstantPointerReferences));
	wf->Insert("core.function.processConstantPointerReferences", "extension.WFHook.core.function.processConstantPointerReferences");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.checkForReturnWithBasicBlocksOnly", &hook_core_function_checkForReturnWithBasicBlocksOnly));
	wf->Insert("core.function.checkForReturnWithBasicBlocksOnly", "extension.WFHook.core.function.checkForReturnWithBasicBlocksOnly");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.resetIndirectBranchesOnFullUpdate", &hook_core_function_resetIndirectBranchesOnFullUpdate));
	wf->Insert("core.function.resetIndirectBranchesOnFullUpdate", "extension.WFHook.core.function.resetIndirectBranchesOnFullUpdate");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.finishUpdate", &hook_core_function_finishUpdate));
	wf->Insert("core.function.finishUpdate", "extension.WFHook.core.function.finishUpdate");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.analyzeIndirectBranches", &hook_core_function_analyzeIndirectBranches));
	wf->Insert("core.function.analyzeIndirectBranches", "extension.WFHook.core.function.analyzeIndirectBranches");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.concurrent.advancedAnalysis", &hook_core_function_concurrent_advancedAnalysis));
	wf->Insert("core.function.concurrent.advancedAnalysis", "extension.WFHook.core.function.concurrent.advancedAnalysis");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.propagateAnalysis", &hook_core_function_propagateAnalysis));
	wf->Insert("core.function.propagateAnalysis", "extension.WFHook.core.function.propagateAnalysis");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.translateTailCalls", &hook_core_function_translateTailCalls));
	wf->Insert("core.function.translateTailCalls", "extension.WFHook.core.function.translateTailCalls");

	wf->RegisterActivity(new Activity("extension.WFHook.core.module.freeAllUnusedAdvancedAnalysisData", &hook_core_module_freeAllUnusedAdvancedAnalysisData));
	wf->Insert("core.module.freeAllUnusedAdvancedAnalysisData", "extension.WFHook.core.module.freeAllUnusedAdvancedAnalysisData");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.analyzeSystemCalls", &hook_core_function_analyzeSystemCalls));
	wf->Insert("core.function.analyzeSystemCalls", "extension.WFHook.core.function.analyzeSystemCalls");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.basicBlockAnalysis", &hook_core_function_basicBlockAnalysis));
	wf->Insert("core.function.basicBlockAnalysis", "extension.WFHook.core.function.basicBlockAnalysis");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.generateHighLevelIL", &hook_core_function_generateHighLevelIL));
	wf->Insert("core.function.generateHighLevelIL", "extension.WFHook.core.function.generateHighLevelIL");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.runCompletionCallbacks", &hook_core_function_runCompletionCallbacks));
	wf->Insert("core.function.runCompletionCallbacks", "extension.WFHook.core.function.runCompletionCallbacks");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.advancedSelector", &hook_core_function_advancedSelector));
	wf->Insert("core.function.advancedSelector", "extension.WFHook.core.function.advancedSelector");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.fullAnalysis", &hook_core_function_fullAnalysis));
	wf->Insert("core.function.fullAnalysis", "extension.WFHook.core.function.fullAnalysis");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.analyzeHLILTypeReferences", &hook_core_function_analyzeHLILTypeReferences));
	wf->Insert("core.function.analyzeHLILTypeReferences", "extension.WFHook.core.function.analyzeHLILTypeReferences");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.analyzeStackAdjustment", &hook_core_function_analyzeStackAdjustment));
	wf->Insert("core.function.analyzeStackAdjustment", "extension.WFHook.core.function.analyzeStackAdjustment");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.findStringReferences", &hook_core_function_findStringReferences));
	wf->Insert("core.function.findStringReferences", "extension.WFHook.core.function.findStringReferences");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.analyzeCallsites", &hook_core_function_analyzeCallsites));
	wf->Insert("core.function.analyzeCallsites", "extension.WFHook.core.function.analyzeCallsites");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.analyzeTailCalls", &hook_core_function_analyzeTailCalls));
	wf->Insert("core.function.analyzeTailCalls", "extension.WFHook.core.function.analyzeTailCalls");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.analyzeCallTypes", &hook_core_function_analyzeCallTypes));
	wf->Insert("core.function.analyzeCallTypes", "extension.WFHook.core.function.analyzeCallTypes");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.controlFlowAnalysis", &hook_core_function_controlFlowAnalysis));
	wf->Insert("core.function.controlFlowAnalysis", "extension.WFHook.core.function.controlFlowAnalysis");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.basicAnalysis", &hook_core_function_basicAnalysis));
	wf->Insert("core.function.basicAnalysis", "extension.WFHook.core.function.basicAnalysis");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.runFunctionRecognizers", &hook_core_function_runFunctionRecognizers));
	wf->Insert("core.function.runFunctionRecognizers", "extension.WFHook.core.function.runFunctionRecognizers");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.update", &hook_core_function_update));
	wf->Insert("core.function.update", "extension.WFHook.core.function.update");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.analyzeCachedIndirectStructureReferences", &hook_core_function_analyzeCachedIndirectStructureReferences));
	wf->Insert("core.function.analyzeCachedIndirectStructureReferences", "extension.WFHook.core.function.analyzeCachedIndirectStructureReferences");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.analyzeMLILTypeReferences", &hook_core_function_analyzeMLILTypeReferences));
	wf->Insert("core.function.analyzeMLILTypeReferences", "extension.WFHook.core.function.analyzeMLILTypeReferences");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.commitAnalysisData", &hook_core_function_commitAnalysisData));
	wf->Insert("core.function.commitAnalysisData", "extension.WFHook.core.function.commitAnalysisData");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.intermediateAnalysis", &hook_core_function_intermediateAnalysis));
	wf->Insert("core.function.intermediateAnalysis", "extension.WFHook.core.function.intermediateAnalysis");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.processAnalysisSkip", &hook_core_function_processAnalysisSkip));
	wf->Insert("core.function.processAnalysisSkip", "extension.WFHook.core.function.processAnalysisSkip");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.modeSelector", &hook_core_function_modeSelector));
	wf->Insert("core.function.modeSelector", "extension.WFHook.core.function.modeSelector");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.processCompletionState", &hook_core_function_processCompletionState));
	wf->Insert("core.function.processCompletionState", "extension.WFHook.core.function.processCompletionState");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.generateMediumLevelIL", &hook_core_function_generateMediumLevelIL));
	wf->Insert("core.function.generateMediumLevelIL", "extension.WFHook.core.function.generateMediumLevelIL");

	wf->RegisterActivity(new Activity("extension.WFHook.core.function.checkForReturn", &hook_core_function_checkForReturn));
	wf->Insert("core.function.checkForReturn", "extension.WFHook.core.function.checkForReturn");

	Workflow::RegisterWorkflow(wf, "");

	rc = true;

	cleanup:
	printf("WFHook CorePluginInit() returning %d\n", rc);
	return rc;
}
