//===- ClangBuildSelectLink.cpp  ------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This utility may be invoked in the following manner:
//  clang-build-select-link a.bc b.bc c.bc -o merged.bc
//
// This utility merges all the bc files, then build select_outline_wrapper
// which is a big switch statement that depends on hash values.
// Then it goes back and marks each external function as linkOnceODR
// so the optimnization pass will remove wrappers and external functions.
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/STLExtras.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/IR/AutoUpgrade.h"
#include "llvm/IR/DiagnosticInfo.h"
#include "llvm/IR/DiagnosticPrinter.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Linker/Linker.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/WithColor.h"
#include "llvm/Transforms/IPO/FunctionImport.h"
#include "llvm/Transforms/Utils/FunctionImportUtils.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/LegacyPassNameParser.h"
#include "llvm/Transforms/IPO/AlwaysInliner.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include <memory>
#include <utility>
using namespace llvm;

static cl::list<std::string> InputFilenames(cl::Positional, cl::OneOrMore,
                                            cl::desc("<input bitcode files>"));

static cl::opt<std::string> OutputFilename("o",
                                           cl::desc("Override output filename"),
                                           cl::init("-"),
                                           cl::value_desc("filename"));

static cl::opt<bool> Force("f", cl::desc("Enable binary output on terminals"));

static cl::opt<bool> Verbose("v",
                             cl::desc("Print information about actions taken"));

static ExitOnError ExitOnErr;

// Read bitcode file and return Module.
static std::unique_ptr<Module>
loadFile(const char *argv0, const std::string &FN, LLVMContext &Context) {
  SMDiagnostic Err;
  if (Verbose)
    errs() << "Loading '" << FN << "'\n";
  std::unique_ptr<Module> Result;
  Result = parseIRFile(FN, Err, Context);

  if (!Result) {
    Err.print(argv0, errs());
    return nullptr;
  }

  ExitOnErr(Result->materializeMetadata());
  UpgradeDebugInfo(*Result);

  return Result;
}

static bool linkFiles(const char *argv0, LLVMContext &Context, Linker &L,
                      const cl::list<std::string> &Files, unsigned Flags) {
  // Filter out flags that don't apply to the first file we load.
  unsigned ApplicableFlags = Flags & Linker::Flags::OverrideFromSrc;
  // Similar to some flags, internalization doesn't apply to the first file.
  for (const auto &File : Files) {
    std::unique_ptr<Module> M = loadFile(argv0, File, Context);
    if (!M.get()) {
      errs() << argv0 << ": ";
      WithColor::error() << " loading file '" << File << "'\n";
      return false;
    }
    if (Verbose)
      errs() << "Linking in '" << File << "'\n";
    bool Err = L.linkInModule(std::move(M), ApplicableFlags);
    if (Err)
      return false;

    // All linker flags apply to linking of subsequent files.
    ApplicableFlags = Flags;
  }
  return true;
}

static bool buildSelectFunction(Module *MOUT, LLVMContext &Ctx) {

  // Find select_outline_wrapper decl, because we are about to define it.
  llvm::IRBuilder<> Builder(Ctx);
  llvm::Function *Fn = MOUT->getFunction("select_outline_wrapper");
  if (!Fn) {
    if (Verbose)
      errs() << "No calls to select_outline_wrapper, skipping generation\n";
    return true;
  }

  llvm::BasicBlock *entry = llvm::BasicBlock::Create(Ctx, "entry", Fn, nullptr);
  llvm::BasicBlock *exitbb = llvm::BasicBlock::Create(Ctx, "exit", Fn, nullptr);
  Builder.SetInsertPoint(entry);
  llvm::BasicBlock *defaultbb =
      llvm::BasicBlock::Create(Ctx, "default", Fn, nullptr);
  Builder.SetInsertPoint(defaultbb);
  Builder.CreateBr(exitbb);
  SmallVector<llvm::Value *, 4> PArgs;
  for (auto &Arg : Fn->args())
    PArgs.push_back(&Arg);
  SmallVector<llvm::Value *, 4> CArgs = {PArgs[0], PArgs[1]};
  Builder.SetInsertPoint(entry);

  // Count and build list of global variables
  llvm::SmallVector<llvm::GlobalVariable *, 16> hashglobals;
  unsigned hash_count = 0;
  for (Module::global_iterator globi = MOUT->global_begin(),
                               e = MOUT->global_end();
       globi != e; ++globi) {
    GlobalVariable *GV = &*globi;
    if (GV->hasName()) {
      StringRef name = GV->getName();
      if (name.startswith("_HASHW_")) {
        hash_count++;
        hashglobals.push_back(GV);
      }
    }
  }

  // Create the switch statement
  llvm::SwitchInst *Switch =
      Builder.CreateSwitch(PArgs[2], defaultbb, hash_count);

  if (Verbose)
    errs() << "Generating function " << Fn->getName().str() << " with "
           << hash_count << " case(s). \n";

  // Build a switch case for each hashglobal to call the function
  for (llvm::GlobalVariable *GV : hashglobals) {
    StringRef wrapperName = GV->getName().substr(7);
    llvm::Function *F = MOUT->getFunction(wrapperName);
    if (!F) {
      llvm::errs() << "\n FATAL ERROR, could not find function:\n";
      llvm::errs() << wrapperName.str().c_str() << "\n";
      return false;
    }
    // Get the 64bit hash code from the GV to define the value for the case
    const APInt &value = GV->getInitializer()->getUniqueInteger();
    const uint64_t *rawvalue = value.getRawData();

    Builder.SetInsertPoint(entry);
    llvm::BasicBlock *BB =
        llvm::BasicBlock::Create(Ctx, "BB" + wrapperName, Fn, nullptr);
    Builder.SetInsertPoint(BB);

    // Create the call to the actual wrapper function for this case
    Builder.CreateCall(F, CArgs);
    Builder.CreateBr(exitbb);
    llvm::Value *val = llvm::ConstantInt::get(llvm::Type::getInt64Ty(Ctx),
                                              (long long)*rawvalue);
    Switch->addCase(cast<llvm::ConstantInt>(val), BB);
  }

  // Finish and verify the select_outline_wrapper function
  Builder.SetInsertPoint(exitbb);
  llvm::ReturnInst::Create(Ctx, nullptr, exitbb);
  Fn->setCallingConv(CallingConv::C);
  Fn->removeFnAttr(llvm::Attribute::OptimizeNone);
  Fn->addFnAttr(llvm::Attribute::AlwaysInline);
  Fn->setLinkage(llvm::GlobalValue::LinkOnceODRLinkage);
  if (llvm::verifyFunction(*Fn)) {
    llvm::errs() << "Error in verifying function:\n";
    llvm::errs() << Fn->getName().str().c_str() << "\n";
    return false;
  }

  return true;
}

static bool convertExternsToLinkOnce(Module *MOUT, LLVMContext &Ctx) {
  // Convert all external functions to LinkOnceODR so they get inlined
  // and removed by the optimizer in the next HIP driver step.
  // After next opt step, only kernels will exist
  for (Module::iterator i = MOUT->begin(), e = MOUT->end(); i != e; ++i) {
    llvm::Function *F = &*i;
#if 0
    if (F->hasName()) 
      printf("Function name : %s\n",F->getName().str().c_str());
#endif
    if (!i->isDeclaration() &&
        //      i->getLinkage() == GlobalValue::ExternalLinkage &&
        i->getCallingConv() != llvm::CallingConv::AMDGPU_KERNEL) {
      if (Verbose)
        errs() << "Converting function \'" << F->getName().str().c_str()
               << "\' to LinkOnceODRLinkage.\n";
      F->setLinkage(GlobalValue::LinkOnceODRLinkage);
      F->setVisibility(GlobalValue::ProtectedVisibility);
      F->removeFnAttr(llvm::Attribute::OptimizeNone);
      F->addFnAttr(llvm::Attribute::AlwaysInline);
    }
  }
  return true;
}

static bool runInliner(Module *MOUT, LLVMContext &Ctx) {
  legacy::PassManager PM;
  PassManagerBuilder Builder;
  Builder.Inliner = createAlwaysInlinerLegacyPass();
  Builder.populateModulePassManager(PM);
  PM.run(*MOUT);
  return true;
}

static bool removeStackSaveRestore(Module *MOUT, LLVMContext &Ctx) {
  StringRef fName("llvm.stacksave");
  llvm::Function *F = MOUT->getFunction(fName);
  if (F) {
    printf("\n\n FOUND stacksave \n");
    F->dump();
  }
  return true;
}

int main(int argc, char **argv) {
  InitLLVM InitX(argc, argv);
  ExitOnErr.setBanner(std::string(argv[0]) + ": ");

  LLVMContext Context;

  cl::ParseCommandLineOptions(argc, argv, "clang-build-select-link\n");

  auto Composite = make_unique<Module>("clang-build-select-link", Context);
  Linker L(*Composite);

  // unsigned Flags = Linker::Flags::LinkOnlyNeeded;
  unsigned Flags = Linker::Flags::None;

  if (!linkFiles(argv[0], Context, L, InputFilenames, Flags))
    return 1;

  Module *MOUT = &*Composite;
  if (!buildSelectFunction(MOUT, Context))
    return 1;

  if (!convertExternsToLinkOnce(MOUT, Context))
    return 1;

  if (!runInliner(MOUT, Context))
    return 1;

  if (!removeStackSaveRestore(MOUT, Context))
    return 1;

  std::error_code EC;
  ToolOutputFile Out(OutputFilename, EC, sys::fs::F_None);
  if (EC) {
    WithColor::error() << EC.message() << '\n';
    return 1;
  }

  if (verifyModule(*Composite, &errs())) {
    errs() << argv[0] << ": ";
    WithColor::error() << "linked module is broken!\n";
    return 1;
  }

  if (Verbose)
    errs() << "Writing merged bitcode...\n";

  WriteBitcodeToFile(*Composite, Out.os(), false);

  Out.keep();

  return 0;
}
