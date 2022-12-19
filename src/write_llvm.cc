#include "write_llvm.h"
  
// LLVM headers (many more than needed)
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"

// Yosys headers
#include "kernel/yosys.h"
//#include "kernel/rtlil.h"

USING_YOSYS_NAMESPACE  // Does "using namespace"

// Copied from check_regs.cpp 
#define llvmWidth(a, c) llvm::IntegerType::get(*c, a)
#define llvmInt(val, width, c) llvm::ConstantInt::get(llvmWidth(width, c), val, false);


llvm::Value *generateValue(RTLIL::Wire *wire,
                           std::shared_ptr<llvm::LLVMContext> c,
                           std::shared_ptr<llvm::IRBuilder<>> b)
{
  // TMP: Just return an arbitrary constant
  return llvm::ConstantInt::get(llvmWidth(wire->width, c), 123, false);
  
  //return llvmInt(123, wire->width, c);
}



void write_llvm_ir(RTLIL::Module *unrolledRtlMod, std::string modName, std::string destName, std::string llvmFileName) {


  std::shared_ptr<llvm::LLVMContext> TheContext = std::make_unique<llvm::LLVMContext>();

  std::shared_ptr<llvm::Module> TheModule =
          std::make_unique<llvm::Module>("mod_"+modName+"_"+destName, *TheContext);

  std::shared_ptr<llvm::IRBuilder<>> Builder = std::make_unique<llvm::IRBuilder<>>(*TheContext);


  // Get the yosys RTLIL object representing the destination ASV.
  std::string wireName = "\\"+destName + "_#1";
  RTLIL::Wire *destWire = unrolledRtlMod->wire(wireName);
  if (!destWire) {
    assert(false);
  }


  std::vector<llvm::Type *> argTy;
  // for now, two 32-bit args
  argTy.push_back(llvm::IntegerType::get(*TheContext, 32));
  argTy.push_back(llvm::IntegerType::get(*TheContext, 32));

  // for now, a return type of the desired width
  llvm::Type* retTy = llvm::IntegerType::get(*TheContext, destWire->width);


  // This function type definition is suitable for TheFunction 
  llvm::FunctionType *FT =
    llvm::FunctionType::get(retTy, argTy, false);

  //std::string destSimpleName = funcExtract::var_name_convert(destName, true);

  // Create the main function
  llvm::Function::LinkageTypes linkage = llvm::Function::ExternalLinkage;

  llvm::Function *TheFunction = llvm::Function::Create(FT, linkage,
                    "instr_"+destName, TheModule.get());
                    //destInfo.get_instr_name()+"_"+destSimpleName, TheModule.get());

  // Set the function's arg's names
  TheFunction->getArg(0)->setName("arg0");
  TheFunction->getArg(1)->setName("arg1");

  // basic block
  llvm::BasicBlock *BB = llvm::BasicBlock::Create(*TheContext, "bb_;_"+destName, TheFunction);
  Builder->SetInsertPoint(BB);

  // All the real work happens here 
  llvm::Value *destValue = generateValue(destWire, TheContext, Builder);

  llvm::Instruction* retInst = Builder->CreateRet(destValue);


  llvm::verifyFunction(*TheFunction);
  llvm::verifyModule(*TheModule);

  std::string Str;
  llvm::raw_string_ostream OS(Str);
  OS << *TheModule;
  OS.flush();

  std::ofstream output(llvmFileName);
  output << Str << std::endl;
  output.close();

}
