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
#include "kernel/sigtools.h"
#include "backends/rtlil/rtlil_backend.h"

#include "driver_tools.h"

USING_YOSYS_NAMESPACE  // Does "using namespace"

// Copied from check_regs.cpp 
#define llvmWidth(a, c) llvm::IntegerType::get(*c, a)
#define llvmInt(val, width, c) llvm::ConstantInt::get(llvmWidth(width, c), val, false);


void my_log_sigspec(const RTLIL::SigSpec& sig)
{
  std::stringstream buf;
  RTLIL_BACKEND::dump_sigspec(buf, sig, false);
  log("sigspec: %s\n", buf.str().c_str());
}



void my_log_sigbit(const RTLIL::SigBit& bit)
{
  if (bit.is_wire()) {
    log("sigbit type wire %s offset %d\n", bit.wire->name.c_str(), bit.offset);
  } else {
    log("sigbit type constant %d\n", bit.data);
  }
}


void my_log_wire(const RTLIL::Wire *wire)
{
  log("wire %s  width %d  start_offset %d  port_id %d  input %d  output %d\n", wire->name.c_str(),
      wire->width, wire->start_offset, wire->port_id, wire->port_input, wire->port_output);

}


static DriverFinder finder;


llvm::Value *generateValue(RTLIL::Wire *wire,
                           std::shared_ptr<llvm::LLVMContext> c,
                           std::shared_ptr<llvm::IRBuilder<>> b)
{

  log_debug("RTLIL Wire %s:\n", wire->name.c_str());
  my_log_wire(wire);

  DriverSpec dSpec;
  finder.buildDriverOf(wire, dSpec);

  // Print what drives the bits of this wire

  log_debug("Drivers of each bit:\n");

  int bitnum = 0;
  for (auto& dBit : dSpec.to_driverbit_vector()) {
    if (dBit.is_data()) {
      log("%2d constant value %d\n", bitnum, dBit.data);
    } else if (dBit.is_wire()) {
        log("%2d wire %s [%d]\n", bitnum, dBit.wire->name.c_str(), dBit.offset);
    } else if (dBit.is_cell()) {
        log("%2d cell %s port %s [%d]\n",
            bitnum, dBit.cell->name.c_str(), dBit.port.c_str(), dBit.offset);
    } else {
      log("%2d ?????\n", bitnum);
    }
    bitnum++;
  }


  // TMP: Just return an arbitrary constant
  return llvm::ConstantInt::get(llvmWidth(wire->width, c), 123, false);
  
  //return llvmInt(123, wire->width, c);
}



void write_llvm_ir(RTLIL::Module *unrolledRtlMod, std::string modName, std::string destName, std::string llvmFileName)
{


  log_debug("Building DriverFinder\n");
  finder.build(unrolledRtlMod);
  log_debug("Built DriverFinder\n");
  log_debug("%ld objects\n", finder.size());


  std::shared_ptr<llvm::LLVMContext> TheContext = std::make_unique<llvm::LLVMContext>();

  std::shared_ptr<llvm::Module> TheModule =
          std::make_unique<llvm::Module>("mod_"+modName+"_"+destName, *TheContext);

  std::shared_ptr<llvm::IRBuilder<>> Builder = std::make_unique<llvm::IRBuilder<>>(*TheContext);


  // Get the yosys RTLIL object representing the destination ASV.
  // TODO: Map the original Verilog register name to the actual wire name.
  std::string wireName = destName + "_#1";
  RTLIL::Wire *destWire = unrolledRtlMod->wire(wireName);
  if (!destWire) {
    log_error("Can't find wire for destination ASV %s\n", destName.c_str());
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

  finder.clear();  // Only becasue it is static

}

