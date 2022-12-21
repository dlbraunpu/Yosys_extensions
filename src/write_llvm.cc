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



// Maps:
// 1:  A SigSpec to its canonical SigSpec
// 2: A SigBit to its canonical SigBit
// 3: A Wire to its canonical SigSpec
SigMap sigmap;


dict<RTLIL::SigBit, CellPortBit> canonical_sigbit_to_driving_cell_table;
dict<RTLIL::SigBit, WireBit> canonical_sigbit_to_driving_wire_table;


void buildSignalMaps(RTLIL::Module *module)
{
  sigmap.clear();
  sigmap.set(module);
  canonical_sigbit_to_driving_cell_table.clear();

  for (auto cell : module->cells()) {
    for (auto& conn : cell->connections()) {
      // conn.first is the signal IdString, conn.second is its SigSpec
      if (cell->output(conn.first)) {
        RTLIL::SigSpec canonical_sig = sigmap(conn.second);
        //log("\nCell %s port %s -> ", cell->name.c_str(),  conn.first.c_str());
        //my_log_sigspec(conn.second);
        //log("\ncanonical: ");
        //my_log_sigspec(canonical_sig);
        int idx = 0;
        for (auto& bit : canonical_sig.to_sigbit_vector()) {
          // sigmap(conn.second) is the canonical SigSpec.
          // bit is a canonical SigBit
          //log("  ");
          //my_log_sigbit(bit);
          assert(bit.is_wire());  // A cell can't drive a constant!
          assert(canonical_sigbit_to_driving_cell_table.count(bit) == 0);
          canonical_sigbit_to_driving_cell_table.emplace(bit, CellPortBit{cell, conn.first, idx});
          ++idx;
        }
      }
    }
  }

  for (auto wire : module->wires()) {
    if (wire->port_input) {
      RTLIL::SigSpec canonical_sig = sigmap(wire);
      //log("\nport_input wire :\n");
      //my_log_wire(wire);
      //log("\ncanonical sigspec:\n");
      //my_log_sigspec(canonical_sig);
      int idx = 0;
      for (auto& bit : canonical_sig.to_sigbit_vector()) {
        // sigmap(wire) is the canonical SigSpec.
        // bit is a canonical SigBit
        assert(canonical_sigbit_to_driving_wire_table.count(bit) == 0);  // Multi-driven?
        canonical_sigbit_to_driving_wire_table.emplace(bit, WireBit{wire, idx});
        ++idx;
      }
    }
  }

}



WireBit *getDrivingWire(const RTLIL::SigBit& sigbit)
{
  RTLIL::SigBit canonicalSigbit = sigmap(sigbit);

  //log("getDrivingWire:  ");
  //my_log_sigbit(sigbit);
  //log("canonical:  ");
  //my_log_sigbit(canonicalSigbit);

  auto iter = canonical_sigbit_to_driving_wire_table.find(canonicalSigbit);
  if (iter != canonical_sigbit_to_driving_wire_table.end()) {
    return &(iter->second);
  }
  return nullptr;  // Not driven by a wire
}



CellPortBit *getDrivingCell(const RTLIL::SigBit& sigbit)
{
  RTLIL::SigBit canonicalSigbit = sigmap(sigbit);

  //log("getDrivingCell:  ");
  //my_log_sigbit(sigbit);
  //log("canonical:  ");
  //my_log_sigbit(canonicalSigbit);

  auto iter = canonical_sigbit_to_driving_cell_table.find(canonicalSigbit);
  if (iter != canonical_sigbit_to_driving_cell_table.end()) {
    return &(iter->second);
  }
  return nullptr;  // Not driven by a cell
}






llvm::Value *generateValue(RTLIL::Wire *wire,
                           std::shared_ptr<llvm::LLVMContext> c,
                           std::shared_ptr<llvm::IRBuilder<>> b)
{

  log_debug("RTLIL Wire %s:\n", wire->name.c_str());
  my_log_wire(wire);

  // Print what drives the bits of this wire
  RTLIL::SigSpec sigspec = sigmap(wire);

  log_debug("Drivers of each bit:\n");

  int bitnum = 0;
  for (auto& bit : sigspec.to_sigbit_vector()) {
    if (!bit.is_wire()) {
      log("%2d constant value %d\n", bitnum, bit.data);
    } else {
      WireBit *wb = getDrivingWire(bit);
      if (wb) {
        log("%2d wire %s [%d]\n", bitnum, wb->wire->name.c_str(), wb->bit);
      } else {
        CellPortBit *cpb = getDrivingCell(bit);
        if (cpb) {
          log("%2d cell %s port %s [%d]\n", bitnum, cpb->cell->name.c_str(), cpb->port.c_str(), cpb->bit);
        } else {
          log("%2d no connection!\n", bitnum);
        }
      }
    }
    bitnum++;
  }


  // TMP: Just return an arbitrary constant
  return llvm::ConstantInt::get(llvmWidth(wire->width, c), 123, false);
  
  //return llvmInt(123, wire->width, c);
}



void write_llvm_ir(RTLIL::Module *unrolledRtlMod, std::string modName, std::string destName, std::string llvmFileName)
{


  log_debug("Building signal maps\n");
  buildSignalMaps(unrolledRtlMod);
  log_debug("Built signal maps\n");
  log_debug("%ld cells, %ld wires\n",
             canonical_sigbit_to_driving_cell_table.size(),
             canonical_sigbit_to_driving_wire_table.size());


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

}

