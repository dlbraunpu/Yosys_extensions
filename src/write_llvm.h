#ifndef WRITE_LLVM_H
#define WRITE_LLVM_H
  
// LLVM headers needed below
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Value.h"

// Without this, yosys.h gets confused by the above LLVM headers.  Strange!!!
// It seems to be caused by the identifier "ID" being used in clever ways by both packages.
#include "llvm/IR/PassManager.h"


// Yosys headers
#include "kernel/yosys.h"


// Struct to specify a particular bit of a particular port of a particular cell.
// BTW, all the built-in cells have only one output, named "\Y"
struct CellPortBit {
  Yosys::RTLIL::Cell *cell;
  Yosys::RTLIL::IdString port;
  int bit;
};

// Struct to specify a particular bit of a particular wire
struct WireBit {
  Yosys::RTLIL::Wire *wire;
  int bit;
};


void my_log_sigspec(const Yosys::RTLIL::SigSpec& sig);
void my_log_sigbit(const Yosys::RTLIL::SigBit& bit);

void buildSignalMaps(Yosys::RTLIL::Module *module);

WireBit *getDrivingWire(const Yosys::RTLIL::SigBit& sigbit);

CellPortBit *getDrivingCell(const Yosys::RTLIL::SigBit& sigbit);

llvm::Value *generateValue(Yosys::RTLIL::Wire *wire,
                           std::shared_ptr<llvm::LLVMContext> c,
                           std::shared_ptr<llvm::IRBuilder<>> b);


void write_llvm_ir(Yosys::RTLIL::Module *unrolledRtlMod,
                   std::string modName, std::string destName, std::string llvmFileName);

#endif
