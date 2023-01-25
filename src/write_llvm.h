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

#include "driver_tools.h"

class LLVMWriter {

private:

  class ValueCache {
    public:
      void add(llvm::Value*value, const DriverSpec& driver);
      llvm::Value *find(const DriverSpec& driver);
      void clear() { _dict.clear(); }
      size_t size() { return _dict.size(); }

    private:
      Yosys::dict<DriverSpec, llvm::Value*> _dict;
  };


  std::shared_ptr<llvm::IRBuilder<>> b;
  std::shared_ptr<llvm::LLVMContext> c;
  std::shared_ptr<llvm::Module> llvmMod;



  ValueCache valueCache;
  DriverFinder finder;


  llvm::IntegerType *llvmWidth(unsigned a);


  // Dangerous: only supports up to 64 bits.
  llvm::ConstantInt *llvmInt(uint64_t val, unsigned width);


  // More useful
  llvm::ConstantInt *llvmZero(unsigned width);



  // Find or create a Value representing what drives the given input port of the given cell.
  llvm::Value *generateInputValue(Yosys::RTLIL::Cell *cell,
                                  Yosys::RTLIL::IdString port);


  // Helpers for generateCellOutputValue() below
  llvm::Value *generateUnaryCellOutputValue(Yosys::RTLIL::Cell *cell);
  llvm::Value *generateBinaryCellOutputValue(Yosys::RTLIL::Cell *cell);
  llvm::Value *generateMuxCellOutputValue(Yosys::RTLIL::Cell *cell);
  llvm::Value *generatePmuxCellOutputValue(Yosys::RTLIL::Cell *cell);


  // Create a Value representing the output port of the given cell.
  // Since this is not given a DriverSpec, it does not touch the valueCache.
  // The caller is reponsible for that.
  // TODO: Should it instead make a temporary DriverSpec to access the valueCache?
  llvm::Value *generateCellOutputValue(Yosys::RTLIL::Cell *cell,
                                       Yosys::RTLIL::IdString port);


  // Generate the value of the given chunk, which is constant, or a
  // slice of a single wire or cell output.  The result will be offset
  // by the given amount, and zero-extended to totalWidth.
  llvm::Value *generateValue(const DriverChunk& chunk,
                             int totalWidth, int offset);


  llvm::Value *generateValue(const DriverSpec& dSpec);


  // The wire represents a target ASV, and is not NOT necessarily a port
  llvm::Value *generateDestValue(Yosys::RTLIL::Wire *wire);


  llvm::Function*
  generateFunctionDecl(const std::string& funcName, Yosys::RTLIL::Module *mod,
                       Yosys::RTLIL::Wire *targetPort);


public:
  LLVMWriter();
  ~LLVMWriter();

  void write_llvm_ir(Yosys::RTLIL::Module *unrolledRtlMod,
                     Yosys::RTLIL::Wire *targetPort,
                     std::string modName, 
                     std::string instrName,
                     std::string targetName,
                     std::string llvmFileName);

  void reset();

};


#endif
