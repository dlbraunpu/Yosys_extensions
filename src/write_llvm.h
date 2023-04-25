#ifndef WRITE_LLVM_H
#define WRITE_LLVM_H
  
// LLVM headers needed below
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Dominators.h"

// Without this, yosys.h gets confused by the above LLVM headers.  Strange!!!
// It seems to be caused by the identifier "ID" being used in clever ways by both packages.
#include "llvm/IR/PassManager.h"

// Yosys headers
#include "kernel/yosys.h"

#include "driver_tools.h"

class LLVMWriter {

public:

  struct Options {
    bool verbose_llvm_value_names = false;
    bool cell_based_llvm_value_names = true;
    bool simplify_and_or_gates = true;
    bool simplify_muxes = true;
    bool use_poison = false;
    bool support_hierarchy = false;
    bool support_pmux = false;
    bool optimize_muxes = false;
    int optimize_mux_threshold = -1;
  };

  LLVMWriter(Yosys::RTLIL::Design *des, const Options& options);
  ~LLVMWriter();

  void write_llvm_ir(Yosys::RTLIL::Module *unrolledRtlMod,
                      std::string targetName,  // As specified in allowed_target.txt
                      bool targetIsVec,       // target is ASV vector
                      std::string modName,  // from original Verilog, e.g. "M8080"
                      int num_cycles,
                      std::string llvmFileName,
                      std::string funcName);

  void clearFunctionData();

private:
  class DriverSpecHash {
  public:
    size_t operator() (const DriverSpec& ds) const { return ds.get_hash(); }
  };

  class ValueCache {
    public:
      void add(const DriverSpec& driver, llvm::Value *value);
      llvm::Value *find(const DriverSpec& driver, llvm::BasicBlock *bb);
      void updateDominance() { if (_func) _DT.recalculate(*_func); }
      void clear() { _mmap.clear(); _nHits = 0; _nMisses = 0; _func = nullptr; _DT.reset(); }
      size_t size() const { return _mmap.size(); }
      size_t nHits() const { return _nHits; }
      size_t nMisses() const { return _nMisses; }

    private:
      typedef std::unordered_multimap<DriverSpec, llvm::Value*, DriverSpecHash> MmapType;
      MmapType _mmap;

      size_t _nHits = 0;
      size_t _nMisses = 0;
      llvm::Function *_func;
      llvm::DominatorTree _DT;
  };


  Yosys::RTLIL::Design *design;
  std::unique_ptr<llvm::LLVMContext> c;
  std::unique_ptr<llvm::IRBuilder<>> b;
  llvm::Module *llvmMod;
  llvm::Function *llvmFunc;  // function being generated

  ValueCache valueCache;
  DriverFinder finder;
  Options opts;

  int pmuxIdx;


  llvm::IntegerType *llvmWidth(unsigned a);

  llvm::ArrayType *llvmArrayType(unsigned elemwidth, unsigned nelems);

  llvm::VectorType *llvmVectorType(unsigned elemwidth, unsigned nelems);

  // Dangerous: only supports up to 64 bits.
  llvm::ConstantInt *llvmInt(uint64_t val, unsigned width);


  // More useful
  llvm::ConstantInt *llvmZero(unsigned width);

  llvm::PoisonValue *llvmPoison(unsigned width);
  llvm::UndefValue *llvmUndef(unsigned width);
  llvm::Value * llvmUndefValue(unsigned width); // Considers Options

  unsigned getWidth(llvm::Type *ty);
  unsigned getWidth(llvm::Value *val);

  // Generate a value for a primary input 
  llvm::Value *generatePrimaryInputValue(Yosys::RTLIL::Wire *port);

  // Find or create a Value representing what drives the given input port of the given cell.
  llvm::Value *generateInputValue(Yosys::RTLIL::Cell *cell,
                                  Yosys::RTLIL::IdString port);

  llvm::Value* generateLoad(llvm::Value *array, unsigned elementWidth, unsigned idx,
                             std::string valueName);

  void generateStore(llvm::Value *array, unsigned idx, llvm::Value *val);

  // Helpers for generateCellOutputValue() below
  llvm::Value *generateSimplifiedAndCellOutputValue(llvm::Value *valA, llvm::Value *valB);
  llvm::Value *generateAndCellOutputValue(llvm::Value *valA, llvm::Value *valB);
  llvm::Value *generateUnaryCellOutputValue(Yosys::RTLIL::Cell *cell);
  llvm::Value *generateBinaryCellOutputValue(Yosys::RTLIL::Cell *cell);
  llvm::Value *generateSimplifiedMuxCellOutputValue(Yosys::RTLIL::Cell *cell);
  llvm::Value *generateMuxCellOutputValue(Yosys::RTLIL::Cell *cell);
  llvm::Value *generatePmuxCellOutputValue(Yosys::RTLIL::Cell *cell);

  llvm::Value *generateMagicCellOutputValue(Yosys::RTLIL::Cell *cell,
                                            Yosys::RTLIL::IdString port);

  llvm::Value *generateFFCellOutputValue(Yosys::RTLIL::Cell *cell);

  llvm::Value *
  generateUserDefinedCellOutputValue(Yosys::RTLIL::Cell *cell,
                                     Yosys::RTLIL::IdString port);

  // Create a Value representing the output port of the given cell.
  // Since this is not given a DriverSpec, it does not touch the valueCache.
  // The caller is reponsible for that.
  // TODO: Should it instead make a temporary DriverSpec to access the valueCache?
  llvm::Value *generateCellOutputValue(Yosys::RTLIL::Cell *cell,
                                       Yosys::RTLIL::IdString port);


  // Generate the value of the given chunk, which is constant, or a
  // slice of a single wire or cell output.  The result will be offset
  // by the given amount, and zero-extended to totalWidth.
  llvm::Value *generateChunkValue(const DriverChunk& chunk,
                             int totalWidth, int offset);


  llvm::Value *generateValue(const DriverSpec& dSpec);


  // The wire represents a target ASV, and is not NOT necessarily a port
  llvm::Value *generateDestValue(Yosys::RTLIL::Wire *wire);

  llvm::Type* getLlvmType(Yosys::RTLIL::Wire *port);

  llvm::Function*
  generateFunctionDecl(const std::string& funcName, Yosys::RTLIL::Module *mod,
                       const Yosys::dict<std::string, unsigned>& targetVectors,
                       int retWidth, int retVecSize);

  llvm::Function*
  writeMainFunction(Yosys::RTLIL::Module *unrolledRtlMod,
                    std::string targetName,  // As specified in allowed_target.txt
                    bool targetIsVec,       // target is ASV vector
                    int num_cycles,
                    std::string funcName);

  bool isProperSubModule(Yosys::RTLIL::Module *mod);

  llvm::Function*
  generateSubFunctionDecl(Yosys::RTLIL::Module *mod,
                          Yosys::RTLIL::Wire *returnPort);

  std::string
  getSubFunctionName(Yosys::RTLIL::Module *submod,
                     Yosys::RTLIL::IdString returnPortName);


  llvm::Function*
  writeSubFunction(Yosys::RTLIL::Module *submod,
                   Yosys::RTLIL::IdString returnPortName);

  void
  writeSubFunctions(Yosys::RTLIL::Module *submod);

  void
  recurseSubFunctions(Yosys::RTLIL::Module *mod);


};


#endif
