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

#include "util.h"
#include "driver_tools.h"

USING_YOSYS_NAMESPACE  // Does "using namespace"

// Copied from check_regs.cpp 
#define llvmWidth(a, c) llvm::IntegerType::get(*c, a)
#define llvmInt(val, width, c) llvm::ConstantInt::get(llvmWidth(width, c), val, false);



class ValueTable {
  public:
    void add(llvm::Value*value, const DriverSpec& driver);
    llvm::Value *find(const DriverSpec& driver);
    void clear() { _dict.clear(); }

  private:
    dict<DriverSpec, llvm::Value*> _dict;
};


void ValueTable::add(llvm::Value*value, const DriverSpec& driver)
{
  log_assert (_dict.find(driver) == _dict.end());  // Not already there
  _dict[driver] = value;
}

llvm::Value *ValueTable::find(const DriverSpec& driver)
{
  auto pos = _dict.find(driver);
  if (pos == _dict.end())  {
    return nullptr;
  }
  return pos->second;
}


static ValueTable valueTable;

static DriverFinder finder;


// Create a Value representing the output port of the given cell.
llvm::Value *generateValue(RTLIL::Cell *cell, const RTLIL::IdString& port,
                           std::shared_ptr<llvm::LLVMContext> c,
                           std::shared_ptr<llvm::IRBuilder<>> b)
{

  log("generateValue(): cell port %s %s  width %d:\n", cell->name.c_str(), port.c_str(), cell->getPort(port).size());
  log_assert(cell->output(port));

  DriverSpec dSpec;
  finder.buildDriverOf(cell, port, dSpec);

  // Print what drives the bits of this cell port

  // TODO: Add the DriverSpec and its created Value to the valueTable.

  log_driverspec(dSpec);

  return nullptr;
}


// Generate the value of the given chunk, which is constant, or a
// slice of a single wire or cell output.  The result will be offset
// by the given amount, and zero-extended to totalWidth.
llvm::Value *generateValue(const DriverChunk& dChunk,
                           int totalWidth, int offset,
                           std::shared_ptr<llvm::LLVMContext> c,
                           std::shared_ptr<llvm::IRBuilder<>> b)
{
  assert(totalWidth >= dChunk.size() + offset);

  if (dChunk.isData()) {
    // Sanity checks
    log_assert(dChunk.offset == 0);
    log_assert(dChunk.size() == dChunk.data.size());

    // Build a string of the desired ones and zeros, with 0 padding
    // at the beginning and/or end.

    std::string valStr = RTLIL::Const(dChunk.data).as_string();
    log_assert(valStr.size() == dChunk.size());

    // Check for unwanted x
    for (char& c : valStr) {
      if (c == 'x') {
        log_warning("x-ish driver chunk found: %s\n", valStr.c_str());
        break;
      }
    }

    // Clean up.
    for (char& c : valStr) {
      if (c == 'x') c = '0';
    }

    if (offset > 0) {
      valStr += std::string('0', offset);
    }

    if (totalWidth > dChunk.size() + offset) {
      valStr = std::string('0', totalWidth - chunk.size() - offset) + valStr;
    }
    log_assert(valStr.size() == totalWidth);

    // Don't bother putting pure constants in the valueTable
    return llvm::ConstantInt::get(llvmWidth(totalWidth, c), llvm::StringRef(valStr), 2 /*radix*/);
  }

  // OK, we have a slice of a wire or cell output.

  if (offset == 0) {
    // See if we already have a Value for this object slice
    DriverSpec tmpDs(dChunk);
    llvm::Value *val = valueTable.find(tmpDs);
    if (val) {
     if (offset == 0 && totalWidth == dChunk.size()) {
        return val;  // We already have exactly what we need!

  } 

  if (dChunk.is_wire()) {
    // A slice of a wire, representing a module input port.
    // Their values should have been pre-created as function args.

    llvm::Value *val = valueTable.find(dSpec);
    log_assert(val);
    if (val) {
      return val;  // Should normally be the case
    }
    return nullptr;

  } else if (dSpec.is_cell()) {
    // An entire cell output.
    RTLIL::IdString portName;
    RTLIL::Cell *cell = dSpec.as_cell(portName);
    return generateValue(cell, portName, c, b);

  } else if (dSpec.is_fully_const()) {
    // valStr will be like "01101011010".
    std::string valStr = dSpec.as_const().as_string();

    // Ideally there would not be explicit 'x' values here!
    // The optimizaiton and cleanup already done should have gotten rid of most of them.
    if (!dSpec.is_fully_def()) {
      log_warning("x-ish driver spec found: %s\n", valStr.c_str());

      // Clean up.
      for (char& c : valStr) {
        if (c == 'x') c = '0';
      }
    }

    // Don't bother putting pure constants in the valueTable
    return llvm::ConstantInt::get(llvmWidth(dSpec.size(), c), llvm::StringRef(valStr), 2 /*radix*/);


llvm::Value *generateValue(const DriverSpec& dSpec,
                           std::shared_ptr<llvm::LLVMContext> c,
                           std::shared_ptr<llvm::IRBuilder<>> b)
{
  if (dSpec.is_wire()) {
    // An entire wire, representing a module input port.
    // Their values should have been pre-created as function args.
    llvm::Value *val = valueTable.find(dSpec);
    if (val) {
      return val;  // Should normally be the case
    }
    log_assert(false);
    return nullptr;

  } else if (dSpec.is_cell()) {
    // An entire cell output.
    RTLIL::IdString portName;
    RTLIL::Cell *cell = dSpec.as_cell(portName);
    return generateValue(cell, portName, c, b);

  } else if (dSpec.is_fully_const()) {
    // valStr will be like "01101011010".
    std::string valStr = dSpec.as_const().as_string();

    // Ideally there would not be explicit 'x' values here!
    // The optimizaiton and cleanup already done should have gotten rid of most of them.
    if (!dSpec.is_fully_def()) {
      log_warning("x-ish driver spec found: %s\n", valStr.c_str());

      // Clean up.
      for (char& c : valStr) {
        if (c == 'x') c = '0';
      }
    }

    // Don't bother putting pure constants in the valueTable
    return llvm::ConstantInt::get(llvmWidth(dSpec.size(), c), llvm::StringRef(valStr), 2 /*radix*/);

  } else {
    // A complex driverSpec: a mix of wires, ports, and constants (or slices of them).
    // Generate each chunk's value with the proper offset, and OR them together.

    log("generateValue for complex Driverspec\n");
    log_driverspec(dSpec);


    std::Vector<llvm::Value*> values;
    int offset = 0;
    for (const DriverChunk& chunk : dSpec.chunks()) {
      log_driverchunk(chunk);
      values.push_back(generateValue(chunk, offset, c, b);
      offset += chunk->size();
    }

    return llvm::ConstantInt::get(llvmWidth(dSpec.size(), c), 123, false);  // TMP
  }
}



// The wire represents a target ASV, and is not NOT necessarily a port
llvm::Value *generateDestValue(RTLIL::Wire *wire,
                           std::shared_ptr<llvm::LLVMContext> c,
                           std::shared_ptr<llvm::IRBuilder<>> b)
{

  log("RTLIL Wire %s:\n", wire->name.c_str());
  my_log_wire(wire);

  // Collect the drivers of each bit of the wire
  DriverSpec dSpec;
  finder.buildDriverOf(wire, dSpec);

  // Print what drives the bits of this wire
  log_driverspec(dSpec);
  log("\n");

  return generateValue(dSpec, c, b);
}



llvm::Function*
generateFunctionDecl(RTLIL::Module *mod, std::shared_ptr<llvm::Module> TheModule,
                           RTLIL::Wire *destWire,
                           std::shared_ptr<llvm::LLVMContext> c)
{
  std::vector<llvm::Type *> argTy;

  // Add every module input port, which includes the first-cycle ASV inputs
  // and the unrolled copies of the original input ports.
  for (const RTLIL::IdString& portname : mod->ports) {
    RTLIL::Wire *port = mod->wire(portname);
    log_assert(port);
    if (port->port_input) {
      argTy.push_back(llvm::IntegerType::get(*c, port->width));
    }
  }


  // A return type of the correct width
  llvm::Type* retTy = llvm::IntegerType::get(*c, destWire->width);


  llvm::FunctionType *functype =
    llvm::FunctionType::get(retTy, argTy, false);


  // Strip off the "\" from the wire name.
  std::string destName = destWire->name.str().substr(1);

  // Create the main function
  llvm::Function::LinkageTypes linkage = llvm::Function::ExternalLinkage;

  llvm::Function *func = llvm::Function::Create(functype, linkage,
                    "instr_"+destName, TheModule.get());
                    //destInfo.get_instr_name()+"_"+destSimpleName, TheModule.get());

  // Set the function's arg's names, and add them to the valueTable
  unsigned n = 0;
  for (const RTLIL::IdString& portname : mod->ports) {
    RTLIL::Wire *port = mod->wire(portname);
    if (port->port_input) {
      llvm::Argument *arg = func->getArg(n);
      arg->setName(portname.str());
      valueTable.add(arg, DriverSpec(port));
      n++;
    }
  }

  return func;

}



void write_llvm_ir(RTLIL::Module *unrolledRtlMod, std::string modName, std::string destName, std::string llvmFileName)
{


  log("Building DriverFinder\n");
  finder.build(unrolledRtlMod);
  log("Built DriverFinder\n");
  log("%ld objects\n", finder.size());


  std::shared_ptr<llvm::LLVMContext> llvmContext = std::make_unique<llvm::LLVMContext>();

  std::shared_ptr<llvm::Module> TheModule =
          std::make_unique<llvm::Module>("mod_"+modName+"_"+destName, *llvmContext);

  std::shared_ptr<llvm::IRBuilder<>> Builder = std::make_unique<llvm::IRBuilder<>>(*llvmContext);

  // Get the yosys RTLIL object representing the destination ASV.
  // TODO: Map the original Verilog register name to the actual wire name.
  std::string wireName = "\\" + destName + "_#1";
  RTLIL::Wire *destWire = unrolledRtlMod->wire(wireName);
  if (!destWire) {
    log_error("Can't find wire for destination ASV %s\n", destName.c_str());
    log_assert(false);
  }

  llvm::Function *func = generateFunctionDecl(unrolledRtlMod, TheModule, destWire, llvmContext);

  // basic block
  llvm::BasicBlock *BB = llvm::BasicBlock::Create(*llvmContext, "bb_;_"+destName, func);
  Builder->SetInsertPoint(BB);

  // All the real work happens here 
  llvm::Value *destValue = generateDestValue(destWire, llvmContext, Builder);

  // Testing code:  Print sources of every cell input
  for (auto cell : unrolledRtlMod->cells()) {
    for (auto& conn : cell->connections()) {
      // conn.first is the signal IdString, conn.second is its SigSpec
      if (cell->input(conn.first)) {
        DriverSpec dSpec;
        finder.buildDriverOf(conn.second, dSpec);
        generateValue(dSpec, llvmContext, Builder);
        log("\n");
      }
    }
  }


  llvm::Instruction* retInst = Builder->CreateRet(destValue);


  llvm::verifyFunction(*func);
  llvm::verifyModule(*TheModule);

  std::string Str;
  llvm::raw_string_ostream OS(Str);
  OS << *TheModule;
  OS.flush();

  std::ofstream output(llvmFileName);
  output << Str << std::endl;
  output.close();

  finder.clear();  // Only becasue it is static
  valueTable.clear();  // TODO make a proper class for this stuff

}

