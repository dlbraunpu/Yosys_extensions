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
  assert (_dict.find(driver) == _dict.end());  // Not already there
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

  log("RTLIL cell port %s %s  width %d:\n", cell->name.c_str(), port.c_str(), cell->getPort(port).size());

  DriverSpec dSpec;
  finder.buildDriverOf(cell, port, dSpec);

  // Print what drives the bits of this cell port

  // TODO: Add the DriverSpec and its created Value to the valueTable.

  log_driverspec(dSpec);

  return nullptr;
}


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
    assert(false);
    return nullptr;

  } else if (dSpec.is_cell()) {
    // An entire cell output.
    RTLIL::IdString portName;
    RTLIL::Cell *cell = dSpec.as_cell(portName);
    return generateValue(cell, portName, c, b);

  } else if (dSpec.is_fully_const()) {
    // We do not expect to see explicit 'x' values here!
    assert(dSpec.is_fully_def());

    // valStr will be like "01101011010".
    std::string valStr = dSpec.as_const().as_string();

    // Don't bother putting pure constants in the valueTable
    return llvm::ConstantInt::get(llvmWidth(dSpec.size(), c), llvm::StringRef(valStr), 2 /*radix*/);

  } else {
    // A complex driverSpec: a mix of wires, ports, and constants (or slices of them).
    // Generate each chunk's value with the proper offset, and OR them together.

    log("generateValue for complex Driverspec\n");
    log_driverspec(dSpec);
    for (const DriverChunk& chunk : dSpec.chunks()) {
      log_driverchunk(chunk);
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
    assert(port);
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
    assert(false);
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
        generateValue(cell, conn.first, llvmContext, Builder);
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

