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


LLVMWriter::LLVMWriter()
{

}

LLVMWriter::~LLVMWriter()
{
}

void
LLVMWriter::reset()
{
  finder.clear();
  valueCache.clear();
}



llvm::IntegerType *
LLVMWriter::llvmWidth(unsigned a) {
  return llvm::IntegerType::get(*c, a);
}


// Dangerous: only supports up to 64 bits.
llvm::ConstantInt *
LLVMWriter::llvmInt(uint64_t val, unsigned width)
{
  return llvm::ConstantInt::get(llvmWidth(width), val, false);
}


// More useful
llvm::ConstantInt *
LLVMWriter::llvmZero(unsigned width)
{
  return llvm::ConstantInt::get(llvmWidth(width), 0, false);
}


void LLVMWriter::ValueCache::add(llvm::Value*value, const DriverSpec& driver)
{
  log_assert (_dict.find(driver) == _dict.end());  // Not already there
  _dict[driver] = value;
}

llvm::Value *LLVMWriter::ValueCache::find(const DriverSpec& driver)
{
  auto pos = _dict.find(driver);
  if (pos == _dict.end())  {
    return nullptr;
  }
  return pos->second;
}



// Find or create a Value representing what drives the given input port of the given cell.
llvm::Value *
LLVMWriter::generateInputValue(RTLIL::Cell *cell, const RTLIL::IdString& port)
{
  log_assert(cell->hasPort(port));
  log_assert(cell->input(port));

  DriverSpec dSpec;
  finder.buildDriverOf(cell->getPort(port), dSpec);

  // Get the Value for the input connection
  return generateValue(dSpec);
}




// Create a Value representing the output port of the given cell.
// Since this is not given a DriverSpec, it does not touch the valueCache.
// The caller is reponsible for that.
// TODO: Should it instead make a temporary DriverSpec to access the valueCache?
llvm::Value *
LLVMWriter::generateCellOutputValue(RTLIL::Cell *cell, const RTLIL::IdString& port)
{
  size_t numConns = cell->connections().size();

  log("generateCellOutputValue(): cell port %s %s  width %d:\n", cell->name.c_str(), port.c_str(), cell->getPort(port).size());
  log_assert(cell->output(port));

  // TODO: If \A or \B widths are bigger than their connections, zero
  // or sign-extend the input data.  Consider \SIGNED attributes
  // BTW, SigSpecs and Wires do not have any information about signed-ness

  // Here we handle only builtin cells.
  // Hierarchical modules are a different thing.
  log_assert(cell->name[0] == '$');
  log_assert(cell->type[0] == '$');
  log_assert(numConns >= 2);
  log_assert(numConns <= 4);

  log_assert(port == "\\Y");  // True for all built-in cells.
  unsigned widthY = (unsigned)(cell->getPort(port).size());

  // Get the Value at the first cell input
  RTLIL::IdString A("\\A");
  llvm::Value *valA = generateInputValue(cell, A);
  unsigned widthA = valA->getType()->getIntegerBitWidth();

  // A different case for each possible cell type (unary, binary, and muxes).

  if (numConns == 2) {

    // A unary operator. 
    // TODO: Sanity check: pin widths match driver/load widths.
    // Also that reduce cells have output width of 1.

    log_assert(widthY == widthA || widthY == 1);

    if (cell->type == "$not") {
      return b->CreateNot(valA);
    } else if (cell->type == "$pos") {
      return valA;
    } else if (cell->type == "$neg") {
      return b->CreateNeg(valA);
    } else if (cell->type == "$reduce_and") {
      return b->CreateICmpEQ(b->CreateNot(valA), llvmZero(widthA));
    } else if (cell->type == "$reduce_or" || cell->type == "$reduce_bool") {
      return b->CreateICmpNE(valA, llvmZero(widthA));
    } else if (cell->type == "$reduce_xor") {
      // A trickier operation: XOR, a parity calculation.
      // Need to declare and use the llvm.ctpop intrinsic function.
      std::vector<llvm::Type *> arg_type;
      arg_type.push_back(llvmWidth(widthA));
      llvm::Function *fun = llvm::Intrinsic::getDeclaration(llvmMod.get(), llvm::Intrinsic::ctpop, arg_type);
      llvm::Value *popcnt = b->CreateCall(fun, valA);
      return b->CreateTrunc(popcnt, llvmWidth(1));  // Return low-order bit
    } else if (cell->type == "$reduce_xnor") {
      // Same as reduce_xor, plus invert.
      std::vector<llvm::Type *> arg_type;
      arg_type.push_back(llvmWidth(widthA));
      llvm::Function *fun = llvm::Intrinsic::getDeclaration(llvmMod.get(), llvm::Intrinsic::ctpop, arg_type);
      llvm::Value *popcnt = b->CreateCall(fun, valA);
      return b->CreateNot(b->CreateTrunc(popcnt, llvmWidth(1)));  // Return inverted low-order bit
    } else if (cell->type == "$logic_not") {
      return b->CreateICmpEQ(valA, llvmZero(widthA));
    } 

    log_error("Unsupported unary cell %s\n", cell->type.c_str());
    return valA;

    // TODO: For the unary cells that output a logical value ($reduce_and,
    // $reduce_or, $reduce_xor, $reduce_xnor, $reduce_bool, $logic_not), when
    // the \Y_WIDTH parameter is greater than 1, the output is zero-extended,
    // and only the least significant bit varies.

  }

  // Get the Value at the second cell input
  RTLIL::IdString B("\\B");
  llvm::Value *valB = generateInputValue(cell, B);
  unsigned widthB = valB->getType()->getIntegerBitWidth();

  if (numConns == 3) {

    log_assert(widthY == widthA || widthY == 1);
    log_assert(widthA == widthB);

    if (cell->type == "$and") {
      return b->CreateAnd(valA, valB);
    } else if (cell->type == "$or") {
      return b->CreateOr(valA, valB);
    } else if (cell->type == "$xor") {
      return b->CreateXor(valA, valB);
    } else if (cell->type == "$xnor") {
      return b->CreateNot(b->CreateXor(valA, valB));
    } else if (cell->type == "$shl") {
      return b->CreateShl(valA, valB);
    } else if (cell->type == "$shr") {
      return b->CreateLShr(valA, valB);
    } else if (cell->type == "$sshl") {
      return b->CreateShl(valA, valB);  // Same as $shl
    } else if (cell->type == "$sshr") {
      return b->CreateAShr(valA, valB);
    } else if (cell->type == "$logic_and") {
      return b->CreateAnd(b->CreateICmpNE(valA, llvmZero(widthA)),
                          b->CreateICmpNE(valB, llvmZero(widthB)));
    } else if (cell->type == "$logic_or") {
      return b->CreateOr(b->CreateICmpNE(valA, llvmZero(widthA)),
                          b->CreateICmpNE(valB, llvmZero(widthB)));

      // TODO: $eqx, etc.  $pos

    } else if (cell->type == "$lt") {
      return b->CreateICmpULT(valA, valB);
    } else if (cell->type == "$le") {
      return b->CreateICmpULE(valA, valB);
    } else if (cell->type == "$eq") {
      return b->CreateICmpEQ(valA, valB);
    } else if (cell->type == "$ne") {
      return b->CreateICmpNE(valA, valB);
    } else if (cell->type == "$ge") {
      return b->CreateICmpUGE(valA, valB);
    } else if (cell->type == "$gt") {
      return b->CreateICmpUGT(valA, valB);
    } else if (cell->type == "$add") {
      return b->CreateAdd(valA, valB);
    } else if (cell->type == "$sub") {
      return b->CreateSub(valA, valB);
    } else if (cell->type == "$mul") {
      return b->CreateMul(valA, valB);
    } else if (cell->type == "$div") {
      return b->CreateUDiv(valA, valB);  // Needs work?
    } else if (cell->type == "$mod") {
      return b->CreateUDiv(valA, valB);

      // TODO: $shift and $shiftx, $divfloor, etc.
      // TODO: See above about logic operators with Y width > 1

    } 

    log_warning("Unsupported binary cell %s\n", cell->type.c_str());
    return valA;
  }

  // Get the Value at the third cell input
  RTLIL::IdString S("\\S");
  llvm::Value *valS = generateInputValue(cell, S);
  unsigned widthS = valS->getType()->getIntegerBitWidth();

  if (numConns == 4) {
    // Muxes
    log_assert(widthY == widthA);
    log_assert(widthA == widthB);
    log_assert(widthS == 1);

    if (cell->type == "$mux") {
      return b->CreateSelect(valS, valA, valB);
    } else if (cell->type == "$pmux") {
      log_warning("Unsupported pmux cell %s\n", cell->type.c_str());
      return valA;
    } else if (cell->type == "$tribuf") {
      log_warning("Unsupported tribuf cell %s\n", cell->type.c_str());
      return valA;
    }

    log_warning("Unsupported mux-type cell %s\n", cell->type.c_str());
    return valA;
  }

  log_warning("Totally weird cell %s\n", cell->type.c_str());
  return nullptr;
}


// Generate the value of the given chunk, which is constant, or a
// slice of a single wire or cell output.  The result will be offset
// by the given amount, and zero-extended to totalWidth.
llvm::Value *
LLVMWriter::generateValue(const DriverChunk& chunk,
                           int totalWidth, int offset)
{
  assert(totalWidth >= chunk.size() + offset);

  if (chunk.is_data()) {
    // Sanity checks
    log_assert(chunk.offset == 0);
    log_assert((long unsigned)chunk.size() == chunk.data.size());

    // Build a string of the desired ones and zeros, with 0 padding
    // at the beginning and/or end.

    std::string valStr = RTLIL::Const(chunk.data).as_string();
    log_assert(valStr.size() == (long unsigned)chunk.size());

    // Check for unwanted x
    for (char& ch : valStr) {
      if (ch == 'x') {
        log_warning("x-ish driver chunk found: %s\n", valStr.c_str());
        break;
      }
    }

    // Clean up.
    for (char& ch : valStr) {
      if (ch == 'x') ch = '0';
    }

    if (offset > 0) {
      valStr += std::string('0', offset);
    }

    if (totalWidth > chunk.size() + offset) {
      valStr = std::string('0', totalWidth - chunk.size() - offset) + valStr;
    }
    log_assert(valStr.size() == (long unsigned)totalWidth);

    // Don't bother putting pure constants in the valueCache
    return llvm::ConstantInt::get(llvmWidth(totalWidth), llvm::StringRef(valStr), 2 /*radix*/);
  }

  // OK, we have a slice of a wire or cell output.

  // See if we already have a Value for this object slice
  DriverSpec tmpDs(chunk);
  llvm::Value *val = valueCache.find(tmpDs);

  if (!val) {
    // If not, we have to generate it.
    // Find or make a Value for the entire wire or cell output
    tmpDs = chunk.wire ? DriverSpec(chunk.wire) : DriverSpec(chunk.cell, chunk.port);
    log_assert(tmpDs.is_cell() || tmpDs.is_wire());
    val = valueCache.find(tmpDs);
    if (!val) {
      val = generateValue(tmpDs);
    }

    // Right-shift the value if necessary
    if (chunk.offset > 0) {
      val = b->CreateLShr(val, chunk.offset);
    }

    // Truncate the value if necessary
    log_assert (chunk.width <= chunk.object_width() - chunk.offset); // Basic sanity check
    if (chunk.width < chunk.object_width() - chunk.offset) {
      val = b->CreateZExtOrTrunc(val, llvmWidth(chunk.width));
    }

    // Remember it in case we need it again
    valueCache.add(val, tmpDs);
  }

  // val now represents the slice of wire/port - now we may have to left-shift and/or
  // zero-extend it to the final desired size.

  if (offset == 0 && totalWidth == chunk.size()) {
    return val;  // No padding needed
  }

  if (chunk.offset > 0) {
    val = b->CreateShl(val, offset);
  }

  if (totalWidth > chunk.size() + offset) {
    val = b->CreateZExtOrTrunc(val, llvmWidth(totalWidth));
  }

  // TODO: Is it worth adding this to the valueCache?  It would be necessary
  // to create a relative complex temporary DriverSpec to serve as the key.

  return val;
}


llvm::Value *
LLVMWriter::generateValue(const DriverSpec& dSpec)
{
  llvm::Value *val = valueCache.find(dSpec);
  if (val) {
    return val;  // Should normally be the case for wires
  }

  if (dSpec.is_wire()) {
    // An entire wire, representing a module input port.
    // Their values should have been pre-created as function args
    // and already be in the valueCache.
    log_assert(false);
    return nullptr;

  } else if (dSpec.is_cell()) {
    // An entire cell output.
    RTLIL::IdString portName;
    RTLIL::Cell *cell = dSpec.as_cell(portName);
    llvm::Value *val = generateCellOutputValue(cell, portName);
    valueCache.add(val, dSpec);
    return val;

  } else if (dSpec.is_fully_const()) {
    // valStr will be like "01101011010".
    std::string valStr = dSpec.as_const().as_string();

    // Ideally there would not be explicit 'x' values here!
    // The optimization and cleanup already done should have gotten rid of most of them.
    if (!dSpec.is_fully_def()) {
      log_warning("x-ish driver spec found: %s\n", valStr.c_str());

      // Clean up.
      for (char& ch : valStr) {
        if (ch == 'x') ch = '0';
      }
    }

    // Don't bother putting pure constants in the valueCache
    return llvm::ConstantInt::get(llvmWidth(dSpec.size()), llvm::StringRef(valStr), 2 /*radix*/);

  } else {
    // A complex driverSpec: a mix of wires, ports, and constants (or slices of them).
    // Generate each chunk's value with the proper offset, and OR them together.

    log("generateValue for complex Driverspec\n");
    log_driverspec(dSpec);


    std::vector<llvm::Value*> values;
    int offset = 0;
    for (const DriverChunk& chunk : dSpec.chunks()) {
      log_driverchunk(chunk);
      values.push_back(generateValue(chunk, dSpec.size(), offset));
      offset += chunk.size();
    }

    // OR them all together
    llvm::Value *val = nullptr;
    for (llvm::Value* v : values) {
      if (!val) {
        val = v;
      } else {
        val = b->CreateOr(val, v);
      }
    }

    valueCache.add(val, dSpec);
    return val;
  }
}



// The wire represents a target ASV, and is not NOT necessarily a port
llvm::Value *
LLVMWriter::generateDestValue(RTLIL::Wire *wire)
{

  log("RTLIL Wire %s:\n", wire->name.c_str());
  my_log_wire(wire);

  // Collect the drivers of each bit of the wire
  DriverSpec dSpec;
  finder.buildDriverOf(wire, dSpec);

  // Print what drives the bits of this wire
  log_driverspec(dSpec);
  log("\n");

  return generateValue(dSpec);
}



llvm::Function*
LLVMWriter::generateFunctionDecl(RTLIL::Module *mod, RTLIL::Wire *destWire)
{
  std::vector<llvm::Type *> argTy;

  // Add every module input port, which includes the first-cycle ASV inputs
  // and the unrolled copies of the original input ports.
  for (const RTLIL::IdString& portname : mod->ports) {
    RTLIL::Wire *port = mod->wire(portname);
    log_assert(port);
    if (port->port_input) {
      argTy.push_back(llvmWidth(port->width));
    }
  }


  // A return type of the correct width
  llvm::Type* retTy = llvmWidth(destWire->width);


  llvm::FunctionType *functype =
    llvm::FunctionType::get(retTy, argTy, false);


  // Strip off the "\" from the wire name.
  std::string destName = destWire->name.str().substr(1);

  // Create the main function
  llvm::Function::LinkageTypes linkage = llvm::Function::ExternalLinkage;

  llvm::Function *func = llvm::Function::Create(functype, linkage,
                    "instr_"+destName, llvmMod.get());
                    //destInfo.get_instr_name()+"_"+destSimpleName, llvmMod.get());

  // Set the function's arg's names, and add them to the valueCache
  unsigned n = 0;
  for (const RTLIL::IdString& portname : mod->ports) {
    RTLIL::Wire *port = mod->wire(portname);
    if (port->port_input) {
      llvm::Argument *arg = func->getArg(n);
      arg->setName(portname.str());
      valueCache.add(arg, DriverSpec(port));
      n++;
    }
  }

  return func;

}



void
LLVMWriter::write_llvm_ir(RTLIL::Module *unrolledRtlMod, std::string modName, std::string destName, std::string llvmFileName)
{
  reset();

  log("Building DriverFinder\n");
  finder.build(unrolledRtlMod);
  log("Built DriverFinder\n");
  log("%ld objects\n", finder.size());


  c = std::make_unique<llvm::LLVMContext>();
  b = std::make_unique<llvm::IRBuilder<>>(*c);
  llvmMod = std::make_unique<llvm::Module>("mod_"+modName+"_"+destName, *c);

  // Get the yosys RTLIL object representing the destination ASV.
  // TODO: Map the original Verilog register name to the actual wire name.
  std::string wireName = "\\" + destName + "_#1";
  RTLIL::Wire *destWire = unrolledRtlMod->wire(wireName);
  if (!destWire) {
    log_error("Can't find wire for destination ASV %s\n", destName.c_str());
    log_assert(false);
  }
  my_log_wire(destWire);

  llvm::Function *func = generateFunctionDecl(unrolledRtlMod, destWire);

  // basic block
  llvm::BasicBlock *BB = llvm::BasicBlock::Create(*c, "bb_;_"+destName, func);
  b->SetInsertPoint(BB);

  // All the real work happens here 


  // Collect the drivers of each bit of the destination wire
  DriverSpec dSpec;
  finder.buildDriverOf(destWire, dSpec);

  // Print what drives the bits of this wire
  log_driverspec(dSpec);
  log("\n");

  llvm::Value *destValue = generateValue(dSpec);
  b->CreateRet(destValue);

  log_debug("%lu Values in valueCache\n", valueCache.size());

  llvm::verifyFunction(*func);
  llvm::verifyModule(*llvmMod);

  std::string Str;
  llvm::raw_string_ostream OS(Str);
  OS << *llvmMod;
  OS.flush();

  std::ofstream output(llvmFileName);
  output << Str << std::endl;
  output.close();

  reset();
}
