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

// This file has no dependencies on anything in autoGenILA/src/func_extract

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



static bool
isZero(llvm::Value *val)
{
  if (llvm::ConstantInt *ci = llvm::dyn_cast<llvm::ConstantInt>(val)) {
    return ci->isZero();
  }
  return false;
}



static bool
isAllOnes(llvm::Value *val)
{
  if (llvm::ConstantInt *ci = llvm::dyn_cast<llvm::ConstantInt>(val)) {
    return ci->isMinusOne();
  }
  return false;
}




// Just remove the leading backslash, if any
static std::string
internalToLLVM(RTLIL::IdString name)
{
  const char *s = name.c_str();
  log_assert(s[0] == '\\' || s[0] == '$');
  if (s[0] == '\\') {
    return s+1;
  }
  return s;
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


void
LLVMWriter::ValueCache::add(llvm::Value *value, const DriverSpec& driver)
{

  if (_dict.find(driver) != _dict.end()) {
    // Already there
    log_warning("Repeated calculation of Value for driverspec:\n");
    log_driverspec(driver);
    log("existing Value %p:\n", _dict[driver]);
    _dict[driver]->dump();
    log("new Value %p:\n", value);
    value->dump();
    log_flush();
    return;
  }

  _dict[driver] = value;
}


llvm::Value *
LLVMWriter::ValueCache::find(const DriverSpec& driver)
{
  auto pos = _dict.find(driver);
  if (pos == _dict.end())  {
    return nullptr;
  }
  return pos->second;
}


// Find or create a Value representing what drives the given input port of the given cell.
llvm::Value *
LLVMWriter::generateInputValue(RTLIL::Cell *cell, RTLIL::IdString port)
{
  log_assert(cell->hasPort(port));
  log_assert(cell->input(port));

  DriverSpec dSpec;
  finder.buildDriverOf(cell->getPort(port), dSpec);

  // Get the Value for the input connection
  return generateValue(dSpec);
}



// Return true if the given celltype
// is a redution operator: it returns a single-bit output.
static bool
isReductionCell(RTLIL::IdString celltype)
{
  return celltype.in(
            ID($reduce_and),
            ID($reduce_or),
            ID($reduce_bool),
            ID($reduce_xor),
            ID($reduce_xnor),
            ID($logic_not),
            ID($logic_and),
            ID($logic_or),
            ID($lt),
            ID($le),
            ID($eq),
            ID($ne),
            ID($ge),
            ID($gt));
}


// Create a Value representing the Y output port of the given cell.
// Since this is not given a DriverSpec, it does not touch the valueCache.
// The caller is reponsible for that.
llvm::Value *
LLVMWriter::generateUnaryCellOutputValue(RTLIL::Cell *cell)
{
  // There are three potentially different values of width for any cell
  // connection:  The WIDTH attribute on the cell itself, the width of
  // the connected SigSpec, and the width of the llvm::Value that was
  // generated for the signal.  We control the llvm::Value's width, but the
  // others are set by Yosys optimization of the original Verilog.
  // Adding to the confusion: SigSpec widths are stored as ints, 
  // llvm::Value widths are available as unsigned, and cell WIDTH
  // attributes are available as ints.

  unsigned sigWidthA = (unsigned)(cell->getPort(ID::A).size());  // Size of SigSpec
  unsigned cellWidthA = (unsigned)(cell->parameters[ID::A_WIDTH].as_int());

  unsigned sigWidthY = (unsigned)(cell->getPort(ID::Y).size());  // Size of SigSpec
  unsigned cellWidthY = (unsigned)(cell->parameters[ID::Y_WIDTH].as_int());

  bool signedA = cell->getParam(ID::A_SIGNED).as_bool();

  // Create or find the Value at the cell input
  llvm::Value *valA = generateInputValue(cell, ID::A);  // Possibly lots of recursion here
  unsigned valWidthA = valA->getType()->getIntegerBitWidth();

  bool isReduce = isReductionCell(cell->type);

  log_debug("generateUnaryCellOutputValue(): cell port %s Y width %d:\n",
      cell->name.c_str(), cell->getPort(ID::Y).size());
  log_flush();

  // Sanity check: pin widths match driver/load widths.
  // Also that reduce cells have output width of 1.

  log_assert(sigWidthY == sigWidthA || sigWidthY == 1);
  log_assert(cellWidthY == cellWidthA || cellWidthY == 1);
  log_assert(sigWidthA == cellWidthA);
  log_assert(sigWidthY == cellWidthY);
  log_assert(valWidthA == cellWidthA);

  // Normalize the actual A/Y width to the largest of the cell and Value widths.
  // Presumably the width of an input pin's Value was correctly set when it
  // was generated from the corresponding SigSpec.
  // TODO: Can truncating ever be necessary?
  unsigned workingWidth = std::max({cellWidthA, cellWidthY, valWidthA});

  if (valWidthA < workingWidth) {
    valA = signedA ? b->CreateSExtOrTrunc(valA, llvmWidth(workingWidth)) :
                     b->CreateZExtOrTrunc(valA, llvmWidth(workingWidth));
    valWidthA = valA->getType()->getIntegerBitWidth();
  }

  if (!isReduce && cellWidthY != cellWidthA) {
    log_debug("Mismatched A/Y widths for %s cell %s\n",
                cell->type.c_str(), cell->name.c_str());
    log_flush();
  }

  if (isReduce && cellWidthY != 1) {
    // TODO: zero extend single-bit result.
    log_warning("Oversize Y width for reduction %s cell %s\n",
                cell->type.c_str(), cell->name.c_str());
    log_flush();
  }

  if (cell->type == ID($not)) {
    return b->CreateNot(valA);
  } else if (cell->type == ID($pos)) {
    return valA;
  } else if (cell->type == ID($neg)) {
    return b->CreateNeg(valA);
  } else if (cell->type == ID($reduce_and)) {
    return b->CreateICmpEQ(b->CreateNot(valA), llvmZero(valWidthA));
  } else if (cell->type == ID($reduce_or) || cell->type == ID($reduce_bool)) {
    return b->CreateICmpNE(valA, llvmZero(valWidthA));
  } else if (cell->type == ID($reduce_xor)) {
    // A trickier operation: XOR, a parity calculation.
    // Need to declare and use the llvm.ctpop intrinsic function.
    std::vector<llvm::Type *> arg_type;
    arg_type.push_back(llvmWidth(valWidthA));
    llvm::Function *fun = llvm::Intrinsic::getDeclaration(llvmMod.get(), llvm::Intrinsic::ctpop, arg_type);
    llvm::Value *popcnt = b->CreateCall(fun, valA);
    return b->CreateTrunc(popcnt, llvmWidth(1));  // Return low-order bit
  } else if (cell->type == ID($reduce_xnor)) {
    // Same as reduce_xor, plus invert.
    std::vector<llvm::Type *> arg_type;
    arg_type.push_back(llvmWidth(valWidthA));
    llvm::Function *fun = llvm::Intrinsic::getDeclaration(llvmMod.get(), llvm::Intrinsic::ctpop, arg_type);
    llvm::Value *popcnt = b->CreateCall(fun, valA);
    return b->CreateNot(b->CreateTrunc(popcnt, llvmWidth(1)));  // Return inverted low-order bit
  } else if (cell->type == ID($logic_not)) {
    return b->CreateICmpEQ(valA, llvmZero(valWidthA));
  } 

  log_error("Unsupported unary cell %s\n", cell->type.c_str());
  return valA;

  // TODO: For the unary cells that output a logical value ($reduce_and,
  // $reduce_or, $reduce_xor, $reduce_xnor, $reduce_bool, $logic_not), when
  // the \Y_WIDTH parameter is greater than 1, the output is zero-extended,
  // and only the least significant bit varies.

}


// Create a Value representing the Y output port of the given cell.
llvm::Value *
LLVMWriter::generateBinaryCellOutputValue(RTLIL::Cell *cell)
{
  // See the above rant on widths...

  unsigned sigWidthA = (unsigned)(cell->getPort(ID::A).size());  // Size of SigSpec
  unsigned cellWidthA = (unsigned)(cell->parameters[ID::A_WIDTH].as_int());

  unsigned sigWidthB = (unsigned)(cell->getPort(ID::B).size());  // Size of SigSpec
  unsigned cellWidthB = (unsigned)(cell->parameters[ID::B_WIDTH].as_int());

  unsigned sigWidthY = (unsigned)(cell->getPort(ID::Y).size());  // Size of SigSpec
  unsigned cellWidthY = (unsigned)(cell->parameters[ID::Y_WIDTH].as_int());

  bool signedA = cell->getParam(ID::A_SIGNED).as_bool();
  bool signedB = cell->getParam(ID::B_SIGNED).as_bool();

  // Create or find the Values at the cell inputs
  llvm::Value *valA = generateInputValue(cell, ID::A);  // Possibly lots of recursion here
  unsigned valWidthA = valA->getType()->getIntegerBitWidth();

  llvm::Value *valB = generateInputValue(cell, ID::B);  // Possibly lots of recursion here
  unsigned valWidthB = valB->getType()->getIntegerBitWidth();

  bool isReduce = isReductionCell(cell->type);

  log_debug("test generateBinaryCellOutputValue(): cell port %s Y width %d:\n",
      cell->name.c_str(), cell->getPort(ID::Y).size());
  log_flush();

  // Sanity check: pin widths match driver/load widths.
  // Also that reduce cells have output width of 1.
  
  // I have seen correct cells where Y is narrower than A or B.
  log_assert(sigWidthA == cellWidthA);
  log_assert(sigWidthB == cellWidthB);
  log_assert(sigWidthY == cellWidthY);

  if (cellWidthA != cellWidthB) {
    log_debug("Mismatched A/B widths for %s cell %s\n",
                cell->type.c_str(), cell->name.c_str());
    log_flush();
  }

  if (!isReduce && cellWidthY != cellWidthA) {
    log_debug("Mismatched A/Y widths for %s cell %s\n",
                cell->type.c_str(), cell->name.c_str());
    log_flush();
  }

  if (isReduce && cellWidthY != 1) {
    log_warning("Oversize Y width for reduction %s cell %s\n",
                cell->type.c_str(), cell->name.c_str());
    log_flush();
  }


  // Normalize the actual A/B/Y width to the largest of the cell and Value widths.
  // Presumably the width of an input pin's Value was correctly set when it
  // was generated from the corresponding SigSpec.
  // TODO: Can truncating ever be necessary?
  unsigned workingWidth = std::max({cellWidthA, cellWidthB, cellWidthY, valWidthA, valWidthB});

  if (valWidthA < workingWidth) {
    valA = signedA ? b->CreateSExtOrTrunc(valA, llvmWidth(workingWidth)) :
                     b->CreateZExtOrTrunc(valA, llvmWidth(workingWidth));
    valWidthA = valA->getType()->getIntegerBitWidth();
  }

  if (valWidthB < workingWidth) {
    valB = signedB ? b->CreateSExtOrTrunc(valB, llvmWidth(workingWidth)) :
                     b->CreateZExtOrTrunc(valB, llvmWidth(workingWidth));
    valWidthB = valB->getType()->getIntegerBitWidth();
  }

  log_assert(valWidthA == workingWidth);
  log_assert(valWidthB == workingWidth);

  if (cell->type == ID($and)) {
    // A common case with FF srst signals: an AND gate has a true input,
    // but opt refuses to delete the cell.  BTW CreateAnd() does this
    // same optimization, but only if the RHS is all ones!
    if (isAllOnes(valA)) {
      return valB;
    } else if (isAllOnes(valB)) {
      return valA;
    } else {
      return b->CreateAnd(valA, valB);
    }
  } else if (cell->type == ID($or)) {
    return b->CreateOr(valA, valB);
  } else if (cell->type == ID($xor)) {
    return b->CreateXor(valA, valB);
  } else if (cell->type == ID($xnor)) {
    return b->CreateNot(b->CreateXor(valA, valB));
  } else if (cell->type == ID($shl)) {
    return b->CreateShl(valA, valB);
  } else if (cell->type == ID($shr)) {
    return b->CreateLShr(valA, valB);
  } else if (cell->type == ID($sshl)) {
    return b->CreateShl(valA, valB);  // Same as $shl
  } else if (cell->type == ID($sshr)) {
    return b->CreateAShr(valA, valB);
  } else if (cell->type == ID($logic_and)) {
    return b->CreateAnd(b->CreateICmpNE(valA, llvmZero(valWidthA)),
                        b->CreateICmpNE(valB, llvmZero(valWidthB)));
  } else if (cell->type == ID($logic_or)) {
    return b->CreateOr(b->CreateICmpNE(valA, llvmZero(valWidthA)),
                        b->CreateICmpNE(valB, llvmZero(valWidthB)));

    // TODO: $eqx, etc.  $pos

  } else if (cell->type == ID($lt)) {
    return b->CreateICmpULT(valA, valB);
  } else if (cell->type == ID($le)) {
    return b->CreateICmpULE(valA, valB);
  } else if (cell->type == ID($eq)) {
    return b->CreateICmpEQ(valA, valB);
  } else if (cell->type == ID($ne)) {
    return b->CreateICmpNE(valA, valB);
  } else if (cell->type == ID($ge)) {
    return b->CreateICmpUGE(valA, valB);
  } else if (cell->type == ID($gt)) {
    return b->CreateICmpUGT(valA, valB);
  } else if (cell->type == ID($add)) {
    return b->CreateAdd(valA, valB);
  } else if (cell->type == ID($sub)) {
    return b->CreateSub(valA, valB);
  } else if (cell->type == ID($mul)) {
    return b->CreateMul(valA, valB);
  } else if (cell->type == ID($div)) {
    return b->CreateUDiv(valA, valB);  // Needs work?
  } else if (cell->type == ID($mod)) {
    return b->CreateUDiv(valA, valB);

    // TODO: $shift and $shiftx, $divfloor, etc.
    // TODO: See above about logic operators with Y width > 1
  } 

  log_warning("Unsupported binary cell %s\n", cell->type.c_str());
  return valA;
}



// Create a Value representing the output port of the given 3-input mux cell.
llvm::Value *
LLVMWriter::generateMuxCellOutputValue(RTLIL::Cell *cell)
{
  log_assert(cell->type == ID($mux));

  // See the above rant on widths...
  // Muxes have only WIDTH attribute, applies to A/B/Y
  unsigned cellWidth = (unsigned)(cell->parameters[ID::WIDTH].as_int());

  unsigned sigWidthA = (unsigned)(cell->getPort(ID::A).size());  // Size of SigSpec
  unsigned sigWidthB = (unsigned)(cell->getPort(ID::B).size());  // Size of SigSpec
  unsigned sigWidthS = (unsigned)(cell->getPort(ID::S).size());  // Size of SigSpec
  unsigned sigWidthY = (unsigned)(cell->getPort(ID::Y).size());  // Size of SigSpec

  // Muxes apparently do not have SIGNED attributes.

  // Create or find the Values at the cell inputs
  llvm::Value *valA = generateInputValue(cell, ID::A);  // Possibly lots of recursion here
  unsigned valWidthA = valA->getType()->getIntegerBitWidth();

  llvm::Value *valB = generateInputValue(cell, ID::B);  // Possibly lots of recursion here
  unsigned valWidthB = valB->getType()->getIntegerBitWidth();

  llvm::Value *valS = generateInputValue(cell, ID::S);
  unsigned valWidthS = valS->getType()->getIntegerBitWidth();

  log_debug("generateMuxCellOutputValue(): cell port %s Y width %d:\n",
      cell->name.c_str(), cell->getPort(ID::Y).size());
  log_flush();

  // TODO: Sanity check: pin widths match driver/load widths.

  log_assert(sigWidthA == cellWidth);
  log_assert(sigWidthB == cellWidth);
  log_assert(sigWidthY == cellWidth);
  log_assert(sigWidthS == 1);

  // If A or B widths are different than their connections, zero
  // or sign-extend the input data.  No \SIGNED attributes to consider.
  // I have observed A/B input signals WIDER than the cell width
  if (valWidthA != cellWidth) {
    valA = b->CreateZExtOrTrunc(valA, llvmWidth(cellWidth));
    valWidthA = valA->getType()->getIntegerBitWidth();
  }

  if (valWidthB != cellWidth) {
    valB = b->CreateZExtOrTrunc(valB, llvmWidth(cellWidth));
    valWidthB = valB->getType()->getIntegerBitWidth();
  }

  log_assert(valWidthA == cellWidth);
  log_assert(valWidthB == cellWidth);
  log_assert(valWidthS == 1);

  return b->CreateSelect(valS, valA, valB);
}



// Create a Value representing the output port of the given 3-input pmux cell.
// This is a strange form of mux
// TODO: Yosys optimization can try to get rid pf pmux cells (e.g. the pmuxtree
// command), so we may rarely see them in practice.
llvm::Value *
LLVMWriter::generatePmuxCellOutputValue(RTLIL::Cell *cell)
{
  log_debug("generatePmuxCellOutputValue(): cell port %s widths: A %d B %d S %d:\n",
       cell->name.c_str(),
       cell->getPort(ID::A).size(),
       cell->getPort(ID::B).size(),
       cell->getPort(ID::S).size());
  log_flush();

  log_assert(cell->type == ID($pmux));

  // See the above rant on widths...

  unsigned cellWidthAY = (unsigned)(cell->parameters[ID::WIDTH].as_int());

  unsigned sigWidthA = (unsigned)(cell->getPort(ID::A).size());  // Size of SigSpec

  unsigned sigWidthB = (unsigned)(cell->getPort(ID::B).size());  // Size of SigSpec

  unsigned sigWidthS = (unsigned)(cell->getPort(ID::S).size());  // Size of SigSpec
  unsigned cellWidthS = (unsigned)(cell->parameters[ID::S_WIDTH].as_int());

  unsigned sigWidthY = (unsigned)(cell->getPort(ID::Y).size());  // Size of SigSpec

  // Muxes apparently do not have SIGNED attributes.

  // Create or find the Values at the cell inputs
  llvm::Value *valA = generateInputValue(cell, ID::A);  // Possibly lots of recursion here
  unsigned valWidthA = valA->getType()->getIntegerBitWidth();

  llvm::Value *valB = generateInputValue(cell, ID::B);  // Possibly lots of recursion here
  unsigned valWidthB = valB->getType()->getIntegerBitWidth();

  llvm::Value *valS = generateInputValue(cell, ID::S);
  unsigned valWidthS = valS->getType()->getIntegerBitWidth();

  // Unique characteristic of pmux cells
  unsigned cellWidthB = cellWidthAY * cellWidthS;

  // TODO: Handle width weirdness of $pmux cells!

  log_assert(sigWidthA == cellWidthAY);
  log_assert(sigWidthB == cellWidthB);
  log_assert(sigWidthY == cellWidthAY);
  log_assert(sigWidthS == cellWidthS);

  log_assert(valWidthA == cellWidthAY);
  log_assert(valWidthB == cellWidthB);
  log_assert(valWidthS == cellWidthS);


  // TODO: If A or B widths are not what they should be, zero
  // or sign-extend the input data.  Consider \SIGNED attributes
  // BTW, SigSpecs do not have any information about signed-ness
  // Possible approach: create a truncated or extended version of
  // the input's DriverSpec, and generate (and cache) its value.

  log_error("Unsupported pmux cell %s\n", cell->name.c_str());
  log("A:\n%s\n", log_signal(cell->getPort(ID::A)));
  log("B:\n%s\n", log_signal(cell->getPort(ID::B)));
  log("S:\n%s\n", log_signal(cell->getPort(ID::S)));
  log_flush();
  return valA;
}



// Create a Value representing the output port of the given cell.
// Since this is not given a DriverSpec, it does not touch the valueCache.
// The caller is reponsible for that.
// TODO: Should it instead make a temporary DriverSpec to access the valueCache?
llvm::Value *
LLVMWriter::generateCellOutputValue(RTLIL::Cell *cell, RTLIL::IdString port)
{
  // Here we handle only builtin cells.
  // Hierarchical modules are a different thing.
  if (cell->name[0] != '$' || cell->type[0] != '$') {
    log_error("Unsupported hierarchical cell %s\n", cell->name.c_str());
    return nullptr;
  }


  RTLIL::SigSpec outputSig = cell->getPort(ID::Y);

  log_debug("generateCellOutputValue(): cell port %s Y  width %d:\n",
      cell->name.c_str(), outputSig.size());
  log_flush();

  // All builtin cell outputs are supposed to be Y
  log_assert(port == ID::Y);
  log_assert(cell->output(port));

  llvm::Value *val = nullptr;

  size_t numConns = cell->connections().size();
  switch (numConns) {
    case 2: val = generateUnaryCellOutputValue(cell);
            break;
    case 3: val = generateBinaryCellOutputValue(cell);
            break;
    case 4: if (cell->type == ID($mux)) {
              val = generateMuxCellOutputValue(cell);
            } else if (cell->type == ID($pmux)) {
              val = generatePmuxCellOutputValue(cell);
            } else {
              log_warning("Unsupported %s cell %s\n",
                          cell->type.c_str(), cell->name.c_str());
              val = generateInputValue(cell, ID::A);  // Fallback
            }
            break;
    default: 
      log_warning("Totally weird cell %s\n", cell->type.c_str());
      val = generateInputValue(cell, ID::A);  // Fallback
      break;
  }

  // TODO: Do any necessary width adjustments to result here?

  // If the new Value is an Instruction driving a single wire, name it
  // after that wire, if the wire's name is not auto-generated. But don't
  // rename things, and don't try to name non-Instructions, especially
  // function args.
  if (llvm::isa<llvm::Instruction>(val) && val->getName().empty() && outputSig.is_wire()) {
    RTLIL::IdString valName = outputSig.as_wire()->name;
    if (valName[0] != '$') {
      val->setName(internalToLLVM(valName));
    }
  }

  return val;

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

    std::string valStr = chunk.as_string();
    log_assert(valStr.size() == (long unsigned)chunk.size());

    // Check for unwanted x
    for (char& ch : valStr) {
      if (ch != '0' && ch != '1') {
        log_warning("x-ish driver chunk found: %s\n", valStr.c_str());
        break;
      }
    }

    // Clean up.
    for (char& ch : valStr) {
      if (ch != '0' && ch != '1') ch = '0';
    }

    if (offset > 0) {
      valStr += std::string(offset, '0');  // Effectively a left shift.
    }

    if (totalWidth > chunk.size() + offset) {
      valStr = std::string((totalWidth - chunk.size() - offset), '0') + valStr;
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
    DriverSpec objDs = chunk.wire ? DriverSpec(chunk.wire) : DriverSpec(chunk.cell, chunk.port);
    log_assert(objDs.is_cell() || objDs.is_wire());
    llvm::Value *objVal = generateValue(objDs);  // Will be added to valueCache

    // Right-shift the value if necessary
    if (chunk.offset > 0) {
      val = b->CreateLShr(objVal, chunk.offset);
    } else {
      val = objVal;
    }

    // Truncate the value if necessary
    log_assert (chunk.width <= chunk.object_width() - chunk.offset); // Basic sanity check
    if ((unsigned)chunk.width != val->getType()->getIntegerBitWidth()) {
      val = b->CreateZExtOrTrunc(val, llvmWidth(chunk.width));
    }

    // If we actually did any shifting or truncating, add the new Value to valueCache.
    if (val != objVal) {
      valueCache.add(val, tmpDs);
    }
  }

  // val now represents the slice of wire/port - now we may have to left-shift and/or
  // zero-extend it to the final desired size.

  if (offset == 0 && totalWidth == chunk.size()) {
    return val;  // No padding needed
  }

  // Extend before shifting!
  if ((unsigned)totalWidth != val->getType()->getIntegerBitWidth()) {
    val = b->CreateZExtOrTrunc(val, llvmWidth(totalWidth));
  }

  if (chunk.offset > 0) {
    val = b->CreateShl(val, offset);
  }

  // TODO: Is it worth adding this to the valueCache?  It would be necessary
  // to create a relatively complex temporary DriverSpec to serve as the key.

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

    log_debug("generateValue for complex Driverspec\n");
    log_debug_driverspec(dSpec);


    std::vector<llvm::Value*> values;
    int offset = 0;
    for (const DriverChunk& chunk : dSpec.chunks()) {
      log_debug_driverchunk(chunk);
      values.push_back(generateValue(chunk, dSpec.size(), offset));
      offset += chunk.size();
    }

    if (values.size() == 1) {
      return values[0];  // A single chunk (already added to valueCache).
    }

    // Multiple chunks: OR them all together
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

  log_debug("RTLIL Wire %s:\n", wire->name.c_str());
  my_log_wire(wire);

  // Collect the drivers of each bit of the wire
  DriverSpec dSpec;
  finder.buildDriverOf(wire, dSpec);

  // Print what drives the bits of this wire
  log_debug_driverspec(dSpec);
  log_debug("\n");

  return generateValue(dSpec);
}



llvm::Function*
LLVMWriter::generateFunctionDecl(const std::string& funcName, RTLIL::Module *mod,
                                 RTLIL::Wire *targetPort)
{
  std::vector<llvm::Type *> argTy;

  // Add every module input port, which includes the first-cycle ASV inputs
  // and the unrolled copies of the original input ports.
  for (RTLIL::IdString portname : mod->ports) {
    RTLIL::Wire *port = mod->wire(portname);
    log_assert(port);
    if (port->port_input) {
      argTy.push_back(llvmWidth(port->width));
    }
  }

  // A return type of the correct width
  llvm::Type* retTy = llvmWidth(targetPort->width);

  llvm::FunctionType *functype =
    llvm::FunctionType::get(retTy, argTy, false);

  // Create the main function
  llvm::Function::LinkageTypes linkage = llvm::Function::ExternalLinkage;

  llvm::Function *func = llvm::Function::Create(functype, linkage, funcName, llvmMod.get());

  // Set the function's args' names, and add them to the valueCache.
  // Note that the arg names get translated back to their original Verilog
  // form.  It is important to match the naming convention of the original
  // func_extract program.
  unsigned n = 0;
  for (RTLIL::IdString portname : mod->ports) {
    RTLIL::Wire *port = mod->wire(portname);
    if (port->port_input) {
      llvm::Argument *arg = func->getArg(n);
      arg->setName(internalToV(portname));
      valueCache.add(arg, DriverSpec(port));
      n++;
    }
  }

  return func;
}



void
LLVMWriter::write_llvm_ir(RTLIL::Module *unrolledRtlMod,
                          RTLIL::Wire *targetPort,  // in unrolledRtlMod
                          std::string modName,  // from original Verilog, e.g. "M8080"
                          std::string instrName,  // As specified in instr.txt
                          std::string targetName,  // As specified in allowed_target.txt
                          std::string llvmFileName,
                          std::string funcName)
{
  assert(targetPort->port_output);

  reset();

  log("Building DriverFinder\n");
  finder.build(unrolledRtlMod);
  log("Built DriverFinder\n");
  log("%ld objects\n", finder.size());

  c = std::make_unique<llvm::LLVMContext>();
  b = std::make_unique<llvm::IRBuilder<>>(*c);
  llvmMod = std::make_unique<llvm::Module>("mod_;_"+modName+"_;_"+targetName, *c);

  llvm::Function *func = generateFunctionDecl(funcName, unrolledRtlMod, targetPort);

  // basic block
  llvm::BasicBlock *BB = llvm::BasicBlock::Create(*c, "bb_;_"+targetName, func);
  b->SetInsertPoint(BB);

  // All the real work happens here 

  log_debug("Destination port:\n");
  my_log_debug_wire(targetPort);

  // Collect the drivers of each bit of the destination wire
  DriverSpec dSpec;
  finder.buildDriverOf(targetPort, dSpec);

  // Print what drives the bits of this wire
  log_debug_driverspec(dSpec);
  log_debug("\n");

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
