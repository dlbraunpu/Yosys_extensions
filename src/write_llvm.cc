#include "write_llvm.h"

#include "func_extract/src/branch_mux.h"
  
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
#include "llvm/IR/ValueSymbolTable.h"

// Yosys headers
#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "backends/rtlil/rtlil_backend.h"


// Unfortunately including func_extract/src/util.h triggers the nasty "#define ID" issue.
namespace funcExtract {
  uint32_t get_padded_width(uint32_t width);

  // From func_extract/src/global_data_struct.h
  constexpr const char *RETURN_ARRAY_PTR_ID = "*RETURN_ARRAY_PTR*";  
}


#include "util.h"
#include "driver_tools.h"


USING_YOSYS_NAMESPACE  // Does "using namespace"


LLVMWriter::LLVMWriter(RTLIL::Design *des, const Options &options) 
{
  design = des;
  opts = options;
  c = std::make_unique<llvm::LLVMContext>();
  b = std::make_unique<llvm::IRBuilder<>>(*c);
  llvmMod = nullptr;  // Deleting the Context deletes this.
  llvmFunc = nullptr; // And this.
  pmuxIdx = 0;
}

LLVMWriter::~LLVMWriter()
{
}


// Call this before and after writing each function of an LLVM Module.
void
LLVMWriter::clearFunctionData()
{
  finder.clear();
  valueCache.clear();
  llvmFunc = nullptr; 
}



// Return true iff val is a Constant with a zero value.
static bool
isZero(llvm::Value *val)
{
  if (llvm::ConstantInt *ci = llvm::dyn_cast<llvm::ConstantInt>(val)) {
    return ci->isZero();
  }
  return false;
}



// Return true iff val is a Constant with an all-ones value.
static bool
isAllOnes(llvm::Value *val)
{
  if (llvm::ConstantInt *ci = llvm::dyn_cast<llvm::ConstantInt>(val)) {
    return ci->isMinusOne();
  }
  return false;
}




// Just remove the leading backslash, if any.
// If oldStyle is true, we try to match what the original
// version of func_extract would do, including keeping any
// leading backslash.  This is needed for function arg names.

static std::string
internalToLLVM(RTLIL::IdString name, bool oldStyle = false)
{
  if (oldStyle) {
    std::string str = internalToV(name);
    // Remove any trailing spaces added by internalToV.
    while (!str.empty() && str.back() == ' ') {
      str.pop_back();
    }
    return str;

  } else {

    const char *s = name.c_str();
    log_assert(s[0] == '\\' || s[0] == '$');
    if (s[0] == '\\') {
      return s+1;
    }
    return s;
  }
}


llvm::IntegerType *
LLVMWriter::llvmWidth(unsigned a) {
  return llvm::IntegerType::get(*c, a);
}


llvm::VectorType *
LLVMWriter::llvmVectorType(unsigned elemwidth, unsigned nelems) {
  return llvm::VectorType::get(llvmWidth(elemwidth), nelems, false /*scalable*/);
}


// Dangerous: only supports up to 64 bits.
llvm::ConstantInt *
LLVMWriter::llvmInt(uint64_t val, unsigned width)
{
  log_assert(width <= 64);
  return llvm::ConstantInt::get(llvmWidth(width), val, false);
}


// More useful
llvm::ConstantInt *
LLVMWriter::llvmZero(unsigned width)
{
  return llvm::ConstantInt::get(llvmWidth(width), 0, false);
}


llvm::PoisonValue *
LLVMWriter::llvmPoison(unsigned width)
{
  return llvm::PoisonValue::get(llvmWidth(width));
}


llvm::UndefValue *
LLVMWriter::llvmUndef(unsigned width)
{
  return llvm::UndefValue::get(llvmWidth(width));
}



llvm::Value *
LLVMWriter::llvmUndefValue(unsigned width)
{
  if (opts.use_poison) {
    return llvmPoison(width);
    //return llvmUndef(width);
  } else {
    return llvmZero(width);
  }
}



unsigned
LLVMWriter::getWidth(llvm::Value *val)
{
  if (val->getType()->isVectorTy()) {
    llvm::VectorType *vecTy = llvm::dyn_cast<llvm::VectorType>(val->getType());
    return getWidth(vecTy->getElementType()) * vecTy->getElementCount().getFixedValue();
  }
  if (val->getType()->isIntegerTy()) {
    return val->getType()->getIntegerBitWidth();
  }

  log("Odd type %d\n", val->getType()->getTypeID());
  log_flush();
  log_assert(false);
  return 0;
}


unsigned
LLVMWriter::getWidth(llvm::Type *ty)
{
  if (llvm::VectorType *vecTy = llvm::dyn_cast<llvm::VectorType>(ty)) {
    return getWidth(vecTy->getElementType()) * vecTy->getElementCount().getFixedValue();
  }
  return ty->getIntegerBitWidth();
}


void
LLVMWriter::ValueCache::add(const DriverSpec& driver, llvm::Value *value)
{
  // There is no point in putting non-instructions
  // (e.g. constants or function args) in the cache.
  llvm::Instruction *instr = llvm::dyn_cast<llvm::Instruction>(value);
  if (!instr) {
    return;
  }

  // Grab the Function from the first Instruction we add.
  if (!_func) {
    _func = instr->getFunction();
  } else {
    log_assert(instr->getFunction() == _func);
  }

  // See if we already have an entry for the given driver, in the same BB
  // equal_range() returns a pair of iterators
  auto range = _mmap.equal_range(driver);

  for (auto pos = range.first; pos != range.second; ++pos) {
    llvm::Instruction *entry =  llvm::dyn_cast<llvm::Instruction>(pos->second);
    log_assert(entry);

    if (entry->getParent() == instr->getParent()) {
      log_warning("Repeated calculation of Value for driverspec:\n");
      log_driverspec(driver);
      log("existing Value %p:\n", entry);
      entry->dump();
      log("new Value %p:\n", instr);
      instr->dump();
      log_flush();
      return;
    }
  }

  _mmap.insert(MmapType::value_type(driver,value));
}


// If bb is non-null, this will look for a cached driver in the same BB, or
// in a BB that dominates the given BB.
llvm::Value *
LLVMWriter::ValueCache::find(const DriverSpec& driver, llvm::BasicBlock *bb)
{
  // equal_range() returns a pair of iterators
  auto range = _mmap.equal_range(driver);

  if (range.first == range.second)  {
    ++_nMisses;
    return nullptr;  // Empty cache
  }

  for (auto pos = range.first; pos != range.second; ++pos) {
    llvm::Value *value = pos->second;
    llvm::Instruction *instr =  llvm::dyn_cast<llvm::Instruction>(value);
    log_assert(instr);

    // First look for a cached value in the same BB.
    if (!bb || instr->getParent() == bb) {
      log_debug("returning cached value in BB %s same as desired BB\n",
          instr->getParent()->getName().str().c_str());
      ++_nHits;
      return value;
    }
  }

  // If no luck, look for a value in a dominating BB.
  for (auto pos = range.first; pos != range.second; ++pos) {
    llvm::Value *value = pos->second;
    llvm::Instruction *instr =  llvm::dyn_cast<llvm::Instruction>(value);
    if (_DT.dominates(instr->getParent(), bb)) {
      ++_nHits;
      log_debug("returning cached value in BB %s desired BB: %s\n",
          instr->getParent()->getName().str().c_str(),
          bb->getName().str().c_str());
      return value;
    } else {
      log_debug("cached value in BB %s does not dominate desired BB: %s\n",
          instr->getParent()->getName().str().c_str(),
          bb->getName().str().c_str());
    }
  }

  ++_nMisses;
  return nullptr;
}


// Generate code to load a Value from the given index of the given array.
// Used for accessing ASVs in register arrays.
// Post LLVM 14, pointers are untyped, so we do not try to deduce
// the element size from the array pointer type.  Plus, there may be padding.
// valueName will be applied to the resulting Value, so it can be
// referred to in the generated code.

llvm::Value*
LLVMWriter::generateLoad(llvm::Value *array, unsigned elementWidth, unsigned idx,
             std::string valueName)
{
  uint32_t paddedWidth = funcExtract::get_padded_width(elementWidth);

  llvm::Type *paddedElementTy = llvmWidth(paddedWidth);

  uint32_t idxBitwidth = 32;  // LLVM optimization just switches this to i64...

  // Add a GetElementPtr instruction to calculate the address
  llvm::Value* gep = b->CreateGEP(
          paddedElementTy,
          array,
          std::vector<llvm::Value*> {
              llvm::ConstantInt::get(llvmWidth(idxBitwidth), idx, false) }
          );

  if (paddedWidth == elementWidth) {
    // No width issues: create a load instruction with the correct name.
    return b->CreateLoad(paddedElementTy, gep, valueName);
  } else {
    // De-padding necessary: create a load followed by a trunc instruction with the correct name.
    // Note that CreateZExtOrTrunc() will ignore the supplied name and simply return the
    // input value if no conversion is needed.
    llvm::Value *paddedVal = b->CreateLoad(paddedElementTy, gep);
    llvm::Type *elementTy = llvmWidth(elementWidth);
    return b->CreateTrunc(paddedVal, elementTy, valueName);
  }
}


// Similar to above, but to store to array.  There is no Value to return.
void
LLVMWriter::generateStore(llvm::Value *array, unsigned idx, llvm::Value *val)
{

  uint32_t paddedWidth = funcExtract::get_padded_width(getWidth(val));
  llvm::Type *paddedElementTy = llvmWidth(paddedWidth);
  uint32_t idxBitwidth = 32;  // LLVM optimization just switches this to i64...

  // Add a GetElementPtr instruction to calculate the address
  llvm::Value* gep = b->CreateGEP(
          paddedElementTy,
          array,
          std::vector<llvm::Value*> {
              llvm::ConstantInt::get(llvmWidth(idxBitwidth), idx, false) }
          );

  // If no width conversion is needed, no zext or trunc instruction will be generated here.
  llvm::Value *paddedVal = b->CreateZExtOrTrunc(val, paddedElementTy);

  b->CreateStore(paddedVal, gep);
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


// AND gates are created in several situations, so this is handy.
llvm::Value *
LLVMWriter::generateAndCellOutputValue(llvm::Value *valA, llvm::Value *valB)
{
  if (opts.simplify_and_or_gates) {
    return generateSimplifiedAndCellOutputValue(valA, valB);  
  }
  return b->CreateAnd(valA, valB);  
}


llvm::Value *
LLVMWriter::generateSimplifiedAndCellOutputValue(llvm::Value *valA, llvm::Value *valB) {
  // A common case with FF srst signals: an AND gate has a true input, but opt
  // refuses to delete the cell.  BTW the latest LLVM CreateAnd() will do
  // these optimizations, but only if the RHS is constant!  Generally the
  // binary operators prefer that a constant be the second operand.

  unsigned width = getWidth(valA);
  log_assert(width == getWidth(valB));

  if (isAllOnes(valA)) {
    return valB;
  } else if (isZero(valA)) {
    return llvmZero(width);
  } else if (isZero(valB)) {
    return llvmZero(width);
  } else if (isAllOnes(valA)) {
    return valB;
  } else if (isAllOnes(valB)) {
    return valA;
  } else {
    return b->CreateAnd(valA, valB);
  }
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
  unsigned valWidthA = getWidth(valA);
  log_assert(valWidthA == cellWidthA);

  bool isReduce = isReductionCell(cell->type);

  log_debug("generateUnaryCellOutputValue(): cell port %s Y width %d:\n",
      cell->name.c_str(), cell->getPort(ID::Y).size());
  log_flush();

  // Sanity check: pin widths match driver/load widths.
  // Also that reduce cells have output width of 1.

  //log_assert(sigWidthY == sigWidthA || sigWidthY == 1); // not necessarily true
  //log_assert(cellWidthY == cellWidthA || cellWidthY == 1);
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
    valWidthA = getWidth(valA);
  }

  if (!isReduce && cellWidthY != cellWidthA) {
    log_debug("Mismatched A/Y widths for %s cell %s\n",
                cell->type.c_str(), cell->name.c_str());
    log_flush();
  }

  if (isReduce && cellWidthY != 1) {
    // Later we zero-extend the single-bit result.
    log_warning("Oversize Y width for reduction %s cell %s\n",
                cell->type.c_str(), cell->name.c_str());
    log_flush();
  }

  llvm::Value *val = nullptr;

  if (cell->type == ID($not)) {
    val = b->CreateNot(valA);
  } else if (cell->type == ID($pos)) {
    val = valA;
  } else if (cell->type == ID($neg)) {
    val = b->CreateNeg(valA);
  } else if (cell->type == ID($reduce_and)) {
    log_assert(cellWidthY == 1);
    val = b->CreateICmpEQ(b->CreateNot(valA), llvmZero(valWidthA));
  } else if (cell->type == ID($reduce_or) || cell->type == ID($reduce_bool)) {
    log_assert(cellWidthY == 1);
    val = b->CreateICmpNE(valA, llvmZero(valWidthA));
  } else if (cell->type == ID($reduce_xor)) {
    log_assert(cellWidthY == 1);
    // A trickier operation: XOR, a parity calculation.
    // Need to declare and use the llvm.ctpop intrinsic function.
    std::vector<llvm::Type *> arg_type;
    arg_type.push_back(llvmWidth(valWidthA));
    llvm::Function *fun = llvm::Intrinsic::getDeclaration(llvmMod, llvm::Intrinsic::ctpop, arg_type);
    llvm::Value *popcnt = b->CreateCall(fun, valA);
    val = b->CreateTrunc(popcnt, llvmWidth(1));  // Return low-order bit
  } else if (cell->type == ID($reduce_xnor)) {
    log_assert(cellWidthY == 1);
    // Same as reduce_xor, plus invert.
    std::vector<llvm::Type *> arg_type;
    arg_type.push_back(llvmWidth(valWidthA));
    llvm::Function *fun = llvm::Intrinsic::getDeclaration(llvmMod, llvm::Intrinsic::ctpop, arg_type);
    llvm::Value *popcnt = b->CreateCall(fun, valA);
    val = b->CreateNot(b->CreateTrunc(popcnt, llvmWidth(1)));  // Return inverted low-order bit
  } else if (cell->type == ID($logic_not)) {
    log_assert(cellWidthY == 1);
    val = b->CreateICmpEQ(valA, llvmZero(valWidthA));
  } else {
    log_error("Unsupported unary cell %s\n", cell->type.c_str());
    val = valA;
  }

  return val;
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
  unsigned valWidthA = getWidth(valA);

  llvm::Value *valB = generateInputValue(cell, ID::B);  // Possibly lots of recursion here
  unsigned valWidthB = getWidth(valB);

  bool isReduce = isReductionCell(cell->type);

  log_debug("test generateBinaryCellOutputValue(): cell port %s Y width %d:\n",
      cell->name.c_str(), cell->getPort(ID::Y).size());
  log_flush();

  // Sanity check: pin widths match driver/load widths.
  // Also that reduce cells have output width of 1.
  
  // I have seen correct cells where Y is narrower than A or B.
  // But the port width parameters on the cell should always match
  // the widths of the connected signals.
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
  unsigned workingWidth = 0;
  if (cell->type.in(ID($and), ID($or), ID($xor), ID($xnor), ID($add), ID($sub))) {
    workingWidth = cellWidthY;
  } else {
    workingWidth = std::max({cellWidthA, cellWidthB, cellWidthY, valWidthA, valWidthB});
  }

  if (valWidthA != workingWidth) {
    valA = signedA ? b->CreateSExtOrTrunc(valA, llvmWidth(workingWidth)) :
                     b->CreateZExtOrTrunc(valA, llvmWidth(workingWidth));
    valWidthA = getWidth(valA);
  }

  if (valWidthB != workingWidth) {
    valB = signedB ? b->CreateSExtOrTrunc(valB, llvmWidth(workingWidth)) :
                     b->CreateZExtOrTrunc(valB, llvmWidth(workingWidth));
    valWidthB = getWidth(valB);
  }

  log_assert(valWidthA == workingWidth);
  log_assert(valWidthB == workingWidth);

  llvm::Value *val = nullptr;

  if (cell->type == ID($and)) {
    val = generateAndCellOutputValue(valA, valB);
  } else if (cell->type == ID($or)) {
    if (!opts.simplify_and_or_gates) {
      val = b->CreateOr(valA, valB); 
    } else if (isZero(valA)) {
      val = valB;
    } else if (isZero(valB)) {
      val = valA;
    } else {
      val = b->CreateOr(valA, valB);
    }
  } else if (cell->type == ID($xor)) {
    val = b->CreateXor(valA, valB);
  } else if (cell->type == ID($xnor)) {
    val = b->CreateNot(b->CreateXor(valA, valB));
  } else if (cell->type == ID($shl)) {
    log_assert(!signedB);
    val = b->CreateShl(valA, valB);
  } else if (cell->type == ID($shr)) {
    log_assert(!signedB);
    val = b->CreateLShr(valA, valB);
  } else if (cell->type == ID($sshl)) {
    log_assert(signedA);  // Is this actually required?
    log_assert(!signedB);
    val = b->CreateShl(valA, valB);  // Same as $shl
  } else if (cell->type == ID($sshr)) {
    log_assert(signedA);  // Is this actually required?
    log_assert(!signedB);
    val = b->CreateAShr(valA, valB);
  } else if (cell->type == ID($logic_and)) {
    if (isZero(valA) || isZero(valB)) {
      val = llvmZero(1);
    } else {
      val = b->CreateLogicalAnd(b->CreateICmpNE(valA, llvmZero(valWidthA)),
                                 b->CreateICmpNE(valB, llvmZero(valWidthB)));
    }
  } else if (cell->type == ID($logic_or)) {
    val = b->CreateLogicalOr(b->CreateICmpNE(valA, llvmZero(valWidthA)),
                              b->CreateICmpNE(valB, llvmZero(valWidthB)));

    // TODO: $eqx, etc.  $pos

  } else if (cell->type == ID($lt)) {
    val = b->CreateICmpULT(valA, valB);
  } else if (cell->type == ID($le)) {
    val = b->CreateICmpULE(valA, valB);
  } else if (cell->type == ID($eq)) {
    val = b->CreateICmpEQ(valA, valB);
  } else if (cell->type == ID($ne)) {
    val = b->CreateICmpNE(valA, valB);
  } else if (cell->type == ID($ge)) {
    val = b->CreateICmpUGE(valA, valB);
  } else if (cell->type == ID($gt)) {
    val = b->CreateICmpUGT(valA, valB);
  } else if (cell->type == ID($add)) {
    val = b->CreateAdd(valA, valB);
  } else if (cell->type == ID($sub)) {
    val = b->CreateSub(valA, valB);
  } else if (cell->type == ID($mul)) {
    val = b->CreateMul(valA, valB);
  } else if (cell->type == ID($div)) {
    val = b->CreateUDiv(valA, valB);  // Needs work?
  } else if (cell->type == ID($mod)) {
    val = b->CreateUDiv(valA, valB);

    // TODO: $divfloor, etc.
  } else if (cell->type == ID($shift) || cell->type == ID($shiftx)) {
    // Logical left shift, or right shift if B is negative.
    // $shiftx is supposed to shift in x bits instead of zeros.

    // If input B's MSB is known to be zero, we can avoid worrying about
    // left shifts.
    DriverSpec dSpec;
    finder.buildDriverOf(cell->getPort(ID::B), dSpec);

    if (!signedB || dSpec[dSpec.size()-1] == RTLIL::S0) {
      val = b->CreateLShr(valA, valB);
    } else {
      llvm::Value *shiftR = b->CreateLShr(valA, valB); // Assuming B >= 0
      llvm::Value *shiftL = b->CreateShl(valA, b->CreateNeg(valB));  // Assuming B < 0
      llvm::Value *bIsNeg = b->CreateICmpSLT(valB, llvmZero(valWidthB));
      val = b->CreateSelect(bIsNeg, shiftL, shiftR, "shift_select");
    }
  } else {
    log_error("Unsupported binary cell %s\n", cell->type.c_str());
    val = valA;
  }

  return val;
}


// Create a Value representing the output port of the given 3-input mux cell.
llvm::Value *
LLVMWriter::generateMuxCellOutputValue(RTLIL::Cell *cell)
{
  if (opts.simplify_muxes) {
    return generateSimplifiedMuxCellOutputValue(cell);
  }

  log_assert(cell->type == ID($mux));

  log_debug("generateMuxCellOutputValue(): cell port %s Y width %d:\n",
      cell->name.c_str(), cell->getPort(ID::Y).size());
  log_flush();

  // See the above rant on widths...
  // Muxes have only WIDTH attribute, applies to A/B/Y
  unsigned cellWidth = (unsigned)(cell->parameters[ID::WIDTH].as_int());

  unsigned sigWidthA = (unsigned)(cell->getPort(ID::A).size());  // Size of SigSpec
  unsigned sigWidthB = (unsigned)(cell->getPort(ID::B).size());  // Size of SigSpec
  unsigned sigWidthS = (unsigned)(cell->getPort(ID::S).size());  // Size of SigSpec
  unsigned sigWidthY = (unsigned)(cell->getPort(ID::Y).size());  // Size of SigSpec

  log_assert(sigWidthA == cellWidth);
  log_assert(sigWidthB == cellWidth);
  log_assert(sigWidthY == cellWidth);
  log_assert(sigWidthS == 1);

  // Muxes apparently do not have SIGNED attributes.

  // Create or find the Values at the cell inputs

  // It is vital to generate the S input first, so that the
  // mux can later be optimized to if/else branching.  We don't want
  // select value to depend on an instruction that is part of the A
  // or B calculation.
  llvm::Value *valS = generateInputValue(cell, ID::S);
  unsigned valWidthS = getWidth(valS);
  log_assert(valWidthS == 1);

  llvm::Value *trueVal = generateInputValue(cell, ID::B);  // Possibly lots of recursion here
  unsigned trueValWidth = getWidth(trueVal);

  if (trueValWidth != cellWidth) {
    trueVal = b->CreateZExtOrTrunc(trueVal, llvmWidth(cellWidth));
    trueValWidth = getWidth(trueVal);
  }
  log_assert(trueValWidth == cellWidth);

  llvm::Value *falseVal = generateInputValue(cell, ID::A);  // Possibly lots of recursion here
  unsigned falseValWidth = getWidth(falseVal);

  if (falseValWidth != cellWidth) {
    falseVal = b->CreateZExtOrTrunc(falseVal, llvmWidth(cellWidth));
    falseValWidth = getWidth(falseVal);
  }
  log_assert(falseValWidth == cellWidth);

  log_assert(trueVal && falseVal);
  return b->CreateSelect(valS, trueVal, falseVal);
}


// Create a Value representing the output port of the given 3-input mux cell.
// Avoid actually creating a select instruction if inputs
// are constants, etc.
llvm::Value *
LLVMWriter::generateSimplifiedMuxCellOutputValue(RTLIL::Cell *cell)
{
  log_assert(cell->type == ID($mux));

  log_debug("generateMuxCellOutputValue(): cell port %s Y width %d:\n",
      cell->name.c_str(), cell->getPort(ID::Y).size());
  log_flush();

  // See the above rant on widths...
  // Muxes have only WIDTH attribute, applies to A/B/Y
  unsigned cellWidth = (unsigned)(cell->parameters[ID::WIDTH].as_int());

  unsigned sigWidthA = (unsigned)(cell->getPort(ID::A).size());  // Size of SigSpec
  unsigned sigWidthB = (unsigned)(cell->getPort(ID::B).size());  // Size of SigSpec
  unsigned sigWidthS = (unsigned)(cell->getPort(ID::S).size());  // Size of SigSpec
  unsigned sigWidthY = (unsigned)(cell->getPort(ID::Y).size());  // Size of SigSpec

  log_assert(sigWidthA == cellWidth);
  log_assert(sigWidthB == cellWidth);
  log_assert(sigWidthY == cellWidth);
  log_assert(sigWidthS == 1);

  // Muxes apparently do not have SIGNED attributes.

  // Create or find the Values at the cell inputs
  llvm::Value *valS = generateInputValue(cell, ID::S);
  unsigned valWidthS = getWidth(valS);
  log_assert(valWidthS == 1);

  // WARNING: Yosys and LLVM have opposite definitions of the A and B signals!
  // The Yosys cell's A signal is the "false" value and the B signal is the
  // "true" value.  But llvm's createSelect() function is defined like this:
  //   CreateSelect(Value *C, Value *True, Value *False);

  // If S is a constant zero or one, simply generate and return the A or B input.
  // Theoretically Yosys optimizations would get rid of such things, but
  // apparently not always.

  // TODO: Sanity check: pin widths match driver/load widths.

  // If A or B widths are different than their connections, zero
  // or sign-extend the input data.  No \SIGNED attributes to consider.
  // I have observed A/B input signals WIDER than the cell width

  llvm::Value *trueVal = nullptr;
  unsigned trueValWidth = 0;

  if (!isZero(valS)) {
    trueVal = generateInputValue(cell, ID::B);  // Possibly lots of recursion here
    trueValWidth = getWidth(trueVal);

    if (trueValWidth != cellWidth) {
      trueVal = b->CreateZExtOrTrunc(trueVal, llvmWidth(cellWidth));
      trueValWidth = getWidth(trueVal);
    }
    log_assert(trueValWidth == cellWidth);
  }

  llvm::Value *falseVal = nullptr;
  unsigned falseValWidth = 0;

  if (!isAllOnes(valS)) {
    falseVal = generateInputValue(cell, ID::A);  // Possibly lots of recursion here
    falseValWidth = getWidth(falseVal);

    if (falseValWidth != cellWidth) {
      falseVal = b->CreateZExtOrTrunc(falseVal, llvmWidth(cellWidth));
      falseValWidth = getWidth(falseVal);
    }
    log_assert(falseValWidth == cellWidth);
  }

  if (isAllOnes(valS)) {
    return trueVal;
  } else if (isZero(valS)) {
    return falseVal;
  }

  log_assert(trueVal && falseVal);
  return b->CreateSelect(valS, trueVal, falseVal);
}



// Create a Value representing the output port of the given 3-input pmux cell.
// This is a strange form of mux
// Yosys optimization can get rid pf pmux cells (e.g. the pmuxtree
// command), so we can avoid having to deal with them.
llvm::Value *
LLVMWriter::generatePmuxCellOutputValue(RTLIL::Cell *cell)
{
  if (!opts.support_pmux) {
    log_error("Unsupported pmux cell %s\n", cell->name.c_str());
    log("A:\n%s\n", log_signal(cell->getPort(ID::A)));
    log("B:\n%s\n", log_signal(cell->getPort(ID::B)));
    log("S:\n%s\n", log_signal(cell->getPort(ID::S)));
    log_flush();
    llvm::Value *valA = generateInputValue(cell, ID::A);  // Possibly lots of recursion here
    return valA;
  }

  ++pmuxIdx;


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

  llvm::Value *valS = generateInputValue(cell, ID::S);
  unsigned valWidthS = getWidth(valS);

  // Unique characteristic of pmux cells
  unsigned cellWidthB = cellWidthAY * cellWidthS;

  log_assert(sigWidthA == cellWidthAY);
  log_assert(sigWidthB == cellWidthB);
  log_assert(sigWidthY == cellWidthAY);
  log_assert(sigWidthS == cellWidthS);

  log_assert(valWidthS == cellWidthS);

  unsigned numCases = cellWidthS;
  
  // The driverSpec of input B is typically a concatenation of a bunch of things.
  // For each output choice, we generate the correct slice of B.
  DriverSpec bSpec;
  finder.buildDriverOf(cell->getPort(ID::B), bSpec);

  llvm::BasicBlock *originalBB = b->GetInsertBlock();

  std::string bbBaseName = "switch" + std::to_string(pmuxIdx);

  // Create a new BB for the default case
  llvm::BasicBlock *defaultBB = llvm::BasicBlock::Create(*c, bbBaseName+"_default", llvmFunc);

  // Another BB for the continuation past the switch cases
  llvm::BasicBlock *postBB = llvm::BasicBlock::Create(*c, bbBaseName+"_post", llvmFunc);

  // Make the switch instruction that will terminate the original BB.
  b->SetInsertPoint(originalBB);
  llvm::SwitchInst *switchInst = b->CreateSwitch(valS, defaultBB, numCases);

  // Give defaultBB a final branch to postBB
  b->SetInsertPoint(defaultBB);
  b->CreateBr(postBB);

  // We need to create all the case BBs and their termination branch
  // instructions before adding anything else to the branches, so that
  // we can properly update the dominance tree.
  
  std::vector<llvm::BasicBlock*> bbs(numCases);

  for(unsigned n = 0; n < numCases; n++) {

    // Create a new BB for the this case
    llvm::BasicBlock *caseBB = llvm::BasicBlock::Create(*c,
                bbBaseName+"_case"+std::to_string(n), llvmFunc);
    bbs[n] = caseBB;

    // Add the branch instruction that terminates this case BB
    b->SetInsertPoint(caseBB);
    b->CreateBr(postBB);

    // Create the ConstantInt that is the one-high bit mask for this case
    llvm::ConstantInt *caseVal = llvmInt(1<<n, numCases);

    // Update the switch instruction with the data for this case.
    switchInst->addCase(caseVal, caseBB);
  }

  valueCache.updateDominance();

  // Now fill in each case BB, and the default BB

  b->SetInsertPoint(defaultBB, defaultBB->begin());
  llvm::Value *defaultVal = generateInputValue(cell, ID::A);  // Possibly lots of recursion here

  // We have to put a Phi instruction at the beginning of postBB,
  // to gather the values of each case.
  b->SetInsertPoint(postBB, postBB->begin());
  llvm::PHINode *phiInst = b->CreatePHI(defaultVal->getType(), numCases+1);

  phiInst->addIncoming(defaultVal, defaultBB);
  
  for (unsigned n = 0, offset = 0; n < numCases; n++, offset += cellWidthAY) {

    // Get the previously-created BB for the this case
    llvm::BasicBlock *caseBB = bbs[n];

    // Create the instructions for this case
    b->SetInsertPoint(caseBB, caseBB->begin());
    DriverSpec sliceSpec = bSpec.extract(offset, cellWidthAY) ;
    llvm::Value *sliceVal = generateValue(sliceSpec);  // Possibly lots of recursion here

    //  Update the Phi instruction at the beginning of postBB.
    phiInst->addIncoming(sliceVal, caseBB);
  }

  // From now on, instructions go in the newly-created post BB,
  // right after the Phi instrction we put in it.
  b->SetInsertPoint(postBB);

  return phiInst;
}



// Unrolled memories are modeled by three special "magic" RTLIL cells:
//
// 1: A special "extractor" cell that models the decoding and
//    reading of the memory.
// 2: A special "inserter" cell that models a memory write.
// 3: An optional mux cell that implements a write enable by
//    bypassing the mux.
//
// Here we translate the signals representing the memory
// values to LLVM vectors, and translate the special cells to LLVM
// vector insert and extract instructions.
// 
// Sadly this memory support does not work in practice.  The generated
// LLVM code is semantically correct, but the X86 code generated by Clang
// does not run correctly.  There appear to be silent undocumented limitations
// in the Vector support. The code generator tries very hard to keep the vector
// data in the CPU XMM0-XMM7 registers, which offers no benefit, since all we
// ever do with the memory data is read and write one word at a time.
//
// A more practical approach would be to store the memory data in LLVM global variables.
// It would NOT be sufficient to use a single global array to represent a Verilog
// memory if the unrolled design does multiple writes or a read-after-write.
// The data flow of a memory through the unrolled design would have to be analyzed 
// to know when to make copies of a modified memory to ensure correct behavior.
// The extractor/inserter methodology we use when unrolling the design would
// still be appropriate for that.

llvm::Value *
LLVMWriter::generateMagicCellOutputValue(RTLIL::Cell *cell, RTLIL::IdString port)
{
  // These port names need to be consistent with the code in unroll.cc that creates
  // these cells.
  const RTLIL::IdString ADDR("\\ADDR");
  const RTLIL::IdString DATA("\\DATA");
  const RTLIL::IdString MEM_IN("\\MEM_IN");
  const RTLIL::IdString MEM_OUT("\\MEM_OUT");

  unsigned memWidth = (unsigned)(cell->parameters[ID::WIDTH].as_int());
  unsigned memSize = (unsigned)(cell->parameters[ID::SIZE].as_int());
  unsigned addrSize = (unsigned)(cell->parameters[ID::ABITS].as_int());

  unsigned sigWidthAddr = (unsigned)(cell->getPort(ADDR).size());  // Size of SigSpec
  unsigned sigWidthData = (unsigned)(cell->getPort(DATA).size());  // Size of SigSpec
  unsigned sigWidthMemIn = (unsigned)(cell->getPort(MEM_IN).size());  // Size of SigSpec

  log_assert(sigWidthAddr == addrSize);
  log_assert(sigWidthData == memWidth);
  log_assert(sigWidthMemIn == memWidth*memSize);

  // Create or find the Value at the address input
  llvm::Value *valAddr = generateInputValue(cell, ADDR); 
  log_assert(getWidth(valAddr) == addrSize);

  // Create or find the Value at the MEM_IN input
  llvm::Value *valMemIn = generateInputValue(cell, MEM_IN);
  log_assert(getWidth(valMemIn) == memWidth*memSize);

  if (cell->type == MEM_EXTRACT_MOD_NAME) {
    // Return the extract value (which goes out the DATA signal).
    log_assert(port == DATA);
    return b->CreateExtractElement(valMemIn, valAddr);

  } else if (cell->type == MEM_INSERT_MOD_NAME) {
    // Get the data value to be inserted
    llvm::Value *valData = generateInputValue(cell, DATA);
    log_assert(getWidth(valData) == memWidth);

    // Do the insert and return the updated memory value
    // (which goes out the MEM_OUT signal).
    log_assert(port == MEM_OUT);
    return b->CreateInsertElement(valMemIn, valData, valAddr);

  } else {
    assert(false);
    return nullptr;
  }
}


llvm::Value *
LLVMWriter::generateUserDefinedCellOutputValue(RTLIL::Cell *cell, RTLIL::IdString port)
{
  // If possible, execute a function call to a function previously defined for this cell/output
  RTLIL::Module *submod = design->module(cell->type);
  std::string subFuncName = getSubFunctionName(submod, port);
  llvm::Function *func = llvmMod->getFunction(subFuncName);

  if (!func) {
    log_warning("No function defined for non-builtin cell %s type %s\n",
                cell->name.c_str(), cell->type.c_str());
    RTLIL::SigSpec outputSig = cell->getPort(port);
    return llvmZero(outputSig.size());  // Dummy value  
  }

  std::vector<llvm::Value*> args;
  for (RTLIL::IdString portname : submod->ports) {
    RTLIL::Wire *port = submod->wire(portname);
    log_assert(port);
    if (port->port_input) {
      llvm::Value *argVal = generateInputValue(cell, portname);
      args.push_back(argVal);
    }
  }

  // TODO: Check that args and their types match the function's type?
  // Any error should get flagged downstream by verifyFunction() or opt.

  return b->CreateCall(func, args);
}

llvm::Value *
LLVMWriter::generateFFCellOutputValue(RTLIL::Cell *cell)
{
  // FF cells should not exist in the unrolled design.
  // But when generatin sub-functions, we can tolerate FFs that
  // drive a sub-module output port.

  log_warning("Unsupported FF cell %s type %s\n",
              cell->name.c_str(), cell->type.c_str());

  // Pass the D input through the FF.  This is really only
  // acceptable for simple dffs that drive sub-function outputs.
  llvm::Value *valD = generateInputValue(cell, ID::D);  // Get D input
  return valD;
}


// Create a Value representing the output port of the given cell.
// Since this is not given a DriverSpec, it does not touch the valueCache.
// The caller is reponsible for that.
// TODO: Should it instead make a temporary DriverSpec to access the valueCache?
llvm::Value *
LLVMWriter::generateCellOutputValue(RTLIL::Cell *cell, RTLIL::IdString port)
{
  // This function handles only builtin cells and a couple of magic cells we create.
  // Hierarchical modules are supported in a limited way.

  RTLIL::SigSpec outputSig = cell->getPort(port);

  if (cell->type[0] == '\\') {
    // See if the user-defined cell is one of our magic ones.
    RTLIL::Module *m = design->module(cell->type);
    if (m && m->get_bool_attribute(MEM_MOD_ATTR)) {
      return generateMagicCellOutputValue(cell, port);
    } else if (opts.support_hierarchy) {
      return generateUserDefinedCellOutputValue(cell, port);
    } else {
      log_error("Unsupported hierarchical cell %s type %s\n",
                  cell->name.c_str(), cell->type.c_str());
      return llvmZero(outputSig.size());  // Dummy value  
    }
  }

  // Special case: built-in FF cells.
  if (RTLIL::builtin_ff_cell_types().count(cell->type) != 0) {
    return generateFFCellOutputValue(cell);
  }


  // All builtin combinatorial cell outputs are supposed to be Y
  if (port != ID::Y) {
    log_warning("Cell %s type %s has non-Y output!\n",
                        cell->name.c_str(), cell->type.c_str());
    return llvmZero(outputSig.size());  // Dummy value  
  }

  log_assert(cell->output(port));

  log_debug("generateCellOutputValue(): cell port %s Y  width %d:\n",
      cell->name.c_str(), outputSig.size());
  log_flush();

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
              log_error("Unsupported cell %s type %s\n",
                          cell->name.c_str(), cell->type.c_str());
              val = generateInputValue(cell, ID::A);  // Fallback
            }
            break;
    default: 
      log_warning("Totally weird cell %s type %s\n",
                          cell->name.c_str(), cell->type.c_str());
      val = generateInputValue(cell, ID::A);  // Fallback
      break;
  }

  // For the unary cells that output a logical value ($reduce_and,
  // $reduce_or, $reduce_xor, $reduce_xnor, $reduce_bool, $logic_not), when
  // the \Y_WIDTH parameter is greater than 1, the output is zero-extended,
  // and only the least significant bit varies.
  // Also for cells in general, if the cell's Y width is less than the 
  // width of the calculated value, we must truncate it.

  if (cell->hasParam(ID::Y_WIDTH)) {
    unsigned cellWidthY = (unsigned)(cell->parameters[ID::Y_WIDTH].as_int());
    if (cellWidthY > 0 && cellWidthY != getWidth(val)) {
      val = b->CreateZExtOrTrunc(val, llvmWidth(cellWidthY));
    }
  }

  // If the new Value is an Instruction, optionally give it an
  // explicit name.  But don't re-name things, and don't try to name
  // non-Instructions, especially function args.  Depending on options
  // settings, the name (if any) will be based on the cell or wire name.
  // BTW, Yosys cell names are mostly auto-generated, not user-defined.

  if (llvm::isa<llvm::Instruction>(val) && val->getName().empty()) {
    if (opts.cell_based_llvm_value_names) {
      val->setName(internalToLLVM(cell->name));
    } else if (outputSig.is_wire()) {
      RTLIL::IdString valName = outputSig.as_wire()->name;
      if (opts.verbose_llvm_value_names || valName[0] != '$') { 
        // Default: use only user defined wire names
        val->setName(internalToLLVM(valName));
      }
    }
  }

  return val;
}



// Generate the value of the given chunk, which is constant, or a
// slice of a single wire or cell output.  The result will be offset
// by the given amount, and zero-extended to totalWidth.
llvm::Value *
LLVMWriter::generateChunkValue(const DriverChunk& chunk,
                               int totalWidth, int offset)
{
  log_debug("generateChunkValue totalWidth %d offset %d  ", totalWidth, offset);
  log_debug_driverchunk(chunk);
  log_assert(totalWidth >= chunk.size() + offset);

  if (chunk.is_data()) {
    // Sanity checks
    log_assert(chunk.offset == 0);
    log_assert((long unsigned)chunk.size() == chunk.data.size());

    // Build a string of the desired ones and zeros, with 0 padding
    // at the beginning and/or end.

    std::string valStr = chunk.as_string();
    log_assert(valStr.size() == (long unsigned)chunk.size());


    if (DriverSpec(chunk).is_fully_undef() && totalWidth == chunk.size()) {
      log_assert(offset == 0);
      log_warning("All-x driver chunk found: %s\n", valStr.c_str());
      return llvmUndefValue(totalWidth);

    } else if (!DriverSpec(chunk).is_fully_def()) {
      log_warning("Partial-x driver chunk found: %s width %d\n", valStr.c_str(), totalWidth);

      // Clean up. TODO: Be more clever about mapping 'x' to either 0 or 1,
      // with the goal of simplifying the logic.
      for (char& ch : valStr) {
        if (ch != '0' && ch != '1') ch = '0';
      }
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

  // OK, the chunk is a slice of a wire or cell output.
  log_assert (chunk.size() <= chunk.object_width() - chunk.offset); // Basic sanity check

  if (offset == chunk.offset) {
    // The signal bits do not need to be shifted - we just have to zero-extend
    // and/or truncate it, and maybe zero out some low-order bits.
    // A typical example: { \reg_next_pc___#1_ [31:2], 2'h0 }

    // Find or make a Value for the entire wire or cell output
    DriverSpec objDs = chunk.wire ? DriverSpec(chunk.wire) : DriverSpec(chunk.cell, chunk.port);
    log_assert(objDs.is_cell() || objDs.is_wire());
    llvm::Value *val = generateValue(objDs);  // Will be added to valueCache

    // Truncate any unwanted high-order bits
    if (getWidth(val) > (unsigned)(chunk.size()+chunk.offset)) {
      val = b->CreateTrunc(val, llvmWidth(chunk.size()+chunk.offset));
    }

    // Zero-extend it if necessary to the desired total width
    log_assert(getWidth(val) <= (unsigned)totalWidth);
    if (getWidth(val) < (unsigned)totalWidth) {
      val = b->CreateZExt(val, llvmWidth(totalWidth));
    }

    // Mask off the low-order bits as required
    if (offset > 0) {
      // TODO: It would be more elegant to use llvm::APInt...
      std::string maskStr = std::string((totalWidth - offset), '1') +
                            std::string(offset, '0');

      llvm::ConstantInt *mask = llvm::ConstantInt::get(llvmWidth(totalWidth),
                                  llvm::StringRef(maskStr), 2 /*radix*/);

      val = generateAndCellOutputValue(val, mask);
    }

    // TODO: Is it worth adding this to the valueCache?  It would be necessary
    // to create a relatively complex temporary DriverSpec to serve as the key.

    return val;
  } 

  // The more general case: the signal data needs to be shifted
  // TODO: This can be simplified!

  // See if we already have a Value for this (non-offset) object slice
  DriverSpec tmpDs(chunk);
  llvm::Value *val = valueCache.find(tmpDs, b->GetInsertBlock());

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
    if (getWidth(val) > (unsigned)chunk.size()) {
      val = b->CreateTrunc(val, llvmWidth(chunk.size()));
    }

    // If we actually did any shifting or truncating, add the new Value to valueCache.
    if (val != objVal) {
      valueCache.add(tmpDs, val);
    }
  }

  // val now represents the slice of wire/port - now we may have to left-shift and/or
  // zero-extend it to the final desired size.

  if (offset == 0 && totalWidth == chunk.size()) {
    return val;  // No padding needed
  }

  // Extend before shifting!
  if (getWidth(val) < (unsigned)totalWidth) {
    val = b->CreateZExt(val, llvmWidth(totalWidth));
  }

  if (offset > 0) {
    val = b->CreateShl(val, offset);
  }

  // TODO: Is it worth adding this to the valueCache?  It would be necessary
  // to create a relatively complex temporary DriverSpec to serve as the key.

  return val;
}


// Generate a value for a top-level input port.  These correspond
// to either LLVM function parameters (for regular ASVs) or elements
// of a ASV vector.

llvm::Value *
LLVMWriter::generatePrimaryInputValue(RTLIL::Wire *port)
{
  assert (port->port_input);
  std::string argname = internalToLLVM(port->name, true);  // Take care to match the old func_extract behavior
  llvm::Value *val = nullptr;

  if (!port->has_attribute(TARGET_VECTOR_ATTR)) {
    // A regular ASV that is supposed to have a function argument.
    // Simply find the correct arg.
    val = llvmFunc->getValueSymbolTable()->lookup(argname);
    log_assert(val);

  } else {
    // Get the correct array and index from attributes we previously set on the port,
    // and generate a load instruction to get its value.
    std::string arrayName = port->get_string_attribute(TARGET_VECTOR_ATTR);
    int idx = std::stoi(port->get_string_attribute(TARGET_VECTOR_IDX_ATTR));
    unsigned width = port->width;

    // Find the function arg that is the pointer to the array.
    llvm::Value *array = llvmFunc->getValueSymbolTable()->lookup(arrayName);
    log_assert(array);

    val = generateLoad(array, width, idx, argname);
  }

  log_assert(val);
  return val;
}


// Generate the Value for the given Driverspec.  This function
// may recursively call lots of other stuff.

llvm::Value *
LLVMWriter::generateValue(const DriverSpec& dSpec)
{
  llvm::Value *val = valueCache.find(dSpec, b->GetInsertBlock());
  if (val) {
    return val;  // Should often be the case.
  }

  if (dSpec.is_wire()) {
    // An entire wire, which is supposed to represent a module input port.
    log_debug("generateValue for primary input port\n");
    log_debug_driverspec(dSpec);

    // The generated Value could be either a function arg or a load instruction.
    llvm::Value *val = generatePrimaryInputValue(dSpec.as_wire());
    valueCache.add(dSpec, val);
    return val;

  } else if (dSpec.is_cell()) {
    // An entire cell output.
    RTLIL::IdString portName;
    RTLIL::Cell *cell = dSpec.as_cell(portName);
    llvm::Value *val = generateCellOutputValue(cell, portName);
    valueCache.add(dSpec, val);
    return val;

  } else if (dSpec.is_fully_const()) {
    // valStr will be of the form [01xzm-]*
    std::string valStr = dSpec.as_const().as_string();

    // Ideally there would not be explicit 'x' values here!
    // The optimization and cleanup already done should have gotten rid of most of them.

    if (dSpec.is_fully_undef()) {
      log_warning("All-x driver spec found: %s\n", valStr.c_str());
      return llvmUndefValue(dSpec.size());
    } else if (!dSpec.is_fully_def()) {
      log_warning("Partial-x driver spec found: %s\n", valStr.c_str());

      // Clean up.
      for (char& ch : valStr) {
        if (ch != '0' && ch != '1') ch = '0';
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
      values.push_back(generateChunkValue(chunk, dSpec.size(), offset));
      offset += chunk.size();
    }

    if (values.size() == 1) {
      return values[0];  // A single chunk (already added to valueCache).
    }

    // Multiple chunks: OR them all together
    llvm::Value *val = nullptr;
    for (llvm::Value* v : values) {
      if (!isZero(v)) {
        if (!val) {
          val = v;
        } else {
          val = b->CreateOr(val, v);
        }
      }
    }

    if (!val) {
      // All zero chunks
      return values[0];
    }

    valueCache.add(dSpec, val);
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



// Get the LLVM type of a particular Yosys port.  Usually it is an
// integer of some width, but it could also be an LLVM Vector, if
// the port represents a Verilog memory array.

llvm::Type*
LLVMWriter::getLlvmType(RTLIL::Wire *port)
{
  if (port->has_attribute("\\vector_width")) {
    // The port represents an entire memory, in which case it will 
    // have an LLVM vector type.
    int width = std::stoi(port->get_string_attribute("\\vector_width"));
    int size = std::stoi(port->get_string_attribute("\\vector_size"));
    log_assert(port->width == width*size);
    return llvmVectorType(width, size);
  }

  // A regular scalar integer.
  return llvmWidth(port->width);
}



llvm::Function*
LLVMWriter::generateFunctionDecl(const std::string& funcName, RTLIL::Module *mod,
                                 const Yosys::dict<std::string, unsigned>& targetVectors,
                                 int retWidth,    // Zero for void, negative for array
                                 int retVecSize)  // Non-zero only for LLVM vector return type
{
  std::vector<llvm::Type *> argTypes;

  // Add every module input port, which includes the first-cycle register inputs
  // and the unrolled versions of the original input ports.
  for (RTLIL::IdString portname : mod->ports) {
    RTLIL::Wire *port = mod->wire(portname);
    log_assert(port);
    // Skip ASVs in register arrays.
    if (!port->has_attribute(TARGET_VECTOR_ATTR)) {
      if (port->port_input) {
        argTypes.push_back(getLlvmType(port));
      }
    }
  }

  // Push the types of any register array args (which are of course pointers)
  for(auto vecNameWidth: targetVectors) {
    unsigned width = vecNameWidth.second;

    // The array element width is the padded width of the vector's elements!
    // Note that in LLVM 14, all pointers will be untyped, so we won't need
    // the width here.
    uint32_t paddedWidth = funcExtract::get_padded_width(width);
    llvm::Type *paddedArrayElementTy = llvmWidth(paddedWidth);
    argTypes.push_back(llvm::PointerType::getUnqual(paddedArrayElementTy));

    // Unfortunately in LLVM 13.0.1, 'opt -O3' crashes if we use an opaque pointer here.
    //argTypes.push_back(llvm::PointerType::getUnqual(*c));
  }

  // If the target is a register array, add one more arg that is a pointer to its storage.
  // In this case, the function will return void.
  if(retWidth < 0) {

    uint32_t paddedWidth = funcExtract::get_padded_width(-retWidth);
    llvm::Type *paddedArrayElementTy = llvmWidth(paddedWidth);
    argTypes.push_back(llvm::PointerType::getUnqual(paddedArrayElementTy));

    // Unfortunately in LLVM 13.0.1, 'opt -O3' crashes if we use an opaque pointer here.
    // argTypes.push_back(llvm::PointerType::getUnqual(*TheContext));
  }

  // A return type of the correct width (possibly a LLVM Vector, or void)
  llvm::Type* retTy;
  if (retVecSize > 0) {
    log_assert(retWidth > 0);
    retTy = llvmVectorType(retWidth, retVecSize);
  } else if (retWidth > 0) {
    retTy = llvmWidth(retWidth);
  } else {
    retTy = llvm::Type::getVoidTy(*c); // Result is returned via additional arg added above.
  }

  llvm::FunctionType *functype =
    llvm::FunctionType::get(retTy, argTypes, false);

  // Create the main function
  llvm::Function::LinkageTypes linkage = llvm::Function::ExternalLinkage;

  llvm::Function *func = llvm::Function::Create(functype, linkage, funcName, llvmMod);

  // Set the function's args' names.  Note
  // that the arg names come from attribues we set earlier based on their
  // original Verilog names.  It is important to match the naming convention
  // of the original func_extract program.  Later these argument names will be
  // used to create func_info.txt, which is used by the sim_gen program.

  unsigned n = 0;
  for (RTLIL::IdString portname : mod->ports) {
    RTLIL::Wire *port = mod->wire(portname);
    // Skip ASVs in register arrays.
    if (port->port_input && !port->has_attribute(TARGET_VECTOR_ATTR)) {
      llvm::Argument *arg = func->getArg(n);
      arg->setName(internalToLLVM(portname, true));  // Take care to match the old func_extract behavior
      n++;
    }
  }

  // Set the the register array arg names.  
  // Nothing gets added to the valueCache here - it is done a bit later,
  // since load instructions have to be generated for them.
  for(auto vecNameWidth: targetVectors) {
    llvm::Argument *arg = func->getArg(n);
    arg->setName(vecNameWidth.first);
    n++;
  }

  // If the target is a register array, name the last arg that is a pointer to its storage.
  if(retWidth < 0) {
    llvm::Argument *arg = func->getArg(n);
    arg->setName(funcExtract::RETURN_ARRAY_PTR_ID);  // sim_gen will recognize this name in func_info.txt
  }

  return func;
}


// The main update function is created.  It is assumed that the llvm::Module already exists.
// The LLVM is not written out.
llvm::Function*
LLVMWriter::writeMainFunction(RTLIL::Module *unrolledRtlMod,
                          std::string targetName,  // As specified in allowed_target.txt
                          bool targetIsVec,       // target is ASV vector
                          int num_cycles,
                          std::string funcName)
{

  log_assert(llvmMod);

  clearFunctionData();

  log("Generating main function\n");

  finder.build(unrolledRtlMod);
  log("%ld objects in driverFinder\n", finder.size());

  // We  need a collection of all known input target vectors and their widths.
  // Get this by scanning input ports and looking at attributes that our
  // caller has set on them. 
  Yosys::dict<std::string, unsigned> targetVectors;
  for (RTLIL::IdString portname : unrolledRtlMod->ports) {
    RTLIL::Wire *port = unrolledRtlMod->wire(portname);
    if (port->port_input && port->has_attribute(TARGET_VECTOR_ATTR)) {
      std::string vecName = port->get_string_attribute(TARGET_VECTOR_ATTR);
      if (!targetVectors.count(vecName)) {
        targetVectors[vecName] = port->width;
      } else {
        // Check for consistent widths of each vector element
        log_assert(targetVectors[vecName] == (unsigned)port->width);
      }
    }
  }


  // Now to actually start generating code

  if (!targetIsVec) {
    // Get the Yosys RTLIL object representing the destination ASV.
    RTLIL::IdString portName = cycleize_name(targetName, num_cycles+1);
    RTLIL::Wire *targetPort = unrolledRtlMod->wire(portName);

    if (!targetPort) {
      log_error("Can't find output port %s for destination ASV %s\n", portName.c_str(), targetName.c_str());
      return nullptr;
    }

    int targetWidth;
    int targetVecSize;

    // Figure out the target's width and vector size
    llvm::Type *targetType = getLlvmType(targetPort);
    if (targetType->isIntegerTy()) {
      targetWidth = getWidth(targetType);
      targetVecSize = 0;
    } else if (targetType->isVectorTy()) {
      llvm::VectorType *vecTy = llvm::dyn_cast<llvm::VectorType>(targetType);
      targetWidth = getWidth(vecTy->getElementType());
      targetVecSize = vecTy->getElementCount().getFixedValue();
    } else {
      targetWidth = 0;
      targetVecSize = 0;
      log_assert(false);
    }

    if (targetVecSize > 0) {
      log("Memory array target %s\n", targetName.c_str());
    } else {
      log("Scalar target %s\n", targetName.c_str());
    }

    llvmFunc = generateFunctionDecl(funcName, unrolledRtlMod, targetVectors,
                                    targetWidth, targetVecSize);

    // basic block
    llvm::BasicBlock *BB = llvm::BasicBlock::Create(*c, "bb_;_"+targetName, llvmFunc);
    b->SetInsertPoint(BB);


    log("Target SigSpec: ");
    my_log_wire(targetPort);
    log_assert(targetPort->port_output);
  
    // Collect the drivers of each bit of the destination wire
    DriverSpec dSpec;
    finder.buildDriverOf(targetPort, dSpec);

    // Print what drives the bits of this wire
    log_debug_driverspec(dSpec);
    log_debug("\n");

    llvm::Value *destValue = generateValue(dSpec);

    b->CreateRet(destValue);
  } else {
    log("Vector target %s\n", targetName.c_str());

    llvm::Value *returnValueArray = nullptr;
    std::string cycleizedTargetName = internalToLLVM(cycleize_name(targetName, num_cycles+1));
    log_debug("Cycleized vector target %s\n", cycleizedTargetName.c_str());
    log_flush();

    // Scan over all the input ports, and process all the ones belonging to
    // the given target vector.  The target element width is taken from the first
    // element we find.
    for (RTLIL::IdString portname : unrolledRtlMod->ports) {
      RTLIL::Wire *targetPort = unrolledRtlMod->wire(portname);
      if (targetPort->get_string_attribute(TARGET_VECTOR_ATTR) == cycleizedTargetName) {

        int idx = std::stoi(targetPort->get_string_attribute(TARGET_VECTOR_IDX_ATTR));
        log_debug("Vector target %s[%d]\n", targetName.c_str(), idx);
        log_flush();

        log_assert(targetPort->port_output);

        // Collect the drivers of each bit of the destination wire
        DriverSpec dSpec;
        finder.buildDriverOf(targetPort, dSpec);

        // Print what drives the bits of this wire
        log_debug_driverspec(dSpec);
        log_debug("\n");

        // We cannot declare the function until we know the width of the targets
        if (!llvmFunc) {
          llvmFunc = generateFunctionDecl(funcName, unrolledRtlMod, targetVectors,
                                          -(targetPort->width), 0);

          // Get the function argument that points to where the return values go.
          returnValueArray = llvmFunc->getValueSymbolTable()->lookup(
                                            funcExtract::RETURN_ARRAY_PTR_ID);
          log_assert(returnValueArray);

          // basic block
          llvm::BasicBlock *BB = llvm::BasicBlock::Create(*c, "bb_;_"+targetName, llvmFunc);
          b->SetInsertPoint(BB);
        }


        llvm::Value *destValue = generateValue(dSpec);

        // Store each calculated value into the correct location in the special return array.
        log_assert(returnValueArray);
        generateStore(returnValueArray, idx, destValue);
      }
    }

    b->CreateRetVoid();
  }

  log_assert(llvmFunc);


  log("%lu Values in valueCache\n", valueCache.size());
  log("%lu hits, %lu misses\n", valueCache.nHits(), valueCache.nMisses());
  log("%u LLVM instructions generated\n", llvmMod->getInstructionCount());

  llvm::verifyFunction(*llvmFunc);
  llvm::verifyModule(*llvmMod);

  return llvmFunc;
}



std::string
LLVMWriter::getSubFunctionName(RTLIL::Module *submod,
                               RTLIL::IdString returnPortName)
{
  return "func_;_" + internalToLLVM(submod->name) + "_$" + internalToLLVM(returnPortName);
}



// Generate a function declaration whose parameters are the module's input
// ports, and whose return value is the given output port.  The top-level
// ASVs, etc. are irrelevant.
llvm::Function*
LLVMWriter::generateSubFunctionDecl(RTLIL::Module *submod,
                                    RTLIL::Wire *returnPort)
{
  std::string funcName = getSubFunctionName(submod, returnPort->name);

  std::vector<llvm::Type *> argTypes;

  // Add every module input port. The caller will expect the function args
  // to be ordered this way - it will not match them by name.
  for (RTLIL::IdString portname : submod->ports) {
    RTLIL::Wire *port = submod->wire(portname);
    log_assert(port);
    if (port->port_input) {
      argTypes.push_back(getLlvmType(port));
    }
  }

  log_assert (returnPort->port_output && !returnPort->port_input);

  // A return type of the correct width
  llvm::Type* retTy = llvmWidth(returnPort->width);

  llvm::FunctionType *functype =
    llvm::FunctionType::get(retTy, argTypes, false);

  // Create the actual function object
  llvm::Function::LinkageTypes linkage = llvm::Function::InternalLinkage;

  llvm::Function *func = llvm::Function::Create(functype, linkage, funcName, llvmMod);

  // Set the function's args' names.  
  unsigned n = 0;
  for (RTLIL::IdString portname : submod->ports) {
    RTLIL::Wire *port = submod->wire(portname);
    if (port->port_input) {
      llvm::Argument *arg = func->getArg(n);
      arg->setName(internalToLLVM(portname, true));  // Take care to match the old func_extract behavior
      n++;
    }
  }

  return func;
}


// Write a sub-function, which calculates one output port of a child RTL module.
// The child module is not unrolled, and needs to be purely combinatorial.

llvm::Function*
LLVMWriter::writeSubFunction(RTLIL::Module *submod,
                             RTLIL::IdString returnPortName)
{

  clearFunctionData();  // Resets function-specific stuff, but does not touch llvmMod

  log("Generating sub function for module %s port %s\n",
      submod->name.c_str(), returnPortName.c_str());

  finder.build(submod);
  log("%ld objects in driverFinder\n", finder.size());

  RTLIL::Wire *returnPort = submod->wire(returnPortName);
  llvmFunc = generateSubFunctionDecl(submod, returnPort);
  log_assert(llvmFunc);

  // basic block
  std::string bbName = "bb_;_" + internalToLLVM(submod->name) + "_$" +
                        internalToLLVM(returnPortName);
  llvm::BasicBlock *BB = llvm::BasicBlock::Create(*c, bbName, llvmFunc);
  b->SetInsertPoint(BB);


  log("Return value SigSpec: ");
  my_log_wire(returnPort);
  log_assert(returnPort->port_output);

  // Collect the drivers of each bit of the return port
  DriverSpec dSpec;
  finder.buildDriverOf(returnPort, dSpec);

  log_debug_driverspec(dSpec);
  log_debug("\n");

  // Generate the actual code
  llvm::Value *returnValue = generateValue(dSpec);

  b->CreateRet(returnValue);



  log("%lu Values in valueCache\n", valueCache.size());
  log("%lu hits, %lu misses\n", valueCache.nHits(), valueCache.nMisses());
  log("%u LLVM instructions generated\n", llvmMod->getInstructionCount());

  llvm::verifyFunction(*llvmFunc);

  return llvmFunc;
}

bool
LLVMWriter::isProperSubModule(RTLIL::Module *mod)
{
  // If the module is one of our magic ones for supporting vectors, skip it
  return mod && mod->name[0] != '$' && !mod->get_bool_attribute(MEM_MOD_ATTR);
}


// Write a function of each output port of the given module.
void
LLVMWriter::writeSubFunctions(RTLIL::Module *submod)
{

  for (RTLIL::IdString portname : submod->ports) {
    RTLIL::Wire *port = submod->wire(portname);
    if (port->port_output) {
      std::string subFuncName = getSubFunctionName(submod, portname);
      // If a function by this name does not exist, create it.
      if (!llvmMod->getFunction(subFuncName)) {
        writeSubFunction(submod, portname);
      }
    }
  }
}



// Recursively write functions for output ports of RTL sub-modules.
void
LLVMWriter::recurseSubFunctions(RTLIL::Module *mod)
{

  // Recursively write the sub functions in bottom-up order
  for (auto cell : mod->cells()) {
    RTLIL::Module *submod = design->module(cell->type);
    if (isProperSubModule(submod)) {
      recurseSubFunctions(submod);
    }
  }
  writeSubFunctions(mod);
}



void
LLVMWriter::write_llvm_ir(RTLIL::Module *unrolledRtlMod,
                          std::string targetName,  // As specified in allowed_target.txt
                          bool targetIsVec,       // target is ASV vector
                          std::string modName,  // from original Verilog, e.g. "M8080"
                          int num_cycles,
                          std::string llvmFileName,
                          std::string funcName)
{

  log_assert(!llvmMod);
  llvmMod = new llvm::Module("mod_;_"+modName+"_;_"+targetName, *c);

  clearFunctionData();

  // If desired, write functions for output ports of RTL sub-modules.

  if (opts.support_hierarchy) {
    for (auto cell : unrolledRtlMod->cells()) {
      RTLIL::Module *submod = design->module(cell->type);
      if (isProperSubModule(submod)) {
        recurseSubFunctions(submod);
      }
    }
  }


  writeMainFunction(unrolledRtlMod, targetName, targetIsVec, num_cycles, funcName);

  log_assert(llvmFunc);


  log("%u LLVM instructions generated\n", llvmMod->getInstructionCount());

  llvm::verifyModule(*llvmMod);


  if (opts.optimize_muxes) {
    log("Optimizing muxes...\n");
    BranchMux::convertSelectsToBranches(llvmMod, opts.optimize_mux_threshold);
  }

  std::string Str;
  llvm::raw_string_ostream OS(Str);
  OS << *llvmMod;
  OS.flush();

  std::ofstream output(llvmFileName);
  output << Str << std::endl;
  output.close();

  clearFunctionData();

  delete llvmMod;
  llvmMod = nullptr;  
}


