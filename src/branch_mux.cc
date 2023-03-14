#include "branch_mux.h"
  
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

#include <iostream>
#include <set>
#include <list>


static std::string instrToString(const llvm::Instruction* inst)
{
  std::string str;
  llvm::raw_string_ostream ss(str);
  ss << *inst;
  ss.flush();
  return str;
}

BranchMux::BranchMux(llvm::Function *f) : func(f) 
{
}

BranchMux::~BranchMux()
{
}



// Build fanin cone for a given instruction (including the instruction
// itself).  Stay within the same BasicBlock
void BranchMux::getFaninCone(llvm::Instruction* inst,
                          std::set<llvm::Instruction*>& cone)
{
  cone.insert(inst);
  for (const auto& faninUse : inst->operands()) {
    llvm::Value* faninVal = faninUse.get();
    if (faninVal && llvm::isa<llvm::Instruction>(faninVal)) {
      llvm::Instruction *faninInst = llvm::cast<llvm::Instruction>(faninVal);
      if (cone.count(faninInst) == 0 &&
          faninInst->getParent() == inst->getParent()) {  // In same BB
        getFaninCone(faninInst, cone);   // Recurse depth-first
      }
    }
  }
}


// If the given Value is not an Instruction, this does nothing.
void BranchMux::getFaninCone(llvm::Value* val,
                          std::set<llvm::Instruction*>& cone)
{
  if (val && llvm::isa<llvm::Instruction>(val)) {
    getFaninCone(llvm::cast<llvm::Instruction>(val), cone);
  }
}



// Expel from the given fanin cone any instruction that is also
// used outside the cone and parentInst. (Presumably the root instruction
// of the cone itself is an operand of parentInst.)
void BranchMux::pruneFaninCone(std::set<llvm::Instruction*>& cone,
                               const llvm::Instruction *parentInst)
{
  // Speed trick: Any Instruction belonging to a different BB cannot be in the fanin cone.
  const llvm::BasicBlock *bb = parentInst->getParent();

  // Repeated sweep over the cone, until nothing else can be expelled.
  // When an instruction is expelled from the cone, its fanin must also be expelled.
  for (;;) {
    int ndeleted = 0;
    for (auto it = cone.begin(); it != cone.end(); ) {
      llvm::Instruction *inst = *it;
      assert(inst->getParent() == bb);

      // Check if there is any usage of this Instruction outside of
      // the cone and parentInst.
      bool deleteThis = false;
      for (const llvm::Use& use : inst->uses()) {
        llvm::User *user = use.getUser();
        assert(llvm::isa<llvm::Instruction>(user));
        llvm::Instruction *userInst = llvm::cast<llvm::Instruction>(user);
        if (userInst->getParent() != bb ||
            (userInst != parentInst && !cone.count(userInst))) {
          // The current inst is used outside of the cone, so we will expel it.
          deleteThis = true;
          break;
        }
      }
      if (deleteThis) {
        ndeleted++;
        it = cone.erase(it);  // Properly advance cone iterator
      } else {
        ++it;
      }
    }

    if (ndeleted == 0)
      break;
  }
}



bool BranchMux::convertSelectToBranch(llvm::SelectInst* select)
{

  std::set<llvm::Instruction*> trueFaninCone;
  getFaninCone(select->getTrueValue(), trueFaninCone);

  std::set<llvm::Instruction*> falseFaninCone;
  getFaninCone(select->getFalseValue(), falseFaninCone);

  printf("Select %s: true fanin %lu  false fanin %lu\n", instrToString(select).c_str(), 
          trueFaninCone.size(), falseFaninCone.size());

  pruneFaninCone(trueFaninCone, select);
  pruneFaninCone(falseFaninCone, select);

  printf("  Pruned size: true fanin %lu  false fanin %lu\n", 
          trueFaninCone.size(), falseFaninCone.size());

  return true;
}



bool BranchMux::convertSelectsToBranches()
{
  std::list<llvm::SelectInst*> selects;
  
  // Gather the selects, in reverse order.
  // We can't iterate directly over the contents of the BB
  // since we are going to cut it apart.
  for (auto& bb : func->getBasicBlockList()) {
    for (auto& instr : bb.instructionsWithoutDebug()) {
      if (instr.getOpcode() == llvm::Instruction::Select) {
        llvm::SelectInst& select = llvm::cast<llvm::SelectInst>(instr);
        selects.push_front(&select);
      }
    }
  }

  // Convert them, starting from the end of the function and working backwards.
  for (llvm::SelectInst *select : selects) {
    convertSelectToBranch(select);
  }

  return true;
}
