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


// A compare function that compares Instructions in the same BB by their ordering.
bool BranchMux::InstrLess::operator()(llvm::Instruction* const& a,
                                      llvm::Instruction* const& b) const
{
  if (a == b) return false;

  // Not really meant to be used for Instructions in different BBs.
  // TODO: Compare actual BB ordering in Function, for full usefulness.
  if (a->getParent() != b->getParent()) {
    return a->getParent() < b->getParent();
  }

  return a->comesBefore(b);
}


// Build fanin cone for a given instruction (including the instruction
// itself).  Stay within the same BasicBlock
void BranchMux::getFaninCone(llvm::Instruction* inst, InstSet& cone)
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


// If the given Value is not an Instruction, or the instruction
// dopes not belong to the given bb, this does nothing.
void BranchMux::getFaninCone(llvm::BasicBlock *bb, llvm::Value* val, InstSet& cone)
{
  if (val && llvm::isa<llvm::Instruction>(val)) {
    if (llvm::cast<llvm::Instruction>(val)->getParent() == bb) {
      getFaninCone(llvm::cast<llvm::Instruction>(val), cone);
    }
  }
}



// Expel from the given fanin cone any instruction that is also
// used outside the cone and parentInst. (Presumably the root instruction
// of the cone itself is an operand of parentInst.)
void BranchMux::pruneFaninCone(InstSet& cone, const llvm::Instruction *parentInst)
{
  // Speed trick: Any Instruction belonging to a different BB cannot be in the fanin cone.
  const llvm::BasicBlock *bb = parentInst->getParent();

  // Repeatedly sweep over the cone, until nothing else can be expelled.
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


// This only works if all the instrucitons in teh set belong to the same BB.
llvm::Instruction *BranchMux::firstInstr(const InstSet& set)
{
  llvm::Instruction *first = *(set.begin());
  for (llvm::Instruction *inst : set) {
    if (inst->comesBefore(first)) {
      first = inst;
    }
  }
  return first;
}


// This only works if all the instrucitons in teh set belong to the same BB.
llvm::Instruction *BranchMux::lastInstr(const InstSet& set)
{
  llvm::Instruction *last = *(set.begin());
  for (llvm::Instruction *inst : set) {
    if (last->comesBefore(inst)) {
      last = inst;
    }
  }
  return last;
}



bool BranchMux::convertSelectToBranch(llvm::SelectInst* select, int labelNum)
{
  // Start with the BB containing the select
  llvm::BasicBlock *bb = select->getParent();

  InstSet trueFaninCone;
  getFaninCone(bb, select->getTrueValue(), trueFaninCone);

  InstSet falseFaninCone;
  getFaninCone(bb, select->getFalseValue(), falseFaninCone);

  printf("Select %s: true fanin %lu  false fanin %lu\n", instrToString(select).c_str(), 
          trueFaninCone.size(), falseFaninCone.size());

  pruneFaninCone(trueFaninCone, select);
  pruneFaninCone(falseFaninCone, select);

  printf("  Pruned size: true fanin %lu  false fanin %lu\n", 
          trueFaninCone.size(), falseFaninCone.size());

  // Don't bother creating branches around a single instruction...
  if (trueFaninCone.size() < 2 && falseFaninCone.size() < 2) {
    return false;
  }

  // We make no assumptions about the ordering of the inputs to the select

  std::string labelSuffix = std::to_string(labelNum);

  // Select will be first instr of new BB
  llvm::BasicBlock *trueBB = bb->splitBasicBlock(select, "true_br"+labelSuffix);
  llvm::BasicBlock *falseBB = trueBB->splitBasicBlock(select, "false_br"+labelSuffix);
  llvm::BasicBlock *postBB = falseBB->splitBasicBlock(select, "post"+labelSuffix);

  // fix the terminator (a branch instruction) of trueBB to point to postBB
  llvm::BranchInst *trueTerminator = llvm::cast<llvm::BranchInst>(trueBB->getTerminator());
  trueTerminator->setSuccessor(0, postBB);

  // Remove the recently-created non-conditional terminator branch instruction 
  // from the original B
  bb->getTerminator()->eraseFromParent();

  // Add a new terminator branch instruction to the original BB that
  // jumps to either trueBB or falseBB based on the correct condition.
  llvm::IRBuilder(bb).CreateCondBr(select->getCondition(), trueBB, falseBB);

  // Move all the True cone instructions into the True BB, in their existing order.
  for (auto inst : trueFaninCone) {
    inst->moveBefore(trueBB->getTerminator());
  }

  // Move all the False cone instructions into the False BB, in their existing order.
  for (auto inst : falseFaninCone) {
    inst->moveBefore(falseBB->getTerminator());
  }


  // Stick a PHI instruction at the beginning of the postBB
  // (before the select instruction).
  llvm::IRBuilder postBuilder(postBB);
  postBuilder.SetInsertPoint(postBB, postBB->begin());
  llvm::PHINode *phiInst = postBuilder.CreatePHI(select->getType(), 2);

  // The PHI inherits the true/false Values of the select.
  phiInst->addIncoming(select->getTrueValue(), trueBB);
  phiInst->addIncoming(select->getFalseValue(), falseBB);

  select->replaceAllUsesWith(phiInst);

  // Remember the select instruction's name (if any), then delete it
  llvm::StringRef selectName = select->getName();
  select->eraseFromParent();

  // The new PHI instruction inherits the name of the deleted select instruction
  phiInst->setName(selectName);

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
  // TODO: Is there really any benefit to doing them in this order?
  int n = 1;
  for (llvm::SelectInst *select : selects) {
    if (convertSelectToBranch(select, n)) {
      n++;
      fflush(stdout);
      if (llvm::verifyFunction(*func, &llvm::outs())) {
        llvm::outs().flush();
        printf("\nVerification failed!\n");
        break;
      }
    }
  }


  return true;
}
