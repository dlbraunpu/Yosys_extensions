#ifndef BRANCH_MUX_H
#define BRANCH_MUX_H
  
// LLVM headers needed below
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Value.h"

// Without this, yosys.h gets confused by the above LLVM headers.  Strange!!!
// It seems to be caused by the identifier "ID" being used in clever ways by both packages.
#include "llvm/IR/PassManager.h"


class BranchMux {

public:
  BranchMux(llvm::Function *f);
  ~BranchMux();

  bool convertSelectsToBranches();


private:
  // A compare class that compares Instructions in the same BB by their ordering.
  struct InstrLess {
    bool operator()(llvm::Instruction* const & a,
                    llvm::Instruction* const & b) const;
  };

  // A set with the desired ordering.
  typedef std::set<llvm::Instruction*, InstrLess> InstSet;

  bool convertSelectToBranch(llvm::SelectInst* select, int labelNum);
  void getFaninCone(llvm::BasicBlock *bb, llvm::Value* val, InstSet& faninCone);
  void getFaninCone(llvm::Instruction* inst, InstSet& faninCone);

  void pruneFaninCone(InstSet& faninCone, const llvm::Instruction *parentInst);

  llvm::Instruction *firstInstr(const InstSet& set);
  llvm::Instruction *lastInstr(const InstSet& set);


  std::unique_ptr<llvm::LLVMContext> c;
  std::unique_ptr<llvm::IRBuilder<>> b;
  llvm::Module *mod;
  llvm::Function *func;  // function being modified


};


#endif
