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
  bool convertSelectToBranch(llvm::SelectInst* select);
  void getFaninCone(llvm::Value* val,
                          std::set<llvm::Instruction*>& faninCone);
  void getFaninCone(llvm::Instruction* inst,
                          std::set<llvm::Instruction*>& faninCone);

  void pruneFaninCone(std::set<llvm::Instruction*>& faninCone,
                                 const llvm::Instruction *parentInst);


  std::unique_ptr<llvm::LLVMContext> c;
  std::unique_ptr<llvm::IRBuilder<>> b;
  llvm::Module *mod;
  llvm::Function *func;  // function being modified


};


#endif
