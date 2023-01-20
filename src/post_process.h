#ifndef POST_PROCESS_H
#define POST_PROCESS_H
  
// LLVM headers needed below
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"



class LLVMPostProcessor {

private:

  std::shared_ptr<llvm::IRBuilder<>> b;
  std::shared_ptr<llvm::LLVMContext> c;
  std::shared_ptr<llvm::Module> llvmMod;


public:
  LLVMPostProcessor();
  ~LLVMPostProcessor();

  void post_process_llvm(std::string funcName,  // Name as known to LLVM
                         std::string baseName,  // Basename of LLVM files
                         std::string target);


  void reset();

};


#endif
