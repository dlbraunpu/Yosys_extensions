#include "post_process.h"
  
#include <sys/stat.h>

#include "live_analysis/src/global_data.h"
#include "func_extract/src/global_data_struct.h"
#include "func_extract/src/get_all_update.h"
#include "func_extract/src/helper.h"

#include "llvm/ADT/APInt.h"


#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"


// Yosys headers
#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "backends/rtlil/rtlil_backend.h"

#include "util.h"
#include "driver_tools.h"

USING_YOSYS_NAMESPACE  // Does "using namespace"


LLVMPostProcessor::LLVMPostProcessor()
{

}

LLVMPostProcessor::~LLVMPostProcessor()
{
}

void
LLVMPostProcessor::reset()
{
}


void
LLVMPostProcessor::post_process_llvm(std::string funcName,  // Name as known to LLVM
                                     std::string baseName, // Basename of LLVM files
                                     std::string target)  // ASV name as known to user
{
  reset();

  std::string llvmFileName = baseName+".ll";
  std::string cleanOptoFileName = baseName+".clean-o3-ll";

  time_t startTime = time(NULL);  // should be passed in

  time_t upGenEndTime = time(NULL);  

  // Default g_llvm_path is blank, which means the shell will use $PATH in the usual way.
  std::string optCmd = (funcExtract::g_llvm_path.length() ? funcExtract::g_llvm_path+"/" : "") + "opt";

  // This may be unnecessary with the LLVM generate by this program.
  std::string clean(optCmd+" --instsimplify --deadargelim --instsimplify "+baseName+".tmp-ll -S -o="+baseName+".clean-ll");
  
  //std::string opto_cmd(optCmd+" -O1 "+baseName+".clean-ll -S -o="+baseName+".tmp-o3-ll; opt -passes=deadargelim "+baseName+".tmp-o3-ll -S -o="+cleanOptoFileName+"; rm "+baseName+".tmp-o3-ll");

  std::string opto_cmd(optCmd+" -O3 "+baseName+".clean-ll -S -o="+baseName+".tmp-o3-ll; opt -passes=deadargelim "+baseName+".tmp-o3-ll -S -o="+cleanOptoFileName+"; rm "+baseName+".tmp-o3-ll");

  log("** Begin clean update function\n");
  log_debug("%s\n", clean.c_str());
  system(clean.c_str());
  log("** Begin simplify update function\n");
  log_debug("%s\n", opto_cmd.c_str());
  system(opto_cmd.c_str());
  log("** End simplify update function\n");

  time_t simplifyEndTime = time(NULL);
  uint32_t upGenTime = upGenEndTime - startTime;
  uint32_t simplifyTime = simplifyEndTime - upGenEndTime;
  //funcExtract::g_TimeFileMtx.lock();
  std::ofstream genTimeFile(taintGen::g_path+"/up_gen_time.txt");
  genTimeFile << funcName+":\t"+std::to_string(upGenTime) << std::endl;
  genTimeFile.close();
  std::ofstream simplifyTimeFile(taintGen::g_path+"/simplify_time.txt");
  simplifyTimeFile << funcName+":\t"+std::to_string(simplifyTime) << std::endl;
  simplifyTimeFile.close();
  //funcExtract::g_TimeFileMtx.unlock();


  funcExtract::ArgVec_t argVec;
  bool usefulFunc = false;


  // Load in the optimized LLVM file
  llvm::SMDiagnostic Err;
  llvm::LLVMContext Context;
  std::unique_ptr<llvm::Module> M = llvm::parseIRFile(cleanOptoFileName, Err, Context);

  if (!M) {
    Err.print("func_extract", llvm::errs());
  } else {
    usefulFunc = funcExtract::clean_main_func(*M, funcName);
    if (usefulFunc) {
      
      // Add a C-compatible wrapper function that calls the main function.
      std::string wrapperFuncName = funcExtract::create_wrapper_func(*M, funcName);

      // Annotate the standard x86-64 Clang data layout to the module, to prevent warnings when linking
      // to C/C++ code.
      M->setDataLayout("e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128");

      // Get the data needed to create func_info.txt
      funcExtract::gather_wrapper_func_args(*M, wrapperFuncName, target, argVec);

      struct stat statbuf;
      if ((!funcExtract::g_overwrite_existing_llvm) && stat(llvmFileName.c_str(), &statbuf) == 0) {
        log("Skipping re-generation of existing file %s\n", llvmFileName.c_str());
      } else {
        // Write out the modified IR data to a new file.
        std::error_code EC;
        llvm::raw_fd_ostream OS(baseName+".clean-simp-ll", EC);
        OS << *M;
        OS.close();

        // Rename that file to be the final .ll file
        std::string move("mv "+baseName+".clean-simp-ll "+taintGen::g_path+"/"+llvmFileName);
        log_debug("%s\n", move.c_str());
        system(move.c_str());
      }
    }
  }

  if(usefulFunc) {
    funcExtract::g_fileNameVec.push_back(llvmFileName);        
    toCout("----- For instr "+instrInfo.name+", "+target+" is affected!");
    funcExtract::g_dependVarMapMtx.lock();
    if(funcExtract::g_dependVarMap[instrName].find(target) == funcExtract::g_dependVarMap[instrName].end())
      funcExtract::g_dependVarMap[instrName].emplace(target, argVec);
    else {
      toCout("Warning: for instruction "+instrInfo.name+", target: "+target+" is seen before");
      //abort();
    }
    funcExtract::g_dependVarMapMtx.unlock();
  }
  else {
    toCout("----- For instr "+instrInfo.name+", "+target+" is NOT affected!");
  }


  reset();
}
