#ifndef UF_GENERATOR_H
#define UF_GENERATOR_H
  

#include "func_extract/src/global_data_struct.h"
#include "func_extract/src/check_regs.h"

// Yosys headers
#include "kernel/yosys.h"



class YosysUFGenerator : public funcExtract::UFGenerator {
public:
  struct Options {
    bool save_unrolled = false;
    bool optimize_unrolled = true;
    bool verbose_llvm_value_names = false;
    bool cell_based_llvm_value_names = false;
    bool simplify_and_or_gates = true;
    bool simplify_muxes = true;
    bool use_poison = false;
    bool support_hierarchy = false;
    bool optimize_muxes = false;
    int optimize_mux_threshold = -1;
  };

  YosysUFGenerator(Yosys::RTLIL::Module *srcmod, const Options& opts);
  YosysUFGenerator() = delete;
  ~YosysUFGenerator();

  void print_llvm_ir(funcExtract::DestInfo &destInfo,
                     const uint32_t bound,
                     uint32_t instrIdx,
                     std::string fileName);


private:

  Yosys::RTLIL::Wire *applyPortSignal(Yosys::RTLIL::Wire *origPort,
                               const Yosys::RTLIL::SigSpec& ss, bool forceRemove,
                               Yosys::pool<Yosys::RTLIL::Wire*>& processedPorts);

  void applyInstrEncoding(Yosys::RTLIL::Module* mod,
                          const funcExtract::InstEncoding_t& encoding, int cycles,
                          Yosys::pool<Yosys::RTLIL::Wire*>& processedPorts);

  Yosys::RTLIL::Module *makeUnrolledModule(Yosys::RTLIL::IdString unrolledModName,
                                    Yosys::RTLIL::Module *srcmod,
                                    funcExtract::InstrInfo_t& instrInfo, int num_cycles);


  Yosys::RTLIL::Design *m_des;
  Yosys::RTLIL::Module *m_srcmod;
  Options m_opts;

};



class YosysUFGenFactory : public funcExtract::UFGenFactory {

public:
  YosysUFGenFactory(Yosys::RTLIL::Module *srcmod,
                    const YosysUFGenerator::Options& opts) :
      m_srcmod(srcmod), m_opts(opts) {}

  std::shared_ptr<funcExtract::UFGenerator> makeGenerator() override
  {
    return std::shared_ptr<funcExtract::UFGenerator>(
        new YosysUFGenerator(m_srcmod, m_opts));
  }

private:
  Yosys::RTLIL::Module *m_srcmod;
  YosysUFGenerator::Options m_opts;
};


// An implementation of ModuleInfo which uses data from Yosys
class YosysModuleInfo : public funcExtract::ModuleInfo {

public:
  YosysModuleInfo(Yosys::RTLIL::Module *srcmod);


  // A blank modname implies the top module.
  uint32_t get_var_width_simp(const std::string& varAndSlice,
                              const std::string& modname) override;

  uint32_t get_var_width_cmplx(const std::string& varAndSlice) override;

  bool is_module(const std::string& modname) override;

  // Return true if the given wire is an output port of the top module,
  // and is driven by a fifo instance.
  bool is_fifo_output(const std::string& wire) override;

  // If instname names an instance in the given parent mod, return its module
  // name.  Otherwise return a blank string.  A blank parentmod implies
  // the top module.
  std::string get_module_of_inst(const std::string& instname,
                                 const std::string& parentmod) override;

  // Fill in the provided (empty) vector with the output ports of the given module.
  // Of course, a blank modname implies the top module.
  void get_module_outputs(std::vector<std::string>& outputs,
                          const std::string& modname) override;

  // Fill in the provided (empty) vector with the fifo instance names in the given module.
  // Of course, a blank modname implies the top module.
  void get_fifo_insts(std::vector<std::string>& fifos,
                          const std::string& modname) override;

private:

  Yosys::RTLIL::Design *m_des;

  // The original top module.
  Yosys::RTLIL::Module *m_srcmod;
};


#endif
