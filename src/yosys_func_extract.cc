/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 *  ---
 *
 *
 */


#include "live_analysis/src/global_data.h"
#include "func_extract/src/global_data_struct.h"
#include "func_extract/src/parse_fill.h"
#include "func_extract/src/read_instr.h"
#include "func_extract/src/vcd_parser.h"
#include "func_extract/src/get_all_update.h"
#include "func_extract/src/helper.h"

#include "llvm/ADT/APInt.h"

#include "util.h"
#include "unroll.h"
#include "write_llvm.h"
#include "uf_generator.h"

#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/sigtools.h"
#include "kernel/ff.h"
#include "kernel/mem.h"
#include <string>
#include <sstream>
#include <set>
#include <map>


USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN




struct FuncExtractCmd : public Pass {

  FuncExtractCmd() : Pass("func_extract", "Generate an ILA update function") { }

  void help() override
  {
    //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
    log("\n");
    log("    func_extract [options]\n");
    log("\n");
    log("Generate an ILA update function for a particular instruction and ASV(s)\n");
    log("\n");
  }

  void execute(std::vector<std::string> args, RTLIL::Design *design) override
  {
    log_header(design, "Executing func_extract...\n");

    taintGen::g_path = ".";
    taintGen::g_verb = false;

    bool write_llvm = true;
    bool read_rst = true;

    YosysUFGenerator::Options ufGenOpts;
    ufGenOpts.save_unrolled = false;
    ufGenOpts.optimize_unrolled = true;
    ufGenOpts.verbose_llvm_value_names = false;
    ufGenOpts.cell_based_llvm_value_names = false;
    ufGenOpts.simplify_and_or_gates = true;
    ufGenOpts.simplify_muxes = true;
    ufGenOpts.use_poison = false;

    size_t argidx;
    for (argidx = 1; argidx < args.size(); argidx++) {
      std::string arg = args[argidx];
      
      if (arg == "-no_write_llvm") {
        write_llvm = false;
      } else if (arg == "-save_unrolled") {
        ufGenOpts.save_unrolled = true;
      } else if (arg == "-no_optimize_unrolled") {
        ufGenOpts.optimize_unrolled = false;
      } else if (arg == "-use_poison") {
        ufGenOpts.use_poison = true;
      } else if (arg == "-no_simplify_gates") {
        ufGenOpts.simplify_and_or_gates = false;
      } else if (arg == "-no_simplify_muxes") {
        ufGenOpts.simplify_muxes = false;
      } else if (arg == "-verbose_names") {
        ufGenOpts.verbose_llvm_value_names = true;
      } else if (arg == "-cell_based_names") {
        ufGenOpts.cell_based_llvm_value_names = true;
      } else if (arg == "-no_rst") {
        read_rst = false;
      } else if (arg == "-path" && argidx < args.size()-1) {
        ++argidx;
        taintGen::g_path = args[argidx];
      } else {
        break;
      }
    }
    //extra_args(args, argidx, design);  // can handle selection, etc.

    funcExtract::read_config(taintGen::g_path+"/config.txt");

    taintGen::g_verb = ys_debug();  // Override setting from config.txt

    // read instr.txt, result in g_instrInfo:
    // instruction encodings, write/read ASV, NOP
    funcExtract::read_in_instructions(taintGen::g_path+"/instr.txt");

    RTLIL::IdString srcmodname = verilogToInternal(taintGen::g_topModule);
    log("Specified top module: %s\n", id2cstr(srcmodname));

    RTLIL::Module *srcmod = design->module(srcmodname);
    if (!srcmod) {
      log_cmd_error("No such module: %s  Did you load the design?\n", id2cstr(srcmodname));
    }

    // Read target ASVs and reset data
    funcExtract::read_allowed_targets(taintGen::g_path+"/allowed_target.txt");

    if (read_rst) {
      funcExtract::vcd_parser(taintGen::g_path+"/rst.vcd");
    } else {
      log_warning("rst.vcd will not be read - non-ASV registers will be initialized to zero.\n");
    }


    design->sort();

    if (!srcmod->processes.empty()) {
      log_warning("Module %s contains unmapped RTLIL processes.\n"
                "Running the Yosys 'proc' command to remove them...\n", id2cstr(srcmodname));
      log_push();
      Pass::call(design, "proc");
      log_pop();
      design->sort();
    }


    // Make an implementation of a UFGenFactory that provides
    // instances of YosysUFGenerator, which generates LLVM
    // based on the Yosys in-memory design.
    // Pass in necessary option settings.
    YosysUFGenFactory factory(srcmod, ufGenOpts);

    // Make an implementation of ModuleInfo that funcExtract::FuncExtractFlow
    // needs to look up design data.
    YosysModuleInfo info(srcmod);

    // Give the factory and the query to the driver
    // Our flow ordering is to iterate over ASVs in the inner loop
    // and instructions in the outer loop.  This allows us to use one unrolled
    // design for all the ASVs of a particular instruction.
    // Also, we number cycles increasing over time.
    funcExtract::FuncExtractFlow flow(factory, info, false /*innerLoopIsInstrs*/,
                                      false /*reverseCycleOrder*/);

    // Go do the work
    flow.get_all_update();
  }

} FuncExtractCmd;

PRIVATE_NAMESPACE_END
