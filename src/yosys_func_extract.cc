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

  FuncExtractCmd() : Pass("func_extract", "Generate ILA update functions") { }

  void help() override
  {
    //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
    log("\n");
    log("    func_extract [options]\n");
    log("\n");
    log("Generate ILA update functions for a particular design.\n");
    log("\n");
    log("    -save_unrolled\n");
    log("        Each unrolled copy of the design (typically there is one for each\n");
    log("        instruction) will be saved in RTLIL format before and after\n");
    log("        optimization is performed on it. This is very useful for debugging.\n");
    log("        The filenames will be of the form '<instr_name>_unrolled_<delay>.rtlil'\n");
    log("        and '<instr_name>_unrolled_opto_<delay>.rtlil'\n");
    log("\n");
    log("    -no_optimize_unrolled\n");
    log("        Skip optimization of the unrolled designs. This may greatly\n");
    log("        increase the code generation runtime and the size of the\n");
    log("        generated code.\n");
    log("\n");
    log("    -use_poison\n");
    log("        This will cause an LLVM 'poison' value to be used instead of 0 or 1\n");
    log("        for x (undefined) signal values. This may be helpful in determining\n");
    log("        if x values are not being optimized away and affecting the simulation\n");
    log("        results.\n");
    log("\n");
    log("    -no_simplify_gates\n");
    log("        This will prevent the LLVM code generator from doing simple\n");
    log("        optimizations on logic gates. Possibly useful for debugging.\n");
    log("\n");
    log("    -no_simplify_muxes\n");
    log("        This will prevent the LLVM code generator from doing simple\n");
    log("        optimizations on muxes. Possibly useful for debugging.\n");
    log("\n");
    log("    -pre_opto_mux_to_branch\n");
    log("        Activate the mux-to-branch pass immediately after LLVM code generation.\n");
    log("        This will try to convert LLVM 'select' instructions (typically created.\n");
    log("        from Yosys mux cells) into conditional branches. This can be very\n");
    log("        effective on some designs.\n");
    log("\n");
    log("    -post_opto_mux_to_branch\n");
    log("        Activate the mux-to-branch pass after final LLVM optimization. This\n");
    log("        is typically less effective than doing it pre-opto.\n");
    log("\n");
    log("    -pre_opto_mux_to_branch_threshold <value>\n");
    log("        If pre-opto mux-to-branch conversion is active, an LLVM 'select' will\n");
    log("        not be converted unless one of the generated branches will have at\n");
    log("        least this number of LLVM instructions. The default value is 10.\n");
    log("\n");
    log("    -post_opto_mux_to_branch_threshold <value>\n");
    log("        Same as above, except for post-opto conversion.\n");
    log("\n");
    log("    -verbose_names\n");
    log("        Try to give LLVM instructions names that are based on the corresponding\n");
    log("        RTLIL signal names (instead of default numeric names). Helpful for\n");
    log("        debugging.\n");
    log("\n");
    log("    -cell_based_names\n");
    log("        Try to give LLVM instructions names that are based on the corresponding\n");
    log("        RTLIL cell names (instead of default numeric names). Helpful for\n");
    log("        debugging, but typically less so than signal-based names.\n");
    log("\n");
    log("    -no_rst\n");
    log("        Do not read the reset value data from the file 'rst.vcd'. Instead\n");
    log("        zero will be used for reset values.\n");
    log("\n");
    log("    -overwrite\n");
    log("        By default this command will not overwrite an existing LLVM file.\n");
    log("        This option will force every LLVM file to be written.\n");
    log("        It has the same effect as the 'g_overwrite_existing_llvm' setting in\n");
    log("        the 'config.txt' file.\n");
    log("\n");
    log("    -support_hierarchy\n");
    log("        Activate limited support for Verilog hierarchy. Each output signal\n");
    log("        of a sub-module will have an LLVM function created for it,\n");
    log("        essentially the same as in the original func_extract program.\n");
    log("        This technique is known to work for the AES test case, but will\n");
    log("        generally work correctly only for purely combinatorial sub-modules.\n");
    log("\n");
    log("    -pmux\n");
    log("        Enable support for RTLIL '$pmux' cells. By default these cells are \n");
    log("        converted to mux trees by the Yosys 'pmuxtree' command. With this\n");
    log("        option, they will be translated to LLVM 'switch' instructions.\n");
    log("        Typically this gives no improvement, and can interfere with\n");
    log("        mux-to-branch conversion.\n");
    log("\n");
    log("    -path <path>\n");
    log("        Read and write all data and configuration files from the given\n");
    log("        directory path. By default the current directory is used.\n");
    log("\n");
    log("This command reads and writes the same configuration and data files as the\n");
    log("original standalone func_extract program. One difference is that this\n");
    log("command does not read any Verilog files. It assumes the design has already\n");
    log("been loaded, flattened, and optimized (typically with the Yosys 'prep'\n");
    log("command). The module to be operated upon is specified in the 'instr.txt' file.\n");
    log("\n");
    log("To generate verbose output, either prefix this command with the Yosys\n");
    log("'debug' command, or set the 'g_overwrite_existing_llvm' setting in\n");
    log("the 'config.txt' file.\n");
    log("\n");
  }

  void execute(std::vector<std::string> args, RTLIL::Design *design) override
  {
    log_header(design, "Executing func_extract...\n");

    taintGen::g_path = ".";
    taintGen::g_verb = false;

    bool read_rst = true;
    bool overwrite = false;

    YosysUFGenerator::Options ufGenOpts;
    ufGenOpts.save_unrolled = false;
    ufGenOpts.optimize_unrolled = true;
    ufGenOpts.verbose_llvm_value_names = false;
    ufGenOpts.cell_based_llvm_value_names = false;
    ufGenOpts.simplify_and_or_gates = true;
    ufGenOpts.simplify_muxes = true;
    ufGenOpts.use_poison = false;
    ufGenOpts.support_hierarchy = false;
    ufGenOpts.support_pmux = false;
    ufGenOpts.optimize_muxes = false;
    ufGenOpts.optimize_mux_threshold = -1;

    size_t argidx;
    for (argidx = 1; argidx < args.size(); argidx++) {
      std::string arg = args[argidx];
      
      if (arg == "-save_unrolled") {
        ufGenOpts.save_unrolled = true;
      } else if (arg == "-no_optimize_unrolled") {
        ufGenOpts.optimize_unrolled = false;
      } else if (arg == "-use_poison") {
        ufGenOpts.use_poison = true;
      } else if (arg == "-no_simplify_gates") {
        ufGenOpts.simplify_and_or_gates = false;
      } else if (arg == "-no_simplify_muxes") {
        ufGenOpts.simplify_muxes = false;
      } else if (arg == "-pre_opto_mux_to_branch") {
        ufGenOpts.optimize_muxes = true;
      } else if (arg == "-post_opto_mux_to_branch") {
        funcExtract::g_post_opto_mux_to_branch = true;
      } else if (arg == "-verbose_names") {
        ufGenOpts.verbose_llvm_value_names = true;
      } else if (arg == "-cell_based_names") {
        ufGenOpts.cell_based_llvm_value_names = true;
      } else if (arg == "-no_rst") {
        read_rst = false;
      } else if (arg == "-overwrite") {
        overwrite = true;
      } else if (arg == "-support_hierarchy") {
        ufGenOpts.support_hierarchy = true;
      } else if (arg == "-pmux") {
        ufGenOpts.support_pmux = true;
      } else if (arg == "-path" && argidx < args.size()-1) {
        ++argidx;
        taintGen::g_path = args[argidx];
      } else if (arg == "-pre_opto_mux_to_branch_threshold" && argidx < args.size()-1) {
        ++argidx;
        ufGenOpts.optimize_mux_threshold = std::stoi(args[argidx]);
      } else if (arg == "-post_opto_mux_to_branch_threshold" && argidx < args.size()-1) {
        ++argidx;
        funcExtract::g_post_opto_mux_to_branch_threshold = std::stoi(args[argidx]);
      } else {
        break;
      }
    }
    //extra_args(args, argidx, design);  // can handle selection, etc.

    funcExtract::read_config(taintGen::g_path+"/config.txt");

    // Override settings from config.txt
    if (ys_debug()) taintGen::g_verb = true;
    if (overwrite) funcExtract::g_overwrite_existing_llvm = true; 

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
    // and instructions in the outer loop. This allows us to use one unrolled
    // design for all the ASVs of a particular instruction.
    // Also, we number cycles increasing over time.
    funcExtract::FuncExtractFlow flow(factory, info, false /*innerLoopIsInstrs*/,
                                      false /*reverseCycleOrder*/);

    // Go do the work
    flow.get_all_update();
  }

} FuncExtractCmd;

PRIVATE_NAMESPACE_END
