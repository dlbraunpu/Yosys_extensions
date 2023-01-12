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


// Translate the given string (something as complicated as
// "7'h4+5'h7+5'h13+3'hx+5'h12+5'h8+2'b11", as read from instr.txt) into
// a SigSpec.  The given SigSpec should be freshly-created; it will get filled in.
// This function makes use of Yosys, LLVM, and func_extract code and data structures...

void getSigSpec(const std::string& valStr, RTLIL::SigSpec& spec)
{
  llvm::APInt value = funcExtract::convert_to_single_apint(valStr, false /*xmask*/);
  llvm::APInt xmask = funcExtract::convert_to_single_apint(valStr, true /*xmask*/);

  unsigned width = value.getBitWidth();
  
  for (unsigned n = 0; n < width; ++n) {
    bool bitval = value[n];
    bool not_x = xmask[n];

    RTLIL::SigBit b(not_x ? (bitval ? RTLIL::State::S1 : RTLIL::State::S0) : RTLIL::State::Sx);
    spec.append(b);  // Correct bit ordering?
  }
}


pool<RTLIL::Wire*> processedPorts;


// This function properly sets 0/1/x values on input ports, which may
// represent ASVs, oriinary registers, or top-level input signals.

// If the given SigSpec is all-x, origPort will be left alone.

// If the SigSpec is fully const (0/1), origPort will be un-ported (thus
// becoming a plain wire) and renamed, and the given 0/1 values will be set on
// it.

// If the SigSpec is a mix of 0, 1, and x, origPort will be un-ported and
// renamed, and a new port will be created with its original name. Each 0/1
// bit in SigSpec will be set on origPort, and for each x bit, origPort will
// be connected to the new port.  (The bits in the new port corresponding to
// 0/1 will be left unconnected.)

// However, if forceRemove is true, origPort will always be un-ported, no new
// port will be created, and origPort will get all the given 0/1/x values set
// on it.

// Any newly-created port will be returned.  The new or original port will be
// added to the processedPorts list.  Be sure to call module->fixup_ports()
// after calling this.

RTLIL::Wire *
applyPortSignal(RTLIL::Wire *origPort, const RTLIL::SigSpec& ss, bool forceRemove)
{
  log_assert(origPort->port_input);
  log_assert(processedPorts.count(origPort) == 0);

  if (ss.is_fully_undef() && !forceRemove) {
    processedPorts.insert(origPort);
    return origPort;  // no change needed: common case for ASVs.
  }


  RTLIL::Module *mod = origPort->module;

  RTLIL::IdString origName = origPort->name;

  std::string newStr = "$" + origPort->name.substr(1) + "orig";
  RTLIL::IdString newName = mod->uniquify(newStr);
  mod->rename(origPort, newName);

  RTLIL::Wire *newPort = nullptr;
  if (!ss.is_fully_const() && !forceRemove) {
    // Make a new port only if it is useful and wanted
    newPort = mod->addWire(origName, origPort->width);

    // The new port takes over the old port's status
    newPort->port_input = origPort->port_input;
    newPort->port_output = origPort->port_output;
    // TODO: Copy or move orig port attributes to new wire.
  }
  origPort->port_input = false;  // the orignal port is demoted to an ordinary Wire
  origPort->port_output = false;

  if (!newPort) {
    // Simply connect the SigSpec to the original port wire.
    mod->connect(RTLIL::SigSpec(origPort), ss);
  } else {
    // A partially-constant SigSpec: connect the old port to either the new port or the SigSpec
    // on a bit-by-bit basis.
    log_assert(newPort);

    RTLIL::SigSpec ss2;
    for (int n=0; n < origPort->width; ++n) {
      log_assert(!ss.is_wire());
      if (ss[n].data == RTLIL::State::S0 ||
          ss[n].data == RTLIL::State::S1) {
        ss2.append(ss[n]);
      } else {
        ss2.append(RTLIL::SigBit(newPort, n));
      }
    }
    mod->connect(RTLIL::SigSpec(origPort), ss2);
  }

  if (newPort) processedPorts.insert(newPort);
  return newPort;
}


void
applyInstrEncoding(RTLIL::Module* mod, const funcExtract::InstEncoding_t& encoding, int cycles)
{
  // Go through the encoding data loaded from instr.txt
  for (auto pair : encoding) {
    const std::string& inputName = pair.first;
    const std::vector<std::string>& values = pair.second;
    log_debug("Input variable: %s\n", inputName.c_str());

    // Unlike the original funct_extract program, the unrolled RTL cycle
    // numbering matches the instr.txt cycle numbering: starting at 1, and
    // increasing in time.  Note that the very last cycle (num_cycles+1)
    // should not have any instruction encoding, and NOP values will be used
    // for it.

    for(int cycle = 1; cycle <= cycles+1; ++cycle) {
      // If the encoding has fewer cycles than the specified cycle count, use
      // the NOP values for the remaining cycles.

      std::string valStr;
      if ((unsigned)cycle <= values.size()) {
        valStr = values[cycle-1];
      } else if (funcExtract::g_nopInstr.count(inputName)) {
        valStr = funcExtract::g_nopInstr[inputName];
      } else {
        continue;  // No data to apply
      }
    
      RTLIL::SigSpec ss;
      getSigSpec(valStr, ss);
      log_debug("    RTLIL value: %s\n", log_signal(ss));
      if (ss.empty() || !ss.is_fully_const()) {
        log_error("Cannot understand value for port %s in cycle %d\n", inputName.c_str(), cycle);
        log("    RTLIL value: %s\n", log_signal(ss));
        continue;
      }

      RTLIL::IdString portname = cycleize_name(std::string("\\"+inputName), cycle);
      log_debug("encoding: cycle %d  value %s portname %s\n", cycle, valStr.c_str(), portname.c_str());
      RTLIL::Wire *port = mod->wire(portname);
      if (!port) {
        log_error("Cannot find unrolled port %s\n", portname.c_str());
        continue;
      }

      if (!port->port_input) {
        log_error("Unrolled port %s is not an input\n", portname.c_str());
        continue;
      }

      adjustSigSpecWidth(ss, port->width);
      applyPortSignal(port, ss, false /*forceRemove*/);

      // Set x on any clock inputs. The name of the clock signal is defined in
      // instr.txt.  Normally the clock signals will be dead, since we removed
      // all the registers.
      if (!taintGen::g_recentClk.empty()) {
        RTLIL::IdString clockname = cycleize_name(std::string("\\"+taintGen::g_recentClk), cycle);
        RTLIL::Wire *clockport = mod->wire(clockname);
        if (clockport && clockport->port_input) {
          // Set to x, probably opto will eliminate it.
          RTLIL::SigSpec ss(RTLIL::State::Sx);
          adjustSigSpecWidth(ss, clockport->width);
          applyPortSignal(clockport, ss, true /*forceRemove*/);
        }
      }
    }
  }
}



RTLIL::Module *
makeUnrolledModule(RTLIL::IdString unrolledModName, RTLIL::Module *srcmod,
                   funcExtract::InstrInfo_t* instrInfo, int num_cycles)
{
  RTLIL::Design *design = srcmod->design;
  
  RTLIL::Module *unrolledMod = design->addModule(unrolledModName);

  log("Unrolling module `%s' into `%s' for %d cycles...\n",
      id2cstr(srcmod->name), id2cstr(unrolledModName), num_cycles);
  unroll_module(srcmod, unrolledMod, num_cycles);

  // Make into output ports the final-cycle (num_cycles+1) signals that represent ASVs.
  // Typically these are the from_Q signals created by unroll_module().
  for (auto pair : funcExtract::g_allowedTgt) {
    std::string tmpnam = pair.first;
    if (tmpnam[0] != '\\') {  // Don't double-backslash the name.
      tmpnam = "\\" + tmpnam;
    }
    RTLIL::IdString portname = cycleize_name(tmpnam, num_cycles+1);
    RTLIL::Wire *port = unrolledMod->wire(portname);
    if (port) {
      port->port_output = true;
    } else {
      log_warning("Cannot find unrolled final-cycle signal for ASV %s\n", tmpnam.c_str());
      continue;
    }
  }
  unrolledMod->fixup_ports();  // Necessary since we added ports

  log("Unrolled module statistics:\n");
  log_push();
  Pass::call_on_module(design, unrolledMod, "stat");
  log_pop();

  // Generating code for pmux cells is complicated, so have Yosys
  // replace them with regular muxes.
  log("Removing $pmux cells...\n");
  log_push();
  Pass::call_on_module(design, unrolledMod, "pmuxtree");
  Pass::call_on_module(design, unrolledMod, "stat");
  log_pop();


  // Doing opto here gives little improvement
#if 0
  if (do_opto) {
    // Optimize
    log("Optimizing...\n");
    log_push();
    Pass::call_on_module(design, unrolledMod, "opt");
    Pass::call_on_module(design, unrolledMod, "stat");
    log_pop();
  }
#endif

  log("Applying instruction encoding...\n");
  applyInstrEncoding(unrolledMod, instrInfo->instrEncoding, num_cycles);

  // Identify all first-cycle ASV inputs as processed, to prevent a reset value from
  // being placed upon them.

  for (auto pair : funcExtract::g_allowedTgt) {
    std::string tmpnam = pair.first;
    if (tmpnam[0] != '\\') {  // Don't double-backslash the name.
      tmpnam = "\\" + tmpnam;
    }
    RTLIL::IdString portname = cycleize_name(tmpnam, 1);
    RTLIL::Wire *port = unrolledMod->wire(portname);
    if (!port || !port->port_input) {
      log_warning("Cannot find unrolled first-cycle ASV input port %s\n", portname.c_str());
      continue;
    }
    processedPorts.insert(port);
  }
  unrolledMod->fixup_ports();  // Necessary since we added and removed ports

  // Apply any reset values as needed to input ports for cycle #1.
  // Explicit x reset values are included.
  log("Applying reset values...\n");
  for (auto pair : funcExtract::g_rstVal) {
    std::string tmpnam = pair.first;
    if (tmpnam[0] != '\\') {  // Don't double-backslash the name.
      tmpnam = "\\" + tmpnam;
    }
    RTLIL::IdString portname = cycleize_name(tmpnam, 1);
    RTLIL::Wire *port = unrolledMod->wire(portname);
    if (port && port->port_input && processedPorts.count(port) == 0) {
      const std::string& valStr = pair.second;
      RTLIL::SigSpec ss;
      getSigSpec(valStr, ss);
      log_debug(" signal %s   reset value: %s\n", portname.c_str(), log_signal(ss));
      if (ss.empty() || !ss.is_fully_const()) {
        log_error("Cannot understand reset value %s for port %s\n",
                  log_signal(ss), portname.c_str());
        continue;
      }
      adjustSigSpecWidth(ss, port->width);
      applyPortSignal(port, ss, true /*forceRemove*/);
    }
  }
  unrolledMod->fixup_ports();  // Necessary since we added and removed ports

  // Warn about any non-ASV input ports that have no value,
  // and give them X values.
  for (const RTLIL::IdString& portname : unrolledMod->ports) {
    RTLIL::Wire *port = unrolledMod->wire(portname);
    log_assert(port);
    if (port->port_input && processedPorts.count(port) == 0) {
      log_warning("No value for non-ASV input port %s\n", portname.c_str());
      // Set to x, possibly opto will eliminate it.
      RTLIL::SigSpec ss(RTLIL::State::Sx);
      adjustSigSpecWidth(ss, port->width);
      applyPortSignal(port, ss, true /*forceRemove*/);
    }
  }
  unrolledMod->fixup_ports();  // Necessary since we added and removed ports

  return unrolledMod;
}



struct FuncExtractCmd : public Pass {

  FuncExtractCmd() : Pass("func_extract", "Generate an ILA update function") { }

  void help() override
  {
    //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
    log("\n");
    log("    func_extract <instruction> <asv>... [options]\n");
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
    bool do_opto = true;
    bool read_rst = true;

    if (args.size() < 3) {
      log_error("Not enough arguments!\n");
      return;
    }

    std::string instrName;
    std::vector<std::string> targetNames;

    size_t argidx;
    for (argidx = 1; argidx < args.size(); argidx++) {
      std::string arg = args[argidx];
      
      if (arg[0] != '-') {
        if (instrName.empty()) {
          instrName = arg;
        } else {
          targetNames.push_back(arg);
        }
      } else if (arg == "-no_write_llvm") {
        write_llvm = false;
      } else if (arg == "-no_opto") {
        do_opto = false;
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

    // Read target ASVs and reset data
    funcExtract::read_allowed_targets(taintGen::g_path+"/allowed_target.txt");

    if (read_rst) {
      funcExtract::vcd_parser(taintGen::g_path+"/rst.vcd");
    } else {
      log_warning("rst.vcd will not be read - non-ASV registers will be initialized to zero.\n");
    }

    RTLIL::IdString srcmodname = RTLIL::escape_id(taintGen::g_topModule);
    RTLIL::Module *srcmod = design->module(srcmodname);
    if (!srcmod) {
      log_cmd_error("No such source module: %s\n", id2cstr(srcmodname));
    }

    design->sort();

    if (!srcmod->processes.empty()) {
      log_error("Module %s contains unmapped RTLIL processes.\n"
                "Run the Yosys 'proc' command before this command.\n", id2cstr(srcmodname));
    }

    // Write_verilog does these...
#if 0
    log_push();
    Pass::call(design, "bmuxmap");
    Pass::call(design, "demuxmap");
    Pass::call(design, "clean_zerowidth");
    log_pop();
#endif


    // Find the data for the instruction and ASV of interest
    funcExtract::InstrInfo_t* instrInfo = nullptr;
    for (funcExtract::InstrInfo_t& ii : funcExtract::g_instrInfo) {
      if (ii.name == instrName) {
        instrInfo = &ii;
        break;
      }
    }
    if (!instrInfo) {
      log_cmd_error("No such instruction %s\n", instrName.c_str());
    }

    RTLIL::Module *unrolledMod = nullptr;
    int cur_num_cycles = -1;

    // Generate an update function for each of the given ASVs.
    // TODO: Simple option to generate for all ASVs?
    for (auto targetName : targetNames) {
      if (!funcExtract::g_allowedTgt.count(targetName)) {
        log_cmd_error("No such ASV %s for instruction %s\n", targetName.c_str(), instrName.c_str());
      }
    
      std::vector<uint32_t> delayBounds = funcExtract::get_delay_bounds(targetName, *instrInfo);
      if (delayBounds.size() != 1) {
        log_cmd_error("Delay not defined for ASV %s for instruction %s\n", targetName.c_str(), instrName.c_str());
      }

      int num_cycles = delayBounds[0];

      // See if we can reuse the unrolled module for the current ASV.  This will be the case as
      // long as the instruction and the cycle count do not change.
      if (!unrolledMod || cur_num_cycles != num_cycles) {

        if (unrolledMod) {
          // Delete it, since it has the wrong cycle count.
          log("Design %s must be re-unrolled for cycle count %d\n", id2cstr(unrolledMod->name), num_cycles);
          design->remove(unrolledMod);
        }

        RTLIL::IdString unrolledModName = RTLIL::escape_id(instrName+"_unrolled_"+std::to_string(num_cycles));
        if (design->module(unrolledModName)) {
          log_cmd_error("Unrolled module %s already exists\n", id2cstr(unrolledModName));
        } 

        // Create the new module
        unrolledMod = makeUnrolledModule(unrolledModName, srcmod, instrInfo, num_cycles);
        cur_num_cycles = num_cycles;

        // Re-optimize.  Since we have set a lot of constants on input ports,
        // a lot of simplification can be done.
        if (do_opto) {
          log("Re-optimizing...\n");
          log_push();
          Pass::call_on_module(design, unrolledMod, "opt");
          Pass::call_on_module(design, unrolledMod, "stat");
          log_pop();
        }
      }

      // Get the Yosys RTLIL object representing the destination ASV.
      // TODO: Do a better job of mapping the original Verilog register name to the actual wire name.

      std::string portName = targetName + "_#"+ std::to_string(num_cycles+1);
      if (portName[0] != '\\') {  // Don't double-backslash the name.
        portName = "\\" + portName;
      }
      RTLIL::Wire *targetPort = unrolledMod->wire(portName);

      if (!targetPort) {
        log_warning("Can't find output port wire %s for destination ASV %s\n", portName.c_str(), targetName.c_str());
      } else {
        log("Target SigSpec: ");
        my_log_wire(targetPort);
      }

      if (targetPort && write_llvm) {
        log_header(design, "Writing LLVM data...\n");

        // Same format as original func_extract
        std::string cleanTargetName = funcExtract::var_name_convert(targetName, true);
        std::string llvmName = instrName + "_" + cleanTargetName + "_" + std::to_string(num_cycles)+".ll";

        LLVMWriter writer;
        writer.write_llvm_ir(unrolledMod, targetPort, taintGen::g_topModule /*modName*/,
                             instrName, targetName, llvmName);
        log("LLVM result written to %s\n", llvmName.c_str());
      } else {
        log_warning("LLVM generation skipped.\n");
      }

    }

  }
} FuncExtractCmd;

PRIVATE_NAMESPACE_END
