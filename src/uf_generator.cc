#include "uf_generator.h"
  

#include "live_analysis/src/global_data.h"
#include "func_extract/src/global_data_struct.h"
#include "func_extract/src/get_all_update.h"
#include "func_extract/src/helper.h"
#include "func_extract/src/util.h"


#include "llvm/ADT/APInt.h"

// Yosys headers
#include "kernel/yosys.h"
#include "kernel/sigtools.h"

#include "unroll.h"
#include "write_llvm.h"
#include "util.h"

USING_YOSYS_NAMESPACE  // Does "using namespace"


YosysUFGenerator::YosysUFGenerator(RTLIL::Module *srcmod, bool do_opto)
{
  m_srcmod = srcmod;
  m_des = srcmod->design;
  m_do_opto = do_opto;
}


YosysUFGenerator::~YosysUFGenerator()
{
}




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



// This function properly sets 0/1/x values on input ports, which may
// represent ASVs, oriinary registers, or top-level input signals.

// If the given SigSpec is all-x, origPort will be left alone.

// If the SigSpec is fully const (0/1), origPort will be un-ported (thus
// becoming a plain wire) and renamed, and the SigSpec's 0/1 values will be
// set on the wire.

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

// TODO: It is possible for some (or all?) of origPort's bits to have a
// constant already set on them in the design.  We should probably avoid connecting
// anything else to such a bit.  Checking this would require building and
// using a SigMap.

RTLIL::Wire *
YosysUFGenerator::applyPortSignal(RTLIL::Wire *origPort, const RTLIL::SigSpec& ss, bool forceRemove,
                                  Yosys::pool<Yosys::RTLIL::Wire*>& processedPorts)
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
YosysUFGenerator::applyInstrEncoding(RTLIL::Module* mod, const funcExtract::InstEncoding_t& encoding,
                                     int cycles, Yosys::pool<Yosys::RTLIL::Wire*>& processedPorts)
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

      RTLIL::IdString portname = cycleize_name(inputName, cycle);
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
      applyPortSignal(port, ss, false /*forceRemove*/, processedPorts);

      // Set x on any clock inputs. The name of the clock signal is defined in
      // instr.txt.  Normally the clock signals will be dead, since we removed
      // all the registers.
      if (!taintGen::g_recentClk.empty()) {
        RTLIL::IdString clockname = cycleize_name(taintGen::g_recentClk, cycle);
        RTLIL::Wire *clockport = mod->wire(clockname);
        if (clockport && clockport->port_input) {
          // Set to x, probably opto will eliminate it.
          RTLIL::SigSpec ss(RTLIL::State::Sx);
          adjustSigSpecWidth(ss, clockport->width);
          applyPortSignal(clockport, ss, true /*forceRemove*/, processedPorts);
        }
      }
    }
  }
}



RTLIL::Module *
YosysUFGenerator::makeUnrolledModule(RTLIL::IdString unrolledModName, RTLIL::Module *srcmod,
                   funcExtract::InstrInfo_t& instrInfo, int num_cycles)
{
  RTLIL::Design *design = srcmod->design;
  
  RTLIL::Module *unrolledMod = design->addModule(unrolledModName);
  log_assert(unrolledMod);

  // Mark the module as a special temporary unrolled module
  // TODO: set more attributes so we don't have to parse module names.
  unrolledMod->set_bool_attribute("\\func_extract_unrolled");

  log("Unrolling module `%s' into `%s' for %d cycles...\n",
      id2cstr(srcmod->name), id2cstr(unrolledModName), num_cycles);
  unroll_module(srcmod, unrolledMod, num_cycles);

  // Make into output ports the final-cycle (num_cycles+1) signals that represent ASVs.
  // Typically these are the from_Q signals created by unroll_module().
  for (auto pair : funcExtract::g_allowedTgt) {
    RTLIL::IdString portname = cycleize_name(pair.first, num_cycles+1);
    RTLIL::Wire *port = unrolledMod->wire(portname);
    if (port) {
      port->port_output = true;
    } else {
      log_warning("Cannot find unrolled final-cycle signal for ASV %s\n", pair.first.c_str());
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
  if (m_do_opto) {
    // Optimize
    log("Optimizing...\n");
    log_push();
    Pass::call_on_module(design, unrolledMod, "opt");
    Pass::call_on_module(design, unrolledMod, "stat");
    log_pop();
  }
#endif
  Yosys::pool<Yosys::RTLIL::Wire*> processedPorts;

  log("Applying instruction encoding...\n");
  applyInstrEncoding(unrolledMod, instrInfo.instrEncoding, num_cycles, processedPorts);

  // Identify all first-cycle ASV inputs as processed, to prevent a reset value from
  // being placed upon them.

  for (auto pair : funcExtract::g_allowedTgt) {
    RTLIL::IdString portname = cycleize_name(pair.first, 1);
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
  // TODO: It is possible for some (or all?) of the port's bits to have a
  // constant already set on them in the design.  Will a class between the
  // reset value and that constant cause problems?
  log("Applying reset values...\n");
  for (auto pair : funcExtract::g_rstVal) {
    RTLIL::IdString portname = cycleize_name(pair.first, 1);
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
      applyPortSignal(port, ss, true /*forceRemove*/, processedPorts);
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
      applyPortSignal(port, ss, true /*forceRemove*/, processedPorts);
    }
  }
  unrolledMod->fixup_ports();  // Necessary since we added and removed ports

  return unrolledMod;
}



// Since this generator caches the unrolled design, it would be
// most efficient to call print_llvm_ir repeatedly for each destination
// of the same instruction.

void
YosysUFGenerator::print_llvm_ir(funcExtract::DestInfo &destInfo,
                                const uint32_t bound,
                                uint32_t instrIdx,  // This number is only for printing in messages
                                std::string fileName) 
{

  std::string instr_name = destInfo.get_instr_name();
  std::string targetName = destInfo.get_dest_name();
  std::string funcName = destInfo.get_func_name();

  std::string origModName = internalToV(m_srcmod->name);

  funcExtract::InstrInfo_t& instrInfo =
        funcExtract::g_instrInfo[funcExtract::get_instr_by_name(instr_name)];


  int num_cycles = bound;

  // See if we can reuse any pre-existing unrolled module.
  // This will be the case as long as the instruction and
  // the cycle count do not change.
  // TODO: When do we purge no-longer-needed unrolled modules?

  RTLIL::IdString unrolledModName = RTLIL::escape_id(instr_name+"_unrolled_"+std::to_string(num_cycles));
  RTLIL::Module *unrolledMod = m_des->module(unrolledModName);

  if (unrolledMod) {
    log("Re-using unrolled module %s\n", id2cstr(unrolledModName));
  } else {
    log("New unrolled module %s will be created.\n", id2cstr(unrolledModName));
    unrolledMod = makeUnrolledModule(unrolledModName, m_srcmod, instrInfo, num_cycles);

    // Re-optimize.  Since we have set a lot of constants on input ports,
    // a lot of simplification can be done.
    if (m_do_opto) {
      log("Re-optimizing...\n");
      log_push();
      Pass::call_on_module(m_des, unrolledMod, "opt");
      Pass::call_on_module(m_des, unrolledMod, "stat");
      log_pop();
    }
  }

  // Get the Yosys RTLIL object representing the destination ASV.
  // TODO: Do a better job of mapping the original Verilog register name to the actual wire name.

  RTLIL::IdString portName = cycleize_name(targetName, num_cycles+1);
  RTLIL::Wire *targetPort = unrolledMod->wire(portName);

  if (!targetPort) {
    log_error("Can't find output port wire %s for destination ASV %s\n", portName.c_str(), targetName.c_str());
    return;
  }

  log("Target SigSpec: ");
  my_log_wire(targetPort);
  
  log_header(m_des, "Writing LLVM data...\n");

  Pass::call_on_module(m_des, unrolledMod, "write_rtlil -selected "+fileName+".rtlil");

  LLVMWriter writer;
  writer.write_llvm_ir(unrolledMod, targetPort, origModName,
                       instr_name, targetName, fileName, funcName);
  log("LLVM result written to %s\n", fileName.c_str());

}


YosysModuleInfo::YosysModuleInfo(RTLIL::Module *srcmod)
{
  m_des = srcmod->design;
  m_srcmod = srcmod;
}



// A blank modname implies the top module.
uint32_t YosysModuleInfo::get_var_width_simp(const std::string& var,
                                             const std::string& modname)
{
  RTLIL::Module *mod = modname.empty() ? m_srcmod : m_des->module(verilogToInternal(modname));
  log_assert(mod);

  RTLIL::Wire *wire = mod->wire(verilogToInternal(var));
  log_assert(wire);

  if (!wire) return 0;
  return wire->width;
}


// var might have a module name prefix. This function parses the module name
// and get corresponding module information This syntax is used only in files
// like allowed_target.txt, and is different than a flattened hierarchical
// name  of the form "\<instname>.<varname>"

uint32_t YosysModuleInfo::get_var_width_cmplx(const std::string& var)
{
  if (var.find(".") == std::string::npos || var.substr(0, 1) == "\\") {
    return get_var_width_simp(var, "");
  } else {
    size_t pos = var.find(".");
    std::string modName = var.substr(0, pos);
    std::string varName = var.substr(pos+1);
    if (!is_module(modName)) {
      log_error("Error: module %s not found\n", modName.c_str());
      abort();
    }
    RTLIL::Module *subMod = m_des->module(verilogToInternal(modName));
    return get_var_width_simp(varName, subMod->name.str());
  }
}


bool YosysModuleInfo::is_module(const std::string& modname)
{
  return m_des->module(verilogToInternal(modname)) != nullptr;
}


// Return true if the given wire is an output port of the top module,
// and is driven by a fifo instance.
bool YosysModuleInfo::is_fifo_output(const std::string& wire)
{
  return false; // No fifo support yet.
}


// If instname names an instance in the given parent mod, return its module
// name.  Otherwise return a blank string.  A blank parentmod implies
// the top module.
std::string YosysModuleInfo::get_module_of_inst(const std::string& instname,
                                                const std::string& parentmod)
{
  RTLIL::Module *par_mod = parentmod.empty() ?
          m_srcmod : m_des->module(verilogToInternal(parentmod));
  if (!par_mod) return "";

  RTLIL::Cell *cell = par_mod->cell(verilogToInternal(instname));
  if (!cell) return "";

  return internalToV(cell->type);
}


// Fill in the provided (empty) vector with the output ports of the given module.
// Of course, a blank modname implies the top module.
void YosysModuleInfo::get_module_outputs(std::vector<std::string>& outputs,
                                         const std::string& modname)
{
  RTLIL::Module *mod = modname.empty() ? m_srcmod : m_des->module(verilogToInternal(modname));
  log_assert(mod);

  if (mod) {
    for (auto wireId : mod->ports) {
      RTLIL::Wire *w = mod->wire(wireId);
      if (w && w->port_output) {
        outputs.push_back(internalToV(w->name));
      }
    }
  }
}


// Fill in the provided (empty) vector with the fifo instance names in the given module.
// Of course, a blank modname implies the top module.
void YosysModuleInfo::get_fifo_insts(std::vector<std::string>& fifos,
                                     const std::string& modname)
{
  // Fifos not supported!
}



