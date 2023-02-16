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


YosysUFGenerator::YosysUFGenerator(RTLIL::Module *srcmod, const Options& opts)
{
  m_srcmod = srcmod;
  m_des = srcmod->design;
  m_opts = opts;
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

// If exposeX is false, origPort will be un-ported (thus becoming a plain
// wire) and it will get all the given 0/1/x values set on it.

// If exposeX is true and the given SigSpec is all-x, origPort will be left
// alone.

// If the given SigSpec is fully const (0/1), origPort will be un-ported and
// the SigSpec's 0/1 values will be set on the wire.

// If the SigSpec is a mix of 0/1 and x, origPort will be un-ported and
// renamed, and a new port will be created with its original name. Each 0/1
// bit in SigSpec will be set on origPort, and for each x bit, origPort will
// be connected to the new port.  (The bits in the new port corresponding to
// 0/1 will be left unconnected.)

// Any newly-created port will be returned.  The new or original port will be
// added to the processedPorts list.  Be sure to call module->fixup_ports()
// after calling this.

// TODO: It is possible for some (or all?) of origPort's bits to have a
// constant already set on them in the design (thus making it a multi-driven
// signal).  We should probably avoid connecting anything else to such a bit.
// Checking this would require building and using a SigMap.

RTLIL::Wire *
YosysUFGenerator::applyPortSignal(RTLIL::Wire *origPort, const RTLIL::SigSpec& ss, bool exposeX,
                                  Yosys::pool<Yosys::RTLIL::Wire*>& processedPorts)
{
  log_assert(origPort->port_input);
  log_assert(processedPorts.count(origPort) == 0);
  log_assert(ss.is_fully_const());

  RTLIL::Module *mod = origPort->module;

  // If exposeX is not given, the port is demoted to a plain wire, and it gets
  // the given SigSpec applied to it.
  if (!exposeX) {
    origPort->port_input = false;  // the original port is demoted to an ordinary Wire
    // Connect the SigSpec to the former port's wire.
    mod->connect(RTLIL::SigSpec(origPort), ss);
    processedPorts.insert(origPort);
    return origPort;

  } else if (ss.is_fully_undef()) {
    // no change needed if all-x and exposeX is true: common case for ASVs.
    processedPorts.insert(origPort);
    return origPort;

  } else if (ss.is_fully_def()) {
    // The port becomes a wire with a constant on it: common case for fully-encoded primary inputs
    origPort->port_input = false;
    // Connect the all-0/1 SigSpec to the former port's wire.
    mod->connect(RTLIL::SigSpec(origPort), ss);
    processedPorts.insert(origPort);
    return origPort; 

  } else {
    // Remaining situation is a partially-defined sigspec, and exposeX is true.

    // Rename the original port.  It keeps all its current connections.
    RTLIL::IdString origName = origPort->name;
    std::string newStr = "$" + origPort->name.substr(1) + "orig";
    RTLIL::IdString newName = mod->uniquify(newStr);
    mod->rename(origPort, newName);

    // Make a new port with the orignal port's name
    RTLIL::Wire *newPort = mod->addWire(origName, origPort->width);

    // The new port takes over the old port's status, the old port becomes an
    // ordinary wire.
    // TODO: Copy or move orig port attributes to new wire?
    newPort->port_input = true;
    newPort->port_output = origPort->port_output;
    origPort->port_input = false;
    

    // A partially-constant SigSpec, so connect the old port to either the new port or the SigSpec
    // on a bit-by-bit basis.

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

    processedPorts.insert(newPort);
    return newPort;
  }
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
      applyPortSignal(port, ss, true /*exposeX*/, processedPorts);

    }
  }

  // Set x on any clock inputs for all cycles. The name of the clock signal is defined in
  // instr.txt.  Normally the clock signals will be dead, since we removed
  // all the registers.
  if (!taintGen::g_recentClk.empty()) {
    for(int cycle = 1; cycle <= cycles+1; ++cycle) {
      RTLIL::IdString clockname = cycleize_name(taintGen::g_recentClk, cycle);
      RTLIL::Wire *clockport = mod->wire(clockname);
      if (clockport && clockport->port_input) {
        // Set to x, probably opto will eliminate it.
        RTLIL::SigSpec ss(RTLIL::State::Sx);
        adjustSigSpecWidth(ss, clockport->width);
        applyPortSignal(clockport, ss, false /*exposeX*/, processedPorts);
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

  // Make into output ports the final-cycle (num_cycles+1) signals that
  // represent ASVs.  Typically these are the from_Q signals created by
  // unroll_module(). TODO: If we really need to control the ordering of the 
  // update function arguments, this is a good place to do that.

  // Start with the members of ASV register arrays.  Also set attributes on
  // these ports to indicate which position of which array they belong to.
  // The array names get a cycle number, to be consistent with the original
  // func_extract.  Note that the target vector arrays are NOT Yosys objects,
  // so their names are simple strings.

  for (auto pair: funcExtract::g_allowedTgtVec) {
    std::string vecName = funcExtract::timed_name(pair.first, num_cycles+1);
    int idx = -1;
    for (const std::string& member : pair.second.members) {
      ++idx;
      RTLIL::IdString portname = cycleize_name(member, num_cycles+1);
      RTLIL::Wire *port = unrolledMod->wire(portname);
      if (port) {
        port->port_output = true;
        // Annotate the port with the original target ASV name and
        // its vector information.
        port->set_string_attribute(TARGET_ATTR, member);
        port->set_string_attribute(TARGET_VECTOR_ATTR, vecName);
        port->set_string_attribute(TARGET_VECTOR_IDX_ATTR, std::to_string(idx));
      } else {
        log_warning("Cannot find unrolled final-cycle signal for register array ASV %s\n",
                    member.c_str());
        continue;
      }
    }
  }

  // Now do the regular ASVs.
  for (auto pair : funcExtract::g_allowedTgt) {
    RTLIL::IdString portname = cycleize_name(pair.first, num_cycles+1);
    RTLIL::Wire *port = unrolledMod->wire(portname);
    if (port) {
      port->port_output = true;
      // Annotate the port with the original target ASV name.
      port->set_string_attribute(TARGET_ATTR, pair.first);
    } else {
      log_warning("Cannot find unrolled final-cycle signal for ASV %s\n", pair.first.c_str());
      continue;
    }
  }

  // Finally, set attributes on the (existing) input ports representing first-cycle members of
  // ASV register arrays.  

  for (auto pair: funcExtract::g_allowedTgtVec) {
    std::string vecName = funcExtract::timed_name(pair.first, 1);
    int idx = -1;
    for (const std::string& member : pair.second.members) {
      ++idx;
      RTLIL::IdString portname = cycleize_name(member, 1);
      RTLIL::Wire *port = unrolledMod->wire(portname);
      if (port && port->port_input) {
        // Annotate the port with the original target ASV name and
        // its vector information.
        port->set_string_attribute(TARGET_ATTR, member);
        port->set_string_attribute(TARGET_VECTOR_ATTR, vecName);
        port->set_string_attribute(TARGET_VECTOR_IDX_ATTR, std::to_string(idx));
      } else {
        log_warning("Cannot find unrolled first-cycle input port for register array ASV %s\n",
                    member.c_str());
        continue;
      }
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
  if (m_opts.optimize_unrolled) {
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
      log_warning("Cannot find unrolled first-cycle input port for ASV %s\n", portname.c_str());
      continue;
    }
    processedPorts.insert(port);
  }

  // Same thing for members of ASV register arrays
  for (auto pair: funcExtract::g_allowedTgtVec) {
    for (const std::string& member : pair.second.members) {
      RTLIL::IdString portname = cycleize_name(member, 1);
      RTLIL::Wire *port = unrolledMod->wire(portname);
      if (!port || !port->port_input) {
        log_warning("Cannot find unrolled first-cycle input port for register array ASV %s\n",
                    portname.c_str());
        continue;
      }
      processedPorts.insert(port);
    }
  }

  unrolledMod->fixup_ports();  // Necessary since we added and removed ports

  // Apply any reset values as needed to input ports for cycle #1.
  // Explicit x reset values are included.
  // TODO: It is possible for some (or all?) of the port's bits to have a
  // constant already set on them in the design.  Will a clash between the
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
      applyPortSignal(port, ss, false /*exposeX*/, processedPorts);
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
      applyPortSignal(port, ss, false /*exposeX*/, processedPorts);
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
  bool isVector = destInfo.isVector && !destInfo.isMemVec;


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

    if (m_opts.save_unrolled) {
      std::string rtlilFileName = instr_name+"_unrolled_"+std::to_string(num_cycles)+".rtlil";
      log_push();
      Pass::call_on_module(m_des, unrolledMod, "write_rtlil -selected "+rtlilFileName);
      log_pop();
    }

    // Re-optimize.  Since we have set a lot of constants on input ports,
    // a lot of simplification can be done.
    if (m_opts.optimize_unrolled) {
      log("Optimizing unrolled module...\n");
      log_push();
      Pass::call_on_module(m_des, unrolledMod, "opt -mux_bool");
      Pass::call_on_module(m_des, unrolledMod, "opt_clean -purge");  // Removes all unused wires
      Pass::call_on_module(m_des, unrolledMod, "stat");
      log_pop();

      if (m_opts.save_unrolled) {
        std::string rtlilFileName = instr_name+"_unrolled_opto_"+std::to_string(num_cycles)+".rtlil";
        log_push();
        Pass::call_on_module(m_des, unrolledMod, "write_rtlil -selected "+rtlilFileName);
        log_pop();
      }
    }
  }

  log_header(m_des, "Writing LLVM data...\n");

  LLVMWriter::Options llvmOpts;
  llvmOpts.verbose_llvm_value_names = m_opts.verbose_llvm_value_names;
  llvmOpts.cell_based_llvm_value_names = m_opts.cell_based_llvm_value_names;
  llvmOpts.simplify_and_or_gates = m_opts.simplify_and_or_gates;
  llvmOpts.simplify_muxes = m_opts.simplify_muxes;
  llvmOpts.use_poison = m_opts.use_poison;


  LLVMWriter writer(llvmOpts);
  writer.write_llvm_ir(unrolledMod, targetName, isVector, origModName,
                      num_cycles, fileName, funcName);
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
  if (wire) {
    return wire->width;
  }

  // Possibly the variable is a memory element or the entire memory, which does not have a
  // nicely-named wire associated with it.

  // Strip off any indexing, e.g. "cpuregs[12]"
  static const std::regex bracketRegex("\\[([0-9]+)\\]");
  std::string basename = std::regex_replace(var, bracketRegex, "");
  bool hadIndex = (basename != var);

  RTLIL::Cell *memcell = mod->cell(verilogToInternal(basename));
  // Look for the \WIDTH parameter
  if (memcell && memcell->is_mem_cell()) {
    uint32_t width = memcell->getParam("\\WIDTH").as_int();
    if (hadIndex) return width; // Var is an element of the memory.
    uint32_t size = memcell->getParam("\\SIZE").as_int();
    return width * size;  // Var is the entire memory
  }

  log_assert(false);
  return 0;
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



