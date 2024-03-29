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
 *  A simple and straightforward Verilog backend.
 *
 */

#include "live_analysis/src/global_data.h"
#include "func_extract/src/global_data_struct.h"
#include "func_extract/src/parse_fill.h"
#include "func_extract/src/read_instr.h"
#include "func_extract/src/get_all_update.h"
#include "func_extract/src/helper.h"

#include "llvm/ADT/APInt.h"

#include "unroll.h"
#include "util.h"

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

bool verbose, noattr;

// TODO: Put the functions and global vars below in a proper class.

// This maps registers and memories in the original module to copies
// in the smashed dest module, for a particular cycle
typedef dict<RTLIL::Cell*, RTLIL::Cell*> RegDict;

// This maps registers or memories in the original module to D or Q pin
// SigSpecs in the smashed dest module, for a particular cycle. The dict holds
// a copy of the SigSpec, which will still be valid after the register in the
// dest module is deleted.
typedef dict<RTLIL::Cell*, RTLIL::SigSpec> SigSpecDict;


// Stuff inherited from the code of the write_verilog command.  Is it all needed?
int auto_name_counter, auto_name_offset, auto_name_digits;
std::map<RTLIL::IdString, int> auto_name_map;
std::string auto_prefix, extmem_prefix;

RTLIL::Module *active_module;
dict<RTLIL::SigBit, RTLIL::State> active_initdata;
IdString initial_id;

// Doug: this is inherited from the code of the write_verilog command.  
void reset_auto_counter_id(RTLIL::IdString id, bool may_rename)
{
  const char *str = id.c_str();

  if (*str == '$' && may_rename)
    auto_name_map[id] = auto_name_counter++;

  if (str[0] != '\\' || str[1] != '_' || str[2] == 0)
    return;

  for (int i = 2; str[i] != 0; i++) {
    if (str[i] == '_' && str[i+1] == 0)
      continue;
    if (str[i] < '0' || str[i] > '9')
      return;
  }

  int num = atoi(str+2);
  if (num >= auto_name_offset)
    auto_name_offset = num + 1;
}

// Doug: this is inherited from the code of the write_verilog command.  
void reset_auto_counter(RTLIL::Module *module)
{
  auto_name_map.clear();
  auto_name_counter = 0;
  auto_name_offset = 0;

  reset_auto_counter_id(module->name, false);

  for (auto w : module->wires())
    reset_auto_counter_id(w->name, true);

  for (auto cell : module->cells()) {
    reset_auto_counter_id(cell->name, true);
    reset_auto_counter_id(cell->type, false);
  }

  for (auto it = module->processes.begin(); it != module->processes.end(); ++it)
    reset_auto_counter_id(it->second->name, false);

  auto_name_digits = 1;
  for (size_t i = 10; i < auto_name_offset + auto_name_map.size(); i = i*10)
    auto_name_digits++;

  if (verbose)
    for (auto it = auto_name_map.begin(); it != auto_name_map.end(); ++it)
      log_debug("  renaming `%s' to `%s_%0*d_'.\n", it->first.c_str(), auto_prefix.c_str(), auto_name_digits, auto_name_offset + it->second);
}


// Doug: this is inherited from the code of the write_verilog command.  It makes
// a Verilog-legal name, which is not really necessary in our flow.
std::string cleaned_id(RTLIL::IdString internal_id, bool may_rename = true)
{
  const char *str = internal_id.c_str();
  bool do_escape = false;

  if (may_rename && auto_name_map.count(internal_id) != 0)
    return stringf("%s_%0*d_", auto_prefix.c_str(), auto_name_digits, auto_name_offset + auto_name_map[internal_id]);

  if (*str == '\\')
    str++;

  if ('0' <= *str && *str <= '9')
    do_escape = true;

  for (int i = 0; str[i]; i++)
  {
    if ('0' <= str[i] && str[i] <= '9')
      continue;
    if ('a' <= str[i] && str[i] <= 'z')
      continue;
    if ('A' <= str[i] && str[i] <= 'Z')
      continue;
    if (str[i] == '_')
      continue;
    do_escape = true;
    break;
  }

  const pool<string> keywords = {
    // IEEE 1800-2017 Annex B
    "accept_on", "alias", "always", "always_comb", "always_ff", "always_latch", "and", "assert", "assign", "assume", "automatic", "before",
    "begin", "bind", "bins", "binsof", "bit", "break", "buf", "bufif0", "bufif1", "byte", "case", "casex", "casez", "cell", "chandle",
    "checker", "class", "clocking", "cmos", "config", "const", "constraint", "context", "continue", "cover", "covergroup", "coverpoint",
    "cross", "deassign", "default", "defparam", "design", "disable", "dist", "do", "edge", "else", "end", "endcase", "endchecker",
    "endclass", "endclocking", "endconfig", "endfunction", "endgenerate", "endgroup", "endinterface", "endmodule", "endpackage",
    "endprimitive", "endprogram", "endproperty", "endsequence", "endspecify", "endtable", "endtask", "enum", "event", "eventually",
    "expect", "export", "extends", "extern", "final", "first_match", "for", "force", "foreach", "forever", "fork", "forkjoin", "function",
    "generate", "genvar", "global", "highz0", "highz1", "if", "iff", "ifnone", "ignore_bins", "illegal_bins", "implements", "implies",
    "import", "incdir", "include", "initial", "inout", "input", "inside", "instance", "int", "integer", "interconnect", "interface",
    "intersect", "join", "join_any", "join_none", "large", "let", "liblist", "library", "local", "localparam", "logic", "longint",
    "macromodule", "matches", "medium", "modport", "module", "nand", "negedge", "nettype", "new", "nexttime", "nmos", "nor",
    "noshowcancelled", "not", "notif0", "notif1", "null", "or", "output", "package", "packed", "parameter", "pmos", "posedge", "primitive",
    "priority", "program", "property", "protected", "pull0", "pull1", "pulldown", "pullup", "pulsestyle_ondetect", "pulsestyle_onevent",
    "pure", "rand", "randc", "randcase", "randsequence", "rcmos", "real", "realtime", "ref", "reg", "reject_on", "release", "repeat",
    "restrict", "return", "rnmos", "rpmos", "rtran", "rtranif0", "rtranif1", "s_always", "s_eventually", "s_nexttime", "s_until",
    "s_until_with", "scalared", "sequence", "shortint", "shortreal", "showcancelled", "signed", "small", "soft", "solve", "specify",
    "specparam", "static", "string", "strong", "strong0", "strong1", "struct", "super", "supply0", "supply1", "sync_accept_on",
    "sync_reject_on", "table", "tagged", "task", "this", "throughout", "time", "timeprecision", "timeunit", "tran", "tranif0", "tranif1",
    "tri", "tri0", "tri1", "triand", "trior", "trireg", "type", "typedef", "union", "unique", "unique0", "unsigned", "until", "until_with",
    "untyped", "use", "uwire", "var", "vectored", "virtual", "void", "wait", "wait_order", "wand", "weak", "weak0", "weak1", "while",
    "wildcard", "wire", "with", "within", "wor", "xnor", "xor",
  };
  if (keywords.count(str))
    do_escape = true;

  if (do_escape)
    return "\\" + std::string(str) + " ";
  return std::string(str);
}


// If the SigSpec is an entire single wire, that wire name is returned.
// If it is a slice of that wire, a name with the correct "[]" is returned.
// Otherwise (i.e. a constant or a concatenation) nothing is returned.
bool is_reg_wire(RTLIL::SigSpec sig, std::string &reg_name)
{
  if (!sig.is_chunk() || sig.as_chunk().wire == NULL)
    return false;

  RTLIL::SigChunk chunk = sig.as_chunk();

  reg_name = cleaned_id(chunk.wire->name);
  if (sig.size() != chunk.wire->width) {
    if (sig.size() == 1)
      reg_name += stringf("[%d]", chunk.wire->start_offset +  chunk.offset);
    else if (chunk.wire->upto)
      reg_name += stringf("[%d:%d]", (chunk.wire->width - (chunk.offset + chunk.width - 1) - 1) + chunk.wire->start_offset,
          (chunk.wire->width - chunk.offset - 1) + chunk.wire->start_offset);
    else
      reg_name += stringf("[%d:%d]", chunk.wire->start_offset +  chunk.offset + chunk.width - 1,
          chunk.wire->start_offset +  chunk.offset);
  }

  return true;
}



// Doug: add "__#<cycle>" to the object's name, and ensure that it is unique.
// Because of the uniquification, it is sort of dangerous to parse object names
// to determine the cycle number they are associated with. TODO: Add a cycle
// number attribute to critical objects (e.g. module ports)?

template<class T>
IdString map_name(RTLIL::Module *module, T *object, int cycle)
{
  IdString cycleized_name = cycleize_name(object->name, cycle);
  IdString new_name =  module->uniquify(cycleized_name);
  if (new_name != cycleized_name) {
    log_warning("Collision with cycleized name %s - renamed to %s\n", 
                cycleized_name.c_str(), new_name.c_str());
  }
  return new_name;
}


// Doug: This is worthwhile: the hdlname attribute keeps track of the original pre-unrolled name.
template<class T>
void map_attributes(T *object, IdString orig_object_name)
{
  // Preserve original names via the hdlname attribute, but only for objects with a fully public name.
  if ((object->has_attribute(ID::hdlname) || orig_object_name[0] == '\\')) {
    std::vector<std::string> hierarchy;
    if (object->has_attribute(ID::hdlname))
      hierarchy = object->get_hdlname_attribute();
    else
      hierarchy.push_back(orig_object_name.str().substr(1));
    object->set_hdlname_attribute(hierarchy);
  }
}


// Doug: This is vital, since we are effectively renaming wires: all the sigspecs on
// cell ports and connections must be fixed up.
void map_sigspec(const dict<RTLIL::Wire*, RTLIL::Wire*> &map, RTLIL::SigSpec &sig,
                 RTLIL::Module *into = nullptr)
{
  vector<SigChunk> chunks = sig;
  for (auto &chunk : chunks)
    if (chunk.wire != nullptr && chunk.wire->module != into)
      chunk.wire = map.at(chunk.wire);
  sig = chunks;
}


// Copy the src module's objects into the dest module, renaming them
// based on the given cycle number.  The given RegDict will be filled in.
void smash_module(RTLIL::Module *dest, RTLIL::Module *src, 
                  int cycle, RegDict& registers)
{
  RTLIL::Design *design = dest->design;
  log_assert(src->design == design);

  // Copy the contents of the module src into module dest.  
  log_debug("Smashing for cycle %d\n", cycle);

  dict<IdString, IdString> memory_map;
  for (auto &src_memory_it : src->memories) {
    RTLIL::Memory *new_memory = dest->addMemory(map_name(dest, src_memory_it.second, cycle),
                                                src_memory_it.second);
    map_attributes(new_memory, src_memory_it.second->name);
    memory_map[src_memory_it.first] = new_memory->name;
    design->select(dest, new_memory);
  }

  dict<RTLIL::Wire*, RTLIL::Wire*> wire_map;
  for (auto src_wire : src->wires()) {

    // new_wire inherits the port status of src_wire
    RTLIL::Wire *new_wire = dest->addWire(map_name(dest, src_wire, cycle), src_wire);
    new_wire->port_id = false;

    map_attributes(new_wire, src_wire->name);
    wire_map[src_wire] = new_wire;
    design->select(dest, new_wire);
  }

  // There should not be any processes present - they shoud have already been converted to FFs
  for (auto &src_proc_it : src->processes) {
    RTLIL::Process *new_proc = dest->addProcess(map_name(dest, src_proc_it.second, cycle),
                                                src_proc_it.second);
    map_attributes(new_proc, src_proc_it.second->name);
    for (auto new_proc_sync : new_proc->syncs)
      for (auto &memwr_action : new_proc_sync->mem_write_actions)
        memwr_action.memid = memory_map.at(memwr_action.memid).str();
    auto rewriter = [&](RTLIL::SigSpec &sig) { map_sigspec(wire_map, sig); };
    new_proc->rewrite_sigspecs(rewriter);
    design->select(dest, new_proc);
  }
  log_debug("Smashed wires and processes for cycle %d\n", cycle);

  for (auto src_cell : src->cells()) {
    RTLIL::Cell *new_cell = dest->addCell(map_name(dest, src_cell, cycle), src_cell);
    map_attributes(new_cell, src_cell->name);
    if (new_cell->has_memid()) {
      IdString memid = new_cell->getParam(ID::MEMID).decode_string();
      new_cell->setParam(ID::MEMID, Const(memory_map.at(memid).str()));
    } else if (new_cell->is_mem_cell()) {
      IdString memid = new_cell->getParam(ID::MEMID).decode_string();
      new_cell->setParam(ID::MEMID, Const(cycleize_name(memid, cycle).str()));
    }
    auto rewriter = [&](RTLIL::SigSpec &sig) { map_sigspec(wire_map, sig); };
    new_cell->rewrite_sigspecs(rewriter);
    design->select(dest, new_cell);

    // Warn if we discover explicit hierarchy in the data.
    if (src_cell->type[0] != '$') {
      log_warning("Smashing user-defined %s cell %s for cycle %d\n",
                src_cell->type.c_str(), src_cell->name.c_str(), cycle);
    }


    // For FF and memory cells, update the dict that maps the (cycle-independent) register
    // name to the new cell.  Later we will delete these cells.
    if (RTLIL::builtin_ff_cell_types().count(src_cell->type) > 0) {
      log_debug("Smashing %s cell %s for cycle %d\n",
                src_cell->type.c_str(), src_cell->name.c_str(), cycle);

      registers[src_cell] = new_cell;

    } else if (src_cell->is_mem_cell()) {
      log_debug("Smashing %s memory cell %s for cycle %d\n",
                src_cell->type.c_str(), src_cell->name.c_str(), cycle);

      registers[src_cell] = new_cell;
    }
  }

  // Give the new ports proper port IDs.  (Could be done once, after all cycles are smashed?)
  dest->fixup_ports();

  for (auto &src_conn_it : src->connections()) {
    RTLIL::SigSig new_conn = src_conn_it;
    map_sigspec(wire_map, new_conn.first);
    map_sigspec(wire_map, new_conn.second);
    dest->connect(new_conn);
  }

}



// This makes special modules that are used to represent memory read/write
// access.  The only reason that the modules need to explicitly exist is to
// define the port input/output directions.

void
makeMemoryAccessModules(RTLIL::Design *design)
{
  bool added = false;

  if (!design->module(MEM_EXTRACT_MOD_NAME)) {
    RTLIL::Module *mod = design->addModule(MEM_EXTRACT_MOD_NAME);
    added = true;

    mod->set_bool_attribute(MEM_MOD_ATTR);

    mod->addWire("\\MEM_IN")->port_input = true;
    mod->addWire("\\ADDR")->port_input = true;
    mod->addWire("\\DATA")->port_output = true;
    mod->sort();
    mod->fixup_ports();
    mod->check();
  }

  if (!design->module(MEM_INSERT_MOD_NAME)) {
    RTLIL::Module *mod = design->addModule(MEM_INSERT_MOD_NAME);
    added = true;

    mod->set_bool_attribute(MEM_MOD_ATTR);

    mod->addWire("\\MEM_IN")->port_input = true;
    mod->addWire("\\MEM_OUT")->port_output = true;
    mod->addWire("\\ADDR")->port_input = true;
    mod->addWire("\\DATA")->port_input = true;
    mod->sort();
    mod->fixup_ports();
    mod->check();
  }

  if (added) {
    design->sort();
    design->check();
  }
}



// Add the mux needed to model a FF's SRST or CE signal.  Return the added mux
// cell.  The mux B input gets whatever is connected to the FF D pin, and the
// mux Y is left unconnected.  The mux A input gets a_sig, and the mux S input
// gets s_sig, possibly with an added inverter.

RTLIL::Cell*
wire_up_mux(RTLIL::Module* mod, FfData& ff, RTLIL::SigSpec a_sig,
            RTLIL::SigSpec s_sig, bool invert_s)
{

  log_assert(a_sig.size() == ff.width);

  RTLIL::Cell *mux = mod->addCell(mod->uniquify(ff.name.str()+"_mux"), ID($mux));
  log_debug("Added mux %s\n", mux->name.c_str());
  mux->setParam(ID::WIDTH, ff.width);

  // Connect the signal driving the D pin to the B input of the mux
  mux->setPort(ID::B, ff.sig_d);

  // Connect the provided value to the mux A input.
  mux->setPort(ID::A, a_sig);

  if (invert_s) {
    RTLIL::Cell *inv = mod->addCell(mod->uniquify(ff.name.str()+"_mux_inv"), ID($not));
    log_debug("Added mux inverter %s\n", inv->name.c_str());
    inv->setParam(ID::A_WIDTH, 1);
    inv->setParam(ID::Y_WIDTH, 1);
    inv->setParam(ID::A_SIGNED, 0);

    // Provided signal goes to inverter input
    inv->setPort(ID::A, s_sig);

    // Add a wire to connect the inverter and mux
    RTLIL::Wire *w_inv = mod->addWire(mod->uniquify(ff.name.str()+"_mux_inv"), 1);

    // Wire connects inverter output to mux S input
    inv->setPort(ID::Y, w_inv);
    mux->setPort(ID::S, w_inv);
    
  } else {
    // Provided signal goes directly to mux S input
    mux->setPort(ID::S, s_sig);
  }

  return mux;
}


// Add the logic needed to model a FF's SRST signal.
// Return the cell (AND gate or mux) that implements the reset
RTLIL::Cell*
wire_up_srst(RTLIL::Module* mod, FfData& ff,
             RTLIL::SigSpec& to_D, RTLIL::SigSpec& from_Q)
{
  log_debug("Wire up srst\n");

  // We can use an AND gate if the cell is reset to sero.
  // Otherwise we need a mux with the reset value at one input.

  RTLIL::Cell *reset_gate = nullptr;

  if (ff.val_srst.is_fully_zero()) {

    // To model the reset, add an inverter and an AND gate between D and Q
    // Negative resets don't need the inverter.
    reset_gate = mod->addCell(mod->uniquify(ff.name.str()+"_srst_and"), ID($and));
    log_debug("Added srst AND %s\n", reset_gate->name.c_str());
    reset_gate->setParam(ID::A_WIDTH, ff.width);
    reset_gate->setParam(ID::B_WIDTH, ff.width);
    reset_gate->setParam(ID::Y_WIDTH, ff.width);
    reset_gate->setParam(ID::A_SIGNED, 0);
    reset_gate->setParam(ID::B_SIGNED, 0);

    // Connect the signal driving the D pin to the B input of the AND gate
    reset_gate->setPort(ID::B, ff.sig_d);

    if (ff.pol_srst) {
      // Positive reset needs an inverter
      RTLIL::Cell *inv = mod->addCell(mod->uniquify(ff.name.str()+"_srst_inv"), ID($not));
      log_debug("Added srst inverter %s\n", inv->name.c_str());
      inv->setParam(ID::A_WIDTH, 1);
      inv->setParam(ID::Y_WIDTH, 1);
      inv->setParam(ID::A_SIGNED, 0);

      // Positive reset goes to inverter input
      inv->setPort(ID::A, ff.sig_srst);

      // Add a wire to connect the inverter and AND gate
      RTLIL::Wire *w_inv = mod->addWire(mod->uniquify(ff.name.str()+"_srst_inv"), 1);

      // Wire connects inverter output to AND gate B input
      inv->setPort(ID::Y, w_inv);

      // If the AND gate is wider than 1 bit, we need to concatenate
      // N copies of the control signal
      RTLIL::SigBit sigbit(w_inv);
      std::vector<RTLIL::SigBit> sigbits(ff.width, sigbit);
      RTLIL::SigSpec widened_w_inv(sigbits);

      reset_gate->setPort(ID::A, widened_w_inv);
      
    } else {
      // Negative reset goes directly to B input (duplicated if width > 1)

      RTLIL::SigBit sigbit(ff.sig_srst);
      std::vector<RTLIL::SigBit> sigbits(ff.width, sigbit);
      RTLIL::SigSpec widened_srst(sigbits);

      reset_gate->setPort(ID::A, widened_srst);
    }

  } else {

    // In this case, model the reset by adding a mux between D and Q.
    // Positive resets need an inverter before the mux S input.  We could
    // avoid the inverter by instead switching the mux A and B inputs, but the
    // caller expects the mux B input to have the data signal.  The mux A
    // input of course gets the reset value.

    reset_gate = wire_up_mux(mod, ff, ff.val_srst, ff.sig_srst, ff.pol_srst);
    log_debug("Added srst mux %s\n", reset_gate->name.c_str());
  }

  // Lastly we need a stub wire from the gate output which
  // will send the signal to the next cycle

  RTLIL::Wire *w_d = mod->addWire(mod->uniquify(ff.name.str()+"_gated_d"), ff.width);
  reset_gate->setPort(ID::Y, w_d);

  // Return the modified D and Q connections to the caller.
  to_D = w_d;
  from_Q = ff.sig_q;

  return reset_gate;
}


// Add the logic needed to model a FF's CE signal.
RTLIL::Cell*
wire_up_ce(RTLIL::Module* mod, FfData& ff,
                  RTLIL::SigSpec& to_D, RTLIL::SigSpec& from_Q)
{
  log_debug("Wire up ce\n");

  // To model the enable, add a mux between D and Q
  // Keep in mind the ce signal polarity

  RTLIL::Cell *mux = wire_up_mux(mod, ff, ff.sig_q, ff.sig_ce, !ff.pol_ce);
  log_debug("Added ce mux %s\n", mux->name.c_str());

  // Lastly we need a stub wire from the mux output which
  // will send the signal to the next cycle

  RTLIL::Wire *w_d = mod->addWire(mod->uniquify(ff.name.str()+"_muxed_d"), ff.width);
  mux->setPort(ID::Y, w_d);

  // Return the modified D and Q connections to the caller.
  to_D = w_d;
  from_Q = ff.sig_q;

  return mux;
}


// Replace the given FF cell.
// The signal driving the D pin is returned in to_D.
// The signal driven by the Q pin is returned in from_Q.
// Simple FFs can basically go away, but an enable pin must be converted
// into a mux that feeds to_D directly from from_Q, and
// a sync reset must become an AND gate feeding from_Q.

bool split_ff(RTLIL::Cell *cell,
               RTLIL::SigSpec& to_D, RTLIL::SigSpec& from_Q)
{
  RTLIL::Module *mod = cell->module;


  if (RTLIL::builtin_ff_cell_types().count(cell->type) == 0) {
    log_assert(false);
    return false;  // Not a ff
  }

  FfData ff(nullptr, cell);

  log_debug("\nSplitting FF cell '%s'.  Width %d\n",
            cell->name.c_str(), ff.width);

  // $ff / $_FF_ cell: not supported.
  if (ff.has_gclk) {
    log_error("FF cell `%s' has a gclk, not supported\n", cell->name.c_str());
    return false;
  }

  // clockless FFs not supported
  if (!ff.has_clk) {
    log_error("FF cell `%s' has no clock, not supported\n", cell->name.c_str());
    return false;
  }

  // S/R FFs not supported
  if (ff.has_sr) {
    log_error("S/R FF cell `%s' not supported\n", cell->name.c_str());
    return false;
  }

  // Async reset not supported
  if (ff.has_arst) {
    log_error("FF cell `%s' has async reset, not supported\n", cell->name.c_str());
    return false;
  }

  // Async load not supported
  if (ff.has_aload) {
    log_error("FF cell `%s' has async load, not supported\n", cell->name.c_str());
    return false;
  }


  log_debug("D signal: %s\n", log_signal(ff.sig_d));
  log_debug("Q signal: %s\n", log_signal(ff.sig_q));
  log_debug("Clock signal: %s\n", log_signal(ff.sig_clk));
  if (ff.has_srst) {
    log_debug("SRST signal: %s\n", log_signal(ff.sig_srst));
  }
  if (ff.has_ce) {
    log_debug("CE signal: %s\n", log_signal(ff.sig_ce));
  }


  if (ff.has_srst && ff.has_ce) {
    if (!ff.ce_over_srst) {
      log_debug("Process ce+srst\n");


      RTLIL::SigSpec dummy;
      RTLIL::Cell *and_gate = wire_up_srst(mod, ff, to_D, dummy); // Fills in to_D and dummy

      RTLIL::SigSpec ce_mux_out;
      wire_up_ce(mod, ff, ce_mux_out, from_Q);

      // Connect the ce mux output to the reset input
      and_gate->setPort(ID::B, ce_mux_out);

    } else {
      // This is less common...
      log_warning("process ce_over_srst\n");

      RTLIL::SigSpec dummy;
      RTLIL::Cell *mux = wire_up_ce(mod, ff, to_D, dummy); // Fills in to_D and dummy

      RTLIL::SigSpec ce_rst_out;
      wire_up_srst(mod, ff, ce_rst_out, from_Q);

      // Connect the rst output to the ce mux input
      mux->setPort(ID::B, ce_rst_out);

    }
  } else if (ff.has_srst) {
    log_debug("Process srst\n");
    wire_up_srst(mod, ff, to_D, from_Q); // Fills in to_D and from_Q
  } else if (ff.has_ce) {
    log_debug("Process ce\n");
    wire_up_ce(mod, ff, to_D, from_Q);
  } else {
    // A plain D -> Q connection; no added gates
    // Return (copies of) these to the caller.
    log_debug("Process simple ff\n");
    to_D = ff.sig_d;
    from_Q = ff.sig_q;
  }


  // The FF of course goes away.
  mod->remove(cell);
  return true;
}


// Replace the given memory cell.
// The signal driving the inputs is returned in to_D.
// The signal driven by the outputs is returned in from_Q.
// The unrolled memory is modeled by three cells:
//
// 1: A special "extractor" cell that models the decoding and
//    reading of the memory.
// 2: A special "inserter" cell that models a memory write.
// 3: An optional mux cell that implements a write enable by
//    bypassing the mux.
//
// The LLVM code generator will translate the signals representing the memory
// values to a LLVM vectors, and it will translate the special cells to LLVM
// vector insert and extract instructions.
// 
// This code currently supports only single-port read/write memories, but it
// would be straightforward to add any number of extractors, and to have
// multiple inserters connected in series.
//
// It is assumed that the memory cells are of type $mem_v2, which seems to
// always be the case for recent Yosys releases.  Read clocks, read enables,
// and reset signals are not supported. It is also assumed that all positions
// share the same write enable signal.

bool split_mem(RTLIL::Cell *cell, RTLIL::Cell *orig_cell, int cycle,
               RTLIL::SigSpec& to_D, RTLIL::SigSpec& from_Q)
{
  RTLIL::Module *mod = cell->module;

  if (!cell->is_mem_cell()) {
    log_assert(false);
    return false;  // Not a memory
  }

  // Check for complicated memories.
  // Multiple read ports could easily be supported by adding 
  // multiple extractors
  log_assert(cell->parameters[ID::RD_PORTS].as_int() == 1);
  log_assert(cell->parameters[ID::WR_PORTS].as_int() == 1);
  log_assert(cell->parameters[ID::OFFSET].as_int() == 0);
  log_assert(cell->parameters[ID::RD_CLK_ENABLE].as_int() == 0);

  int size = cell->parameters[ID::SIZE].as_int();
  int width = cell->parameters[ID::WIDTH].as_int();

  log_debug("\nSplitting memory cell '%s'. Size %d  Width %d\n",
            cell->name.c_str(), size, width);

  RTLIL::IdString cellname = cell->name;

  // Rename the cell, because we want to create a wire of the same name.
  // The cell gets deleted at the end of this function, so the actual name is
  // irrelevant.
  mod->rename(cell, mod->uniquify("$dying_cyclized_mem_cell"));

  // Create Wires that represent the memory, and make SigSpecs that will 
  // be used to connect all of them between cycles.
  RTLIL::SigSpec sig_d;
  RTLIL::SigSpec sig_q;

  // Make two really wide wires to represent the entire memory.
  // Add attributes to identify them as vectors of signals, for the benefit of
  // LLVM.
  std::string mem_name = orig_cell->name.str();

  RTLIL::IdString wd_name = mod->uniquify(cycleize_name(mem_name+"_d", cycle));
  RTLIL::Wire *wd = mod->addWire(wd_name, width*size);
  wd->set_string_attribute("\\vector_size", std::to_string(size));
  wd->set_string_attribute("\\vector_width", std::to_string(width));
  sig_d.append(wd);

  RTLIL::IdString wq_name = mod->uniquify(cycleize_name(mem_name, cycle));
  RTLIL::Wire *wq = mod->addWire(wq_name, width*size);
  wq->set_string_attribute("\\vector_size", std::to_string(size));
  wq->set_string_attribute("\\vector_width", std::to_string(width));
  sig_q.append(wq);

  RTLIL::Cell *extractor = mod->addCell(mod->uniquify(cellname.str()+"_extract"),
                                        MEM_EXTRACT_MOD_NAME);
  extractor->setParam(ID::ABITS, cell->parameters[ID::ABITS]);
  extractor->setParam(ID::SIZE, cell->parameters[ID::SIZE]);
  extractor->setParam(ID::WIDTH, cell->parameters[ID::WIDTH]);
  extractor->setPort("\\MEM_IN", sig_q);
  extractor->setPort("\\ADDR", cell->getPort(ID::RD_ADDR));
  extractor->setPort("\\DATA", cell->getPort(ID::RD_DATA));

  RTLIL::Cell *inserter = mod->addCell(mod->uniquify(cellname.str()+"_insert"),
                                       MEM_INSERT_MOD_NAME);
  inserter->setParam(ID::ABITS, cell->parameters[ID::ABITS]);
  inserter->setParam(ID::SIZE, cell->parameters[ID::SIZE]);
  inserter->setParam(ID::WIDTH, cell->parameters[ID::WIDTH]);
  inserter->setPort("\\MEM_IN", sig_q);
  inserter->setPort("\\ADDR", cell->getPort(ID::WR_ADDR));
  inserter->setPort("\\DATA", cell->getPort(ID::WR_DATA));

  // Make a really wide wire to connect the extractor output to the write
  // enable mux
  RTLIL::IdString wmux_name = mod->uniquify(cellname.str()+"_wmux");
  RTLIL::Wire *wmux = mod->addWire(wmux_name, width*size);
  wmux->set_string_attribute("\\VECTOR_SIZE", std::to_string(size));
  wmux->set_string_attribute("\\VECTOR_WIDTH", std::to_string(width));

  inserter->setPort("\\MEM_OUT", wmux);

  // Make a really wide mux
  RTLIL::Cell *mux = mod->addCell(mod->uniquify(cellname.str()+"_mux"), ID($mux));
  log_debug("Added memory write mux %s\n", mux->name.c_str());
  mux->setParam(ID::WIDTH, width*size);

  // The mux B input (S==1) gets the wire connected to the output of the extractor
  mux->setPort(ID::B, wmux);

  // The mux A input (S==0) gets the from_Q signal
  mux->setPort(ID::A, sig_q);

  // The mux Y output goes to the to_D signal
  mux->setPort(ID::Y, sig_d);

  // The mux S input gets first bit of the write enable signal.
  // Presumably all the WR_EN bits are the same.
  RTLIL::SigSpec wren = cell->getPort(ID::WR_EN);
  mux->setPort(ID::S, wren[0]);


  log_debug("Read data signal: %s\n", log_signal(sig_d));
  log_debug("Write data signal: %s\n", log_signal(sig_q));

  to_D = sig_d;
  from_Q = sig_q;

  // The memory of course goes away.
  mod->remove(cell);
  return true;
}



void join_sigs(RTLIL::Module *destmod,
               const RTLIL::SigSpec& from_sig, const RTLIL::SigSpec& to_sig)
{
  log_assert(!from_sig.empty());
  log_assert(!to_sig.empty());
  log_assert(from_sig.size() == to_sig.size());

  log_debug("Joining sigs:\n");
  my_log_debug_sigspec(from_sig);
  my_log_debug_sigspec(to_sig);

  // Warning: there is a bug in RTLIL::Module::connect():  If the first
  // SigSpec has any constant bits, that bit position will be left out of the
  // connection.  But that will not be the case for constant bits in the
  // second sigSpec.  So, pass from_sig (which could often have constant bits)
  // as the second SigBit.  A comment in rtlil.cc at line 2214 says that the
  // goal is to avoid connecting constants to other constants, but the
  // implementation does not do that.

  assert(!to_sig.has_const());
  destmod->connect(to_sig, from_sig);

}



void unroll_module(RTLIL::Module *srcmod, RTLIL::Module *destmod, int num_cycles)
{
    auto_prefix = "";
    auto_name_map.clear();

    makeMemoryAccessModules(destmod->design);

    // Copy the source module's attributes to it.
    for (auto &attr : srcmod->attributes) {
      destmod->attributes[attr.first] = attr.second;
    }

    SigSpecDict to_Ds0;
    SigSpecDict to_Ds1;

    // We unroll forwards in time, and (unlike the original
    // func_extract program) the cycles are numbered forwards in time.
    // The data flow is from cycle 1 to cycle <num_cycles+1>,
    // Ultimately the current ASV values will be fed into the
    // input ports associated with cycle 1, and the new ASV value
    // will be available at an output port associated with cycle <num_cycles+1>.
    for (int cycle = 1; cycle <= num_cycles+1; ++cycle) {

      RegDict cur_cycle_regs;

      smash_module(destmod, srcmod, cycle, cur_cycle_regs);

      // For efficiency we use a pair of SigSpecDicts, which alternate 
      // between the roles of 'current' and 'prev'.
      SigSpecDict& prev_cycle_to_Ds = (cycle&0x01) ? to_Ds0 : to_Ds1;
      SigSpecDict& cur_cycle_to_Ds = (cycle&0x01) ? to_Ds1 : to_Ds0;

      cur_cycle_to_Ds.clear();

      for (auto pair : cur_cycle_regs) {
        RTLIL::Cell *orig_reg = pair.first;
        RTLIL::Cell *cycle_reg = pair.second;

        // This sets to_D and from_Q
        RTLIL::SigSpec to_D;
        RTLIL::SigSpec from_Q;
        if (orig_reg->is_mem_cell()) {
          split_mem(cycle_reg, orig_reg, cycle, to_D, from_Q);
        } else {
          split_ff(cycle_reg, to_D, from_Q);
        }

        cur_cycle_to_Ds[orig_reg] = to_D;

        RTLIL::SigSpec& prev_cycle_to_D = prev_cycle_to_Ds[orig_reg];


        if (cycle == 1) {
          // Make the starting cycle's from_Q signal an input port.
          // These ports are where initial ASV values or reset values will
          // be fed into the circuit.
          // If the sigspec specifies more than one wire, things are tricky.
          // To fix that, we may need to add an extra wire.
          // TODO: the port needs to have a hdlname attribute or something
          // similar to identify the  original Verilog register.  The wire name
          // is not always helpful for this.
          // BTW, the ports for non-ASVs will typically get a constant reset value
          // put on them and get un-ported, and will get optimized away.
          log_debug("first cycle input signal: ");
          my_log_debug_sigspec(from_Q);

          // TODO: How to supply reset value?  Observed case: one wide
          // signal feeds several FFs.  So for slices, make the entire wire an
          // input port.

          RTLIL::Wire *initialPort = nullptr;
          if (from_Q.is_wire()) {
            initialPort = from_Q.as_wire();
          } else if (from_Q.is_chunk() && from_Q.as_chunk().is_wire()) {
            initialPort = from_Q.as_chunk().wire;
            log_warning("Initial cycle Q signal is a slice of a wire!\n");
            my_log_sigspec(from_Q);
          } else if (from_Q.empty()) {
            log_warning("Initial cycle Q signal is unconnected!\n");
          } else if (from_Q.is_fully_const()) {
            log_warning("Initial cycle Q signal is constant!\n");
          } else {
            log_warning("Initial cycle Q signal is complicated:\n");
            my_log_sigspec(from_Q);
            // I have observed a case where from_Q was a complex subset of a wire's bits.
            for (auto chunk : from_Q.chunks()) {
              if (chunk.is_wire()) {
                chunk.wire->port_input = true;
              }
            }
          }

          if (initialPort) {
            initialPort->port_input = true;
            log_debug("First cycle input port %s\n", initialPort->name.c_str());
          }
        }

        if (cycle > 1) {
          // Connect the previous cycle's to_D (driver) signal to the current
          // cycle's from_Q (load) signal.
          // Remember: the previously-created cycle is the previous cycle in time!
          // The cycles are numbered forwards in time.
          join_sigs(destmod, prev_cycle_to_D, from_Q);
        }

        // The from_Q signals of the final cycle (num_cycles+1) may be
        // turned into ports by the caller, but only for signals representing
        // ASVs.  Non-ASV from_Q signals (and their fanout) are generally
        // useless, and will get optimized away.

      }
    }

    destmod->fixup_ports();

    auto_name_map.clear();
}




