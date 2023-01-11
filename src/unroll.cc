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
#include "write_llvm.h"
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

// This maps registers in original module to copies in the smashed dest module,
// for a particular cycle
typedef dict<RTLIL::Cell*, RTLIL::Cell*> RegDict;

// This maps registers in original module to D or Q pin SigSpecs in smashed dest module, for
// a particular cycle. The dict holds a copy of the SigSpec, which will still be valid
// after the register in the dest module is deleted.
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


// This make a Verilog-friendly cleaned-up name that we don't really care about.
std::string cellname(RTLIL::Cell *cell)
{
  if (!false && cell->name[0] == '$' && RTLIL::builtin_ff_cell_types().count(cell->type) && cell->hasPort(ID::Q) && !cell->type.in(ID($ff), ID($_FF_)))
  {
    RTLIL::SigSpec sig = cell->getPort(ID::Q);
    if (GetSize(sig) != 1 || sig.is_fully_const())
      goto no_special_reg_name;

    RTLIL::Wire *wire = sig[0].wire;

    if (wire->name[0] != '\\')
      goto no_special_reg_name;

    std::string cell_name = wire->name.str();

    size_t pos = cell_name.find('[');
    if (pos != std::string::npos)
      cell_name = cell_name.substr(0, pos) + "_reg" + cell_name.substr(pos);
    else
      cell_name = cell_name + "_reg";

    if (wire->width != 1)
      cell_name += stringf("[%d]", wire->start_offset + sig[0].offset);

    if (active_module && active_module->count_id(cell_name) > 0)
        goto no_special_reg_name;

    return cleaned_id(cell_name);
  }
  else
  {
no_special_reg_name:
    return cleaned_id(cell->name).c_str();
  }
}



// Doug: add "_#<cycle>" to the object's name, and ensure that it is unique.
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


    // For FF cells, update the dict that maps the (cycle-independent) register
    // name to the new cell.  Later we will delete these cells.
    if (RTLIL::builtin_ff_cell_types().count(src_cell->type) > 0) {
      log_debug("Smashing ff cell %s for cycle %d\n", src_cell->name.c_str(), cycle);

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


// Add the logic needed to model a FF's SRST signal.
void wire_up_srst(RTLIL::Module* mod, FfData& ff,
                  RTLIL::SigSpec& to_D, RTLIL::SigSpec& from_Q)
{
  log_debug("Wire up srst\n");
  // To model the reset, add an inverter and an AND gate between D and Q
  // Negative resets don't need the inverter.
  RTLIL::Cell *and_gate = mod->addCell(mod->uniquify(ff.name.str()+"_srst_and"), ID($and));
  log_debug("Adding srst AND %s\n", and_gate->name.c_str());
  and_gate->setParam(ID::A_WIDTH, ff.width);
  and_gate->setParam(ID::B_WIDTH, ff.width);
  and_gate->setParam(ID::Y_WIDTH, ff.width);
  and_gate->setParam(ID::A_SIGNED, 0);
  and_gate->setParam(ID::B_SIGNED, 0);

  // Connect the signal driving the D pin to the A input of the AND gate
  and_gate->setPort(ID::A, ff.sig_d);

  if (ff.pol_srst) {
    // Positive reset needs an inverter
    RTLIL::Cell *inv = mod->addCell(mod->uniquify(ff.name.str()+"_srst_inv"), ID($not));
    log_debug("Adding srst inverter %s\n", inv->name.c_str());
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

    and_gate->setPort(ID::B, widened_w_inv);
    
  } else {
    // Negative reset goes directly to B input (duplicated if width > 1)

    RTLIL::SigBit sigbit(ff.sig_srst);
    std::vector<RTLIL::SigBit> sigbits(ff.width, sigbit);
    RTLIL::SigSpec widened_srst(sigbits);

    and_gate->setPort(ID::B, widened_srst);
  }

  // Lastly we need a stub wire from the AND gate output which
  // will send the signal to the next cycle

  RTLIL::Wire *w_d = mod->addWire(mod->uniquify(ff.name.str()+"_gated_d"), ff.width);
  and_gate->setPort(ID::Y, w_d);

  // Return the modified D and Q connections to the caller.
  to_D = w_d;
  from_Q = ff.sig_q;
}


// Add the logic needed to model a FF's CE signal.
void wire_up_ce(RTLIL::Module* mod, FfData& ff,
                  RTLIL::SigSpec& to_D, RTLIL::SigSpec& from_Q)
{
  log_debug("Wire up ce\n");
  // To model the enable, add a mux between D and Q
  // Keep in mind the ce signal polarity
  RTLIL::Cell *mux = mod->addCell(mod->uniquify(ff.name.str()+"_ce_mux"), ID($mux));
  log_debug("Adding srst mux %s\n", mux->name.c_str());
  mux->setParam(ID::WIDTH, ff.width);

  if (ff.pol_ce) {
    // Positive enable
    mux->setPort(ID::A, ff.sig_q);  // enable=0, previous stage signal is passed through
    mux->setPort(ID::B, ff.sig_d);  // enable=1, FF gets normal input
  } else {
    // Negative enable, opposite situation
    mux->setPort(ID::A, ff.sig_d);  
    mux->setPort(ID::B, ff.sig_q); 
  }

  mux->setPort(ID::S, ff.sig_ce);   // Mux select

  // Lastly we need a stub wire from the mux output which
  // will send the signal to the next cycle

  RTLIL::Wire *w_d = mod->addWire(mod->uniquify(ff.name.str()+"_muxed_d"), ff.width);
  mux->setPort(ID::Y, w_d);

  // Return the modified D and Q connections to the caller.
  to_D = w_d;
  from_Q = ff.sig_q;
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
    return false;  // Not a ff
  }

  FfData ff(nullptr, cell);


  std::string reg_name = cellname(cell);
  log_debug("\nSplitting FF cell '%s' known to some as '%s'.  Width %d\n",
            cell->name.c_str(), reg_name.c_str(), ff.width);

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
      wire_up_srst(mod, ff, to_D, from_Q); // Fills in to_D and from_Q
      RTLIL::SigSpec dummy_ss;
      // Yes, wire_up_ce() will insert the mux ahead of the AND gate added by wire_up_srst().
      wire_up_ce(mod, ff, dummy_ss, dummy_ss);
    } else {
      // This is less common...
      log_warning("TODO: process ce_over_srst\n");
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


void join_sigs(RTLIL::Module *destmod,
               const RTLIL::SigSpec& from_sig, const RTLIL::SigSpec& to_sig)
{
  log_assert(!from_sig.empty());
  log_assert(!to_sig.empty());
  log_assert(from_sig.size() == to_sig.size());

  destmod->connect(from_sig, to_sig);

}



void unroll_module(RTLIL::Module *srcmod, RTLIL::Module *destmod, int num_cycles)
{
    auto_prefix = "";
    auto_name_map.clear();

    // Copy the source module's attributes to it.
    for (auto &attr : srcmod->attributes) {
      destmod->attributes[attr.first] = attr.second;
    }

    SigSpecDict to_Ds0;
    SigSpecDict from_Qs0;

    SigSpecDict to_Ds1;
    SigSpecDict from_Qs1;

    // We unroll forwards in time, and (unlike the original
    // func_extract program) the cycles are numbered forwards in time.
    // The data flow is from cycle 1 to cycle <num_cycles+1>,
    // Ultimately the current ASV values will be fed into the
    // input ports associated with cycle 1, and the new ASV value
    // will be available at an output port associated with cycle <num_cycles+1>.
    for (int cycle = 1; cycle <= num_cycles+1; ++cycle) {

      RegDict cur_cycle_regs;

      smash_module(destmod, srcmod, cycle, cur_cycle_regs);

      // For efficiency we use pairs of SigSpecDicts, which alternate 
      // between the roles of 'current' and 'prev'.
      SigSpecDict& prev_cycle_to_Ds = (cycle&0x01) ? to_Ds0 : to_Ds1;

      SigSpecDict& cur_cycle_to_Ds = (cycle&0x01) ? to_Ds1 : to_Ds0;
      SigSpecDict& cur_cycle_from_Qs = (cycle&0x01) ? from_Qs1 : from_Qs0;

      cur_cycle_to_Ds.clear();
      cur_cycle_from_Qs.clear();

      for (auto pair : cur_cycle_regs) {
        RTLIL::SigSpec to_D;
        RTLIL::SigSpec from_Q;

        RTLIL::Cell *orig_reg = pair.first;
        RTLIL::Cell *cycle_reg = pair.second;

        // This sets to_D and from_Q
        split_ff(cycle_reg, to_D, from_Q);

        cur_cycle_to_Ds[orig_reg] = to_D;
        cur_cycle_from_Qs[orig_reg] = from_Q;

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
            log_warning("initial cycle Q signal is a slice of a wire!\n");
            my_log_sigspec(from_Q);
          } else {
            log_warning("initial cycle Q signal contains multiple wires!\n");
            my_log_sigspec(from_Q);
          }

          if (initialPort) {
            initialPort->port_input = true;
            log_debug("first cycle input port %s\n", initialPort->name.c_str());
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




