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

bool verbose, noattr;

// Doug

// Map registers in original module to copies smashed dest module, for a particular cycle
typedef dict<RTLIL::Cell*, RTLIL::Cell*> RegDict;

// Map registers in original module to D or Q pin SigSpecs in smashed dest module, for a particular cycle.
// The dict holds a copy of the SigSpec, which will still be valid after the register is the dest module is deleted.
typedef dict<RTLIL::Cell*, RTLIL::SigSpec> SigSpecDict;


int auto_name_counter, auto_name_offset, auto_name_digits;
std::map<RTLIL::IdString, int> auto_name_map;
std::string auto_prefix, extmem_prefix;

RTLIL::Module *active_module;
dict<RTLIL::SigBit, RTLIL::State> active_initdata;
SigMap active_sigmap;
IdString initial_id;

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




// Doug: add "_#<cycle>" to the name
IdString cycleize_name(IdString object_name, int cycle)
{
  return stringf("%s_#%d", object_name.c_str(), cycle);
}


// Doug: add "_#<cycle>" to the object's name, and ensure that it is unique.
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

// Doug: This is vital, since we are effectively renaming wires: all the sigspecs on cell ports and connections
// must be fixed up.
void map_sigspec(const dict<RTLIL::Wire*, RTLIL::Wire*> &map, RTLIL::SigSpec &sig, RTLIL::Module *into = nullptr)
{
  vector<SigChunk> chunks = sig;
  for (auto &chunk : chunks)
    if (chunk.wire != nullptr && chunk.wire->module != into)
      chunk.wire = map.at(chunk.wire);
  sig = chunks;
}


void smash_module(RTLIL::Design *design, RTLIL::Module *dest, 
                  RTLIL::Module *src, SigMap &sigmap, int cycle,
                  RegDict& registers)
{
  // Copy the contents of the module src into module dest.  
  log("Smashing for cycle %d\n", cycle);

  dict<IdString, IdString> memory_map;
  for (auto &src_memory_it : src->memories) {
    RTLIL::Memory *new_memory = dest->addMemory(map_name(dest, src_memory_it.second, cycle), src_memory_it.second);
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
    RTLIL::Process *new_proc = dest->addProcess(map_name(dest, src_proc_it.second, cycle), src_proc_it.second);
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

  dest->fixup_ports();  // Give the new ports proper port IDs.  (Could be done once, after all cycles are smashed?)

  for (auto &src_conn_it : src->connections()) {
    RTLIL::SigSig new_conn = src_conn_it;
    map_sigspec(wire_map, new_conn.first);
    map_sigspec(wire_map, new_conn.second);
    dest->connect(new_conn);
  }

}


void wire_up_srst(RTLIL::Module* mod, FfData& ff,
                  RTLIL::SigSpec& d_fanin, RTLIL::SigSpec& q_fanout)
{
  log_debug("Wire up srst\n");
  // To model the reset, add an inverter and an AND gate between D and Q
  // Negative resets don't need the inverter.
  RTLIL::Cell *and_gate = mod->addCell(mod->uniquify("$srst_and"), ID($and));
  log_debug("Adding srst AND %s", and_gate->name.c_str());
  and_gate->setParam(ID::A_WIDTH, ff.width);
  and_gate->setParam(ID::B_WIDTH, ff.width);
  and_gate->setParam(ID::Y_WIDTH, ff.width);
  and_gate->setParam(ID::A_SIGNED, 0);
  and_gate->setParam(ID::B_SIGNED, 0);

  // Connect the signal driving the D pin to the A input of the AND gate
  and_gate->setPort(ID::A, ff.sig_d);

  if (ff.pol_srst) {
    // Positive reset needs an inverter
    RTLIL::Cell *inv = mod->addCell(mod->uniquify("$srst_inv"), ID($not));
    log_debug("Adding srst inverter %s", inv->name.c_str());
    inv->setParam(ID::A_WIDTH, 1);
    inv->setParam(ID::Y_WIDTH, 1);
    inv->setParam(ID::A_SIGNED, 0);

    // Positive reset goes to inverter input
    inv->setPort(ID::A, ff.sig_srst);

    // Add a wire to connect the inverter and AND gate
    RTLIL::Wire *w_inv = mod->addWire(mod->uniquify("$srst_inv"), 1);

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

  RTLIL::Wire *w_d = mod->addWire(mod->uniquify("$gated_d"), ff.width);
  and_gate->setPort(ID::Y, w_d);

  // Return the modified D and Q connections to the caller.
  d_fanin = w_d;
  q_fanout = ff.sig_q;
}


void wire_up_ce(RTLIL::Module* mod, FfData& ff,
                  RTLIL::SigSpec& d_fanin, RTLIL::SigSpec& q_fanout)
{
  log_debug("Wire up ce\n");
  // To model the enable, add a mux between D and Q
  // Keep in mind the ce signal polarity
  RTLIL::Cell *mux = mod->addCell(mod->uniquify("$ce_mux"), ID($mux));
  log_debug("Adding srst mux %s", mux->name.c_str());
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

  RTLIL::Wire *w_d = mod->addWire(mod->uniquify("$muxed_d"), ff.width);
  mux->setPort(ID::Y, w_d);

  // Return the modified D and Q connections to the caller.
  d_fanin = w_d;
  q_fanout = ff.sig_q;
}


// Replace the given FF cell:
// The signal driving the D pin is returned in d_fanin.
// The signal driven by the Q pin is returned in q_fanout
// An enable pin is converted into a mux that feeds q_fanout directly from d_fanin, and
// a sync reset becomes an AND gate feeding q_fanout.

bool split_ff(RTLIL::Cell *cell,
               RTLIL::SigSpec& d_fanin, RTLIL::SigSpec& q_fanout)
{
  RTLIL::Module *mod = cell->module;


  if (RTLIL::builtin_ff_cell_types().count(cell->type) == 0) {
    return false;  // Not a ff
  }

  FfData ff(nullptr, cell);


  std::string reg_name = cellname(cell);
  log_debug("\nSplitting FF cell '%s' known to some as '%s'.  Width %d\n", cell->name.c_str(), reg_name.c_str(), ff.width);

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
      wire_up_srst(mod, ff, d_fanin, q_fanout); // Fills in d_fanin and q_fanout
      RTLIL::SigSpec dummy_ss;
      // Yes, wire_up_ce() will insert the mux ahead of the AND gate added by wire_up_srst().
      wire_up_ce(mod, ff, dummy_ss, dummy_ss);
    } else {
      // This is less common...
      log_warning("TODO: process ce_over_srst\n");
    }
  } else if (ff.has_srst) {
    log_debug("Process srst\n");
    wire_up_srst(mod, ff, d_fanin, q_fanout); // Fills in d_fanin and q_fanout
  } else if (ff.has_ce) {
    log_debug("Process ce\n");
    wire_up_ce(mod, ff, d_fanin, q_fanout);
    d_fanin = ff.sig_d;
    q_fanout = ff.sig_q;
  } else {
    // A plain D -> Q connection; no added gates
    // Return (copies of) these to the caller.
    log_debug("Process simple ff\n");
    d_fanin = ff.sig_d;
    q_fanout = ff.sig_q;
  }


  // The FF of course goes away.
  mod->remove(cell);
  return true;
}


void join_sigs(RTLIL::Module *destmod, RTLIL::SigSpec& from_sig, RTLIL::SigSpec& to_sig)
{
  log_assert(!from_sig.empty());
  log_assert(!to_sig.empty());
  log_assert(from_sig.size() == to_sig.size());

  destmod->connect(from_sig, to_sig);

}



struct DougSmashCmd : public Pass {

  DougSmashCmd() : Pass("doug_smash", "Smash one module into another, with objhect renaming") { }

  void help() override
  {
    //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
    log("\n");
    log("    doug_smash <destmod> <srcmod> <cycle count> [options]\n");
    log("\n");
    log("Do whatever Doug is working on\n");
    log("\n");
  }

  void execute(std::vector<std::string> args, RTLIL::Design *design) override
  {
    log_header(design, "Executing Doug's stuff.\n");


    int num_cycles = 1;

    verbose = false;
    noattr = false;
    auto_prefix = "";


    auto_name_map.clear();


    if (args.size() < 4) {
      log_error("Not enough arguments!");
      return;
    }

    RTLIL::IdString destmodname = RTLIL::escape_id(args[1]);
    RTLIL::Module *destmod = design->module(destmodname);
    if (destmod) {
      log_cmd_error("Destination module %s already exists\n", id2cstr(destmodname));
    }

    RTLIL::IdString srcmodname = RTLIL::escape_id(args[2]);
    RTLIL::Module *srcmod = design->module(srcmodname);
    if (!srcmod) {
      log_cmd_error("No such source module: %s\n", id2cstr(srcmodname));
    }

    num_cycles = atoi(args[3].c_str());
    if (num_cycles < 1) {
      log_cmd_error("Bad num_cycles value %d\n", num_cycles);
    }

    size_t argidx;
    for (argidx = 4; argidx < args.size(); argidx++) {
      std::string arg = args[argidx];
      if (arg == "-noattr") {
        noattr = true;
        continue;
      }
      if (arg == "-v") {
        verbose = true;
        continue;
      }
      break;
    }
    extra_args(args, argidx, design);


#if 0
    log_push();
    Pass::call(design, "bmuxmap");
    Pass::call(design, "demuxmap");
    Pass::call(design, "clean_zerowidth");
    log_pop();
#endif

    design->sort();

    if (!srcmod->processes.empty()) {
      log_warning("Module %s contains unmapped RTLIL processes. RTLIL processes\n"
                  "can't always be mapped directly to Verilog always blocks. Unintended\n"
                  "changes in simulation behavior are possible! Use \"proc\" to convert\n"
                  "processes to logic networks and registers.\n", id2cstr(srcmodname));
    }


    // Create the new module
    destmod = design->addModule(RTLIL::escape_id(destmodname.str()));

    log("Smashing module `%s' into `%s' for num_cycles %d.\n", id2cstr(srcmodname), id2cstr(destmodname), num_cycles);


    // Copy the source module's attributes to it.
    for (auto &attr : srcmod->attributes) {
      destmod->attributes[attr.first] = attr.second;
    }

    SigMap sigmap(destmod);


    SigSpecDict d_fanins0;
    SigSpecDict q_fanouts0;

    SigSpecDict d_fanins1;
    SigSpecDict q_fanouts1;

    // We unroll backwards in time.  The data flow is from cycle <num_cycles> to cycle 1.
    for (int cycle = 1; cycle <= num_cycles; ++cycle) {

      RegDict cur_cycle_regs;

      smash_module(design, destmod, srcmod, sigmap, cycle, cur_cycle_regs);

      SigSpecDict& prev_cycle_q_fanouts = (cycle&0x01) ? q_fanouts0 : q_fanouts1;

      SigSpecDict& cur_cycle_d_fanins = (cycle&0x01) ? d_fanins1 : d_fanins0;
      SigSpecDict& cur_cycle_q_fanouts = (cycle&0x01) ? q_fanouts1 : q_fanouts0;

      cur_cycle_d_fanins.clear();
      cur_cycle_q_fanouts.clear();


      for (auto pair : cur_cycle_regs) {
        RTLIL::SigSpec d_fanin;
        RTLIL::SigSpec q_fanout;

        RTLIL::Cell *orig_reg = pair.first;
        RTLIL::Cell *cycle_reg = pair.second;

        split_ff(cycle_reg, d_fanin, q_fanout);

        cur_cycle_d_fanins[orig_reg] = d_fanin;
        cur_cycle_q_fanouts[orig_reg] = q_fanout;

        RTLIL::SigSpec& prev_cycle_q_fanout = prev_cycle_q_fanouts[orig_reg];


        if (cycle > 1) {
          // Connect the current cycle's d_fanin signal to the previously-created cycle's q_fanout signal.
          // Remember: the previously-created cycle is the next cycle in time!
          // The cycles are numbered backwards in time.
          join_sigs(destmod, d_fanin, prev_cycle_q_fanout);
        }

        // Make every cycle's d_fanin signal an output port
        // If the sigspec specifies more than one wire, things are tricky.
        // To fix that, we may need to add an extra wire.
        // TODO: the port needs to have a hdlname attribute or something similar to identify the 
        // original Verilog register.  The wire name is not helpful for this: it may barely resemble
        // the original register name.
        log("first cycle output port: ");
        my_log_sigspec(d_fanin);
        if (d_fanin.is_wire()) {
          d_fanin.as_wire()->port_output = true;
        } else {
          log_warning("output signal is not a single wire!\n");
        }

        if (cycle == num_cycles) {
          // Make the starting cycle's q_fanout signal an input port
          // If the register was originally driven by an input port, 
          // the signal will still be an input port for every cycle.
          // If the sigspec specifies more than one wire, things are tricky.
          // To fix that, we may need to add an extra wire.
          // TODO: the port needs to have a hdlname attribute or something similar to identify the 
          // original Verilog register.  The wire name is not helpful for this.
          log("final cycle input port: ");
          my_log_sigspec(q_fanout);
          if (q_fanout.is_wire()) {
            q_fanout.as_wire()->port_input = true;
          } else {
            log_warning("input signal is not a single wire!\n");
          }
        }
      }

    }

    destmod->fixup_ports();

    auto_name_map.clear();

    log_header(design, "Writing LLVM data...\n");
    std::string asvName = "$0\\FAC1[95:0]";  // TODO: need to map from original Verilog reg name to cycle #0 output name
    write_llvm_ir(destmod, "xxx"/*module name*/, asvName, "xxx.llvm" /*output file name*/);
  }
} DougSmashCmd;

PRIVATE_NAMESPACE_END
