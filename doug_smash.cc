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
int cycle;


int auto_name_counter, auto_name_offset, auto_name_digits, extmem_counter;
std::map<RTLIL::IdString, int> auto_name_map;
std::set<RTLIL::IdString> reg_wires;
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
      log("  renaming `%s' to `%s_%0*d_'.\n", it->first.c_str(), auto_prefix.c_str(), auto_name_digits, auto_name_offset + it->second);
}

std::string next_auto_id()
{
  return stringf("%s_%0*d_", auto_prefix.c_str(), auto_name_digits, auto_name_offset + auto_name_counter++);
}

std::string id(RTLIL::IdString internal_id, bool may_rename = true)
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

bool is_reg_wire(RTLIL::SigSpec sig, std::string &reg_name)
{
  if (!sig.is_chunk() || sig.as_chunk().wire == NULL)
    return false;

  RTLIL::SigChunk chunk = sig.as_chunk();

  if (reg_wires.count(chunk.wire->name) == 0)
    return false;

  reg_name = id(chunk.wire->name);
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

    return id(cell_name);
  }
  else
  {
no_special_reg_name:
    return id(cell->name).c_str();
  }
}





bool rename_cells(RTLIL::Module *module, int cycle)
{
  for (auto c : module->cells()) {
    std::string newname = c->name.str() + "_#" + std::to_string(cycle);
    module->rename(c, newname);
  }
  return true;
}


bool rename_wires(RTLIL::Module *module, int cycle)
{
  for (auto w : module->wires()) {
    std::string newname = w->name.str() + "_#" + std::to_string(cycle);
    module->rename(w, newname);
  }
  module->fixup_ports();

  return true;
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
  return module->uniquify(cycleize_name(object->name, cycle));
}


// Doug: Is this even needed?
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

void map_sigspec(const dict<RTLIL::Wire*, RTLIL::Wire*> &map, RTLIL::SigSpec &sig, RTLIL::Module *into = nullptr)
{
  vector<SigChunk> chunks = sig;
  for (auto &chunk : chunks)
    if (chunk.wire != nullptr && chunk.wire->module != into)
      chunk.wire = map.at(chunk.wire);
  sig = chunks;
}


void smash_module(RTLIL::Design *design, RTLIL::Module *dest, 
                  RTLIL::Module *src, SigMap &sigmap, int cycle)
{
  // Copy the contents of the module src into module dest.  

  dict<IdString, IdString> memory_map;
  for (auto &src_memory_it : src->memories) {
    RTLIL::Memory *new_memory = dest->addMemory(map_name(dest, src_memory_it.second, cycle), src_memory_it.second);
    map_attributes(new_memory, src_memory_it.second->name);
    memory_map[src_memory_it.first] = new_memory->name;
    design->select(dest, new_memory);
  }

  dict<RTLIL::Wire*, RTLIL::Wire*> wire_map;
  dict<IdString, IdString> positional_ports;
  for (auto src_wire : src->wires()) {
    if (src_wire->port_id > 0)
      positional_ports.emplace(stringf("$%d", src_wire->port_id), src_wire->name);

    RTLIL::Wire *new_wire = nullptr;
    if (src_wire->name[0] == '\\') {
      RTLIL::Wire *hier_wire = dest->wire(cycleize_name(src_wire->name, cycle));
      if (hier_wire != nullptr && hier_wire->get_bool_attribute(ID::hierconn)) {
        hier_wire->attributes.erase(ID::hierconn);
        if (GetSize(hier_wire) < GetSize(src_wire)) {
          log_warning("Widening signal %s.%s to match size of %s.%s (cycle %d).\n",
            log_id(dest), log_id(hier_wire), log_id(src), log_id(src_wire), cycle);
          hier_wire->width = GetSize(src_wire);
        }
        new_wire = hier_wire;
      }
    }
    if (new_wire == nullptr) {
      new_wire = dest->addWire(map_name(dest, src_wire, cycle), src_wire);
      new_wire->port_input = new_wire->port_output = false;
      new_wire->port_id = false;
    }

    map_attributes(new_wire, src_wire->name);
    wire_map[src_wire] = new_wire;
    design->select(dest, new_wire);
  }

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
  }

  for (auto &src_conn_it : src->connections()) {
    RTLIL::SigSig new_conn = src_conn_it;
    map_sigspec(wire_map, new_conn.first);
    map_sigspec(wire_map, new_conn.second);
    dest->connect(new_conn);
  }

}


struct DougSmashCmd : public Pass {

  DougSmashCmd() : Pass("doug_smash", "Smash one module into another, with objhect renaming") { }

  void help() override
  {
    //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
    log("\n");
    log("    doug_smash <destmod> <srcmod> <cycle number> [options]\n");
    log("\n");
    log("Do whatever Doug is working on\n");
    log("\n");
  }

  void execute(std::vector<std::string> args, RTLIL::Design *design) override
  {
    log_header(design, "Executing Doug's stuff.\n");



    verbose = false;
    cycle = 1;
    noattr = false;
    auto_prefix = "";


    auto_name_map.clear();
    reg_wires.clear();


    if (args.size() < 4) {
      log_error("Not enough arguments!");
      return;
    }

    RTLIL::IdString destmodname = RTLIL::escape_id(args[1]);
    RTLIL::Module *destmod = design->module(destmodname);
    if (!destmod) {
      log_cmd_error("No such destination module: %s\n", id2cstr(destmodname));
    }

    RTLIL::IdString srcmodname = RTLIL::escape_id(args[2]);
    RTLIL::Module *srcmod = design->module(srcmodname);
    if (!srcmod) {
      log_cmd_error("No such source module: %s\n", id2cstr(srcmodname));
    }

    if (srcmod == destmod) {
      log_cmd_error("Same module specified for both source and destination!\n");
    }

    cycle = atoi(args[3].c_str());
    if (cycle < 0) {
      log_cmd_error("Bad cycle value %d\n", cycle);
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



    log("Smashing module `%s' into `%s' for cycle %d.\n", id2cstr(srcmodname), id2cstr(destmodname), cycle);

    SigMap sigmap(destmod);

    smash_module(design, destmod, srcmod, sigmap, cycle);


    auto_name_map.clear();
    reg_wires.clear();
  }
} DougSmashCmd;

PRIVATE_NAMESPACE_END
