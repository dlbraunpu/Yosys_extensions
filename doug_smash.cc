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
      log("  renaming `%s' to `%s_%0*d_'.\n", it->first.c_str(), auto_prefix.c_str(), auto_name_digits, auto_name_offset + it->second);
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





void dump_const(std::ostream &f, const RTLIL::Const &data, int width = -1, int offset = 0, bool no_decimal = false, bool escape_comment = false)
{
  bool nostr = false;
  bool decimal = false;
  bool nohex = false;
  bool nodec = false;

  bool set_signed = (data.flags & RTLIL::CONST_FLAG_SIGNED) != 0;
  if (width < 0)
    width = data.bits.size() - offset;
  if (width == 0) {
    // See IEEE 1364-2005 Clause 5.1.14.
    f << "{0{1'b0}}";
    return;
  }
  if (nostr)
    goto dump_hex;
  if ((data.flags & RTLIL::CONST_FLAG_STRING) == 0 || width != (int)data.bits.size()) {
    if (width == 32 && !no_decimal && !nodec) {
      int32_t val = 0;
      for (int i = offset+width-1; i >= offset; i--) {
        log_assert(i < (int)data.bits.size());
        if (data.bits[i] != State::S0 && data.bits[i] != State::S1)
          goto dump_hex;
        if (data.bits[i] == State::S1)
          val |= 1 << (i - offset);
      }
      if (decimal)
        f << stringf("%d", val);
      else if (set_signed && val < 0)
        f << stringf("-32'sd%u", -val);
      else
        f << stringf("32'%sd%u", set_signed ? "s" : "", val);
    } else {
  dump_hex:
      if (nohex)
        goto dump_bin;
      vector<char> bin_digits, hex_digits;
      for (int i = offset; i < offset+width; i++) {
        log_assert(i < (int)data.bits.size());
        switch (data.bits[i]) {
        case State::S0: bin_digits.push_back('0'); break;
        case State::S1: bin_digits.push_back('1'); break;
        case RTLIL::Sx: bin_digits.push_back('x'); break;
        case RTLIL::Sz: bin_digits.push_back('z'); break;
        case RTLIL::Sa: bin_digits.push_back('?'); break;
        case RTLIL::Sm: log_error("Found marker state in final netlist.");
        }
      }
      if (GetSize(bin_digits) == 0)
        goto dump_bin;
      while (GetSize(bin_digits) % 4 != 0)
        if (bin_digits.back() == '1')
          bin_digits.push_back('0');
        else
          bin_digits.push_back(bin_digits.back());
      for (int i = 0; i < GetSize(bin_digits); i += 4)
      {
        char bit_3 = bin_digits[i+3];
        char bit_2 = bin_digits[i+2];
        char bit_1 = bin_digits[i+1];
        char bit_0 = bin_digits[i+0];
        if (bit_3 == 'x' || bit_2 == 'x' || bit_1 == 'x' || bit_0 == 'x') {
          if (bit_3 != 'x' || bit_2 != 'x' || bit_1 != 'x' || bit_0 != 'x')
            goto dump_bin;
          hex_digits.push_back('x');
          continue;
        }
        if (bit_3 == 'z' || bit_2 == 'z' || bit_1 == 'z' || bit_0 == 'z') {
          if (bit_3 != 'z' || bit_2 != 'z' || bit_1 != 'z' || bit_0 != 'z')
            goto dump_bin;
          hex_digits.push_back('z');
          continue;
        }
        if (bit_3 == '?' || bit_2 == '?' || bit_1 == '?' || bit_0 == '?') {
          if (bit_3 != '?' || bit_2 != '?' || bit_1 != '?' || bit_0 != '?')
            goto dump_bin;
          hex_digits.push_back('?');
          continue;
        }
        int val = 8*(bit_3 - '0') + 4*(bit_2 - '0') + 2*(bit_1 - '0') + (bit_0 - '0');
        hex_digits.push_back(val < 10 ? '0' + val : 'a' + val - 10);
      }
      f << stringf("%d'%sh", width, set_signed ? "s" : "");
      for (int i = GetSize(hex_digits)-1; i >= 0; i--)
        f << hex_digits[i];
    }
    if (0) {
  dump_bin:
      f << stringf("%d'%sb", width, set_signed ? "s" : "");
      if (width == 0)
        f << stringf("0");
      for (int i = offset+width-1; i >= offset; i--) {
        log_assert(i < (int)data.bits.size());
        switch (data.bits[i]) {
        case State::S0: f << stringf("0"); break;
        case State::S1: f << stringf("1"); break;
        case RTLIL::Sx: f << stringf("x"); break;
        case RTLIL::Sz: f << stringf("z"); break;
        case RTLIL::Sa: f << stringf("?"); break;
        case RTLIL::Sm: log_error("Found marker state in final netlist.");
        }
      }
    }
  } else {
    if ((data.flags & RTLIL::CONST_FLAG_REAL) == 0)
      f << stringf("\"");
    std::string str = data.decode_string();
    for (size_t i = 0; i < str.size(); i++) {
      if (str[i] == '\n')
        f << stringf("\\n");
      else if (str[i] == '\t')
        f << stringf("\\t");
      else if (str[i] < 32)
        f << stringf("\\%03o", str[i]);
      else if (str[i] == '"')
        f << stringf("\\\"");
      else if (str[i] == '\\')
        f << stringf("\\\\");
      else if (str[i] == '/' && escape_comment && i > 0 && str[i-1] == '*')
        f << stringf("\\/");
      else
        f << str[i];
    }
    if ((data.flags & RTLIL::CONST_FLAG_REAL) == 0)
      f << stringf("\"");
  }
}


void dump_sigchunk(std::ostream &f, const RTLIL::SigChunk &chunk, bool no_decimal = false)
{
  if (chunk.wire == NULL) {
    dump_const(f, chunk.data, chunk.width, chunk.offset, no_decimal);
  } else {
    if (chunk.width == chunk.wire->width && chunk.offset == 0) {
      f << stringf("%s", id(chunk.wire->name).c_str());
    } else if (chunk.width == 1) {
      if (chunk.wire->upto)
        f << stringf("%s[%d]", id(chunk.wire->name).c_str(), (chunk.wire->width - chunk.offset - 1) + chunk.wire->start_offset);
      else
        f << stringf("%s[%d]", id(chunk.wire->name).c_str(), chunk.offset + chunk.wire->start_offset);
    } else {
      if (chunk.wire->upto)
        f << stringf("%s[%d:%d]", id(chunk.wire->name).c_str(),
            (chunk.wire->width - (chunk.offset + chunk.width - 1) - 1) + chunk.wire->start_offset,
            (chunk.wire->width - chunk.offset - 1) + chunk.wire->start_offset);
      else
        f << stringf("%s[%d:%d]", id(chunk.wire->name).c_str(),
            (chunk.offset + chunk.width - 1) + chunk.wire->start_offset,
            chunk.offset + chunk.wire->start_offset);
    }
  }
}

void dump_sigspec(std::ostream &f, const RTLIL::SigSpec &sig)
{
  if (GetSize(sig) == 0) {
    // See IEEE 1364-2005 Clause 5.1.14.
    f << "{0{1'b0}}";
    return;
  }
  if (sig.is_chunk()) {
    dump_sigchunk(f, sig.as_chunk());
  } else {
    f << stringf("{ ");
    for (auto it = sig.chunks().rbegin(); it != sig.chunks().rend(); ++it) {
      if (it != sig.chunks().rbegin())
        f << stringf(", ");
      dump_sigchunk(f, *it, true);
    }
    f << stringf(" }");
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
  log("Smashed wires and processes for cycle %d\n", cycle);

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
    // name to the new cell
    if (RTLIL::builtin_ff_cell_types().count(src_cell->type) > 0) {
      log("Smashing ff cell %s for cycle %d\n", src_cell->name.c_str(), cycle);

      // Generate the official register name, usually from the Q signal name
      std::string reg_name = cellname(src_cell);
      FfData ff(nullptr, src_cell);
      is_reg_wire(ff.sig_q, reg_name);

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


void wire_up_srst(std::ostream &f, RTLIL::Module* mod, FfData& ff,
                  RTLIL::SigSpec& d_src, RTLIL::SigSpec& q_dest)
{
  f << "Wire up srst\n";
  // To model the reset, add an inverter and an AND gate between D and Q
  // Negative resets don't need the inverter.
  RTLIL::Cell *and_gate = mod->addCell(mod->uniquify("$srst_and"), ID($and));
  f << "Adding srst AND " << and_gate->name.str();
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
    f << "Adding srst inverter " << inv->name.str();
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
  d_src = w_d;
  q_dest = ff.sig_q;
}


void wire_up_ce(std::ostream &f, RTLIL::Module* mod, FfData& ff,
                  RTLIL::SigSpec& d_src, RTLIL::SigSpec& q_dest)
{
  f << "Wire up ce\n";
  // To model the enable, add a mux between D and Q
  // Keep in mind the ce signal polarity
  RTLIL::Cell *mux = mod->addCell(mod->uniquify("$ce_mux"), ID($mux));
  f << "Adding srst mux " << mux->name.str();
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
  d_src = w_d;
  q_dest = ff.sig_q;
}


// Replace the given FF cell:
// The wire driving the Q pin becomes an input port.
// The wire driven by the Q pin becomes an output port.
// An enable pin is converted into a mux that feeds the input port directly to the output port, and
// a sync reset becomes an AND gate on the output port

bool split_ff(std::ostream &f, RTLIL::Cell *cell,
               RTLIL::SigSpec& d_src, RTLIL::SigSpec& q_dest)
{
  RTLIL::Module *mod = cell->module;


  if (RTLIL::builtin_ff_cell_types().count(cell->type) == 0) {
    return false;  // Not a ff
  }

  FfData ff(nullptr, cell);


  std::string reg_name = cellname(cell);

  f << stringf("\nSplitting FF cell '%s'.  Width %d\n", cell->name.c_str(), ff.width);

  // $ff / $_FF_ cell: not supported.
  if (ff.has_gclk) {
    log_error("FF cell `%s' has a gclk, not supported\n", reg_name.c_str());
    return false;
  }

  // clockless FFs not supported
  if (!ff.has_clk) {
    log_error("FF cell `%s' has no clock, not supported\n", reg_name.c_str());
    return false;
  }

  // S/R FFs not supported
  if (ff.has_sr) {
    log_error("S/R FF cell `%s' not supported\n", reg_name.c_str());
    return false;
  }

  // Async reset not supported
  if (ff.has_arst) {
    log_error("FF cell `%s' has async reset, not supported\n", reg_name.c_str());
    return false;
  }

  // Async load not supported
  if (ff.has_aload) {
    log_error("FF cell `%s' has async load, not supported\n", reg_name.c_str());
    return false;
  }


  std::string old_reg_name = reg_name;
  bool out_is_reg_wire = is_reg_wire(ff.sig_q, reg_name);
  f << stringf("Old reg name '%s' translated to '%s'   is_reg_wire: %d\n",
                old_reg_name.c_str(), reg_name.c_str(), out_is_reg_wire);

  f << "D signal: ";
  dump_sigspec(f, ff.sig_d);
  f << "\n";

  f << "Q signal: ";
  dump_sigspec(f, ff.sig_q);
  f << "\n";

  f << "Clock signal: ";
  dump_sigspec(f, ff.sig_clk);
  f << "\n";

  if (ff.has_srst) {
    f << "SRST signal: ";
    dump_sigspec(f, ff.sig_srst);
    f << "\n";
  }

  if (ff.has_ce) {
    f << "CE signal: ";
    dump_sigspec(f, ff.sig_ce);
    f << "\n";
  }



  if (ff.has_srst && ff.has_ce) {
    if (ff.ce_over_srst) {
    f << "TODO: ce_over_srst\n";
#if 0
    f << stringf("if (%s", ff.pol_ce ? "" : "!");
    dump_sigspec(f, ff.sig_ce);
    f << stringf(")\n");
    f << stringf("%s" "    if (%s", indent.c_str(), ff.pol_srst ? "" : "!");
    dump_sigspec(f, ff.sig_srst);
    f << stringf(") %s <= ", reg_name.c_str());
    dump_sigspec(f, ff.val_srst);
    f << stringf(";\n");
    f << stringf("%s" "    else ", indent.c_str());
#endif
    } else {
      f << "TODO: not ce_over_srst\n";
    }
    // TMP
    f << "TODO: Process srst+ce properly\n";
    wire_up_ce(f, mod, ff, d_src, q_dest);
    //d_src = ff.sig_d;
    //q_dest = ff.sig_q;
  } else if (ff.has_srst) {
    wire_up_srst(f, mod, ff, d_src, q_dest);
  } else if (ff.has_ce) {
    f << "Process ce\n";
    wire_up_ce(f, mod, ff, d_src, q_dest);
    d_src = ff.sig_d;
    q_dest = ff.sig_q;
  } else {
    // A plain D -> Q connection; no added gates
    // Return (copies of) these to the caller.
    f << "Process simple ff\n";
    d_src = ff.sig_d;
    q_dest = ff.sig_q;
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



    log("Smashing module `%s' into `%s' for num_cycles %d.\n", id2cstr(srcmodname), id2cstr(destmodname), num_cycles);

    SigMap sigmap(destmod);


    SigSpecDict d_srcs0;
    SigSpecDict q_dests0;

    SigSpecDict d_srcs1;
    SigSpecDict q_dests1;

    // We unroll backwards in time.  The data flow is from cycle <num_cycles> to cycle 1.
    for (int cycle = 1; cycle <= num_cycles; ++cycle) {

      RegDict cur_cycle_regs;

      smash_module(design, destmod, srcmod, sigmap, cycle, cur_cycle_regs);

      SigSpecDict& prev_cycle_d_srcs = (cycle&0x01) ? d_srcs0 : d_srcs1;

      SigSpecDict& cur_cycle_d_srcs = (cycle&0x01) ? d_srcs1 : d_srcs0;
      SigSpecDict& cur_cycle_q_dests = (cycle&0x01) ? q_dests1 : q_dests0;

      cur_cycle_d_srcs.clear();
      cur_cycle_q_dests.clear();


      for (auto pair : cur_cycle_regs) {
        RTLIL::SigSpec d_src;
        RTLIL::SigSpec q_dest;

        RTLIL::Cell *orig_reg = pair.first;
        RTLIL::Cell *cycle_reg = pair.second;

        split_ff(std::cout, cycle_reg, d_src, q_dest);

        cur_cycle_d_srcs[orig_reg] = d_src;
        cur_cycle_q_dests[orig_reg] = q_dest;

        RTLIL::SigSpec& prev_cycle_d_src = prev_cycle_d_srcs[orig_reg];


        if (cycle > 1) {
          // Connect the current cycle's Q pin to the previous cycle's D pin
          join_sigs(destmod, q_dest, prev_cycle_d_src);
        }

        if (cycle == 1) {
          // Make ports of the first cycle's Q pin
        } else if (cycle == num_cycles) {
          // Make ports of the last cycle's D pin
        }
      }

    }



    auto_name_map.clear();
  }
} DougSmashCmd;

PRIVATE_NAMESPACE_END
