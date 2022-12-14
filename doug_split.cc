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

bool decimal = false;
bool nostr = false;
bool nodec = false;
bool nohex = false;


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


void dump_const(std::ostream &f, const RTLIL::Const &data, int width = -1, int offset = 0, bool no_decimal = false, bool escape_comment = false)
{
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

void dump_reg_init(std::ostream &f, SigSpec sig)
{
	Const initval;
	bool gotinit = false;

	for (auto bit : active_sigmap(sig)) {
		if (active_initdata.count(bit)) {
			initval.bits.push_back(active_initdata.at(bit));
			gotinit = true;
		} else {
			initval.bits.push_back(State::Sx);
		}
	}

	if (gotinit) {
		f << " = ";
		dump_const(f, initval);
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


// Replace a FF cell:
// The wire driving the Q pin becomes an input port.
// The wire driven by the Q pin becomes an output port.
// An enable pin is converted into a mux that feeds the input port directly to the output port, and
// a sync reset becomes an AND gate on the output port

bool split_ff(std::ostream &f, RTLIL::Cell *cell)
{

  std::string indent = "  ";

  if (RTLIL::builtin_ff_cell_types().count(cell->type) == 0) {
    return false;  // Not a ff
  }

  FfData ff(nullptr, cell);
  std::string reg_name = cellname(cell);

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


  bool out_is_reg_wire = is_reg_wire(ff.sig_q, reg_name);

  if (!out_is_reg_wire) {
    if (ff.width == 1)
      f << stringf("%s" "reg %s", indent.c_str(), reg_name.c_str());
    else
      f << stringf("%s" "reg [%d:0] %s", indent.c_str(), ff.width-1, reg_name.c_str());
    dump_reg_init(f, ff.sig_q);
    f << ";\n";
  }

  SigSpec sig_d = ff.sig_d;


  f << stringf("%s" "always%s @(%sedge ", indent.c_str(), false ? "_ff" : "", ff.pol_clk ? "pos" : "neg");
  dump_sigspec(f, ff.sig_clk);
  f << stringf(")\n");

  f << stringf("%s" "  ", indent.c_str());

  if (ff.has_srst && ff.has_ce && ff.ce_over_srst) {
    f << stringf("if (%s", ff.pol_ce ? "" : "!");
    dump_sigspec(f, ff.sig_ce);
    f << stringf(")\n");
    f << stringf("%s" "    if (%s", indent.c_str(), ff.pol_srst ? "" : "!");
    dump_sigspec(f, ff.sig_srst);
    f << stringf(") %s <= ", reg_name.c_str());
    dump_sigspec(f, ff.val_srst);
    f << stringf(";\n");
    f << stringf("%s" "    else ", indent.c_str());
  } else {
    if (ff.has_srst) {
      f << stringf("if (%s", ff.pol_srst ? "" : "!");
      dump_sigspec(f, ff.sig_srst);
      f << stringf(") %s <= ", reg_name.c_str());
      dump_sigspec(f, ff.val_srst);
      f << stringf(";\n");
      f << stringf("%s" "  else ", indent.c_str());
    }
    if (ff.has_ce) {
      f << stringf("if (%s", ff.pol_ce ? "" : "!");
      dump_sigspec(f, ff.sig_ce);
      f << stringf(") ");
    }
  }

  f << stringf("%s <= ", reg_name.c_str());
  dump_sigspec(f, sig_d);
  f << stringf(";\n");

  if (!out_is_reg_wire) {
    f << stringf("%s" "assign ", indent.c_str());
    dump_sigspec(f, ff.sig_q);
    f << stringf(" = %s;\n", reg_name.c_str());
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





struct DougSplitCmd : public Pass {

  DougSplitCmd() : Pass("doug_split", "split registers in preparation for unrolling") { }

  void help() override
  {
    //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
    log("\n");
    log("    doug_split <modname> [options]\n");
    log("\n");
    log("Split registers\n");
    log("\n");
  }

  void execute(std::vector<std::string> args, RTLIL::Design *design) override
  {
    log_header(design, "Executing doug_split.\n");



    verbose = false;
    cycle = 1;
    noattr = false;
    auto_prefix = "";


    auto_name_map.clear();
    reg_wires.clear();


    if (args.size() < 2) {
      log_error("Not enough arguments!");
      return;
    }

    RTLIL::IdString modname = RTLIL::escape_id(args[1]);
    RTLIL::Module *mod = design->module(modname);
    if (!mod) {
      log_cmd_error("No such module: %s\n", id2cstr(modname));
    }

    size_t argidx;
    for (argidx = 2; argidx < args.size(); argidx++) {
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

    if (!mod->processes.empty()) {
      log_warning("Module %s contains unmapped RTLIL processes. RTLIL processes\n"
                  "can't always be mapped directly to Verilog always blocks. Unintended\n"
                  "changes in simulation behavior are possible! Use \"proc\" to convert\n"
                  "processes to logic networks and registers.\n", id2cstr(modname));
    }



    for (auto cell : mod->cells()) {
      if (RTLIL::builtin_ff_cell_types().count(cell->type) > 0) {
        split_ff(std::cout, cell);
      }
    }
    

    auto_name_map.clear();
    reg_wires.clear();
  }
} DougSplitCmd;

PRIVATE_NAMESPACE_END
