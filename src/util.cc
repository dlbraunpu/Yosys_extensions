
#include "func_extract/src/helper.h"

// Yosys headers
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "backends/rtlil/rtlil_backend.h"


#include "util.h"

USING_YOSYS_NAMESPACE

void my_log_sigspec(const RTLIL::SigSpec& sig)
{
  std::stringstream buf;
  RTLIL_BACKEND::dump_sigspec(buf, sig, false);
  log("sigspec: %s\n", buf.str().c_str());
}

void my_log_debug_sigspec(const RTLIL::SigSpec& sig)
{
  if (ys_debug()) my_log_sigspec(sig);
}



void my_log_sigbit(const RTLIL::SigBit& bit)
{
  if (bit.is_wire()) {
    log("sigbit type wire %s offset %d\n", bit.wire->name.c_str(), bit.offset);
  } else {
    log("sigbit type constant %d\n", bit.data);
  }
}

void my_log_debug_sigbit(const RTLIL::SigBit& bit)
{
  if (ys_debug()) my_log_sigbit(bit);
}


void my_log_wire(const RTLIL::Wire *wire)
{
  log("wire %s  width %d  start_offset %d  port_id %d  input %d  output %d\n", wire->name.c_str(),
      wire->width, wire->start_offset, wire->port_id, wire->port_input, wire->port_output);

}

void my_log_debug_wire(const RTLIL::Wire *wire)
{
  if (ys_debug()) my_log_wire(wire);
}


// Doug: add a trailing "__#<cycle>_" to the name - the format used by the
// orignal func_extract code.  Since we are starting with a legal Yosys
// internal name, there is no need to worry about the leading character.
IdString cycleize_name(IdString object_name, int cycle)
{
  return IdString(funcExtract::timed_name(object_name.c_str(), cycle));
}

// Doug: add a leading "\" and a
// trailing "__#<cycle>_" to the name.
IdString cycleize_name(const std::string& name, int cycle)
{
  // If the user name already has a backslash (e.g. "\reg[4]" or "\modx.reg"),
  // don't add a second backslash (Yosys would just remove it).
  std::string slashedName = (name[0] == '\\') ? name : std::string("\\")+name;
  return IdString(funcExtract::timed_name(slashedName, cycle));
}


// Doug: translate the idScring to verilog, then remove any trailing "__#<cycle>_".
// The goal to to take a cycleized Yosys name and recover the original Verilog
// name.
std::string decycleize_name(IdString object_name)
{
  std::string v_name = internalToV(object_name);
  //std::pair<std::string, std::pair<uint32_t, std::string>>
  auto pair = funcExtract::parse_name_idx(v_name);
  return pair.first;
}



// Truncate or zero-extend the SigSpec as necessary to make it the given width.
// An all-x value will be x-extended.
void
adjustSigSpecWidth(RTLIL::SigSpec& ss, int newWidth)
{
  int oldWidth = ss.size();
  if (oldWidth > newWidth) {
    ss.remove(newWidth, oldWidth - newWidth);
  } else if (oldWidth < newWidth) {
    RTLIL::State padding = ss.is_fully_undef() ? RTLIL::State::Sx : RTLIL::State::S0;
    while (ss.size() < newWidth)
      ss.append(padding);
  }
}


// Pretty much cut-and-pasted from the Yosys write_verilog code.
// Map an internal name to the equivalent Verilog name it was presumably
// made from.  Remove a leading backslash, unless it is needed to make
// the name a legal Verilog identifier.  We cheat a little, considering
// a "___#nn_" substring (used in unrolled names) to be legal.
//
std::string internalToV(IdString internal_id)
{
  const char *str = internal_id.c_str();

  if (*str == '$') {
    // Auto-generated names are returned unchanged.
    return std::string(str);
  }

  bool do_escape = false;

  if (*str == '\\')
    str++;

  // We don't care if there is a '#' in a properly unrolled name, but we do need
  // to escape any '#' in a different context.
  // TODO: Ideally we would use functions in funcExtract to parse the
  // unrolled name, convert the base portion, and re-unroll the result.
  
  static const std::regex unrolled_re("[^\\s#]___#\\d+_");
  bool is_unrolled = std::regex_match(str, unrolled_re);

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
    if (str[i] == '#' && is_unrolled)
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


IdString verilogToInternal(const std::string& name)
{
  // If the user name already has a backslash (e.g. "\reg[4]" or "\modx.reg"),
  // don't add a second backslash (Yosys would just remove it).
  return RTLIL::escape_id(name);
}
