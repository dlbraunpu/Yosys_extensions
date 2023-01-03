#include "util.h"
  
// LLVM headers (many more than needed)

// Yosys headers
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "backends/rtlil/rtlil_backend.h"

USING_YOSYS_NAMESPACE

void my_log_sigspec(const RTLIL::SigSpec& sig)
{
  std::stringstream buf;
  RTLIL_BACKEND::dump_sigspec(buf, sig, false);
  log("sigspec: %s\n", buf.str().c_str());
}



void my_log_sigbit(const RTLIL::SigBit& bit)
{
  if (bit.is_wire()) {
    log("sigbit type wire %s offset %d\n", bit.wire->name.c_str(), bit.offset);
  } else {
    log("sigbit type constant %d\n", bit.data);
  }
}


void my_log_wire(const RTLIL::Wire *wire)
{
  log("wire %s  width %d  start_offset %d  port_id %d  input %d  output %d\n", wire->name.c_str(),
      wire->width, wire->start_offset, wire->port_id, wire->port_input, wire->port_output);

}


// Doug: add "_#<cycle>" to the name
IdString cycleize_name(IdString object_name, int cycle)
{
  return stringf("%s_#%d", object_name.c_str(), cycle);
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

