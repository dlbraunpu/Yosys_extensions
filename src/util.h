#ifndef UTIL_H
#define UTIL_H

#include "kernel/yosys.h"


void my_log_sigspec(const Yosys::RTLIL::SigSpec& sig);
void my_log_sigbit(const Yosys::RTLIL::SigBit& bit);
void my_log_wire(const Yosys::RTLIL::Wire *wire);

void my_log_debug_sigspec(const Yosys::RTLIL::SigSpec& sig);
void my_log_debug_sigbit(const Yosys::RTLIL::SigBit& bit);
void my_log_debug_wire(const Yosys::RTLIL::Wire *wire);

// Doug: add "_#<cycle>" to the name
Yosys::RTLIL::IdString cycleize_name(const std::string& name, int cycle);
Yosys::RTLIL::IdString cycleize_name(Yosys::RTLIL::IdString object_name, int cycle);

std::string internalToV(Yosys::RTLIL::IdString internal_id);

// Truncate or zero-extend the SigSpec as necessary to make it the given width.
// An all-x value will be x-extended.
void
adjustSigSpecWidth(Yosys::RTLIL::SigSpec& ss, int newWidth);


#endif
