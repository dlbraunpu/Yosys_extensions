#ifndef YOSYS_EXTENSIONS_UTIL_H
#define YOSYS_EXTENSIONS_UTIL_H

#include "kernel/yosys.h"


void my_log_sigspec(const Yosys::RTLIL::SigSpec& sig);
void my_log_sigbit(const Yosys::RTLIL::SigBit& bit);
void my_log_wire(const Yosys::RTLIL::Wire *wire);

void my_log_debug_sigspec(const Yosys::RTLIL::SigSpec& sig);
void my_log_debug_sigbit(const Yosys::RTLIL::SigBit& bit);
void my_log_debug_wire(const Yosys::RTLIL::Wire *wire);

// Doug: add "___#<cycle>" to the name
Yosys::RTLIL::IdString cycleize_name(const std::string& name, int cycle);
Yosys::RTLIL::IdString cycleize_name(Yosys::RTLIL::IdString object_name, int cycle);

// Remove any leading "\" and any trailing "___#<cycle>".
std::string decycleize_name(Yosys::RTLIL::IdString object_name);

std::string internalToV(Yosys::RTLIL::IdString internal_id);
Yosys::RTLIL::IdString verilogToInternal(const std::string& name);

// Truncate or zero-extend the SigSpec as necessary to make it the given width.
// An all-x value will be x-extended.
void
adjustSigSpecWidth(Yosys::RTLIL::SigSpec& ss, int newWidth);

// Used for attributes set in uf_generator.cc and read in write_llvm.cc
constexpr const char *TARGET_ATTR = "\\func_extract_target";
constexpr const char *TARGET_VECTOR_ATTR = "\\func_extract_target_vector";
constexpr const char *TARGET_VECTOR_IDX_ATTR = "\\func_extract_target_vector_idx";

#endif
