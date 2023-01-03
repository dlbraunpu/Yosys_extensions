#ifndef UNROLL_H
#define UNROLL_H

#include "kernel/yosys.h"

void unroll_module(Yosys::RTLIL::Module *srcmod, Yosys::RTLIL::Module *destmod, int num_cycles);

#endif
