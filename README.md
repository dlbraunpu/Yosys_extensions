# Yosys extensions

This is an implementation of func_extract (https://github.com/yuzeng2333/autoGenILA)
that is built on top of the Yosys internal data model, and run as a
Yosys extension command.  It reads
the same configuration files and generates the same output files as the
original func_extract.


## To build:

If necessary, edit `CMakeLists.txt` so that the `YOSYS_DIR` and `AUTO_GEN_ILA_DIR`
definitions point to an up-to-date copy of these packages.

Ensure that LLVM version 14 is available in a place where `cmake` can find it.

Do:

      mkdir build
      cd build
      cmake ..
      make

The result is a shared library: `build/libyosys_func_extract.so`.


## To run:

1. Read the original `func_extract` documentation to learn what the program does and how to prepare the input data it needs.

2. Ensure that the Verilog design and the various configuration
files (e.g. `instr.txt`) are available.  The Verilog files can be anywhere,
but typically the configuration files and output files will be located in the current directory.

3. Write a Yosys script that will load and optimize the Verilog design and invoke the `funct_extract` command, e.g.:

        read_verilog path/to/my_design.v

        prep -top my_design

        hierarchy -check
        proc
        memory -nordff
        proc
        flatten
        opt_clean

        func_extract [<options>]

Typically you can generate the required reset data file (`rst.vcd`) in the same script, just before the `func_extract` command, for example:

        sim -n 5 -clock clk -resetn resetn -rstlen 5 -vcd ./rst.vcd

4. Invoke Yosys, loading the shared library and running the script:

        yosys -m /path/to/libyosys_func_extract.so my_script.ys
        
As with the original `func_extract, the result will be collection of update functions in the form of textual LLVM IR files.  Several other text files will
be generated that are meant to be read by the companion `sim_gen` program, which generates C++ code that will ultimately be linked to the update functions to produce a simulation executable.
    
## Command-line options:

The func_extract command takes a number of command-line options, listed below.
A few options control
the optimization algorithms, but a majority are meant for debugging.

The command reads and writes the same configuration and data files as the
original standalone `func_extract` program. One difference is that the
command does not directly read any Verilog files. It assumes the design has already
been loaded, flattened, and optimized (typically with the Yosys `prep`
command). The module to be operated upon is specified in the `instr.txt` file.
    
    
        -save_unrolled
            Each unrolled copy of the design (typically there is one for each
            instruction) will be saved in RTLIL format before and after
            optimization is performed on it. This is very useful for debugging.
            The filenames will be of the form '<instr_name>_unrolled_<delay>.rtlil'
            and '<instr_name>_unrolled_opto_<delay>.rtlil'
    
        -no_optimize_unrolled
            Skip optimization of the unrolled designs. This may greatly
            increase the code generation runtime and the size of the
            generated code.
    
        -use_poison
            This will cause an LLVM 'poison' value to be used instead of 0 or 1
            for x (undefined) signal values. This may be helpful in determining
            if x values are not being optimized away and affecting the simulation
            results.
    
        -no_simplify_gates
            This will prevent the LLVM code generator from doing simple
            optimizations on logic gates. Possibly useful for debugging.
    
        -no_simplify_muxes
            This will prevent the LLVM code generator from doing simple
            optimizations on muxes. Possibly useful for debugging.
    
        -pre_opto_mux_to_branch
            Activate the mux-to-branch pass immediately after LLVM code generation.
            This will try to convert LLVM 'select' instructions (typically created.
            from Yosys mux cells) into conditional branches. This can be very
            effective on some designs.
    
        -post_opto_mux_to_branch
            Activate the mux-to-branch pass after final LLVM optimization. This
            is typically less effective than doing it pre-opto.
    
        -pre_opto_mux_to_branch_threshold <value>
            If pre-opto mux-to-branch conversion is active, an LLVM 'select' will
            not be converted unless one of the generated branches will have at
            least this number of LLVM instructions. The default value is 10.
    
        -post_opto_mux_to_branch_threshold <value>
            Same as above, except for post-opto conversion.
    
        -verbose_names
            Try to give LLVM instructions names that are based on the corresponding
            RTLIL signal names (instead of default numeric names). Helpful for
            debugging.
    
        -cell_based_names
            Try to give LLVM instructions names that are based on the corresponding
            RTLIL cell names (instead of default numeric names). Helpful for
            debugging, but typically less so than signal-based names.
    
        -no_rst
            Do not read the reset value data from the file 'rst.vcd'. Instead
            zero will be used for reset values.
    
        -overwrite
            By default this command will not overwrite an existing LLVM file.
            This option will force every LLVM file to be written.
            It has the same effect as the 'g_overwrite_existing_llvm' setting in
            the 'config.txt' file.
    
        -support_hierarchy
            Activate limited support for Verilog hierarchy. Each output signal
            of a sub-module will have an LLVM function created for it,
            essentially the same as in the original func_extract program.
            This technique is known to work for the AES test case, but will
            generally work correctly only for purely combinatorial sub-modules.
    
        -pmux
            Enable support for RTLIL '$pmux' cells. By default these cells are 
            converted to mux trees by the Yosys 'pmuxtree' command. With this
            option, they will be translated to LLVM 'switch' instructions.
            Typically this gives no improvement, and can interfere with
            mux-to-branch conversion.
    
        -path <path>
            Read and write all data and configuration files from the given
            directory path. By default the current directory is used.
    
To generate verbose output, either prefix this command with the Yosys
`debug` command, or set the `g_overwrite_existing_llvm` setting in
the `config.txt` file.

## General Advice

1. Review the documentation for the original `func_extract` program and examine the published test cases (https://github.com/dlbraunpu/func_extract_test) to understand what `func_extract` can and cannot do, and how to prepare the necessary configuration files.

2. Be sure that your Yosys flow script includes the `flatten` and `proc` commands, which will transform the design into a usable form.  The `prep` command is also good to use.

3. For debugging and experimenting, you can add any Yosys commands you please to the script.  The `write_rtlil` command is good for dumping the flattened and optimized design.  Note that the `write_verilog` command is less useful for debugging or saving/restoring the design, since it makes a number of transformation to represent the design in Verilog semantics.  The Yosys RTLIL format is an exact representation of the internal data model, and is fairly easy to read.

4. Read the Yosys manual! (https://yosys.readthedocs.io/en/latest/)

## Optional Capabilities

### Mux-to-Branch Conversion

Yosys tends to create many muxes in the design, and both versions of `func_extract` normally convert these to LLVM `select` instructions.
A downside of `select` is that both operands of the instruction will be calculated, even though one will be kept and the other discarded.  When compiling high-level languages, a non-trivial select statement (e.g.`? :` in C++) will normally be translated to LLVM conditional branches and jumps, thus avoiding the unneeded calculations.  But apparently LLVM's back-end optimizations will not ever convert an LLVM `select` to conditional branches.

We have implemented a special LLVM mux-to-branch optimization function, which will replace `select` instructions with conditional branches and jumps whenever it can be done correctly, and it is likely that the generated code will be improved.  This can be activated with the `-pre_opto_mux_to_branch` option.  (There is also a `-post_opto_mux_to_branch` capability, but this is usually less effective than the pre-opto version.)  The algorithm can be tuned with the `-pre_opto_mux_to_branch_threshold` option described above.

The mux-to-branch algorithm seems quite robust, and it could probably be turned on by default.

### Hierarchy Support
Normally the design should be flattened.  However, `func_extract` has **limited**
support for design hierarchy, essentially the same as what the original `func_extract` supports.  If there are many instances of a sub-module, preserving it may reduce the `func_extract` runtime and the size of the generated update functions (unfortunately the simulation runtime will not be improved).  To ensure correct simulation results, the preserved module **must** be purely combinatorial.

To preserve a sub-module in the Yosys data-preparation flow, it must be given the `keep_hierarchy` attribute before flattening.  For example, to preserve module `X`, add this to your script:

    setattr -mod -set keep_hierarchy 1 X
    flatten

The `aes_128_xram` test case has an examples of flattened and hierarchical flows.

### Verilog Memory Support

The supported Yosys flow uses the `memory` command to convert Verilog memories to individual word FFs and decoder mux trees.  A disadvantage of this is that evaluating the decoder tree is less efficient than simply indexing an array during simulation runtime.

The original `func_extract` can model Verilog memories as global memory arrays that are accessed via a computed index.  However, I was concerned that this approach can produce incorrect behavior if a memory is read after being written, written multiple times in different clock cycles, or written by multiple update functions.

The Yosys-based `func_extract` takes a different approach: it will model Verilog memories as LLVM `vector` data types, using the LLVM `extract` and `insert` instructions to read and write individual words.  This approach  generates compact LLVM IR code with the correct semantics, but unfortunately the LLVM X86 code generator generally does not create correct machine code for our test cases, and the simulations give incorrect results or crash.

If you with to experiment with this feature,you can activate it by telling
Yosys to preserve the Verilog memories, with the `memory -nomap` command.  When this is done, you should be able to observe `$mem_v2` cells in the design RTLIL representation, and `func_extract` will attempt to model these memory cells in the generated LLVM IR code.

One limitation is that memories with multiple read/write ports, read enables, or per-bit write enables are not supported.

### `$pmux` Cell Support

Yosys RTLIL typically models Verilog case statements with a special `$pmux` cell, which is essentially a one-hot multi-input mux.  Normally `func_extract` runs the Yosys `pmuxtree` command under the hood, which converts `$pmux` cells to trees of regular muxes.  If the `-pmux` option is given to `func_extract`, it will preserve the `$pmux` cells and model them in LLVM as a `switch` instruction, multiple branch instructions, and a separate code block for each case.

This `$pmux` conversion flow runs robustly and produces correct LLVM IR code, but unfortunately it rarely seems to give any simulation performance improvement, and its output can degrade the performance of the (more useful) mux-to-branch algorithm described above.

## Limitations

Compared to the original func_extract, the Yosys-based version has some minor limitations:

1. It cannot model Verilog memories as LLVM global arrays (but see the above discussion of this topic).

2. The original `func_extract` had some support for capturing multi-cycle output port data with FIFOs.  This is not implemented in the Yosys-based version.

3. Multi-threading has never been tested, and probably does not work.  However the program is fast enough that multi-threading would be of little benefit.

4. Flows that use the `added_work_set.txt` data file have never been tested.



