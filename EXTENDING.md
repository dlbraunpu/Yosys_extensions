# Advice for maintaining and extending this program

## First Steps

1. **Read the Yosys Manual!!!**   (https://yosyshq.readthedocs.io/projects/yosys/en/latest/)  It is fairly short, but almost every word in the *Implementation Overview*, *Internal Cell Library*, and *Programming Yosys Extensions* chapters is relevant.

2. Understand the basic Yosys flow that is used in the func_extract test cases: the `read_verilog`, `prep`, `opt`, etc. commands.

3. Understand the Yosys RTLIL data model, as described in the manual.  Read the .rtlil file for some design (created by `write_rtlil`) to get some hands-on experience with the data model.  (Note that the Yosys AST data model is unimportant to us)

4. Get an overview of the Yosys API for the RTLIL data model.  Most of it is defined on a single Yosys header file: `kernel/rtlil.h`.  Naturally you can find many many usage examples in the Yosys source tree, as well as this program.  It is especially important to understand the `SigSpec` class and how `Wire` objects interact with other RTLIL objects.

5. Review the RTL cell library described in the manual, and look at the `.rtlil` file for an actual design to see how they are used. (Note that the single-bit gate-level cells are not important to us.)

6. Study the details of the Yosys `SigSpec`, `SigChunk`, and `SigBit` classes.  These are powerful and elegant, and widely used in the RTLIL data model.

## Func_extract Software Architecture

This program is implemented as a plugin extension to Yosys (so there is no `main()` function or standalone executable).  The basic instructions for building and running it are in the `README.md` file. You can see what other libraries and packages are required by reading the `CMakeLists.txt` file.

There are 4 main software components:

1. The code in this repository.
2. The original func_extract code in `autoGenILA/src/func_extract`
3. Yosys itself.
4. LLVM

The C++ files in this repository includes headers from the other 3 components.
Fortunately all 4 of these packages seem to be able to co-exist in the same build.  If you ever see strange compiler errors relating to `#define ID`, they can be resolved by rearranging the order in which header files are included.

Each of these package has its own functions and classes for generating messages, reporting errors, asserting, etc.  In the code within this repository do these things the Yosys way.

### Top-Level Control Flow

1. The file `yosys_func_extract.cc` contains the top-level implementation of the `func_extract` command.  This is implemented in the standard Yosys way (see the manual!), the same as almost every command built into Yosys.

2. The command first calls several functions from the original `func_extract` (in namespaces `funcExtract` and `taintGen`) to load the configuration files (`config.txt`, `instr.txt`, `rst.vcd`, and `allowed_target.txt`) into the same data structures used by the original `funct_extract`.

3. The main func_extract code-generation flow is then executed, like this:

```C++
    YosysUFGenFactory factory(srcmod, ufGenOpts);
    
    YosysModuleInfo info(srcmod);
    
    funcExtract::FuncExtractFlow flow(factory, info, false /*innerLoopIsInstrs*/,
                                      false /*reverseCycleOrder*/);
                                    
    flow.get_all_update();
```

The class `FuncExtractFlow` in the original `func_extract` code implements the flow for both versions of `func_extract`.  The class `YosysUFGenFactory` implements the Yosys-based code generator that  `FuncExtractFlow` will call. `FuncExtractFlow` performs the iterating over instructions and ASVs, the back-end LLVM processing and optimizations, etc. for both version of the program.

The class `YosysUFGenFactory` focuses on translating the Yosys RLTIL design representation into LLVM instructions for a particular update function and ASV.  The class `YosysModuleInfo` provides design query callbacks that allow `FuncExtractFlow` to obtain information about the design without knowing anything about how it is represented in memory.

The original `func_extract` has its own `UFGenFactory` and `ModuleInfo` class implementations that perform the same operations, using its internal data structures and code instead of Yosys's. (Don't forget that the original `func_extract` does not use Yosys code at all.)

### Code Generation Flow

The Yosys-based code generation flow (class `YosysUFGenerator`) is implemented in `uf_generator.cc`.  The main entry point is `YosysUFGenerator::print_llvm_ir()`.  The flow does these things:

1. Create an unrolled version of the design.  This is done by the function `YosysUFGenerator::makeUnrolledModule()`.   If a suitable unrolled design has been created for a different ASV of the same instruction, it will be re-used.
The unrolled module will have the instruction's input signal values applied to it.

2. The function `applyInstrEncoding()` is called to set the instruction encoding values on the cycle-specific input ports.  Port bits with an `X` value in tehencoding will remain as input ports, while bits with a `0` or `1` value will be de-ported.  The optimization performed in the next step will get rid of them.

2. Call some Yosys optimization command to optimize the unrolled module.  This is accomplished with code like this:

       Pass::call_on_module(m_des, unrolledMod, "opt -mux_bool");

3. Statistics are  printed, and the unrolled module can be written out for debugging.

4. Call the  LLVM writer, implemented in the class `LLVMWriter`.  This will generate the LLVM file (named \<instr\>_\<asv\>_\<cycles\>.tmp-ll)

The final optimization of the LLVM IR file is performed by the common top-level flow described above.

### Module Unrolling Details

The code for module unrolling is in the file `unroll.cc`.  These steps are done:

1. The function `smash_module()` repeatedly copies the design, once for each clock cycle, from the original (flattened) design module into the new temporary module.  For each copy, cells and wires are given unique cycle-specific names.  (Much of the copying code was derived from the code of the  Yosys `copy` command.)  Some tables are built to keep track of the relationship between FFs in the original design and their per-cycle unrolled counterparts.

2. For each clock cycle, the FFs of that cycle must be split: The signals that drive the FF D signals in Cycle *N* must be connected to the corresponding FF Q signals of cycle *N+1*, and the FF cell must be deleted.  This is done by the function `split_ff()`.   Some situations require some extra work:
   1. In the first and last clock cycles, the FF D and Q signals get made into top-level ports so that the initial and final signal values can be set and read.  Top-level module inputs will have a port for each clock cycle.
   2. Memory cells get a special form of unrolling: getting turned onto special 'insert' and 'extract' cells that will be specially processed by the LLVM writer. (Memory cell does not completely work, although the code in `unroll.cc` is sound.)
   3. Some FF cells have reset and/or write enable signals.  These must be modeled in the unrolled design by with additional muxes or gates.  This is done by functions like `wire_up_ce()` and `wire_up_srst()`.

3. The ports representing ASVs are labeled with RTLIL attributes, which will guide the LLVM code generation.

### LLVM Code Generation

Code generation is done by the class `LLVMWriter` in `llvm_writer.cc`.

The main entry point is the function `write_llvm_ir()`.  This function creates the `llvm::Module` that will contain the update function,
creates a `llvm::Function` for the update function, and fills it with LLVM instructions that calculate the new ASV value(s) based on the input parameters.
If the unrolled design contains sub-modules, additional `llvm::Function`s will be created for them, and called from the main function.

The code generation algorithm recursively traverses the design netlist starting at the desired output port, ending when the input ports (which are
represented by LLVM function parameters) are reached.  For each Yosys RTL cell encountered, LLVM code is recursively generated to calculate its input value, and the appropriate LLVM instruction
is generated to calculate the cell output value.  Most RTL cells (e.g. AND, OR) can be represented by a single LLVM insctruction, but some cells need to be modeled by multiple LLVM inscructions.
Slicing and concatenation of signals will get modeled by LLVM extension, truncation, shifting and masking operations.

The top-level coded generation algorithm is implemented by this code in `LLVMWriter::writeMainFunction()`:

    // Collect the drivers of each bit of the destination wire
    DriverSpec dSpec;
    finder.buildDriverOf(targetPort, dSpec);

    // Print what drives the bits of this wire
    log_debug_driverspec(dSpec);
    log_debug("\n");

    llvm::Value *destValue = generateValue(dSpec);

    b->CreateRet(destValue);
  
The function `generateValue()` will recursively generate the code for the entire fanin cone of the desired result.  Note how
`DriverFinder::buildDriverOf()` maps from the module output port (which represents the new ASV value) to whetever actually drives it.
(`DriverFinder` and `DriverSpec` are described in detail below).

The function `LLVMWriter::generateValue(const DriverSpec& dSpec)` is (recursively) called in several places, and does a lot of work.
It picks apart the given driver spec, calls other functions to generate the values of cell outputs or top-level input ports, and finally
does any necessary masking, shifting, extending, etc. to assemble the desired result.

If `generateValue()` encounters a RTL cell output port, it calls `generateCellOutputValue()` to generate the `llvm::Value` that represents it.
`generateCellOutputValue()` calls one of various functions which process each type of RTL cell.  For a typical cell, `generateValue()` is called to
generate `llvm::Value`s for each of its inputs.  Any necessary widening or truncation is done on those values, and finally they are used as
operands for the LLVM instruction that calculates the RTL cell's output.  (Beware: The RTL cell input/output bit widths may not match the
signals that drive them, and the truncation/extension rules described in the Yosys Manual have to be carefully followed).

The class `ValueCache` maintains a map from `DriverSpec` objects to the `llvm::Value` objects that have been generated to calculate their values.
This cache allows a `llvm::Value` to be re-used as often as necessary in different places, without re-calculating it from scratch.
Without this cache, the generated code would be much larger.  The cache understands the dominance relationships of the function's Basic Blocks,
so that we can guarantee that a `llvm::Value` will not ever be used without first being generated.  (The function `llvm::verifyFunction()` is
called at the end of code generation to ensure that there are no accidental violations of dominance.)  Normally an update function will have
only a single Basic Block (and thus no branching instructions), but some optional optimizations for RTL `$mux` and `$pmux` cells may create
additional BBs and branches.

### Code Generation Support Classes

The file `driver_tools.cc` contains several important classes that are vital to code generation.

The class `DriverSpec` represents the drivers of each bit of a (possibly) multi-bit signal.  It is essentially a more powerful version of
the Yosys `SigSpec` class (in fact, it was created by copying and editing the `SigSpec` code).  Remember that a `SigSpec` object models a signal as a
concatenation of wire slices and 0/1/x/z constant values. But a `DriverSpec` object instead models the *driver* of a signal: a concatenation
of three things: a cell output port slice, a wire slice (representing a top-level input port), and a 0/1/x/z constant value.
`DriverSpec` objects can be constructed and manipulated very much like `SigSpec` objects.  Several functions in `write_llvm.cc` take
`DriverSpec` parameters, and the important `ValueCache` class in `write_llvm.h` uses them as hashable keys.

The classes `DriverChunk` and `DriverBit` are used to implement `DriverSpec` (similar to the Yosys `SigChunk` and `SigBit` classes).

The class `DriverFinder` builds and maintains tables that map from signal receivers (i.e. cell input ports and top-level output ports) to
whatever drives them.  As you no doubt remember from the Yosys Manual, the RTLIL data model does not have direct links from wires to
the cell ports and other wires connected to them.  An instance of `DriverFinder` is built and used to perform this wire-to-port mapping.

These two functions are the main API for `DriverFinder`:

    // Get a description of what drives the given wire. driver gets filled in.
    void buildDriverOf(Yosys::RTLIL::Wire *wire, DriverSpec& driver);
          
    // Get a description of what drives the given SigSpec. driver gets filled in.
    void buildDriverOf(const Yosys::RTLIL::SigSpec& sigspec, DriverSpec& driver);

 
