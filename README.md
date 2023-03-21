# Yosys extensions

To build:

    If necessary, edit CMakeLists.txt so that the YOSYS_DIR and AUTO_GEN_ILA_DIR
    definitions point to an up-to-date copy of these packages.

    Ensure that LLVM version 14 is available in a place where cmake can find it.

    Do:

      mkdir build
      cd build
      cmake ..
      make
