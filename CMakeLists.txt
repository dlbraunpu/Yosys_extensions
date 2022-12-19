cmake_minimum_required(VERSION 3.9)

project (doug_smash VERSION 1.0 DESCRIPTION "yosys extension for function extraction")

set(CMAKE_CXX_STANDARD 11)

# Stuff required for Yosys
set(YOSYS_DIR /home/dlbraun/.local/share/yosys)
include_directories(${YOSYS_DIR}/include)
add_compile_options(-Wall -Wextra -ggdb -MD -MP -std=c++11 -Os -rdynamic)
add_compile_definitions(
    _YOSYS_
    YOSYS_ENABLE_READLINE YOSYS_ENABLE_PLUGINS
    YOSYS_ENABLE_GLOB YOSYS_ENABLE_ZLIB
    YOSYS_ENABLE_TCL YOSYS_ENABLE_ABC
    YOSYS_ENABLE_COVER
)
link_libraries(-lstdc++ -lm -lrt -lreadline -lffi -ldl -lz -ltcl8.6 -ltclstub8.6)

# Stuff required for LLVM
find_package (LLVM 13 REQUIRED)
include_directories(${LLVM_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})

# Stuff required by our existing func_extract code
set(AUTO_GEN_ILA_DIR /home/dlbraun/autoGenILA/src)
link_directories(${AUTO_GEN_ILA_DIR}/live_analysis/build)
link_directories(${AUTO_GEN_ILA_DIR}/func_extract/build)

find_package (Z3 4.8 REQUIRED)

find_package (glog 0.4.0 REQUIRED)


aux_source_directory(./src SRC_DIR)


set(CMAKE_BUILD_TYPE Debug)

set(CMAKE_CXX_FLAGS_DEBUG "$ENV{CXXFLAGS} -O0 -Wall -g")

set(YOSYS_EXTENSION_LDLIBS "-lstdc++ -lm -lrt -lreadline -lffi -ldl -lz -ltcl8.6 -ltclstub8.6")


llvm_map_components_to_libnames(llvm_libs support core irreader)


# The shared library that will contain the Yosys extension we are making
add_library(${PROJECT_NAME} SHARED
    ./doug_smash.cc
    ./dummy.cc
)

target_link_libraries(${PROJECT_NAME} ${Z3_LIBRARIES})
target_link_libraries(${PROJECT_NAME} glog::glog)
target_link_libraries(${PROJECT_NAME} ${llvm_libs})
target_link_libraries(${PROJECT_NAME} TaintGenLib)
target_link_libraries(${PROJECT_NAME} FuncExtractLib)

include_directories(${Z3_INCLUDE_DIR})


# Add tags target 
set_source_files_properties(tags PROPERTIES GENERATED true)
add_custom_target(tags
    COMMAND ctags -R  --extra=+f .
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR})


enable_testing()
