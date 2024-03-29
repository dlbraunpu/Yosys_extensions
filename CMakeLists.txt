cmake_minimum_required(VERSION 3.9)

project (yosys_func_extract VERSION 1.0 DESCRIPTION "yosys extension for ILA update function extraction")

# LLVM 13 requires this
set(CMAKE_CXX_STANDARD 17)

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
set(YOSYS_LIBS -lstdc++ -lm -lrt -lreadline -lffi -ldl -lz -ltcl8.6 -ltclstub8.6)


# Stuff required for LLVM

# Look for existing LLVM installation
#find_package (LLVM 14 REQUIRED)

# Force use of Doug's LLVM build
find_package (LLVM 14 REQUIRED PATHS /home/dlbraun/.local/ NO_DEFAULT_PATH)

include_directories(${LLVM_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})
llvm_map_components_to_libnames(llvm_libs support core irreader)


# Stuff required by our existing func_extract code
set(AUTO_GEN_ILA_DIR /home/dlbraun/autoGenILA/src)
# Include .h files like this: #include live_analysis/src/global_data.h
include_directories(${AUTO_GEN_ILA_DIR})
link_directories(${AUTO_GEN_ILA_DIR}/live_analysis/build)
link_directories(${AUTO_GEN_ILA_DIR}/func_extract/build)


find_package (glog 0.4.0 REQUIRED)


aux_source_directory(./src SRC_DIR)


set(CMAKE_BUILD_TYPE Debug)

set(CMAKE_CXX_FLAGS_DEBUG "$ENV{CXXFLAGS} -Og -Wall -g")



# The shared library that will contain the Yosys extension we are making
add_library(${PROJECT_NAME} SHARED ${SRC_DIR})

# A statically linked version
#add_library(${PROJECT_NAME} ${SRC_DIR})

target_link_libraries(${PROJECT_NAME} ${YOSYS_LIBS})
target_link_libraries(${PROJECT_NAME} glog::glog)
target_link_libraries(${PROJECT_NAME} TaintGenLib)
target_link_libraries(${PROJECT_NAME} FuncExtractLib)
target_link_libraries(${PROJECT_NAME} ${llvm_libs})



# Add tags target 
set_source_files_properties(tags PROPERTIES GENERATED true)
add_custom_target(tags
    COMMAND ctags -R --extra=+fq ${CMAKE_SOURCE_DIR}
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR})


enable_testing()
