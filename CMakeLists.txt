# We use some cmake features not available below this version.
cmake_minimum_required(VERSION 3.2)

# Write generated executables into a `bin` dir under the build dir.
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

# Define project name, and point to the `main` for that target.
project(berk VERSION 0.0.1)
add_executable(${PROJECT_NAME} src/berk.cpp)

# Enable debugging symbols (ie, `-g`).
set(CMAKE_BUILD_TYPE RelWithDebInfo)

# Require at least C++17.
target_compile_features(${PROJECT_NAME} PUBLIC cxx_std_17)

# Teach cmake to search the include dir for headers.
target_include_directories(
    ${PROJECT_NAME} PUBLIC ${PROJECT_SOURCE_DIR}/include
)

# Process "input" files to generate source during build. Generated files will be
# placed under the build dir, so we need to teach cmake to also search the`
# build dir for header files.
configure_file(config/config.h.cmake_in ${CMAKE_BINARY_DIR}/include/config.h)

# Here, we teach cmake to search under build dir for any headers generated
# during build time.
target_include_directories(
    ${PROJECT_NAME} PUBLIC "${CMAKE_BINARY_DIR}/include"
)

# Ensure individual commands are printed during build.
# set(CMAKE_VERBOSE_MAKEFILE ON)

# Teach this invocation of `cmake` where to find required `conan` packages.
include(${CMAKE_BINARY_DIR}/conanbuildinfo.cmake)
conan_basic_setup()

# Setup for building against LLVM.
#
# See also: https://llvm.org/docs/CMake.html#embedding-llvm-in-your-project

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

include_directories(${LLVM_INCLUDE_DIRS})
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
add_definitions(${LLVM_DEFINITIONS_LIST})

# Find the libraries that correspond to the LLVM components
# that we wish to use
llvm_map_components_to_libnames(llvm_libs support core irreader)

# Link against LLVM libraries
target_link_libraries(${PROJECT_NAME} ${llvm_libs})
