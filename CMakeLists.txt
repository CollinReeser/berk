cmake_minimum_required(VERSION 3.2)

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

# Process "input" files to generate source during build. Generated files will
# be placed in the build dir, so we need to teach cmake to also search the`
# build dir for header files.
configure_file(config/config.h.cmake_in config.h)

# Here, we teach cmake to search the build dir for any headers generated during
# build time.
target_include_directories(
    ${PROJECT_NAME} PUBLIC "${PROJECT_BINARY_DIR}"
)

# Ensure individual commands are printed during build.
set(CMAKE_VERBOSE_MAKEFILE ON)

# Teach this invocation of `cmake` where to find required `conan` packages.
include(${CMAKE_BINARY_DIR}/conanbuildinfo.cmake)
conan_basic_setup()
