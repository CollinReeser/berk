cmake_minimum_required(VERSION 3.2)

project(berk VERSION 0.0.1)
add_executable(berk berk.cpp)

target_compile_features(berk PUBLIC cxx_std_11)

configure_file(config.h.cmake_in config.h)
target_include_directories(
    berk PUBLIC "${PROJECT_BINARY_DIR}"
)

# set(CMAKE_VERBOSE_MAKEFILE ON)

include(${CMAKE_BINARY_DIR}/conanbuildinfo.cmake)
conan_basic_setup()
