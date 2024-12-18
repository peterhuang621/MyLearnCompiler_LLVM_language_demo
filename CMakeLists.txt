cmake_minimum_required(VERSION 3.20)
project("llvm_language_demo" LANGUAGES C CXX)
set(CMAKE_CXX_COMPILER "clang++")

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -w")

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)

set(CMAKE_PREFIX_PATH "/opt/homebrew/opt/llvm")

include_directories(/opt/homebrew/include ${CMAKE_PREFIX_PATH}/include)
link_directories(/opt/homebrew/lib ${CMAKE_PREFIX_PATH}/lib)

add_executable(lexer src/lexer.cpp)