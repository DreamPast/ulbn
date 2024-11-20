cmake_minimum_required(VERSION 3.0)

project(ulbn-test)
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

add_executable(test test.cpp)
target_include_directories(test PRIVATE ${CMAKE_SOURCE_DIR}/../)

if(CMAKE_COMPILER_IS_GNUCXX)
    target_compile_options(test PRIVATE -Wall -Wextra)
elseif(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
    target_compile_options(test PRIVATE
        -Weverything
        -Wno-unused-macros
        -Wno-zero-as-null-pointer-constant
        -Wno-unsafe-buffer-usage
        -Wno-reserved-identifier
        -Wno-language-extension-token
        -Wno-missing-prototypes
        -Wno-unused-function
        -Wno-c++98-compat
        -Wno-c++98-compat-pedantic
        -Wno-c++11-long-long
        # Following warnings are "test.cpp" specific
        -Wno-float-equal
        -Wno-global-constructors
    )
elseif(MSVC)
    target_compile_options(test PRIVATE /W4)
endif()
