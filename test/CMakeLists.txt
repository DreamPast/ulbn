cmake_minimum_required(VERSION 3.0)

project(ulbn-test)
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

add_executable(ulbn-test test.cpp)
target_include_directories(ulbn-test PRIVATE ${CMAKE_SOURCE_DIR}/../)

# enable most warnings
if(CMAKE_COMPILER_IS_GNUCXX)
    target_compile_options(ulbn-test PRIVATE -Wall -Wextra -Wno-misleading-indentation)
elseif(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
    target_compile_options(ulbn-test PRIVATE
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
        -Wno-padded
        -Wno-disabled-macro-expansion
        # Following warnings are "test.cpp" specific
        -Wno-float-equal
        -Wno-global-constructors
    )
elseif(MSVC)
    target_compile_options(ulbn-test PRIVATE /W4)
endif()

enable_testing()
add_test(NAME ${PROJECT_NAME} COMMAND ulbn-test)
