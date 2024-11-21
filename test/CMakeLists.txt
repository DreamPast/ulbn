cmake_minimum_required(VERSION 3.10)

project(ulbn-test)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

add_executable(ulbn-test test.cpp)
set_target_properties(ulbn-test PROPERTIES CXX_STANDARD 20)
target_include_directories(ulbn-test PRIVATE ${PROJECT_SOURCE_DIR}/../)
target_link_libraries(ulbn-test PRIVATE ulbn)

if(CMAKE_COMPILER_IS_GNUCXX)
    target_compile_options(ulbn-test PRIVATE -Wall -Wextra -Wno-misleading-indentation)
elseif(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
    target_compile_options(ulbn-test PRIVATE
        ${CLANG_ALL_C_WARNINGS} ${CLANG_CLOSE_WARNINGS}

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
        -Wno-float-equal
        -Wno-global-constructors
    )
elseif(MSVC)
    target_compile_options(ulbn-test PRIVATE
        /Wall /WX ${MSVC_CLOSE_WARNINGS}

        /wd4514 # 'function' : unreferenced inline function has been removed
        /wd4623 # 'derived class' : default constructor was implicitly defined as deleted because a base class default constructor is inaccessible or deleted
        /wd5027 # 'type': move assignment operator was implicitly defined as deleted
        /wd4626 # 'derived class' : assignment operator was implicitly defined as deleted because a base class assignment operator is inaccessible or deleted
        /wd4710 # 'function' : function not inlined
    )
endif()

add_test(NAME ulbn-test COMMAND ulbn-test)
