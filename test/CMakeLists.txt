cmake_minimum_required(VERSION 3.10)

project(ulbn-test)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

add_executable(ulbn-test test.cpp)
set_target_properties(ulbn-test PROPERTIES CXX_STANDARD 20)
target_include_directories(ulbn-test PRIVATE ${PROJECT_SOURCE_DIR}/../)
target_link_libraries(ulbn-test PRIVATE ulbn)

if(CMAKE_COMPILER_IS_GNUCXX)
    target_compile_options(ulbn-test PRIVATE
        ${GCC_ALL_CXX_WARNINGS} ${GCC_CLOSE_WARNINGS}
    )
elseif(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
    target_compile_options(ulbn-test PRIVATE
        ${CLANG_ALL_C_WARNINGS} ${CLANG_CLOSE_WARNINGS}

        -Wno-missing-prototypes
        -Wno-disabled-macro-expansion
        -Wno-float-equal
        -Wno-global-constructors
        -Wno-zero-as-null-pointer-constant # todo: why "<=>" 0 is viewed as a null pointer constant?
    )
elseif(MSVC)
    target_compile_options(ulbn-test PRIVATE ${MSVC_ALL_WARNINGS} ${MSVC_CLOSE_WARNINGS})
endif()

add_test(NAME ulbn-test COMMAND ulbn-test)
