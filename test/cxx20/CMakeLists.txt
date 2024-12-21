cmake_minimum_required(VERSION 3.10)

project(ulbn-test)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

set(TEST_LIST
    arithmetic_operation
    bit_operation
    cast_from
    cast_to
    compare
    number_theory
    other
    random
)

foreach(TEST_ENTRY ${TEST_LIST})
    set(TEST_NAME ulbn-test-${TEST_ENTRY})

    add_executable(${TEST_NAME} test_${TEST_ENTRY}.cpp)
    set_target_properties(${TEST_NAME} PROPERTIES CXX_STANDARD 20)
    target_include_directories(${TEST_NAME} PRIVATE ${PROJECT_SOURCE_DIR}/../../)
    target_link_libraries(${TEST_NAME} PRIVATE ulbn)

    if(CMAKE_COMPILER_IS_GNUCXX)
        target_compile_options(${TEST_NAME} PRIVATE
            ${GCC_ALL_CXX_WARNINGS} ${GCC_CLOSE_WARNINGS}
        )
    elseif(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
        target_compile_options(${TEST_NAME} PRIVATE
            ${CLANG_ALL_C_WARNINGS} ${CLANG_CLOSE_WARNINGS}

            -Wno-missing-prototypes
            -Wno-disabled-macro-expansion
            -Wno-float-equal
            -Wno-global-constructors
            -Wno-zero-as-null-pointer-constant # todo: why "<=>" 0 is viewed as a null pointer constant?
        )
    elseif(MSVC)
        target_compile_options(${TEST_NAME} PRIVATE ${MSVC_ALL_WARNINGS} ${MSVC_CLOSE_WARNINGS})
    endif()

    add_test(NAME ${TEST_NAME} COMMAND ${TEST_NAME})
endforeach()
