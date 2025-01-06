cmake_minimum_required(VERSION 3.10)

project(ulbn-test-cxx20-limb8)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)



add_library(ulbn-cxx20-limb8-build STATIC build.c)
target_include_directories(ulbn-cxx20-limb8-build PRIVATE ${PROJECT_SOURCE_DIR}/../../)
if(CMAKE_COMPILER_IS_GNUCXX)
  target_compile_options(ulbn-cxx20-limb8-build PRIVATE
    ${GCC_ALL_C_WARNINGS} ${GNUC_CLOSE_WARNINGS} ${DISABLE_WARNINGS}
  )
elseif(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
  target_compile_options(ulbn-cxx20-limb8-build PRIVATE
    ${CLANG_ALL_C_WARNINGS} ${CLANG_CLOSE_WARNINGS} ${DISABLE_WARNINGS}
  )
elseif(MSVC)
  target_compile_options(ulbn-cxx20-limb8-build PRIVATE
    ${MSVC_ALL_WARNINGS} ${MSVC_CLOSE_WARNINGS} ${DISABLE_WARNINGS})
endif()



set(TEST_LIST
    arithmetic_operation
    bit_operation
    cast_from
    cast_to
    compare
    divmod_2exp
    number_theory
    other
    pow_root
    random
)

foreach(TEST_ENTRY ${TEST_LIST})
    set(TEST_NAME ulbn-test-cxx20-limb8-${TEST_ENTRY})

    add_executable(${TEST_NAME} ${PROJECT_SOURCE_DIR}/../cxx20/${TEST_ENTRY}.cpp)
    target_compile_definitions(${TEST_NAME} PRIVATE TEST_DEBUG_LIMB8)
    set_target_properties(${TEST_NAME} PROPERTIES CXX_STANDARD 20)
    target_include_directories(${TEST_NAME} PRIVATE ${PROJECT_SOURCE_DIR}/../../)
    target_link_libraries(${TEST_NAME} PRIVATE ulbn-cxx20-limb8-build)


    if(CMAKE_COMPILER_IS_GNUCXX)
        target_compile_options(${TEST_NAME} PRIVATE
            ${GNUC_ALL_CXX_WARNINGS} ${GNUC_CLOSE_WARNINGS}
        )
    elseif(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
        target_compile_options(${TEST_NAME} PRIVATE
            ${CLANG_ALL_CXX_WARNINGS} ${CLANG_CLOSE_WARNINGS}

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
