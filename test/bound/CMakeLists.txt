cmake_minimum_required(VERSION 3.10)

project(ulbn-test-bound)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

if(CMAKE_COMPILER_IS_GNUCXX)
  set(DISABLE_WARNINGS
    -Wno-used-but-marked-unused
    -Wno-missing-noreturn
    -Wno-shadow
    -Wno-padded
  )
elseif(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
  set(DISABLE_WARNINGS
    -Wno-used-but-marked-unused
    -Wno-missing-noreturn
    -Wno-shadow
    -Wno-padded
  )
else()
  set(DISABLE_WARNINGS
    /wd4459 # declaration of 'identifier' hides global declaration
    /wd4464 # relative include path contains '..'
  )
endif()



add_library(ulbn-bound-build STATIC build.c)
target_include_directories(ulbn-bound-build PRIVATE ${PROJECT_SOURCE_DIR}/../../)
if(CMAKE_COMPILER_IS_GNUCXX)
  target_compile_options(ulbn-bound-build PRIVATE
    ${GCC_ALL_C_WARNINGS} ${GNUC_CLOSE_WARNINGS} ${DISABLE_WARNINGS}
  )
elseif(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
  target_compile_options(ulbn-bound-build PRIVATE
    ${CLANG_ALL_C_WARNINGS} ${CLANG_CLOSE_WARNINGS} ${DISABLE_WARNINGS}
  )
elseif(MSVC)
  target_compile_options(ulbn-bound-build PRIVATE
    ${MSVC_ALL_WARNINGS} ${MSVC_CLOSE_WARNINGS} ${DISABLE_WARNINGS})
endif()



set(TEST_LIST
  arithmetic_operation
)

foreach(TEST_ENTRY ${TEST_LIST})
  set(TEST_NAME ulbn-test-bound-${TEST_ENTRY})

  add_executable(${TEST_NAME} ${TEST_ENTRY}.c)
  target_include_directories(${TEST_NAME} PRIVATE ${PROJECT_SOURCE_DIR}/../../)
  target_link_libraries(${TEST_NAME} PRIVATE ulbn-bound-build)

  if(CMAKE_COMPILER_IS_GNUCXX)
    target_compile_options(${TEST_NAME} PRIVATE
      ${GNUC_ALL_C_WARNINGS} ${GNUC_CLOSE_WARNINGS} ${DISABLE_WARNINGS})
  elseif(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
    target_compile_options(${TEST_NAME} PRIVATE
      ${CLANG_ALL_C_WARNINGS} ${CLANG_CLOSE_WARNINGS} ${DISABLE_WARNINGS})
  elseif(MSVC)
    target_compile_options(${TEST_NAME} PRIVATE
      ${MSVC_ALL_WARNINGS} ${MSVC_CLOSE_WARNINGS} ${DISABLE_WARNINGS})
  endif()

  if(UNIX)
    target_link_libraries(${TEST_NAME} PRIVATE m)
  endif()

  add_test(NAME ${TEST_NAME} COMMAND ${TEST_NAME})
endforeach()
