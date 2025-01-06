cmake_minimum_required(VERSION 3.10)

project(ulbn)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

option(BUILD_SHARED_LIBRARY "Build shared library" OFF)
option(IGNORE_WARNINGS "Ignore warnings" OFF)

option(BUILD_TEST "Build test" ON)
option(BUILD_SHORT_LIMB_TEST "Build test for short `ulbn_limb_t`" ON)


if(BUILD_SHARED_LIBRARY)
    add_library(ulbn SHARED ulbn.c)
    add_library(ulbn-cxx SHARED ./test_build/ulbn_build.cpp)
    add_library(ulbn-hxx SHARED ./test_build/ulbn_build_hpp.cpp)
else()
    add_library(ulbn STATIC ulbn.c)
    add_library(ulbn-cxx STATIC ./test_build/ulbn_build.cpp)
    add_library(ulbn-hxx STATIC ./test_build/ulbn_build_hpp.cpp)
endif()

if(BUILD_SHARED_LIBRARY)
    target_compile_definitions(ulbn PRIVATE ULBN_CONF_EXPORT_PUBLIC=1)
    target_compile_definitions(ulbn-cxx PRIVATE ULBN_CONF_EXPORT_PUBLIC=1)
    target_compile_definitions(ulbn-hxx PRIVATE ULBN_CONF_EXPORT_PUBLIC=1)
endif()

set_target_properties(ulbn-cxx PROPERTIES CXX_STANDARD 98)
set_target_properties(ulbn-hxx PROPERTIES CXX_STANDARD 20)
target_include_directories(ulbn-cxx PRIVATE ./)
target_include_directories(ulbn-hxx PRIVATE ./)


set(GNUC_ALL_C_WARNINGS
    -Wall
    -Wextra
    -Werror
    # -Wpedantic

    -Wcast-align
    -Wcast-qual
    -Wdisabled-optimization
    -Wformat=2
    -Winit-self
    -Wlogical-op
    -Wmissing-declarations
    -Wmissing-include-dirs
    -Wredundant-decls
    -Wshadow
    -Wsign-conversion
    -Wstrict-overflow=5
    -Wswitch-default
    -Wundef
    # -Wabi
    -Waggregate-return
    -Wconversion
    -Winline
    -Winvalid-pch
    -Wmissing-format-attribute
    -Wnormalized=nfc
    -Wpadded
    -Wstack-protector
    -Wstrict-aliasing=3
    -Wswitch-enum
    -Wunsafe-loop-optimizations
)
set(GUNC_ALL_CXX_WARNINGS
    ${GNUC_ALL_C_WARNINGS}
    -Wctor-dtor-privacy
    -Wnoexcept
    -Weffc++
    -Wzero-as-null-pointer-constant
    -Woverloaded-virtual
    -Wstrict-null-sentinel
    -Wsign-promo
    -Wuseless-cast
    -Wold-style-cast
)
set(GNUC_CLOSE_WARNINGS
    -Wno-misleading-indentation
    -Wno-padded
)

set(CLANG_ALL_C_WARNINGS -Weverything)
set(CLANG_ALL_CXX_WARNINGS -Weverything)
set(CLANG_CLOSE_WARNINGS
    -Wno-unknown-warning-option
    -Wno-reserved-identifier
    -Wno-language-extension-token
    -Wno-padded
    -Wno-weak-vtables
    -Wno-unused-macros

    -Wno-long-long
    -Wno-c++98-compat
    -Wno-c++98-compat-pedantic
    -Wno-c++11-long-long
    -Wno-unsafe-buffer-usage
    -Wno-pre-c11-compat
)

set(MSVC_ALL_WARNINGS
    /Wall /WX)
set(MSVC_CLOSE_WARNINGS
    /wd4514 # 'function' : unreferenced inline function has been removed
    /wd4710 # 'function' : function not inlined
    /wd4711 # function 'function' selected for inline expansion
    /wd4820 # 'bytes' bytes padding added after construct 'member_name'
    /wd5045 # Compiler will insert Spectre mitigation for memory load if /Qspectre switch specified
    /wd5039 # pointer or reference to potentially throwing function passed to extern C function under -EHc. Undefined behavior may occur if this function throws an exception.
)

if(IGNORE_WARNINGS)
    set(GNUC_ALL_C_WARNINGS)
    set(GNUC_ALL_CXX_WARNINGS)
    set(CLANG_ALL_C_WARNINGS)
    set(CLANG_ALL_CXX_WARNINGS)
    set(MSVC_ALL_WARNINGS)
    set(MSVC_CLOSE_WARNINGS)
endif()

# enable most warnings
if(CMAKE_COMPILER_IS_GNUCXX)
    target_compile_options(ulbn PRIVATE ${GNUC_ALL_C_WARNINGS} ${GNUC_CLOSE_WARNINGS})
    target_compile_options(ulbn-cxx PRIVATE ${GNUC_ALL_CXX_WARNINGS} ${GNUC_CLOSE_WARNINGS})
    target_compile_options(ulbn-hxx PRIVATE ${GNUC_ALL_CXX_WARNINGS} ${GNUC_CLOSE_WARNINGS})
elseif(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
    target_compile_options(ulbn PRIVATE ${CLANG_ALL_C_WARNINGS} ${CLANG_CLOSE_WARNINGS})
    target_compile_options(ulbn-cxx PRIVATE ${CLANG_ALL_CXX_WARNINGS} ${CLANG_CLOSE_WARNINGS})
    target_compile_options(ulbn-hxx PRIVATE ${CLANG_ALL_CXX_WARNINGS} ${CLANG_CLOSE_WARNINGS})
elseif(MSVC)
    target_compile_options(ulbn PRIVATE ${MSVC_ALL_WARNINGS} ${MSVC_CLOSE_WARNINGS})
    target_compile_options(ulbn-cxx PRIVATE ${MSVC_ALL_WARNINGS} ${MSVC_CLOSE_WARNINGS})
    target_compile_options(ulbn-hxx PRIVATE ${MSVC_ALL_WARNINGS} ${MSVC_CLOSE_WARNINGS})
endif()


# link "libm"
if(UNIX)
    target_link_libraries(ulbn PRIVATE m)
    target_link_libraries(ulbn-cxx PRIVATE m)
    target_link_libraries(ulbn-hxx PRIVATE m)
endif()


# add test
if(BUILD_TEST)
    enable_testing()
    add_subdirectory(test/cxx20)
    add_subdirectory(test/bound)

    if(BUILD_SHORT_LIMB_TEST)
        add_subdirectory(test/cxx20-limb8)
        add_subdirectory(test/cxx20-limb16)
        add_subdirectory(test/cxx20-limb32)
    endif()
endif()
