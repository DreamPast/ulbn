cmake_minimum_required(VERSION 3.10)

project(ulbn)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

option(BUILD_SHARED_LIBRARY "Build shared library" OFF)
option(BUILD_TEST "Build test" ON)

if(BUILD_SHARED_LIBRARY)
    add_library(ulbn SHARED ulbn.c)
    target_compile_definitions(ulbn PRIVATE ULBN_CONF_EXPORT_PUBLIC=1)

    add_library(ulbn-cxx SHARED ulbn_build.cpp)
    target_compile_definitions(ulbn-cxx PRIVATE ULBN_CONF_EXPORT_PUBLIC=1)
    set_target_properties(ulbn-cxx PROPERTIES CXX_STANDARD 98)
else()
    add_library(ulbn STATIC ulbn.c)

    add_library(ulbn-cxx STATIC ulbn_build.cpp)
    set_target_properties(ulbn-cxx PROPERTIES CXX_STANDARD 98)
endif()
if(UNIX)
    target_link_libraries(ulbn PRIVATE m)
endif()

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
    -Wno-unused
    -Wno-misleading-indentation
    -Wno-padded
)

set(CLANG_ALL_C_WARNINGS
    -Weverything
)
set(CLANG_ALL_CXX_WARNINGS
    -Weverything
)
set(CLANG_CLOSE_WARNINGS
    -Wno-unsafe-buffer-usage
    -Wno-unused-macros
    -Wno-reserved-identifier
    -Wno-language-extension-token
    -Wno-missing-prototypes
    -Wno-unused-function
    
    -Wno-long-long
    -Wno-c++98-compat
    -Wno-c++98-compat-pedantic
    -Wno-c++11-long-long
)

set(MSVC_CLOSE_WARNINGS
    /wd4711 # function 'function' selected for inline expansion
    /wd4820 # 'bytes' bytes padding added after construct 'member_name'
    /wd5045 # Compiler will insert Spectre mitigation for memory load if /Qspectre switch specified
    /wd5039 # pointer or reference to potentially throwing function passed to extern C function under -EHc. Undefined behavior may occur if this function throws an exception.
)

# enable most warnings
if(CMAKE_COMPILER_IS_GNUCXX)
    target_compile_options(ulbn PRIVATE ${GNUC_ALL_C_WARNINGS} ${GNUC_CLOSE_WARNINGS})
    target_compile_options(ulbn-cxx PRIVATE ${GNUC_ALL_CXX_WARNINGS} ${GNUC_CLOSE_WARNINGS})
elseif(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
    target_compile_options(ulbn PRIVATE ${CLANG_ALL_C_WARNINGS} ${CLANG_CLOSE_WARNINGS})
    target_compile_options(ulbn-cxx PRIVATE ${CLANG_ALL_CXX_WARNINGS} ${CLANG_CLOSE_WARNINGS})
elseif(MSVC)
    target_compile_options(ulbn PRIVATE /Wall /WX ${MSVC_CLOSE_WARNINGS})
    target_compile_options(ulbn-cxx PRIVATE /Wall /WX ${MSVC_CLOSE_WARNINGS})
endif()

if(BUILD_TEST)
    enable_testing()
    add_subdirectory(test)
endif()
