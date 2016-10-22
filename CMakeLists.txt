# Build control file for example PP-aware refactoring code
#
#    Copyright (C) 2016 Jeff Trull <edaskel@att.net>
# 
#    Distributed under the Boost Software License, Version 1.0. (See accompanying
#    file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
# 
# 
#

cmake_minimum_required( VERSION 2.8.12 )

# we expect LLVM_ROOT to be defined
set( LLVM_ROOT "" CACHE PATH "path to the LLVM build containing the AST tools" )
if( NOT LLVM_ROOT )
  message( FATAL_ERROR "please set LLVM_ROOT to the root of your LLVM build" )
endif()

# get LLVM include and library deps
execute_process( COMMAND ${LLVM_ROOT}/build/bin/llvm-config --cxxflags 
  OUTPUT_VARIABLE LLVM_CXXFLAGS OUTPUT_STRIP_TRAILING_WHITESPACE )
execute_process( COMMAND ${LLVM_ROOT}/build/bin/llvm-config --ldflags
  OUTPUT_VARIABLE LLVM_LDFLAGS OUTPUT_STRIP_TRAILING_WHITESPACE )
execute_process( COMMAND ${LLVM_ROOT}/build/bin/llvm-config --libs
  OUTPUT_VARIABLE LLVM_LIBS OUTPUT_STRIP_TRAILING_WHITESPACE )
string( REPLACE " " ";" LLVM_LIBS "${LLVM_LIBS}" )
execute_process( COMMAND ${LLVM_ROOT}/build/bin/llvm-config --system-libs
  OUTPUT_VARIABLE LLVM_SYSLIBS OUTPUT_STRIP_TRAILING_WHITESPACE )
string( REPLACE " " ";" LLVM_SYSLIBS "${LLVM_SYSLIBS}" )

include_directories( SYSTEM
                     ${LLVM_ROOT}/tools/clang/include
                     ${LLVM_ROOT}/build/tools/clang/include
                     ${LLVM_ROOT}/include
                   )

# libs.  TODO: can I get llvm-config to list these for me somehow? Is there a consolidated lib?
set( CLANG_AST_LIBS
        -Wl,--start-group
	clangAST
	clangAnalysis
	clangBasic
	clangDriver
	clangEdit
        clangFormat 
	clangFrontend
	clangFrontendTool
	clangLex
	clangParse
	clangSema
	clangEdit
	clangASTMatchers
	clangRewrite
	clangRewriteFrontend
	clangStaticAnalyzerFrontend
	clangStaticAnalyzerCheckers
	clangStaticAnalyzerCore
	clangSerialization
	clangToolingCore
	clangTooling
        -Wl,--end-group
        ${LLVM_LIBS}
        ${LLVM_SYSLIBS}
)

set( Boost_USE_STATIC_LIBS ON )
find_package( Boost 1.60 REQUIRED COMPONENTS system wave thread filesystem )
include_directories(SYSTEM ${Boost_INCLUDE_DIRS})


add_definitions( -std=c++14 )
if (CMAKE_COMPILER_IS_GNUCC OR (CMAKE_CXX_COMPILER_ID STREQUAL "Clang"))
  add_definitions(-Wall -Wextra -Werror)  # be conservative about checks
  if( CMAKE_COMPILER_IS_GNUCXX )
    set( CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fuse-ld=gold" )
  endif()
endif()

# without this we still get symbols but many things are optimized out
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -O0")

# Clang-using example

add_executable( c2p conditional_to_policy.cpp )
# Note Clang is normally compiled without exceptions or RTTI... tread carefully
set_target_properties( c2p PROPERTIES
  COMPILE_FLAGS "${LLVM_CXXFLAGS} -std=c++14 -fexceptions"
  LINK_FLAGS "${LLVM_LDFLAGS}"
  LINK_LIBRARIES "${CLANG_AST_LIBS}"
)

# Conditional compilation analysis of whole text example, using Boost.Wave and SMT 
# Requires CVC4

# User is supposed to have supplied CVC4_ROOT on the CMake command line with -D
set( CVC4_ROOT "" CACHE PATH "Path to the CVC4 build" )
if( "${CVC4_ROOT}" STREQUAL "" )
  message( WARNING "No value provided for CVC4_ROOT; the deadc0de executable will not be built" )
else()
  find_library( CVC4_LIB cvc4 ${CVC4_ROOT}/lib )
  if( NOT CVC4_LIB )
    message( FATAL_ERROR "Cannot find the CVC4 library within ${CVC4_ROOT}/lib; did you compile it?" )
  endif()
  find_library( GMP_LIB gmp )
  if( NOT GMP_LIB )
    message( FATAL_ERROR "The GMP library is required for building preprocessor conditional analysis" )
  endif()

  # Boost.Wave (lexer) example
  add_compile_options( -Wno-deprecated )        # CVC4 uses some old stuff
  add_executable( deadc0de analyze_conditionals.cpp )
  set_target_properties( deadc0de PROPERTIES
    # COMPILE_DEFINITIONS BOOST_SPIRIT_DEBUG # Uncomment in case of emergency
    LINK_LIBRARIES "${Boost_LIBRARIES};${CVC4_LIB};${GMP_LIB}"
  )
  target_include_directories( deadc0de SYSTEM PRIVATE "${Boost_INCLUDE_DIRS};${CVC4_ROOT}/include" )
  
endif()
