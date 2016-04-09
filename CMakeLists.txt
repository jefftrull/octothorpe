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

# In case of emergency, uncomment:
# add_definitions( -DBOOST_SPIRIT_DEBUG )

# Boost.Wave (lexer) example
add_executable( ac analyze_conditionals.cpp )
target_link_libraries( ac ${Boost_LIBRARIES} )
