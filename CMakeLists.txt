# Build control file for example PP-aware refactoring code
#
#    Copyright (C) 2016 Jeff Trull <edaskel@att.net>
# 
#    Distributed under the Boost Software License, Version 1.0. (See accompanying
#    file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
# 
# 
#

cmake_minimum_required( VERSION 3.12 )

project( Octothorpe )

set( CMAKE_CXX_STANDARD 14 )
set( CMAKE_EXPORT_COMPILE_COMMANDS ON )

# We will pick up LLVM via the somewhat more modern "Config" route
# so set CMAKE_PREFIX_PATH accordingly

find_package( Clang )

include_directories( SYSTEM ${CLANG_INCLUDE_DIRS} ${LLVM_INCLUDE_DIRS} )


# libs.  TODO: can I get llvm-config to list these for me somehow? Is there a consolidated lib?
set( CLANG_AST_LIBS
        -Wl,--start-group
	clangAST
	clangASTMatchers
	clangTooling
        -Wl,--end-group
        ${LLVM_LIBS}
        ${LLVM_SYSLIBS}
)

set( Boost_USE_STATIC_LIBS ON )
find_package( Boost 1.60 REQUIRED COMPONENTS system wave thread filesystem )

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
  COMPILE_FLAGS "${LLVM_CXXFLAGS} -fexceptions -fno-rtti" # LLVM doesn't like RTTI
  LINK_FLAGS "${LLVM_LDFLAGS}"
  LINK_LIBRARIES "${CLANG_AST_LIBS}"
)

# Conditional compilation analysis of whole text example, using Boost.Wave and SMT 
# Requires CVC4. User must ensure CVC4Config.cmake is in the CMAKE_PREFIX_PATH.

find_package( CVC4 )

if( "${CVC4_FOUND}" STREQUAL "" )
  message( WARNING "No value provided for CVC4_ROOT; the deadc0de executable will not be built" )
else()

  add_executable( deadc0de analyze_conditionals.cpp )
#  set_target_properties( deadc0de PROPERTIES
#    COMPILE_DEFINITIONS BOOST_SPIRIT_DEBUG # Uncomment in case of emergency
#  )
  target_link_libraries( deadc0de Boost::system Boost::wave Boost::boost CVC4::cvc4 )
  
endif()

# Style detector example
add_executable( sd style_detect.cpp )
target_link_libraries( sd Boost::wave Boost::boost )
set_target_properties( sd PROPERTIES
   COMPILE_DEFINITIONS BOOST_SPIRIT_DEBUG # Uncomment in case of emergency
   CXX_STANDARD 17
)
