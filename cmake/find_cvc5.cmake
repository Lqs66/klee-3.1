
#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#

# Try to find the CVC5 library and headers
#
# This module defines
# CVC5_FOUND
# CVC5_INCLUDE_DIRS
# CVC5_LIBRARIES
# CVC5_VERSION

find_package(cvc5 CONFIG REQUIRED)

if (cvc5_FOUND)
  set(ENABLE_SOLVER_CVC5_DEFAULT ON)
else()
  set(ENABLE_SOLVER_CVC5_DEFAULT OFF)
endif()

option(ENABLE_SOLVER_CVC5 "Enable CVC5 solver support" ${ENABLE_SOLVER_CVC5_DEFAULT})

if(ENABLE_SOLVER_CVC5)
  message(STATUS "CVC5 solver support enabled")
  if(cvc5_FOUND)
    message(STATUS "Found CVC5 version ${cvc5_VERSION}")
    set(ENABLE_CVC5 1) # For config.h
    list(APPEND KLEE_SOLVER_LIBRARIES cvc5::cvc5)
  else()
    message(FATAL_ERROR "CVC5 not found. Try setting -DCVC5_DIR=/path/to/cvc5 where"
      " `/path` is the directory containing `cvc5Config.cmake`")
  endif()
else()
  message(STATUS "CVC5 solver support disabled")
  set(ENABLE_CVC5 0)
endif()
