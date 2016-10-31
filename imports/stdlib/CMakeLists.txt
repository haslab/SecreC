#
# Copyright (C) 2015 Cybernetica
#
# Research/Commercial License Usage
# Licensees holding a valid Research License or Commercial License
# for the Software may use this file according to the written
# agreement between you and Cybernetica.
#
# GNU Lesser General Public License Usage
# Alternatively, this file may be used under the terms of the GNU Lesser
# General Public License version 3 as published by the Free Software
# Foundation and appearing in the file LICENSE.LGPLv3 included in the
# packaging of this file.  Please review the following information to
# ensure the GNU Lesser General Public License version 3 requirements
# will be met: http://www.gnu.org/licenses/lgpl-3.0.html.
#
# For further information, please contact us at sharemind@cyber.ee.
#

CMAKE_MINIMUM_REQUIRED(VERSION 2.8)
PROJECT(SHAREMIND_STDLIB CXX)

INCLUDE("${CMAKE_CURRENT_SOURCE_DIR}/config.local" OPTIONAL)
INCLUDE("${CMAKE_CURRENT_BINARY_DIR}/config.local" OPTIONAL)

FIND_PACKAGE(Doxygen REQUIRED)

FILE(GLOB_RECURSE SharemindStdlib_ALLFILES
     "${CMAKE_CURRENT_SOURCE_DIR}/lib/*.sc"
     "${CMAKE_CURRENT_SOURCE_DIR}/tests/*.sc"
     "${CMAKE_CURRENT_SOURCE_DIR}/tests/*.sh"
)
ADD_CUSTOM_TARGET("include_SharemindStdlib_ALLFILES_in_IDE" SOURCES
                  ${SharemindStdlib_ALLFILES})

# Stdlib:

# Note that this globbing is done by cmake, not by make, hence sometimes clean might be required.
FILE(GLOB SharemindStdlib_FILES "${CMAKE_CURRENT_SOURCE_DIR}/lib/*.sc")
INSTALL(FILES ${SharemindStdlib_FILES}
        DESTINATION "lib/sharemind/stdlib")

# Stdlib documentation:

ADD_CUSTOM_TARGET(stdlib_docs ALL
                  COMMAND "./build_html.sh"
                  WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/docs")

INSTALL(DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/docs/html"
        DESTINATION "share/doc/sharemind/stdlib")
