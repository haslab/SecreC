#!/bin/bash
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

# Exit status of piped commands is zero only if all commands succeed
set -o pipefail

if [ ! -d "${SHAREMIND_PATH}" ]; then
    echo 'Required environment variable SHAREMIND_PATH missing or does not point to a directory!' 1>&2
    exit 1
fi

# readlink on OS X does not behave as on Linux
# http://stackoverflow.com/questions/1055671/how-can-i-get-the-behavior-of-gnus-readlink-f-on-a-mac
if [ `uname -s` = "Darwin" ]; then
  CWD=`pwd`
  TARGET_FILE=$0

  cd "`dirname "${TARGET_FILE}"`"
  TARGET_FILE=`basename "${TARGET_FILE}"`

  # Iterate down a (possible) chain of symlinks
  while [ -L "${TARGET_FILE}" ]
  do
    TARGET_FILE=`readlink "${TARGET_FILE}"`
    cd "`dirname "${TARGET_FILE}"`"
    TARGET_FILE=`basename "${TARGET_FILE}"`
  done
  unset -v TARGET_FILE

  # Compute the canonicalized name by finding the physical path
  # for the directory we're in and appending the target file.
  ABSSP=`pwd -P`
  cd "$CWD"
  unset -v CWD
else
  ABSS=`readlink -f "$0"`
  ABSSP=`dirname "$ABSS"`
  unset -v ABSS
fi

TEST_PATH="${ABSSP}"

if [ -d "${SHAREMIND_PATH}/lib" ]; then
  NEW_LD_LIBRARY_PATH="${LD_LIBRARY_PATH}${LD_LIBRARY_PATH:+:}${SHAREMIND_PATH}/lib"
fi

SCC="${SHAREMIND_PATH}/bin/scc"
STDLIB="${SHAREMIND_PATH}/lib/sharemind/stdlib"
EMULATOR="${SHAREMIND_PATH}/bin/Emulator"
TEST_PARSER="${TEST_PATH}/emulatortestparser.py"

compile() {
    local SC="$1"
    local SB="$2"

    LD_LIBRARY_PATH="${NEW_LD_LIBRARY_PATH}" "${SCC}" \
        --include "${TEST_PATH}" --include "${STDLIB}" \
        --input "${SC}" --output "${SB}"
}

run_test() {
    local SB="$1"
    local TEST_NAME="$2"
    local CWD=`pwd`; cd "`dirname ${EMULATOR}`"
    ((LD_LIBRARY_PATH="${NEW_LD_LIBRARY_PATH}" \
            "./`basename ${EMULATOR}`" --conf=emulator.cfg "${CWD}/${SB}" \
                | python "${TEST_PARSER}" \
                | sed "s#^#${TEST_NAME}#g") \
         3>&1 1>&2 2>&3 3>&- | sed "s#^#${TEST_NAME}#g") \
         3>&1 1>&2 2>&3 3>&-
    local RV=$?
    cd "${CWD}"
    return ${RV}
}

run() {
    local SC="$1"
    local TESTSET="$2"
    local SC_BN=`basename "${SC}"`
    local SB_BN="${SC_BN%.sc}.sb"
    local SB=`mktemp sharemind_stlib_runtests.$$.XXXXXXXXXX.sb`
    local RV=$?; if [ $RV -ne 0 ]; then return $RV; fi

    local TEST_NAME="[${SC}]: "
    if [ -n "${TESTSET}" ]; then
        TEST_NAME="[${TESTSET}\/`basename "${SC_BN}"`]: "
    fi

    compile "${SC}" "${SB}" && run_test "${SB}" "${TEST_NAME}"
    local RV=$?
    rm "${SB}"
    return ${RV}
}

run_all() {
    for TESTS in `find "${ABSSP}" -mindepth 1 -maxdepth 1 -type d | sort`; do
        local TESTS_BN=`basename "${TESTS}"`
        for TEST in `find "${TESTS}" -mindepth 1 -maxdepth 1 -type f -name "*.sc" | sort`; do
            run "${TEST}" "${TESTS_BN}"
            local RV=$?; if [ ${RV} -ne 0 ]; then return ${RV}; fi
        done
    done

    return 0
}

if [ "x$1" = "x" ]; then
    run_all
elif [ -f "$1" ]; then
    run "$1"
elif [ -d "$1" ]; then
    for TEST in `find "$1" -mindepth 1 -maxdepth 1 -type f -name "*.sc" | sort`; do
        run "${TEST}" `basename "$1"`
        RV=$?; if [ ${RV} -ne 0 ]; then exit ${RV}; fi
    done
else
    echo "Usage of `basename "$0"`:"
    echo "runtests.sh [filename.sc]"
    echo "If no filename is specified, all tests will be run."
fi
