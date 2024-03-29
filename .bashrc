#!/bin/bash

##############################################################
##
# INSTRUCTIONS (LINUX):
#
# 1. Open a terminal in the current directory and write
#
#       ~$ source .bashrc
#
#    to add `fzn2<solver>.py` scripts to the PATH.
#
# 2. SMT/OMT solvers can be downloaded and manually installed
#    in the `tools` directory if these are not already readily
#    available on the system. Please notice that the name of
#    the binary file of some SMT/OMT solvers might vary
#    depending on its version or the platform, so it might
#    be necessary to update the `binary_filename()` function
#    within some `fzn2<solver>.py` scripts.
#
##
##############################################################

export BASE_DIR=$(pwd)

##############################################################
##
# CHANGE ONLY IF REALLY NECESSARY
##
##############################################################

export PATH_BIN="${BASE_DIR}/bin"
export PATH_BCLT="${BASE_DIR}/tools/bclt"
export PATH_CVC4="${BASE_DIR}/tools/CVC4-1.7"
export PATH_OPTIMATHSAT="${BASE_DIR}/tools/optimathsat-1.7.4-linux-64-bit/bin"
export PATH_Z3="${BASE_DIR}/tools/z3/build"

##############################################################
##
# DO NOT TOUCH
##
##############################################################

function def_colors ()
{
    export GREEN="\\033[1;32m"
    export NORMAL="\\033[0;39m"
    export RED="\\033[1;31m"
    export PINK="\\033[1;35m"
    export BLUE="\\033[1;34m"
    export WHITE="\\033[0;02m"
    export WHITE2="\\033[1;08m"
    export YELLOW="\\033[1;33m"
    export CYAN="\\033[1;36m"
}
def_colors

PATH="${PATH}":"${PATH_BIN}"
PATH="${PATH}":"${PATH_BCLT}"
PATH="${PATH}":"${PATH_CVC4}"
PATH="${PATH}":"${PATH_OPTIMATHSAT}"
PATH="${PATH}":"${PATH_Z3}"
