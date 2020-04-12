#!/usr/bin/env python3
#!python

"""
A compiler from FlatZinc to SMT-LIB enriched with cvc4 optimization extensions.
"""

import argparse
import os
import subprocess
import sys
from shutil import which
import fzn2smt2

###
### MAIN
###


def main():
    """The main executable."""
    known_args, other_args = get_cmdline_options()

    run_cvc4(known_args, other_args)


###
### COMMAND-LINE PARSING
###


def get_cmdline_options():
    """parses and returns input parameters."""
    parser = argparse.ArgumentParser(description=("A tool for solving FlatZinc "
                                                  "problems with cvc4."))

    main_group = parser.add_argument_group("Main Options")

    main_group.add_argument("model", metavar="<model>.fzn", type=argparse.FileType('r'),
                            help="The FlatZinc model", action=check_file_ext('fzn'))

    enc_group = parser.add_argument_group("Encoding Options")
    # opt.fzn.bv_integers (false)
    group = enc_group.add_mutually_exclusive_group()
    group.add_argument("--bv-enc", help="Encode ints with the SMT-LIB Bit-Vector type.",
                       action="store_true", default=False)
    group.add_argument("--int-enc", help="Encode ints with the SMT-LIB Int type.",
                       action="store_true", default=True)

    # opt.fzn.asoft_encoding (true)
    enc_group.add_argument("--cardinality-networks",
                           help="Enable cardinality networks (when applicable).",
                           action="store_true", default=False)

    # opt.fzn.bv_all_different (true)
    enc_group.add_argument("--bv-alldifferent",
                           help="all-different constraints encoded with Bit-Vectors.",
                           action="store_true", default=False)

    # parse
    known_args, other_args = parser.parse_known_args()

    known_args.solver = "cvc4"
    known_args.smt2 = "{}.cvc4.smt2".format(os.path.splitext(known_args.model)[0])

    return known_args, other_args


def check_file_ext(extension):
    """Checks that the argument extension matches the given extension."""
    class Act(argparse.Action): # pylint: disable=too-few-public-methods
        """Act."""
        def __call__(self, parser, namespace, file, option_string=None):
            """Check that the argument extension matches the given extension"""
            ext = os.path.splitext(file.name)[1][1:]
            if ext != extension:
                option_string = '({})'.format(option_string) if option_string else ''
                parser.error("file doesn't end with `{}' {}".format(extension, option_string))
            else:
                setattr(namespace, self.dest, file.name)
    return Act


###
###
###


def get_cmdline_args(known_args, other_args):
    """Determines the command-line arguments for the optimathsat call."""
    args = ["cvc4", known_args.smt2]

    args.extend(other_args)
    return args


def run_cvc4(known_args, other_args):
    """Calls cvc4."""

    if which("cvc4") is None:
        sys.exit("error: the binary of `cvc4' has not been found in the path.")

    # Generate SMT-LIB file
    fzn2smt2.fzn2smt2(known_args, [])

    args = get_cmdline_args(known_args, other_args)

    subprocess.run(args, text=True)



###
###
###


if __name__ == "__main__":
    MIN_PYTHON = (3, 5)
    if sys.version_info < MIN_PYTHON:
        sys.exit("Python %s.%s or later is required.\n" % MIN_PYTHON)

    main()
