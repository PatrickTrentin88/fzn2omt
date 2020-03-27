#!/usr/bin/env python3
#!python

import argparse
import fzn2smt2
import os
import subprocess
import sys
from shutil import which

###
### MAIN
###


def main():
    """The main executable."""
    known_args, other_args = get_cmdline_options()

    run_bclt(known_args, other_args)


###
### COMMAND-LINE PARSING
###


def get_cmdline_options():
    """parses and returns input parameters."""
    parser = argparse.ArgumentParser(description="A tool for solving FlatZinc problems with bclt.")

    main_group = parser.add_argument_group("Main Options")

    main_group.add_argument("model", metavar="<model>.fzn", type=argparse.FileType('r'),
                        help="The FlatZinc model", action=check_file_ext('fzn'))

    main_group.add_argument("--success", help="Print success as response to commands",
                        action="store_true", default=False)

    enc_group = parser.add_argument_group("Encoding Options")

    # opt.fzn.asoft_encoding (true)
    enc_group.add_argument("--cardinality-networks", help="Enable cardinality networks (when applicable).",
                        action="store_true", default=False)

    # bclt bounds
    enc_group.add_argument("--bclt-lower", help="Set the default lower-bound for any objective when using the bclt solver.",
                           default="-1000000000")
    enc_group.add_argument("--bclt-upper", help="Set the default upper-bound for any objective when using the bclt solver",
                           default="1000000000")

    # parse
    known_args, other_args = parser.parse_known_args()

    known_args.solver = "bclt"
    known_args.bv_enc = False
    known_args.int_enc = True
    known_args.bv_alldifferent = False
    known_args.smt2 = "{}.smt2".format(os.path.splitext(known_args.model)[0])

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
    args = ["bclt", "-file", known_args.smt2 ]

    if not known_args.success:
        args.extend(["-success", "false"])

    args.extend(other_args)
    return args


def run_bclt(known_args, other_args):

    if which("bclt") is None:
        sys.exit("error: the binary of `bclt' has not been found in the path.")

    # Generate SMT-LIB file
    fzn2smt2.fzn2smt2(known_args, other_args)

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



