#!/usr/bin/env python3
#!python

import argparse
import fileinput
import os
import subprocess
import sys

###
### MAIN
###

def main():
    """The main executable."""
    known_args, other_args = get_cmdline_options()

    optimathsat(known_args, other_args)


###
### COMMAND-LINE PARSING
###

def get_cmdline_options():
    """parses and returns input parameters."""
    parser = argparse.ArgumentParser(description="A simple wrapper around OptiMathSAT.")

    parser.add_argument("model", metavar="<model>.fzn", type=argparse.FileType('r'),
                        help="The FlatZinc model", action=check_file_ext('fzn'))

    parser.add_argument("--smt2", "--output-smt2-to-file", metavar="<file>.smt2",
                        type=argparse.FileType('w'), help="Filename for the generated SMT-LIB output",
                        default=None, action=check_file_ext('smt2'))

    parser.add_argument("--compile-only", help="Compile only (do not run solver).",
                        action="store_true", default=False)

    # opt.fzn.bv_integers (false)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--bv-enc", help="Encode ints with the SMT-LIB Bit-Vector type.",
                        action="store_true", default=False)
    group.add_argument("--int-enc", help="Encode ints with the SMT-LIB Int type.",
                        action="store_true", default=True)

    # opt.fzn.asoft_encoding (true)
    parser.add_argument("--cardinality-networks", help="Enable cardinality networks (when applicable).",
                        action="store_true", default=False)


    # opt.fzn.bv_all_different (true)
    parser.add_argument("--bv-alldifferent", help="all-different constraints encoded with Bit-Vectors.",
                        action="store_true", default=False)

    # opt.fzn.partial_solutions (false)
    parser.add_argument("--partial-solutions", help="Print any sub-optimal solution satisfying the input model.",
                        action="store_true", default=False)

    # opt.fzn.all_solutions (false)
    parser.add_argument("--all-solutions", help="Print all solutions of the input problem. If this is an optimization problem, it prints all solutions with the same optimal value.",
                        action="store_true", default=False)

    # opt.fzn.max_solutions (0)
    parser.add_argument("--max-solutions", help="Maximum number of solutions printed.",
                        metavar="N", type=int, default=0)

    # parse
    known_args, other_args = parser.parse_known_args()

    # extra dependency rules
    if (known_args.compile_only and not known_args.smt2):
        parser.error("--compile-only requires --smt2.")

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
    args = ["optimathsat", "-input=fzn", known_args.model ]

    if known_args.smt2:
        args.extend(["-debug.api_call_trace=1",
                     "-debug.api_call_trace_dump_config=False",
                     "-debug.api_call_trace_filename={}".format(known_args.smt2)])
        if known_args.compile_only:
            args.append("-debug.solver_enabled=False")

    if known_args.bv_enc:
        args.append("-opt.fzn.bv_integers=True")
    else:
        # NOTE: use --int-enc by default
        args.append("-opt.fzn.bv_integers=False")

    args.append("-opt.fzn.asoft_encoding={}".format(known_args.cardinality_networks))
    args.append("-opt.fzn.bv_all_different={}".format(known_args.bv_alldifferent))
    args.append("-opt.fzn.partial_solutions={}".format(known_args.partial_solutions))
    args.append("-opt.fzn.all_solutions={}".format(known_args.all_solutions))
    args.append("-opt.fzn.max_solutions={}".format(known_args.max_solutions))

    args.extend(other_args)
    return args


def mangle_smt2_basic(smt2_file, other_args):
    """Extends SMT-LIB file with nice-to-have hooks."""

    with fileinput.input(smt2_file, inplace=True) as fd:
        for line in fd:
            if "set-option" in line:
                # (set-option:opt.priority ...)
                priority_list = list(filter(lambda h: len(h) == 3, map(lambda g: g[14:], filter(lambda f: "-opt.priority=" in f, other_args))))
                if len(priority_list) > 0:
                    priority = priority_list[-1]
                    print("(set-option:opt.priority {})".format(priority))

                # (set-option:produce-models true)
                print("(set-option:produce-models true)")

            # print line
            print(line, end='')

    with open(smt2_file, "a+") as f:
        f.write("(get-objectives)\n")
        f.write("(get-model)\n")


def optimathsat(known_args, other_args):
    args = get_cmdline_args(known_args, other_args)

    result = subprocess.run(args, capture_output=True, text=True)

    # print stdout
    if not known_args.compile_only:
        if len(result.stdout) > 0:
            print(result.stdout, end='')

    # print stderr
    if len(result.stderr) > 0:
        print(result.stderr, end='')

    # apply minor changes to SMT-LIB file
    if known_args.smt2:
        mangle_smt2_basic(known_args.smt2, other_args)


###
###
###

if __name__ == "__main__":
    MIN_PYTHON = (3, 5)
    if sys.version_info < MIN_PYTHON:
        sys.exit("Python %s.%s or later is required.\n" % MIN_PYTHON)

    main()



