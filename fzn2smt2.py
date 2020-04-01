#!/usr/bin/env python3
#!python

import argparse
import os
import sys
import fzn2optimathsat


###
### MAIN
###


def main():
    """The main executable."""
    known_args, other_args = get_cmdline_options()

    fzn2smt2(known_args, other_args)


###
### COMMAND-LINE PARSING
###


def get_cmdline_options():
    """parses and returns input parameters."""
    parser = argparse.ArgumentParser(description="A FlatZinc compiler to SMT-LIBv2 with OMT extensions.")

    main_group = parser.add_argument_group("Main Options")

    main_group.add_argument("model", metavar="<model>.fzn", type=argparse.FileType('r'),
                        help="The FlatZinc model", action=check_file_ext('fzn'))

    main_group.add_argument("--smt2", metavar="<file>.smt2",
                        type=argparse.FileType('w'), help="Filename for the generated SMT-LIB output",
                        default=None, action=check_file_ext('smt2'))

    main_group.add_argument("--solver", choices=["bclt", "optimathsat", "z3"],
                            help="The SMT-LIB output must be compatible with the target OMT solver.",
                            default="optimathsat")

    enc_group = parser.add_argument_group("Encoding Options")
    # opt.fzn.bv_integers (false)
    group = enc_group.add_mutually_exclusive_group()
    group.add_argument("--bv-enc", help="Encode ints with the SMT-LIB Bit-Vector type.",
                        action="store_true", default=False)
    group.add_argument("--int-enc", help="Encode ints with the SMT-LIB Int type.",
                        action="store_true", default=True)

    # opt.fzn.asoft_encoding (true)
    enc_group.add_argument("--cardinality-networks", help="Enable cardinality networks (when applicable).",
                        action="store_true", default=False)

    # opt.fzn.bv_all_different (true)
    enc_group.add_argument("--bv-alldifferent", help="all-different constraints encoded with Bit-Vectors.",
                        action="store_true", default=False)

    # bclt bounds
    enc_group.add_argument("--bclt-lower", help="Set the default lower-bound for any objective when using the bclt solver.",
                           default="-1000000000")
    enc_group.add_argument("--bclt-upper", help="Set the default upper-bound for any objective when using the bclt solver",
                           default="1000000000")

    # parse
    known_args, other_args = parser.parse_known_args()

    if not known_args.smt2:
        known_args.smt2 = "{}.smt2".format(os.path.splitext(known_args.model)[0])

    # extra dependency rules
    if (known_args.bv_enc and known_args.solver == "bclt"):
        parser.error("bclt does not support BV optimization.")

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


def fzn2smt2(known_args, other_args):

    # Generate SMT-LIB file
    known_args.compile_only=True
    known_args.partial_solutions=False
    known_args.all_solutions=False
    known_args.all_solutions_opt=False
    known_args.max_solutions=0
    known_args.random_seed=None
    known_args.experimental_non_linear=False
    known_args.finite_precision=None
    fzn2optimathsat.optimathsat(known_args, other_args)


###
###
###


if __name__ == "__main__":
    MIN_PYTHON = (3, 5)
    if sys.version_info < MIN_PYTHON:
        sys.exit("Python %s.%s or later is required.\n" % MIN_PYTHON)

    main()



