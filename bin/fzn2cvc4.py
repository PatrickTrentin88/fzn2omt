#!/usr/bin/env python3
#!python

"""
A simple wrapper around CVC4, and a compiler from FlatZinc
to SMT-LIBv2 compatible with CVC4.
"""

import argparse
import io
import mmap
import os
import re
import shutil
import subprocess
import sys
import tempfile
import common
import fzn2optimathsat


############
############
############
### CVC4 ###
############
############
############

# TODO:
# - this does not handle MacOS correctly,
#   it needs further testing.
# - this does not handle older CVC4 versions,
#   something more flexible would be useful.
def binary_filename():
    """Returns the expected filename for CVC4's binary."""
    return 'cvc4-1.7-win64-op.exe' if os.name == 'nt' else \
           'cvc4-1.7-x86_64-linux-opt'


def cvc4(config, solver_config=None):
    """Runs CVC4 with the given configuration."""

    common.exit_if_binary_not_in_path(binary_filename())

    if config.smt2:
        cvc4_compile(config)
    else:
        cvc4_solve(config, solver_config)



########################
########################
### FLATZINC SOLVING ###
########################
########################

def cvc4_solve(config, solver_config=None):
    """Solves a FlatZinc model with CVC4.

    The FlatZinc model is compiled to a SMT-LIBv2
    formula with OptiMathSAT first."""
    assert common.is_binary_in_path(binary_filename())
    assert not config.smt2

    with tempfile.TemporaryDirectory() as tmp_dir:
        config.smt2 = os.path.join(tmp_dir, "formula.smt2")
        config.ovars = os.path.join(tmp_dir, "output_vars.txt")
        output_trace = os.path.join(tmp_dir, "trace.out")

        # 1. generate SMT-LIB + OVARS files
        cvc4_compile(config)

        # 2. parse OVARS skeleton
        oskeleton = common.extract_solution_skeleton(config.ovars)

        # 3. solve
        args = cvc4_solve_cmdline_args(config)
        if solver_config:
            args.extend(solver_config)

        with open(output_trace, "w") as out_f:
            result = subprocess.run(args, text=True, stderr=subprocess.PIPE,
                                    stdout=out_f)

        # 4. display any error
        if result.stderr:
            print(result.stderr, file=sys.stderr, end='')

        # 5. extract status
        status = cvc4_extract_search_status(output_trace)

        # 6. extract model(s)
        models = cvc4_extract_models(output_trace)

        common.print_search_status(config, status, models, oskeleton)


def cvc4_solve_cmdline_args(config):
    """Determines the command-line arguments for the CVC4 call."""
    assert config.smt2

    args = [binary_filename(),
            config.smt2]

    return args

def cvc4_extract_search_status(tracefile):
    """Extracts and returns the search status from the
    given tracefile."""

    ret = common.UNKNOWN

    if not common.is_file_empty(tracefile):

        uns_regex = re.compile(rb"^unsat$", re.MULTILINE)
        sat_regex = re.compile(rb"^sat$", re.MULTILINE)

        with io.open(tracefile, 'r') as fd_trace:
            output = mmap.mmap(fd_trace.fileno(), 0, access=mmap.ACCESS_READ)

            uns_match = re.search(uns_regex, output)
            sat_match = re.search(sat_regex, output)

            assert sum([bool(x) for x in (uns_match, sat_match)]) <= 1

            if sat_match:
                ret = common.SAT
            elif uns_match:
                ret = common.UNSAT
            else:
                ret = common.UNKNOWN

    return ret

def cvc4_extract_models(tracefile):
    """Extract and returns all models contained
    in the given tracefile."""

    models = []

    if not common.is_file_empty(tracefile):
        regex = re.compile((rb"\(define-fun (.*) \(\) "
                            rb"(Int|Bool|Real|\(_ BitVec [0-9]+\))"
                            rb"\n? +(.*)\)"))
        regex_pvt = re.compile(r"^_private_(.*)")

        with io.open(tracefile, 'r') as fd_trace:
            output = mmap.mmap(fd_trace.fileno(), 0, access=mmap.ACCESS_READ)
            model = {}
            for match in re.finditer(regex, output):
                var, stype, value = (x.decode("utf-8") for x in match.groups())

                if "BitVec" in stype:
                    stype = "BitVec"

                var = var.replace('_@_', '|')
                var = var.replace('_@@_', ':')

                if re.match(regex_pvt, var):
                    var = ".{}".format(var[9:])

                if var in model:
                    models.append(model)
                    model = {}

                model[var] = common.smtlib_to_python_type(stype, value)

            if model:
                models.append(model)

    return models



###########################
###########################
### SMT-LIB COMPILATION ###
###########################
###########################

def cvc4_compile(config):
    """Compiles a FlatZinc model in SMT-LIB format."""
    assert common.is_binary_in_path(binary_filename())
    assert config.smt2

    optimathsat_config = argparse.Namespace(**vars(config))
    optimathsat_config.compile_raw = True

    if not hasattr(optimathsat_config, 'ovars'):
        optimathsat_config.ovars = None

    fzn2optimathsat.optimathsat(optimathsat_config)

    make_smtlib_compatible_with_cvc4(config, optimathsat_config)


def make_smtlib_compatible_with_cvc4(config, optimathsat_config): # pylint: disable=R0912
    """Modifies SMT-LIB file with CVC4-specific syntax."""
    if common.is_file_empty(config.smt2):
        return

    tmp_file_name = None

    with io.open(config.smt2, 'rt') as in_f:
        formula = mmap.mmap(in_f.fileno(), 0, access=mmap.ACCESS_READ)

        with tempfile.NamedTemporaryFile(mode="w+t", delete=False) as out_f:
            tmp_file_name = out_f.name

            # Consume first two lines
            out_f.write(formula.readline().decode("utf-8"))
            out_f.write(formula.readline().decode("utf-8"))

            # Print header
            for header_line in common.get_smtlib_header_lines(optimathsat_config,
                                                              "CVC4"):
                out_f.write(header_line)

            # Consume third line
            out_f.write(formula.readline().decode("utf-8"))

            # Print logic
            out_f.write("(set-logic ALL)\n")

            # Print config
            out_f.write("(set-option :produce-models true)\n")
            if config.random_seed:
                out_f.write("(set-option :random-seed {})\n".format(config.random_seed))

            # copy formula, except for minimize/maximize/check-sat
            objectives = []
            for line in iter(formula.readline, b""):
                obj = common.match_objective(line)

                if obj:
                    if config.bv_enc:
                        regex = re.compile(rb" %b \(\) \(_ BitVec ([0-9]+)\)"
                                           % obj.term.encode("utf-8"))
                        match = re.search(regex, formula)
                        if match:
                            obj.bv_width = int(match.group(1))

                    objectives.append(obj)

                elif common.match_check_sat(line):
                    continue
                else:
                    line = line.replace(b'|', b'_@_')
                    line = line.replace(b':', b'_@@_')
                    line = line.replace(b' .', b' _private_')
                    if config.bv_enc:
                        line = line.replace(b'_ to_bv ', b'_ int2bv ')
                        # TODO: handle sbv_to_int
                    out_f.write(line.decode("utf-8"))

            # footer
            for obj in objectives:
                for line in cvc4_objective_to_str(config, obj):
                    out_f.write(line)
            out_f.write("(check-sat)\n")
            out_f.write("(get-model)\n")
            out_f.write("(exit)\n")

    # overwrite raw SMT-LIB file with OptiMathSAT-specific file
    if tmp_file_name:
        shutil.copy(tmp_file_name, config.smt2)


def cvc4_objective_to_str(config, obj):
    """Yields CVC4's command to optimize a goal."""
    if config.ignore_objs:
        direction = "minimize" if obj.minimize else "maximize"
        yield "; objectives are not supported\n"
        yield "; ({} {})\n".format(direction, obj.term)
    else:
        common.eprint("error: objectives are not supported")
        sys.exit(1)



#####################
#####################
### I/O INTERFACE ###
#####################
#####################

def cvc4_parse_cmdline_options():
    """parses and returns input parameters."""
    parser = argparse.ArgumentParser(description=("A tool for solving FlatZinc "
                                                  "problems with CVC4."))

    main_group = parser.add_argument_group("Main Options")

    main_group.add_argument("model", metavar="<model>.fzn",
                            type=argparse.FileType('r'),
                            help="The FlatZinc model",
                            action=common.check_file_ext('fzn'))

    main_group.add_argument("--smt2", "--output-smt2-to-file",
                            metavar="<filename>.smt2",
                            type=argparse.FileType('w'),
                            action=common.check_file_ext('smt2'),
                            help="Filename for the generated SMT-LIB output",
                            default=None)

    ###################
    # ENCODING config #
    ###################

    enc_group = parser.add_argument_group("Encoding Options")

    group = enc_group.add_mutually_exclusive_group()
    group.add_argument("--bv-enc", help="Encode ints with the SMT-LIB Bit-Vector type.",
                       action="store_true", default=False)
    group.add_argument("--int-enc", help="Encode ints with the SMT-LIB Int type.",
                       action="store_true", default=True)

    enc_group.add_argument("--cardinality-networks",
                           help="Enable cardinality networks (when applicable).",
                           action="store_true", default=False)

    enc_group.add_argument("--bv-alldifferent",
                           help="all-different constraints encoded with Bit-Vectors.",
                           action="store_true", default=False)

    enc_group.add_argument("--ignore-objs",
                           help=("Ignore any objective contained in the input "
                                 "FlatZinc problem rather than terminate the "
                                 "execution with an error."),
                           action="store_true", default=False)

    ##################
    # SEARCH config #
    ##################

    search_group = parser.add_argument_group("Search Options")

    # Random Seed
    search_group.add_argument("--random-seed", "-r",
                              help=("Set seed for pseudo-random number generators."),
                              metavar="N", type=int, default=None)

    ##################
    # MODEL PRINTING #
    ##################

    model_group = parser.add_argument_group("Model Options")

    model_group.add_argument("--finite-precision",
                             help=("Print infinite-precision rational numbers "
                                   "as finite precision decimals using the specified "
                                   "precision level. Must be larger or equal 2."),
                             action=common.check_finite_precision(),
                             metavar="prec", type=int, default=None)

    ###################
    # IGNORED config #
    ###################

    ignore_group = parser.add_argument_group("Ignored Options")

    # Ignored config
    ignore_group.add_argument("--free-search", "-f",
                              help=("No need to follow search specification. "
                                    "(CVC4 ignores all search specifications)"),
                              action="store_true", default=True)
    ignore_group.add_argument("--num-threads", "-p",
                              help=("Number of threads. "
                                    "(Requires special CVC4 version)"),
                              metavar="N", type=int, default=1)

    # parse
    config, solver_config = parser.parse_known_args()

    config.int_enc = not config.bv_enc

    if config.finite_precision and \
            config.finite_precision >= 2:
        config.float_fmt = "%.{}g".format(config.finite_precision)
    else:
        config.float_fmt = "%g"

    return config, solver_config



############
############
### MAIN ###
############
############

def main():
    """The main entry point of this program."""
    min_python = (3, 7)
    if sys.version_info < min_python:
        sys.exit("Python %s.%s or later is required.\n" % min_python)

    config, solver_config = cvc4_parse_cmdline_options()

    cvc4(config, solver_config)


if __name__ == "__main__":
    main()
