#!/usr/bin/env python3
#!python
# pylint: disable=C0103

"""
A simple wrapper around Barcelogic, and a compiler from FlatZinc
to SMT-LIBv2 enriched with Barcelogic optimization extensions.

NOTE(s):
- Barcelogic may incorrectly return `unsat' on some optimization
  problems if they contain any non-linear arithmetic constraint,
  because it does not support OMT(NIRA).
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

##################
##################
##################
### BARCELOGIC ###
##################
##################
##################

def binary_filename():
    """Returns the expected filename for Barcelogic's binary."""
    return "bclt"


def barcelogic(config, solver_config=None):
    """Runs Barcelogic with the given configuration."""

    common.exit_if_binary_not_in_path(binary_filename())

    if config.smt2:
        barcelogic_compile(config)
    else:
        barcelogic_solve(config, solver_config)



########################
########################
### FLATZINC SOLVING ###
########################
########################

def barcelogic_solve(config, solver_config=None):
    """Solves a FlatZinc model with Barcelogic.

    The FlatZinc model is compiled to a SMT-LIBv2
    formula with OptiMathSAT first."""
    assert common.is_binary_in_path(binary_filename())
    assert not config.smt2

    with tempfile.TemporaryDirectory() as tmp_dir:
        config.smt2 = os.path.join(tmp_dir, "formula.smt2")
        config.ovars = os.path.join(tmp_dir, "output_vars.txt")
        output_trace = os.path.join(tmp_dir, "trace.out")

        # 1. generate SMT-LIB + OVARS files
        barcelogic_compile(config)

        # 2. parse OVARS skeleton
        oskeleton = common.extract_solution_skeleton(config.ovars)

        # 3. solve
        args = barcelogic_solve_cmdline_args(config)
        if solver_config:
            args.extend(solver_config)

        with open(output_trace, "w") as out_f:
            result = subprocess.run(args, text=True, stderr=subprocess.PIPE,
                                    stdout=out_f)

            # 4. display any error
            if result.returncode not in [1, 10] or result.stderr:
                print(result.stderr, file=sys.stderr, end='')
                with open(output_trace, "r") as in_f:
                    print(in_f.read(), file=sys.stderr, end='')
                sys.exit(1)

        # 5. extract status
        status = barcelogic_extract_search_status(output_trace)

        # 6. extract model(s)
        models = barcelogic_extract_models(output_trace)

        # 7. print status + model(s)
        is_opt_problem = common.is_optimization_problem(config.model)
        common.print_search_status(config, status, models, oskeleton, is_opt_problem)


def barcelogic_solve_cmdline_args(config):
    """Determines the command-line arguments for the barcelogic call."""
    assert config.smt2

    args = [binary_filename(),
            "-file",
            config.smt2,
            "-success",
            "false"]

    return args

def barcelogic_extract_search_status(tracefile):
    """Extracts and returns the search status from the
    given tracefile."""

    ret = common.UNKNOWN

    if not common.is_file_empty(tracefile):

        uns_regex = re.compile(rb"^unsat$", re.MULTILINE)
        sat_regex = re.compile(rb"^sat$", re.MULTILINE)
        opt_regex = re.compile(rb"^\(optimal .*\)$", re.MULTILINE)

        with io.open(tracefile, 'r') as fd_trace:
            output = mmap.mmap(fd_trace.fileno(), 0, access=mmap.ACCESS_READ)

            uns_match = re.search(uns_regex, output)
            sat_match = re.search(sat_regex, output)
            opt_match = re.search(opt_regex, output)

            # NOTE: in Barcelogic, this may be violated if the optimization
            # search interval is unsatisfiable for one optimization goal but
            # satisfiable for another (requires multi-objective optimization).
            # Currently, we do not handle this corner case. Report any violation.
            assert sum([bool(x) for x in (uns_match, sat_match, opt_match)]) <= 1

            if any((sat_match, opt_match)):
                ret = common.SAT
            elif uns_match:
                ret = common.UNSAT
            else:
                ret = common.UNKNOWN

    return ret

def barcelogic_extract_models(tracefile):
    """Extract and returns all models contained
    in the given tracefile."""

    regex = re.compile(rb"\( define-fun (.*) \( \) (Int|Bool|Real) (.*) \)")

    models = []

    if not common.is_file_empty(tracefile):
        with io.open(tracefile, 'r') as fd_trace:
            output = mmap.mmap(fd_trace.fileno(), 0, access=mmap.ACCESS_READ)
            model = {}
            for match in re.finditer(regex, output):
                var, stype, value = (x.decode("utf-8") for x in match.groups())

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

def barcelogic_compile(config):
    """Compiles a FlatZinc model in SMT-LIB format."""
    assert common.is_binary_in_path(binary_filename())
    assert config.smt2

    optimathsat_config = argparse.Namespace(**vars(config))
    optimathsat_config.int_enc = True
    optimathsat_config.bv_enc = False
    optimathsat_config.compile_raw = True

    if not hasattr(optimathsat_config, 'ovars'):
        optimathsat_config.ovars = None

    fzn2optimathsat.optimathsat(optimathsat_config)

    make_smtlib_compatible_with_barcelogic(config, optimathsat_config)


def make_smtlib_compatible_with_barcelogic(config, optimathsat_config):
    """Modifies SMT-LIB file with Barcelogic-specific syntax."""
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
                                                              "bclt"):
                out_f.write(header_line)

            # Consume third line
            out_f.write(formula.readline().decode("utf-8"))

            # Print logic
            out_f.write("(set-logic ALL)\n")

            # Print config
            if config.random_seed:
                out_f.write("(set-option :random-seed {})\n".format(config.random_seed))

            # copy formula, except for minimize/maximize/check-sat
            objectives = []
            for line in iter(formula.readline, b""):
                obj = common.match_objective(line)
                if obj:
                    objectives.append(obj)
                elif common.match_check_sat(line):
                    continue
                else:
                    line = barcelogic_suppress_to_int(line)
                    out_f.write(line.decode("utf-8"))

            # footer
            if objectives:
                for obj in objectives:
                    for line in barcelogic_objective_to_str(config, obj):
                        out_f.write(line)
                    out_f.write("(get-model)\n")
                out_f.write("(exit)\n")
            else:
                out_f.write("(check-sat)\n")
                out_f.write("(get-model)\n")
                out_f.write("(exit)\n")

    # overwrite raw SMT-LIB file with OptiMathSAT-specific file
    if tmp_file_name:
        shutil.copy(tmp_file_name, config.smt2)


def barcelogic_suppress_to_int(bline):
    """Replaces (to_int ...) with (+ 0 ...).

    Barcelogic does not support (to_int ...).
    MathSAT5 uses (to_int ...) even when it is not
    necessary (e.g. (to_int 5.0))."""
    return bline.replace(b"(to_int ", b"(+ 0 ")


def barcelogic_objective_to_str(config, obj):
    """Returns the Print an optimization goal using the syntax of Barcelogic."""
    goal = obj.term if obj.minimize else "(- {})".format(obj.term)
    lower = int(config.bclt_lower) if obj.minimize else int(config.bclt_upper) * -1
    upper = int(config.bclt_upper) if obj.minimize else int(config.bclt_lower) * -1
    if lower < 0:
        lower = "(- {})".format(-1 * lower)
    if upper < 0:
        upper = "(- {})".format(-1 * upper)
    yield "(check-omt {} {} {})\n".format(goal, lower, upper)



#####################
#####################
### I/O INTERFACE ###
#####################
#####################

def barcelogic_parse_cmdline_options():
    """parses and returns input parameters."""
    parser = argparse.ArgumentParser(description=("A tool for solving FlatZinc "
                                                  "problems with Barcelogic."),
                                     formatter_class=argparse.ArgumentDefaultsHelpFormatter)

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

    enc_group.add_argument("--cardinality-networks",
                           help="Enable cardinality networks (when applicable).",
                           action="store_true", default=False)

    # bclt bounds
    enc_group.add_argument("--bclt-lower",
                           help=("Set the default lower-bound for any objective when "
                                 "using Barcelogic."), default="-1000000000")
    enc_group.add_argument("--bclt-upper",
                           help=("Set the default upper-bound for any objective when "
                                 "using Barcelogic."), default="1000000000")

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
                                    "(Barcelogic ignores all search "
                                    "specifications)"),
                              action="store_true", default=True)
    ignore_group.add_argument("--num-threads", "-p",
                              help=("Number of threads. "
                                    "(Barcelogic is single threaded)"),
                              metavar="N", type=int, default=1)

    # parse
    config, solver_config = parser.parse_known_args()

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

    config, solver_config = barcelogic_parse_cmdline_options()

    barcelogic(config, solver_config)


if __name__ == "__main__":
    main()
