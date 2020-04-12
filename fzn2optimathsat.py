#!/usr/bin/env python3
#!python

"""
An simple wrapper around the FlatZinc interface of OptiMathSAT, and
a compiler from FlatZinc to SMT-LIB enriched with OptiMathSAT extensions.
"""

import argparse
import fileinput
import mmap
import os
import re
import subprocess
import sys
from shutil import which

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
                        type=argparse.FileType('w'), action=check_file_ext('smt2'),
                        help="Filename for the generated SMT-LIB output",
                        default=None)

    parser.add_argument("--compile-only", help="Compile only (do not run solver).",
                        action="store_true", default=False)

    ####################
    # ENCODING OPTIONS #
    ####################

    # opt.fzn.bv_integers (false)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--bv-enc", help="Encode ints with the SMT-LIB Bit-Vector type.",
                       action="store_true", default=False)
    group.add_argument("--int-enc", help="Encode ints with the SMT-LIB Int type.",
                       action="store_true", default=True)

    # opt.fzn.asoft_encoding (true)
    parser.add_argument("--cardinality-networks",
                        help="Enable cardinality networks (when applicable).",
                        action="store_true", default=False)


    # opt.fzn.bv_all_different (true)
    parser.add_argument("--bv-alldifferent",
                        help="all-different constraints encoded with Bit-Vectors.",
                        action="store_true", default=False)

    ##################
    # SEARCH OPTIONS #
    ##################

    # Random Seed
    parser.add_argument("--random-seed", "-r",
                        help=("Set seed for pseudo-random number generators."),
                        metavar="N", type=int, default=None)

    # non-linear
    parser.add_argument("--experimental-non-linear", "-e",
                        help=("Activates experimental non-linear support. "
                              "Enabling this option can negatively impact the "
                              "performance."), action="store_true", default=False)

    # opt.fzn.partial_solutions (false)
    parser.add_argument("--partial-solutions",
                        help=("Print any sub-optimal solution satisfying "
                              "the input model."), action="store_true", default=False)

    # opt.fzn.all_solutions (false)
    parser.add_argument("--all-solutions-opt",
                        help=("Print all solutions of the input problem. "
                              "If this is an optimization problem, it prints all "
                              "solutions with the same optimal value."),
                        action="store_true", default=False)

    # MiniZinc style all solutions
    parser.add_argument("--all-solutions", "-a",
                        help=("Print all solutions of the input problem. "
                              "With satisfaction problems, it enables "
                              "'--all-solutions-opt'. With optimization "
                              "problems, it enables '--partial-solutions'."),
                        action="store_true", default=False)

    # opt.fzn.max_solutions (0)
    parser.add_argument("--max-solutions", "-n",
                        help="Maximum number of solutions printed.",
                        metavar="N", type=int, default=0)

    ##################
    # MODEL PRINTING #
    ##################

    # opt.fzn.finite_precision_model (false)
    # opt.fzn.finite_precision (32)
    parser.add_argument("--finite-precision",
                        help=("Print infinite-precision rational numbers "
                              "as finite precision decimals using the specified "
                              "precision level. Must be larger or equal 2."),
                        action=check_finite_precision(),
                        metavar="prec", type=int, default=None)

    ###################
    # IGNORED OPTIONS #
    ###################

    # Ignored Options
    parser.add_argument("--free-search", "-f",
                        help=("No need to follow search specification. "
                              "(OptiMathSAT always ignores all search specifications)"),
                        action="store_true", default=True)
    parser.add_argument("--num-threads", "-p",
                        help=("Number of threads. (OptiMathSAT can use only one thread)"),
                        metavar="N", type=int, default=1)

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


def check_finite_precision():
    """Checks that the argument finite precision matches the given restriction."""
    class Act(argparse.Action): # pylint: disable=too-few-public-methods
        """Act."""
        def __call__(self, parser, namespace, value, option_string=None):
            """Check that the argument finite precision matches the given restriction."""
            if value < 2:
                option_string = '({})'.format(option_string) if option_string else ''
                parser.error("minimum finite precision is 2 {}".format(option_string))
            else:
                setattr(namespace, self.dest, value)
    return Act


###
###
###

def get_cmdline_args(known_args, other_args):
    """Determines the command-line arguments for the optimathsat call."""
    args = ["optimathsat", "-input=fzn", known_args.model]

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
    args.append("-opt.fzn.max_solutions={}".format(known_args.max_solutions))

    if known_args.all_solutions:
        if is_optimization_problem(known_args.model):
            known_args.partial_solutions = True
        else:
            known_args.all_solutions_opt = True

    args.append("-opt.fzn.all_solutions={}".format(known_args.all_solutions_opt))
    args.append("-opt.fzn.partial_solutions={}".format(known_args.partial_solutions))

    if known_args.finite_precision:
        args.append("-opt.fzn.finite_precision_model=True")
        args.append("-opt.fzn.finite_precision={}".format(known_args.finite_precision))

    if known_args.experimental_non_linear:
        args.append("-preprocessor.toplevel_propagation=False")

    if known_args.random_seed:
        args.append("-random_seed={}".format(known_args.random_seed))

    args.extend(other_args)
    return args


def is_optimization_problem(fzn_file):
    """Checks whether the FlatZinc problem contains an optimization goal."""
    with open(fzn_file, 'r') as fd_fzn:
        fd_mmap = mmap.mmap(fd_fzn.fileno(), 0, access=mmap.ACCESS_READ)
        return re.search(b"solve .*satisfy;", fd_mmap) is None


def print_config(known_args, target_solver):
    """Prints the compiler configuration used to generate an
    SMT-LIB formula."""
    print(";; encoder configuration:")
    print(";;    --int-enc={}".format(known_args.int_enc))
    print(";;    --bv-enc={}".format(known_args.bv_enc))
    print(";;    --bv_alldifferent={}".format(known_args.bv_alldifferent))
    print(";;    --cardinality-networks={}".format(known_args.cardinality_networks))
    print(";; target solver: {}".format(target_solver))
    print(";;")


def mangle_smt2_for_optimathsat(known_args, other_args, is_opt):
    """Modifies SMT-LIB file with OptiMathSAT-specific syntax."""

    with fileinput.input(known_args.smt2, inplace=True) as fd_smt2:
        for line in fd_smt2:
            if line[1:11] == "set-option":
                print_config(known_args, "optimathsat")
                print(line, end='')
                print("(set-option :produce-models true)")

                if is_opt:
                    priority_list = list(filter(lambda h: len(h) == 3,
                                                map(lambda g: g[14:],
                                                    filter(lambda f: "-opt.priority="
                                                           in f, other_args))))
                    if priority_list:
                        priority = priority_list[-1]
                        print("(set-option :opt.priority {})".format(priority))
                        print("(set-option :config opt.par.mode=callback)")
                    print("(set-option :config opt.print_objectives=true)")


            elif line[1:10] == "check-sat":
                print(line, end='')
                if is_opt:
                    print("(get-objectives)")
                print("(get-model)")
                print("(exit)")

            else:
                # print line
                print(line, end='')


def get_objective(known_args, line):
    """Collects information about an optimization goal
    declaration in SMT-LIB enriched with OptiMathSAT
    optimization extensions."""
    ret = None
    regex = re.compile((r"\((minimize|maximize) ([^:]*?) ?(:signed)? ?"
                        r"(:lower ([^:]*?))? ?(:upper ([^:]*?))?\)$"))
    matches = regex.findall(line)
    if matches:
        match = matches[0]
        ret = {
            "minimize" : match[0] == 'minimize',
            "goal"     : match[1],
            "signed"   : match[2] == ':signed',
            "lower"    : match[4] if known_args.solver != "bclt" or match[4] != ''
                         else known_args.bclt_lower,
            "upper"    : match[6] if known_args.solver != "bclt" or match[6] != ''
                         else known_args.bclt_upper,
            "is_bv"    : known_args.bv_enc,
        }
        assert ret["signed"], "error: unexpected unsigned goal."

    return ret


def bclt_print_objective(obj):
    """Print an optimization goal using the syntax of Barcelogic."""
    goal = obj["goal"] if obj["minimize"] else "(- {})".format(obj["goal"])
    lower = int(obj["lower"]) if obj["minimize"] else int(obj["upper"]) * -1
    upper = int(obj["upper"]) if obj["minimize"] else int(obj["lower"]) * -1
    if lower < 0:
        lower = "(- {})".format(-1 * lower)
    if upper < 0:
        upper = "(- {})".format(-1 * upper)
    print("(check-omt {} {} {})".format(goal, lower, upper))


def mangle_smt2_for_bclt(known_args, other_args, is_opt): # pylint: disable=unused-argument
    """Modifies SMT-LIB file with BCLT-specific syntax."""

    num_objectives = 0
    with fileinput.input(known_args.smt2, inplace=True) as fd_smt2:
        for line in fd_smt2:

            # set logic
            if line[1:11] == "set-option":
                # NOTE: the global-decls option generated by MathSAT5 is suppressed
                print_config(known_args, "bclt")
                print("(set-logic QF_LIRA)")
                print("(set-option :produce-models true)")

            # delete (check-sat) if optimization problem
            elif line[1:10] == "check-sat":
                if not is_opt:
                    print(line, end="")
                print("(get-model)")
                print("(exit)")

            # print objectives
            else:
                obj = get_objective(known_args, line)
                if obj:
                    bclt_print_objective(obj)
                    num_objectives += 1

                # else: print line
                else:
                    # NOTE:
                    # - to_int is unsupported in bclt
                    # - MathSAT5 uses to_int even when unecessary, e.g.
                    #       (to_int 5.0)
                    #   instead of
                    #       5
                    # => to_int is_replaced with a dummy expression
                    line.replace("(to_int ", "(+ 0 ")
                    print(line, end='')

    if num_objectives > 1:
        raise Exception("bclt cannot handle multi-objective OMT problems.")


def z3_print_objective(known_args, obj, decls):
    """Print an optimization goal using the syntax of Z3."""
    if known_args.bv_enc:
        z3_print_bv_objective(obj, decls)
    else:
        z3_print_lira_objective(obj)


def z3_print_lira_objective(obj):
    """Print a LIRA optimization goal using the syntax of Z3."""
    if obj["lower"]:
        print("(assert (<= {} {}))".format(obj["lower"], obj["goal"]))

    if obj["upper"]:
        print("(assert (<= {} {}))".format(obj["goal"], obj["upper"]))

    if obj["minimize"]:
        print("(minimize {})".format(obj["goal"]))
    else:
        print("(maximize {})".format(obj["goal"]))


def z3_print_bv_objective(obj, decls):
    """Print a BV optimization goal using the syntax of Z3."""
    if obj["goal"] not in decls.keys():
        sys.exit("error: declaration for objective '{}' not found.".format(obj["goal"]))

    nbits = int(re.findall("([0-9]+)", decls[obj["goal"]])[0])
    mask = "#b1" + "0" * (nbits - 1)
    ubv_goal = "(bvor (bvand {0} (bvnot {1})) (bvand (bvnot {0}) {1}))".format(
                mask, obj["goal"])

    if obj["lower"]:
        print("(assert (bvsle {} {}))".format(obj["lower"], obj["goal"]))

    if obj["upper"]:
        print("(assert (bvsle {} {}))".format(obj["goal"], obj["upper"]))

    if obj["minimize"]:
        print("(minimize {})".format(ubv_goal))
    else:
        print("(maximize {})".format(ubv_goal))


def mangle_smt2_for_z3(known_args, other_args, is_opt): # pylint: disable=unused-argument
    """Modifies SMT-LIB file with Z3-specific syntax."""

    regex = re.compile(r" (.*?) \(\) (\(_ BitVec [0-9]*\))")

    decls = {}
    with fileinput.input(known_args.smt2, inplace=True) as fd_smt2:
        for line in fd_smt2:

            # set logic
            if line[1:11] == "set-option":
                # NOTE: the global-decls option generated by MathSAT5 is suppressed
                print_config(known_args, "z3")
                if known_args.bv_enc:
                    print("(set-logic QF_BV)")
                else:
                    print("(set-logic QF_LIRA)")
                print("(set-option :produce-models true)")
                if known_args.bv_enc:
                    print("(set-option :pp.bv-literals false)")

            # delete (check-sat) if optimization problem
            elif line[1:10] == "check-sat":
                print(line, end='')
                if is_opt:
                    print("(get-objectives)")
                print("(get-model)")
                print("(exit)")

            # print objectives
            else:
                obj = get_objective(known_args, line)
                if obj:
                    z3_print_objective(known_args, obj, decls)

                # else: print line
                else:
                    matches = regex.findall(line)
                    if matches:
                        decls[matches[0][0]] = matches[0][1]

                    print(line, end='')


def mangle_smt2_for_cvc4(known_args, other_args, is_opt): # pylint: disable=unused-argument
    """Modifies SMT-LIB file with cvc4-specific syntax."""

    with fileinput.input(known_args.smt2, inplace=True) as fd_smt2:
        for line in fd_smt2:

            # set logic
            if line[1:11] == "set-option":
                # NOTE: the global-decls option generated by MathSAT5 is suppressed
                print_config(known_args, "cvc4")
                if known_args.bv_enc:
                    print("(set-logic QF_BV)")
                else:
                    print("(set-logic QF_LIRA)")
                print("(set-option :produce-models true)")

            # get model
            elif line[1:10] == "check-sat":
                print(line, end='')
                print("(get-model)")
                print("(exit)")

            # print objectives as comments
            else:
                obj = get_objective(known_args, line)
                if obj:
                    line = line.replace(".", "private_var_")
                    print("; {}".format(line), end='')

                # else: print line
                else:
                    line = line.replace(".", "private_var_")
                    print(line, end='')


def optimathsat(known_args, other_args):
    """Calls OptiMathSAT."""
    args = get_cmdline_args(known_args, other_args)

    if which("optimathsat") is None:
        sys.exit("error: the binary of `optimathsat' has not been found in the path.")

    if known_args.compile_only:
        result = subprocess.run(args, capture_output=True, text=True)

        # print stderr
        if result.stderr:
            print(result.stderr, end='')

    else:
        subprocess.run(args, text=True)

    # apply minor changes to SMT-LIB file
    if known_args.smt2:
        is_opt = is_optimization_problem(known_args.model)
        if not hasattr(known_args, "solver") or known_args.solver == "optimathsat":
            mangle_smt2_for_optimathsat(known_args, other_args, is_opt)
        elif known_args.solver == "bclt":
            mangle_smt2_for_bclt(known_args, other_args, is_opt)
        elif known_args.solver == "z3":
            mangle_smt2_for_z3(known_args, other_args, is_opt)
        elif known_args.solver == "cvc4":
            if is_opt:
                print("warning: optimization problems are not "
                      "supported by cvc4.", file=sys.stderr)
            mangle_smt2_for_cvc4(known_args, other_args, is_opt)
        else:
            sys.exit("error: unsupported solver '{}'.".format(known_args.solver))



###
###
###

if __name__ == "__main__":
    MIN_PYTHON = (3, 5)
    if sys.version_info < MIN_PYTHON:
        sys.exit("Python %s.%s or later is required.\n" % MIN_PYTHON)

    main()
