#!/usr/bin/env python3
#!python

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
    parser.add_argument("--max-solutions", "-n", help="Maximum number of solutions printed.",
                        metavar="N", type=int, default=0)

    # MiniZinc style all solutions
    # If enabled, it overrides --partial-solutions and --all-solutions
    parser.add_argument("--all-solutions-mzn", "-a", help="Print all solutions of the input problem.",
                        action="store_true", default=False)

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
    args.append("-opt.fzn.max_solutions={}".format(known_args.max_solutions))

    if (known_args.all_solutions_mzn):
        if is_optimization_problem(known_args.model):
            args.append("-opt.fzn.all_solutions=False")
            args.append("-opt.fzn.partial_solutions=True")
        else:
            args.append("-opt.fzn.all_solutions=True")
            args.append("-opt.fzn.partial_solutions=False")
    else:
        args.append("-opt.fzn.partial_solutions={}".format(known_args.partial_solutions))
        args.append("-opt.fzn.all_solutions={}".format(known_args.all_solutions))

    args.extend(other_args)
    return args

def is_optimization_problem(fzn_file):
    with open(fzn_file, 'r') as fd:
        fd_mmap = mmap.mmap(fd.fileno(), 0, access=mmap.ACCESS_READ)
        if re.search(b"solve .*satisfy;", fd_mmap) is not None:
            return False
        else:
            return True

def print_config(known_args, target_solver):
    print(";; encoder configuration:")
    print(";;    --int-enc={}".format(known_args.int_enc))
    print(";;    --bv-enc={}".format(known_args.bv_enc))
    print(";;    --bv_alldifferent={}".format(known_args.bv_alldifferent))
    print(";;    --cardinality-networks={}".format(known_args.cardinality_networks))
    print(";; target solver: {}".format(target_solver))
    print(";;")


def mangle_smt2_for_optimathsat(known_args, other_args, is_opt):
    """Modifies SMT-LIB file with OptiMathSAT-specific syntax."""

    with fileinput.input(known_args.smt2, inplace=True) as fd:
        for line in fd:
            if line[1:11] == "set-option":
                print_config(known_args, "optimathsat")
                print(line, end='')
                print("(set-option :produce-models true)")

                if is_opt:
                    priority_list = list(filter(lambda h: len(h) == 3, map(lambda g: g[14:], filter(lambda f: "-opt.priority=" in f, other_args))))
                    if len(priority_list) > 0:
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
    ret = None
    regex = re.compile(r"\((minimize|maximize) ([^:]*?) ?(:signed)? ?(:lower ([^:]*?))? ?(:upper ([^:]*?))?\)$")
    matches = regex.findall(line)
    if len(matches) > 0:
        match = matches[0]
        ret = {
            "minimize" : match[0] == 'minimize',
            "goal"     : match[1],
            "signed"   : match[2] == ':signed',
            "lower"    : match[4] if known_args.solver != "bclt" or match[4] != '' else known_args.bclt_lower,
            "upper"    : match[6] if known_args.solver != "bclt" or match[6] != '' else known_args.bclt_upper,
            "is_bv"    : known_args.bv_enc,
        }
        assert ret["signed"], "error: unexpected unsigned goal."

    return ret


def bclt_print_objective(obj):
    goal = obj["goal"] if obj["minimize"] else "(- {})".format(obj["goal"])
    lower = int(obj["lower"]) if obj["minimize"] else int(obj["upper"]) * -1
    upper = int(obj["upper"]) if obj["minimize"] else int(obj["lower"]) * -1
    if lower < 0:
        lower = "(- {})".format(-1 * lower)
    if upper < 0:
        upper = "(- {})".format(-1 * upper)
    print("(check-omt {} {} {})".format(goal, lower, upper))


def mangle_smt2_for_bclt(known_args, other_args, is_opt):
    """Modifies SMT-LIB file with BCLT-specific syntax."""

    regex = re.compile(b"\((minimize|maximize) (.*?) ?(:signed)? ?(:lower (.*?))? ?(:upper (.*?))?\)")

    num_objectives = 0
    with fileinput.input(known_args.smt2, inplace=True) as fd:
        for line in fd:

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
    if known_args.bv_enc:
        z3_print_bv_objective(obj, decls)
    else:
        z3_print_lira_objective(obj)


def z3_print_lira_objective(obj):
    if len(obj["lower"]) > 0:
        print("(assert (<= {} {}))".format(obj["lower"], obj["goal"]))

    if len(obj["upper"]) > 0:
        print("(assert (<= {} {}))".format(obj["goal"], obj["upper"]))

    if obj["minimize"]:
        print("(minimize {})".format(obj["goal"]))
    else:
        print("(maximize {})".format(obj["goal"]))


def z3_print_bv_objective(obj, decls):
    if obj["goal"] not in decls.keys():
        sys.exit("error: declaration for objective '{}' not found.".format(obj["goal"]))

    nbits = int(re.findall("([0-9]+)", decls[obj["goal"]])[0])
    mask = "#b1" + "0" * (nbits - 1)
    ubv_goal = "(bvor (bvand {} (bvnot {})) (bvand (bvnot {}) {}))".format(mask, obj["goal"], mask, obj["goal"])

    if len(obj["lower"]) > 0:
        print("(assert (bvsle {} {}))".format(obj["lower"], obj["goal"]))

    if len(obj["upper"]) > 0:
        print("(assert (bvsle {} {}))".format(obj["goal"], obj["upper"]))

    if obj["minimize"]:
        print("(minimize {})".format(ubv_goal))
    else:
        print("(maximize {})".format(ubv_goal))


def mangle_smt2_for_z3(known_args, other_args, is_opt):
    """Modifies SMT-LIB file with Z3-specific syntax."""

    regex = re.compile(" (.*?) \(\) (\(_ BitVec [0-9]*\))")

    decls = {}
    with fileinput.input(known_args.smt2, inplace=True) as fd:
        for line in fd:

            # set logic
            if line[1:11] == "set-option":
                # NOTE: the global-decls option generated by MathSAT5 is suppressed
                print_config(known_args, "z3")
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
                    if len(matches) > 0:
                        decls[matches[0][0]] = matches[0][1]

                    print(line, end='')


def optimathsat(known_args, other_args):
    args = get_cmdline_args(known_args, other_args)

    if which("optimathsat") is None:
        sys.exit("error: the binary of `optimathsat' has not been found in the path.")

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
        is_opt = is_optimization_problem(known_args.model)
        if not hasattr(known_args, "solver") or known_args.solver == "optimathsat":
            mangle_smt2_for_optimathsat(known_args, other_args, is_opt)
        elif known_args.solver == "bclt":
            mangle_smt2_for_bclt(known_args, other_args, is_opt)
        elif known_args.solver == "z3":
            mangle_smt2_for_z3(known_args, other_args, is_opt)
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



