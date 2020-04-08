# DESCRIPTION

Python scripts to solve FlatZinc models with Optimization Modulo Theories solvers
like, e.g., [Barcelogic](https://barcelogic.com/),
[OptiMathSAT](http://optimathsat.disi.unitn.it/) and
[z3](https://github.com/Z3Prover/z3).

The FlatZinc model can be generated using the standard
[minizinc](https://www.minizinc.org/)
compiler or the customized
[**emzn2fzn**](https://github.com/PatrickTrentin88/emzn2fzn)
compiler for 
[OptiMathSAT](http://optimathsat.disi.unitn.it/).


# Functionality

- All tools support the encoding based on the `QF_LIRA` logic
  (option `--int-enc`).
  Both [OptiMathSAT](http://optimathsat.disi.unitn.it/) and
  [z3](https://github.com/Z3Prover/z3) support also the encoding
  based on the `QF_BV` logic (option `--bv-enc`).


- Both [OptiMathSAT](http://optimathsat.disi.unitn.it/) and
  [z3](https://github.com/Z3Prover/z3)
  support the following multi-objective combinations over
  FlatZinc models:

    - Multi-Independent optimization (`box`): each objective is considered an independent
      optimization goal from the others, so there is one optimal solution for each
      goal;
    - Lexicographic optimization (`lex`): the objectives are optimized in decreasing
      order of priority, so there is only one optimal solution;
    - Pareto optimization (`par`): all Pareto-optimal solutions are returned;

  A **FlatZinc** model with multiple objectives may look like:

      solve minimize cost, maximize profit;

  To know how to select the desired multi-objective combination
  with [OptiMathSAT](http://optimathsat.disi.unitn.it/) and
  [z3](https://github.com/Z3Prover/z3), look at the examples below.


# INSTALLATION

The scripts require `Python 3.7` or superior.

To install the scripts, add the current directory
to the `PATH` environment variable:

    export PATH=$PATH:.../fzn2omt

It is also necessary to add the binaries of
[Barcelogic](https://barcelogic.com/),
[OptiMathSAT](http://optimathsat.disi.unitn.it/) and
[z3](https://github.com/Z3Prover/z3)
to the `PATH` environment variable.

Notice that the conversion from **FlatZinc** to **SMT-LIB** (v. 2)
uses the `fzn2omt` interface of [OptiMathSAT](http://optimathsat.disi.unitn.it/),
so this tool is required even when solving the problems
with the other tools.

To make these changes permanent, please consider editing the
`~/.bashrc` file.


# USAGE

Options that are not captured by the scripts are handed
to the underlying OMT solver.

## fzn2smt2

    ~$ fzn2smt2.py -h
    usage: fzn2smt2.py [-h] [--smt2 <file>.smt2] [--solver {bclt,optimathsat,z3}]
                       [--bv-enc | --int-enc] [--cardinality-networks]
                       [--bv-alldifferent] [--bclt-lower BCLT_LOWER]
                       [--bclt-upper BCLT_UPPER]
                       <model>.fzn
    
    A FlatZinc compiler to SMT-LIBv2 with OMT extensions.
    
    optional arguments:
      -h, --help            show this help message and exit
    
    Main Options:
      <model>.fzn           The FlatZinc model
      --smt2 <file>.smt2    Filename for the generated SMT-LIB output
      --solver {bclt,optimathsat,z3}
                            The SMT-LIB output must be compatible with the target
                            OMT solver.
    
    Encoding Options:
      --bv-enc              Encode ints with the SMT-LIB Bit-Vector type.
      --int-enc             Encode ints with the SMT-LIB Int type.
      --cardinality-networks
                            Enable cardinality networks (when applicable).
      --bv-alldifferent     all-different constraints encoded with Bit-Vectors.
      --bclt-lower BCLT_LOWER
                            Set the default lower-bound for any objective when
                            using the bclt solver.
      --bclt-upper BCLT_UPPER
                            Set the default upper-bound for any objective when
                            using the bclt solver

## fzn2bclt.py

    ~$ fzn2bclt.py -h
    usage: fzn2bclt.py [-h] [--success] [--cardinality-networks]
                       [--bclt-lower BCLT_LOWER] [--bclt-upper BCLT_UPPER]
                       <model>.fzn
    
    A tool for solving FlatZinc problems with bclt.
    
    optional arguments:
      -h, --help            show this help message and exit
    
    Main Options:
      <model>.fzn           The FlatZinc model
      --success             Print success as response to commands
    
    Encoding Options:
      --cardinality-networks
                            Enable cardinality networks (when applicable).
      --bclt-lower BCLT_LOWER
                            Set the default lower-bound for any objective when
                            using the bclt solver.
      --bclt-upper BCLT_UPPER
                            Set the default upper-bound for any objective when
                            using the bclt solver

## fzn2optimathsat.py

    ~$ fzn2optimathsat.py -h
    usage: fzn2optimathsat.py [-h] [--smt2 <file>.smt2] [--compile-only]
                              [--bv-enc | --int-enc] [--cardinality-networks]
                              [--bv-alldifferent] [--random-seed N]
                              [--experimental-non-linear] [--partial-solutions]
                              [--all-solutions-opt] [--all-solutions]
                              [--max-solutions N] [--finite-precision prec]
                              [--free-search] [--num-threads N]
                              <model>.fzn
    
    A simple wrapper around OptiMathSAT.
    
    positional arguments:
      <model>.fzn           The FlatZinc model
    
    optional arguments:
      -h, --help            show this help message and exit
      --smt2 <file>.smt2, --output-smt2-to-file <file>.smt2
                            Filename for the generated SMT-LIB output
      --compile-only        Compile only (do not run solver).
      --bv-enc              Encode ints with the SMT-LIB Bit-Vector type.
      --int-enc             Encode ints with the SMT-LIB Int type.
      --cardinality-networks
                            Enable cardinality networks (when applicable).
      --bv-alldifferent     all-different constraints encoded with Bit-Vectors.
      --random-seed N, -r N
                            Set seed for pseudo-random number generators.
      --experimental-non-linear, -e
                            Activates experimental non-linear support. Enabling
                            this option can negatively impact the performance.
      --partial-solutions   Print any sub-optimal solution satisfying the input
                            model.
      --all-solutions-opt   Print all solutions of the input problem. If this is
                            an optimization problem, it prints all solutions with
                            the same optimal value.
      --all-solutions, -a   Print all solutions of the input problem. With
                            satisfaction problems, it enables '--all-solutions-
                            opt'. With optimization problems, it enables '--
                            partial-solutions'.
      --max-solutions N, -n N
                            Maximum number of solutions printed.
      --finite-precision prec
                            Print infinite-precision rational numbers as finite
                            precision decimals using the specified precision
                            level. Must be larger or equal 2.
      --free-search, -f     No need to follow search specification. (OptiMathSAT
                            always ignores all search specifications)
      --num-threads N, -p N
                            Number of threads. (OptiMathSAT can use only one
                            thread)


The option to set the desired multi-objective optimization is:

    -opt.priority=[box|lex|par]
    
**e.g.**

     ~$ fzn2optimathsat.py <model.fzn> -opt.priority=par
     ...

## fzn2z3.py

    ~$ fzn2z3.py -h
    usage: fzn2z3.py [-h] [--bv-enc | --int-enc] [--cardinality-networks]
                     [--bv-alldifferent]
                     <model>.fzn
    
    A tool for solving FlatZinc problems with z3.
    
    optional arguments:
      -h, --help            show this help message and exit
    
    Main Options:
      <model>.fzn           The FlatZinc model
    
    Encoding Options:
      --bv-enc              Encode ints with the SMT-LIB Bit-Vector type.
      --int-enc             Encode ints with the SMT-LIB Int type.
      --cardinality-networks
                            Enable cardinality networks (when applicable).
      --bv-alldifferent     all-different constraints encoded with Bit-Vectors.

The option to set the desired multi-objective optimization is:

    opt.priority=[box|lex|par]
    
**e.g.**

     ~$ fzn2z3.py <model.fzn> opt.priority=par
     ...


# EXAMPLES

These examples require [OptiMathSAT](http://optimathsat.disi.unitn.it/)
version `1.6.2` or superior.

    # -c    : compile only
    # --fzn : target FlatZinc model
    ~$ minizinc -c --fzn examples/warehouses.fzn examples/warehouses.mzn

## Example #01: Solving with [OptiMathSAT](http://optimathsat.disi.unitn.it/)

**Note:** only [OptiMathSAT](http://optimathsat.disi.unitn.it/) can print
the model in a `DZN`-friendly format.

- simple example:

      ~$ fzn2optimathsat.py examples/warehouses.fzn
      % objective: total (optimal model)
      total = 383;
      supplier = array1d(1..10, [5, 2, 5, 1, 5, 2, 2, 3, 2, 3]);
      open = array1d(1..5, [true, true, true, false, true]);
      cost = array1d(1..10, [30, 27, 70, 2, 4, 22, 5, 13, 35, 55]);
      ----------
      ==========

- all solutions with the same optimal value:

      ~$ fzn2optimathsat.py examples/flatzinc_allsolutions.fzn --all-solutions-opt
      % allsat model
      x = 3;
      y = 0;
      r1 = true;
      r2 = false;
      ----------
      % allsat model
      x = 3;
      y = 1;
      r1 = true;
      r2 = false;
      ----------
      ==========

- all partial solutions encountered along the optimization search:

      ~$ fzn2optimathsat.py examples/flatzinc_allsolutions.fzn --partial-solutions
      % objective: x (model)
      x = 2;
      y = 0;
      r1 = true;
      r2 = true;
      ----------
      % objective: x (model)
      x = 3;
      y = 0;
      r1 = true;
      r2 = false;
      ----------
      % objective: x (optimal model)
      x = 3;
      y = 0;
      r1 = true;
      r2 = false;
      ----------
      ==========

- multi-objective optimization:

      ~$ fzn2optimathsat.py examples/flatzinc_multiobjective.fzn -opt.priority=box
      % objective: x (optimal model)
      x = 3;
      y = 0;
      ----------
      % objective: y (optimal model)
      x = 0;
      y = 3;
      ----------
      ==========

      ~$ fzn2optimathsat.py examples/flatzinc_multiobjective.fzn -opt.priority=lex
      % lexicographic search (optimal model)
      x = 3;
      y = 1;
      ----------
      ==========

      ~$ fzn2optimathsat.py examples/flatzinc_multiobjective.fzn -opt.priority=par
      % pareto search (optimal model)
      x = 3;
      y = 1;
      ----------
      % pareto search (optimal model)
      x = 1;
      y = 3;
      ----------
      % pareto search (optimal model)
      x = 2;
      y = 2;
      ----------
      ==========


## Example #02: Solving with [Barcelogic](https://barcelogic.com/)

    ~$ fzn2bclt.py examples/warehouses.fzn
    (optimal 383)
    (
     ( define-fun X_INTRODUCED_0_ ( ) Int 5 )
     ( define-fun X_INTRODUCED_1_ ( ) Int 2 )
     ( define-fun X_INTRODUCED_2_ ( ) Int 5 )
     ...
     ( define-fun X_INTRODUCED_174_ ( ) Int 0 )
     ( define-fun X_INTRODUCED_175_ ( ) Bool false )
     ( define-fun X_INTRODUCED_176_ ( ) Int 0 )
    )

**Note:** [Barcelogic](https://barcelogic.com/) handles only
minimization objectives, so the actual goal of a maximization
problem is replaced with the minimization of the opposite
target. When this happens, the value printed in the first line
of the output is not the optimal value of the original objective
function.

## Example #03: Solving with [z3](https://github.com/Z3Prover/z3)

    ~$ fzn2z3.py examples/warehouses.fzn
    sat
    (objectives
     (total 383)
    )
    (model 
      (define-fun X_INTRODUCED_173_ () Bool
        false)
      (define-fun X_INTRODUCED_76_ () Bool
        false)
      (define-fun X_INTRODUCED_13_ () Bool
        false)
      ...
      (define-fun X_INTRODUCED_87_ () Int
        4)
      (define-fun X_INTRODUCED_63_ () Int
        1)
      (define-fun X_INTRODUCED_15_ () Int
        30)
    )
    
**Note:** when using the **SMT-LIB** encoding based on the `QF_BV`
Logic, [z3](https://github.com/Z3Prover/z3) can handle only maximization
targets. Therefore, the actual minimization goal is replaced with a
custom maximization objective that forces the minimization of the
original goal. When this happens, the value printed in the first lines
of the output is not the optimal value of the original objective function.

# NOTES

Please contact the author of this repository, or the current maintainer
of the [`OptiMathSAT`](http://optimathsat.disi.unitn.it/), in the case
that there is still any persisting issue with your `MiniZinc` models.


# Contributors

This project is authored by [Patrick Trentin](http://www.patricktrentin.com) (<patrick.trentin.88@gmail.com>).

