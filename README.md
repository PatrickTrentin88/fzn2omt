# DESCRIPTION

Python scripts to solve FlatZinc models with Optimization Modulo Theories solvers
like, e.g., [Barcelogic](https://barcelogic.com/),
[OptiMathSAT](http://optimathsat.disi.unitn.it/) and
[z3](https://github.com/Z3Prover/z3).

Satisfaction FlatZinc models can also be solved with Satisfiability Modulo
Theories solvers like, e.g., [CVC4](https://cvc4.github.io/).

The FlatZinc model can be generated using the standard
[minizinc](https://www.minizinc.org/)
compiler or the customized
[**emzn2fzn**](https://github.com/PatrickTrentin88/emzn2fzn)
compiler for 
[OptiMathSAT](http://optimathsat.disi.unitn.it/).


# Functionality

- All tools support the encoding based on the `QF_LIRA` logic
  (option `--int-enc`), that may sometimes be extended to `QF_NIRA`
  when the input problem requires it.
  [OptiMathSAT](http://optimathsat.disi.unitn.it/),
  [z3](https://github.com/Z3Prover/z3) and
  [CVC4](https://cvc4.github.io/) support also the encoding
  based on the `QF_BV` logic (option `--bv-enc`).

- [OptiMathSAT](http://optimathsat.disi.unitn.it/) has some
  [limited support for Global Constraints](http://optimathsat.disi.unitn.it/pages/fznreference.html),
  when the Bit-Vector encoding is not used (option `--bv-enc`).
  Until conclusive experimental evidence of their effectiveness
  has been collected on a wide set of benchmarks, the maintainers
  of [OptiMathSAT](http://optimathsat.disi.unitn.it/) do not
  recommend using them.

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

- [Barcelogic](https://barcelogic.com/) does not have native support
  for multi-objective optimization. Thus, multiple optimization targets
  are solved incrementally.


# REQUIREMENTS

The scripts require

- `Python 3.7` or superior
-  [OptiMathSAT](http://optimathsat.disi.unitn.it/) `1.7.0` or superior


# INSTALLATION

To install the scripts, add the current directory
to the `PATH` environment variable:

    export PATH=$PATH:.../fzn2omt

It is also necessary to add the binaries of
[Barcelogic](https://barcelogic.com/),
[OptiMathSAT](http://optimathsat.disi.unitn.it/),
[z3](https://github.com/Z3Prover/z3) and
[CVC4](https://cvc4.github.io/)
to the `PATH` environment variable.
)
Notice that the conversion from **FlatZinc** to **SMT-LIB** (v. 2)
uses the `fzn2omt` interface of [OptiMathSAT](http://optimathsat.disi.unitn.it/),
so this tool is required even when solving the problems
with the other tools.

To make these changes permanent, please consider editing the
`~/.bashrc` file.

Linux users can also edit and source the contents of the `.bashrc`
file distributed with this project.


# Solving with [OptiMathSAT](http://optimathsat.disi.unitn.it/): fzn2optimathsat.py

The option to set the desired multi-objective optimization is:

    -opt.priority=[box|lex|par]
    
**e.g.**

     ~$ fzn2optimathsat.py <model.fzn> -opt.priority=par
     ...

[OptiMathSAT](http://optimathsat.disi.unitn.it/) may print a
sub-optimal model when the objective function is unbounded or,
according to its infinite-precision arithmetic engine, equal
to `K +/- epsilon` for some `K` and some arbitrarily small
`epsilon`. In such cases, [OptiMathSAT](http://optimathsat.disi.unitn.it/)
prints a warning message with the exact optimal value:

    ~$ fzn2optimathsat.py examples/unit_tests/unbounded.fzn
    % objective: x (optimal model)
    % warning: x is unbounded: (- oo)
    x = -1000000000;
    ----------
    ==========

### [OptiMathSAT](http://optimathsat.disi.unitn.it/) examples

- compilation:

      ~$ fzn2optimathsat.py examples/coloring.fzn --smt2 coloring.smt2
      ~$ ls
      coloring.smt2

- solving:

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


# Solving with [Z3](https://github.com/Z3Prover/z3): fzn2z3.py

The option to set the desired multi-objective optimization is:

    opt.priority=[box|lex|par]
    
**e.g.**

     ~$ fzn2z3.py <model.fzn> opt.priority=par
     ...

[z3](https://github.com/Z3Prover/z3) may print a
sub-optimal model when the objective function is unbounded or,
according to its infinite-precision arithmetic engine, equal
to `K +/- epsilon` for some `K` and some arbitrarily small
`epsilon`. 

    ~$ fzn2z3.py examples/unit_tests/unbounded.fzn
    x = 0;
    ----------
    ==========

### [z3](https://github.com/Z3Prover/z3) examples

- compilation:

      ~$ fzn2z3.py examples/coloring.fzn --smt2 coloring.smt2
      ~$ ls
      coloring.smt2

- solving:

      ~$ fzn2z3.py examples/warehouses.fzn
      total = 383;
      supplier = array1d(1..10, [5, 2, 5, 1, 5, 2, 2, 3, 2, 3]);
      open = array1d(1..5, [true, true, true, false, true]);
      cost = array1d(1..10, [30, 27, 70, 2, 4, 22, 5, 13, 35, 55]);
      ----------
      ==========


# Solving with [Barcelogic](https://barcelogic.com/): fzn2bclt.py

Some FlatZinc problems require an encoding based on OMT(NIRA),
which is not supported by [Barcelogic](https://barcelogic.com/).
For such problems, [Barcelogic](https://barcelogic.com/) may
incorrectly return `unsat`.

[Barcelogic](https://barcelogic.com/) requires objective functions
to have a known, and finite, domain. When lower/upper bounds are
not provided manually (options `--bclt-lower` and `--bclt-upper`),
the default search interval is [-1000000000,1000000000]. Setting
an inappropriate search interval may cause [Barcelogic](https://barcelogic.com/)
to provide the incorrect answer (e.g. `unsat` or the wrong optimal value).

### [Barcelogic](https://barcelogic.com/) examples

- compilation:

      ~$ fzn2bclt.py examples/coloring.fzn --smt2 coloring.smt2
      ~$ ls
      coloring.smt2

- solving:

      ~$ fzn2bclt.py examples/warehouses.fzn
      total = 383;
      supplier = array1d(1..10, [5, 2, 5, 1, 5, 2, 2, 3, 2, 3]);
      open = array1d(1..5, [true, true, true, false, true]);
      cost = array1d(1..10, [30, 27, 70, 2, 4, 22, 5, 13, 35, 55]);
      ----------
      ==========


# Solving with [CVC4](https://cvc4.github.io/): fzn2cvc4.py

[CVC4](https://cvc4.github.io/) is a SMT solver and does not support optimization.

Normally, attempting to solve an optimization problem with CVC4
results in an error message.

    ~$ fzn2cvc4.py examples/unit_tests/opt.fzn
    error: objectives are not supported

It is possible to force [CVC4](https://cvc4.github.io/) to solve the input problem
by ignoring the objective function. Naturally, the resulting
model is not guaranteed to be optimal.

    ~$ fzn2cvc4.py examples/unit_tests/opt.fzn --ignore-objs
    objective = 0;
    ----------

### [CVC4](https://cvc4.github.io/) examples

- compilation:

      ~$ fzn2z3.py examples/coloring.fzn --smt2 coloring.smt2
      ~$ ls
      coloring.smt2

- solving:

      ~$ fzn2z3.py examples/coloring.fzn
      numColors = 4;
      x = array1d(1..6, [1, 1, 2, 3, 4, 4]);
      ----------


# NOTES

Please contact the author of this repository, or the current maintainer
of the [`OptiMathSAT`](http://optimathsat.disi.unitn.it/), in the case
that there is still any persisting issue with your `MiniZinc` models.


# Contributors

This project is authored by [Patrick Trentin](http://www.patricktrentin.com) (<patrick.trentin.88@gmail.com>).

