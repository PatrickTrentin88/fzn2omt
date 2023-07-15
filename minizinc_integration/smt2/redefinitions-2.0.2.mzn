% This file contains redefinitions of standard builtins for version 2.0.2
% that can be overridden by solvers.


predicate symmetry_breaking_constraint(var bool: b) = b;

predicate redundant_constraint(var bool: b) = b;


predicate array_var_bool_element_nonshifted(var int: idx, array[int] of var bool: x, var bool: c) =
  optimathsat_element_bool(idx, array1d(x), c, index_set(x));

predicate array_var_int_element_nonshifted(var int: idx, array[int] of var int: x, var int: c) =
  optimathsat_element_int(idx, array1d(x), c, index_set(x));

predicate array_var_float_element_nonshifted(var int: idx, array[int] of var float: x, var float: c) =
  optimathsat_element_float(idx, array1d(x), c, index_set(x));

predicate array_var_set_element_nonshifted(var int: idx, array[int] of var set of int: x, var set of int: c) =
  optimathsat_element_set(idx, array1d(x), c, index_set(x));


predicate optimathsat_element_bool(var int: idx,
                                    array[int] of var bool: x,
                                    var bool: c,
                                    set of int: xdom);

predicate optimathsat_element_int(var int: idx,
                                  array[int] of var int: x,
                                  var int: c,
                                  set of int: xdom);

predicate optimathsat_element_float(var int: idx,
                                    array[int] of var float: x,
                                    var float: c,
                                    set of int: xdom);

predicate optimathsat_element_set(var int: idx,
                                  array[int] of var set of int: x,
                                  var set of int: c,
                                  set of int: xdom);
