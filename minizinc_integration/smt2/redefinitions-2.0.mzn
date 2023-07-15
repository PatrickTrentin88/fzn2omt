% This file contains redefinitions of standard builtins that can be overridden
% by solvers.

predicate bool_clause_reif(array[int] of var bool: as,
                           array[int] of var bool: bs,
                           var bool: b) = 
    optimathsat_bool_clause_reif(as, bs, b);


predicate array_int_maximum(var int: m, array[int] of var int: x) =
    optimathsat_array_int_maximum(m, x);

predicate array_float_maximum(var float: m, array[int] of var float: x) =
    optimathsat_array_float_maximum(m, x);

predicate array_int_minimum(var int: m, array[int] of var int: x) =
    optimathsat_array_int_minimum(m, x);

predicate array_float_minimum(var float: m, array[int] of var float: x) =
    optimathsat_array_float_minimum(m, x);


predicate optimathsat_bool_clause_reif(array[int] of var bool: as,
                                       array[int] of var bool: bs,
                                       var bool: b);

predicate optimathsat_array_int_maximum(var int: m,
                                        array[int] of var int: x);

predicate optimathsat_array_float_maximum(var float: m,
                                          array[int] of var float: x);

predicate optimathsat_array_int_minimum(var int: m,
                                        array[int] of var int: x);

predicate optimathsat_array_float_minimum(var float: m,
                                          array[int] of var float: x);
