predicate minimum_arg_float(array[int] of var float: x, var int: i) =
    optimathsat_minimum_arg_float(x, i, index_set(x));

predicate optimathsat_minimum_arg_float(array[int] of var float: x,
                                        var int: i,
                                        set of int: xdom);

