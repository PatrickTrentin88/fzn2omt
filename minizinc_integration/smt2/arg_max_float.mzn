predicate maximum_arg_float(array[int] of var float: x, var int: i) =
    optimathsat_maximum_arg_float(x, i, index_set(x));

predicate optimathsat_maximum_arg_float(array[int] of var float: x,
                                        var int: i,
                                        set of int: xdom);
