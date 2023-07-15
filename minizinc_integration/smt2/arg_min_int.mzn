predicate minimum_arg_int(array[int] of var int: x, var int: i) =
    optimathsat_minimum_arg_int(x, i, index_set(x));

predicate optimathsat_minimum_arg_int(array[int] of var int: x,
                                      var int: i,
                                      set of int: xdom);
