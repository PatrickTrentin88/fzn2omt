predicate maximum_arg_int(array[int] of var int: x, var int: i) =
    optimathsat_maximum_arg_int(x, i, index_set(x));

predicate optimathsat_maximum_arg_int(array[int] of var int: x,
                                      var int: i,
                                      set of int: xdom);
