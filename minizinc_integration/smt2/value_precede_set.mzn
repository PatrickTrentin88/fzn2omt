predicate value_precede_set(int: s, int: t, array[int] of var set of int: x) =
    optimathsat_value_precede_set(s, t, x);

predicate optimathsat_value_precede_set(int: s,
                                        int: t,
                                        array[int] of var set of int: x);
