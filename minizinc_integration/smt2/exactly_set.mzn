%-----------------------------------------------------------------------------%
% Requires exactly 'n' variables in 'x' to take the value 'v'.
%-----------------------------------------------------------------------------%

predicate exactly_set(int: n, array[int] of var set of int: x, set of int: v) =
    optimathsat_exactly_set(n, x, v);

predicate optimathsat_exactly_set(int: n,
                                  array[int] of var set of int: x,
                                  set of int: v);
