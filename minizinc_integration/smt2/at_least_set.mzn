%-----------------------------------------------------------------------------%
% Requires at least 'n' variables in 'x' to take the value 'v'.
%-----------------------------------------------------------------------------%

predicate at_least_set(int: n, array[int] of var set of int: x, set of int: v) =
    optimathsat_at_least_set(n, x, v);

predicate optimathsat_at_least_set(int: n,
                                  array[int] of var set of int: x,
                                  set of int: v);
