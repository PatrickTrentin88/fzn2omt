%-----------------------------------------------------------------------------%
% Requires exactly 'n' variables in 'x' to take the value 'v'.
%-----------------------------------------------------------------------------%

predicate fzn_exactly_int(int: n, array[int] of var int: x, int: v) =
    optimathsat_exactly_int(n, x, v);

predicate optimathsat_exactly_int(int: n,
                                  array[int] of var int: x,
                                  int: v);
