%-----------------------------------------------------------------------------%
% Requires at least 'n' variables in 'x' to take the value 'v'.
%-----------------------------------------------------------------------------%

predicate fzn_at_least_int(int: n, array[int] of var int: x, int: v) =
    optimathsat_at_least_int(n, x, v);

predicate optimathsat_at_least_int(int: n,
                                   array[int] of var int: x,
                                   int: v);
