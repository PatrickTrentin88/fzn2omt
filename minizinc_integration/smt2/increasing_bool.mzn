%-----------------------------------------------------------------------------%
% Requires that the array 'x' is in increasing order (duplicates are allowed).
%-----------------------------------------------------------------------------%

predicate increasing_bool(array[int] of var bool: x) =
    optimathsat_increasing_bool(x);

predicate optimathsat_increasing_bool(array[int] of var bool: x);
