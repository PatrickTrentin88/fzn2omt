%-----------------------------------------------------------------------------%
% Requires that the array 'x' is in increasing order (duplicates are allowed).
%-----------------------------------------------------------------------------%

predicate increasing_set(array[int] of var set of int: x) =
    optimathsat_increasing_set(x);

predicate optimathsat_increasing_set(array[int] of var set of int: x);

