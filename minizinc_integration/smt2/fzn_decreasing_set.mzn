%-----------------------------------------------------------------------------%
% Requires that the array 'x' is in decreasing order (duplicates are allowed).
%-----------------------------------------------------------------------------%

predicate fzn_decreasing_set(array[int] of var set of int: x) =
    optimathsat_decreasing_set(x);

predicate optimathsat_decreasing_set(array[int] of var set of int: x);

