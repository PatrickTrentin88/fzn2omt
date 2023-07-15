%-----------------------------------------------------------------------------%
% Requires that the array 'x' is in decreasing order (duplicates are allowed).
%-----------------------------------------------------------------------------%

predicate decreasing_bool(array[int] of var bool: x) =
    optimathsat_decreasing_bool(x);

predicate optimathsat_decreasing_bool(array[int] of var bool: x);
