%-----------------------------------------------------------------------------%
% Requires that the array 'x' is in decreasing order (duplicates are allowed).
%-----------------------------------------------------------------------------%

predicate decreasing_float(array[int] of var float: x) =
    optimathsat_decreasing_float(x);

predicate optimathsat_decreasing_float(array[int] of var float: x);

