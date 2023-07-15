%-----------------------------------------------------------------------------%
% Requires that the array 'x' is in increasing order (duplicates are allowed).
%-----------------------------------------------------------------------------%

predicate increasing_float(array[int] of var float: x) =
    optimathsat_increasing_float(x);

predicate optimathsat_increasing_float(array[int] of var float: x);
