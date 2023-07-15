%-----------------------------------------------------------------------------%
% Requires that the array 'x' is in increasing order (duplicates are allowed).
%-----------------------------------------------------------------------------%

predicate increasing_int(array[int] of var int: x) =
    optimathsat_increasing_int(x);

predicate optimathsat_increasing_int(array[int] of var int: x);

