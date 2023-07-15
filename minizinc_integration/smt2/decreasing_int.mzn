%-----------------------------------------------------------------------------%
% Requires that the array 'x' is in decreasing order (duplicates are allowed).
%-----------------------------------------------------------------------------%

predicate decreasing_int(array[int] of var int: x) =
    optimathsat_decreasing_int(x);

predicate optimathsat_decreasing_int(array[int] of var int: x);
