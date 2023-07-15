%-----------------------------------------------------------------------------%
% Constrains the array of objects 'x' to be all different.
%-----------------------------------------------------------------------------%

predicate all_different_set(array[int] of var set of int: x) =
    optimathsat_all_different_set(x);

predicate optimathsat_all_different_set(array[int] of var set of int: x);
