%-----------------------------------------------------------------------------%
% Requires that 'y' occurs in the array or set 'x'.
%-----------------------------------------------------------------------------%

predicate member_set(array[int] of var set of int: x, var set of int: y) =
    optimathsat_member_set(x, y);

predicate optimathsat_member_set(array[int] of var set of int: x,
                                 var set of int: y);
