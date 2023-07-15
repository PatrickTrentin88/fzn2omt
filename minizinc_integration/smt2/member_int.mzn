%-----------------------------------------------------------------------------%
% Requires that 'y' occurs in the array or set 'x'.
%-----------------------------------------------------------------------------%

predicate member_int(array[int] of var int: x, var int: y) =
    optimathsat_member_int(x, y);

predicate optimathsat_member_int(array[int] of var int: x,
                                 var int: y);
