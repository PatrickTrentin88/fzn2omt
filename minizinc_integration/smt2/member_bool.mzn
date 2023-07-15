%-----------------------------------------------------------------------------%
% Requires that 'y' occurs in the array or set 'x'.
%-----------------------------------------------------------------------------%

predicate member_bool(array[int] of var bool: x, var bool: y) =
    optimathsat_member_bool(x, y);

predicate optimathsat_member_bool(array[int] of var bool: x,
                                  var bool: y);
