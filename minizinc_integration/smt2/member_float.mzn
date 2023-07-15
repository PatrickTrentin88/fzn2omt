%-----------------------------------------------------------------------------%
% Requires that 'y' occurs in the array or set 'x'.
%-----------------------------------------------------------------------------%

predicate member_float(array[int] of var float: x, var float: y) =
    optimathsat_member_float(x, y);

predicate optimathsat_member_float(array[int] of var float: x,
                                   var float: y);

