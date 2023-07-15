%-----------------------------------------------------------------------------%
% Constrains 'm' to be the maximum of the values in 'x'.
% Assumptions: |x| > 0.
%-----------------------------------------------------------------------------%

include "redefinitions-2.0.mzn";

predicate maximum_int(var int: m, array[int] of var int: x) =
    array_int_maximum(m, x);
