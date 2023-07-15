%-----------------------------------------------------------------------------%
% Constrains 'm' to be the minimum of the values in 'x'.
% Assumptions: |x| > 0.
%-----------------------------------------------------------------------------%

include "redefinitions-2.0.mzn";

predicate minimum_int(var int: m, array[int] of var int: x) =
    array_int_minimum(m, x);
