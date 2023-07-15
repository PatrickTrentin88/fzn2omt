%-----------------------------------------------------------------------------%
% Constrains 'm' to be the maximum of the values in 'x'.
% Assumptions: |x| > 0.
%-----------------------------------------------------------------------------%

include "redefinitions-2.0.mzn";

predicate maximum_float(var float: m, array[int] of var float: x) =
    array_float_maximum(m, x);
