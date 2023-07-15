%-----------------------------------------------------------------------------%
% Constrains 'm' to be the minimum of the values in 'x'.
% Assumptions: |x| > 0.
%-----------------------------------------------------------------------------%

include "redefinitions-2.0.mzn";

predicate minimum_float(var float: m, array[int] of var float: x) =
	array_float_minimum(m, x);
