/** @group globals
  Requires that the image of function \a x (represented as an array) on set
  of values \a s is \a t.  ub(\a s) must be a subset of index_set(\a x) otherwise an
  assertion failure will occur.
*/
predicate fzn_range(array[int] of var int: x, var set of int: s,
                                          var set of int: t) =
        optimathsat_range(x, s, t, index_set(x))
    ;

predicate optimathsat_range(array[int] of var int: x,
                            var set of int: s,
                            var set of int: t,
                            set of int: xdom);
