/** @group globals.alldifferent
  Requires that the number of distinct values in \a x is \a n.
*/
predicate nvalue(var int: n, array[int] of var int: x) =
    optimathsat_nvalue(n, x);

predicate optimathsat_nvalue(var int: n,
                             array[int] of var int: x);
