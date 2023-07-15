/**  @group globals.counting
  Requires exactly \a n variables in \a x to take one of the values in \a v.
*/
predicate among(var int: n, array[int] of var int: x, set of int: v) =
    optimathsat_among(n, x, v);

predicate optimathsat_among(var int: n,
                            array[int] of var int: x,
                            set of int: v);
