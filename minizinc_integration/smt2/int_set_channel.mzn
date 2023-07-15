/** @group globals.channeling
  Requires that array of int variables \a x and array of set variables \a y
  are related such that (\a x[\p i] = \p j) &#8596; (\p i in \a y[\p j]).
*/
predicate int_set_channel(array[int] of var int: x,
                          array[int] of var set of int: y) =
    forall(i in index_set(x)) (x[i] in index_set(y)) /\
    forall(j in index_set(y)) (y[j] subset index_set(x)) /\
    optimathsat_int_set_channel(x, y, index_set(x), index_set(y));

predicate optimathsat_int_set_channel(array[int] of var int: x,
                                      array[int] of var set of int: y,
                                      set of int: xdom,
                                      set of int: ydom);
