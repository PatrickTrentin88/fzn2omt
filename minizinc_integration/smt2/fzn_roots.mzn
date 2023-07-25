/** @group globals
  Requires that \a x[\p i] in \a t for all \p i in \a s
*/
predicate roots(array[int] of var int: x, var set of int: s,
                                          var set of int: t) =
        optimathsat_roots(x, s, t, index_set(x))
    ;

predicate optimathsat_roots(array[int] of var int: x,
                            var set of int: s,
                            var set of int: t,
                            set of int: xdom);
