include "count.mzn";

/** @group globals.counting
  Requires that the number of occurrences of \a cover[\p i] in \a x is \a counts[\p i].
*/
predicate global_cardinality(array[int] of var int: x,
                             array[int] of int: cover,
                             array[int] of var int: counts) =
        optimathsat_global_cardinality(x, cover, counts)
    ;

predicate optimathsat_global_cardinality(array[int] of var int: x,
                                         array[int] of int: cover,
                                         array[int] of var int: counts);
