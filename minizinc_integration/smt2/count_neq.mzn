/** @group globals.counting
  Constrains \a c to be not equal to the number of occurrences
  of \a y in \a x. 
*/
predicate count_neq(array[int] of var int: x, var int: y, var int: c) =
    optimathsat_count_neq(x, y, c);

predicate optimathsat_count_neq(array[int] of var int: x,
                                var int: y,
                                var int: c);

