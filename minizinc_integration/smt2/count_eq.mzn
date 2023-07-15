/** @group globals.counting
  Constrains \a c to be the number of occurrences of \a y in \a x. 
*/
predicate count_eq(array[int] of var int: x, var int: y, var int: c) =
    optimathsat_count_eq(x, y, c);

predicate optimathsat_count_eq(array[int] of var int: x,
                               var int: y,
                               var int: c);
