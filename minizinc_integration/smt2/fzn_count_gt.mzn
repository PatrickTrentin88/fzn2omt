/** @group globals.counting
  Constrains \a c to be strictly greater than the number of occurrences
  of \a y in \a x. 
*/
predicate fzn_count_gt(array[int] of var int: x, var int: y, var int: c) =
    optimathsat_count_gt(x, y, c);

predicate optimathsat_count_gt(array[int] of var int: x,
                               var int: y,
                               var int: c);

