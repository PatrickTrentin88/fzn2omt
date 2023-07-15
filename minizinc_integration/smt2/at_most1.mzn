/**  @group globals.counting
  Requires that each pair of sets in \a s overlap in at most one element.
*/
predicate at_most1(array[int] of var set of int: s) = 
    optimathsat_at_most1(s);

predicate atmost1(array[int] of var set of int: s) =
    optimathsat_at_most1(s);

predicate optimathsat_at_most1(array[int] of var set of int: s);

