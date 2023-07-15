/**  @group globals.alldifferent
  Constrain the array of sets of integers \a S to be pairwise disjoint.
*/
predicate all_disjoint(array[int] of var set of int: S) = 
    optimathsat_all_disjoint(S);

predicate optimathsat_all_disjoint(array[int] of var set of int: S);
