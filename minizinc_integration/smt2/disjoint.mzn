/** @group globals Requires that sets \a s1 and \a s2 do not intersect. */

predicate disjoint(var set of int: s1, var set of int: s2) =
    optimathsat_disjoint(s1, s2);

predicate optimathsat_disjoint(var set of int: s1,
                               var set of int: s2);

