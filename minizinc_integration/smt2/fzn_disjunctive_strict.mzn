/** @group globals.scheduling
  Requires that a set of tasks given by start times \a s and durations \a d
  do not overlap in time. Tasks with duration 0 CANNOT be scheduled at any time,
  but only when no other task is running.

  Assumptions:
  - forall \p i, \a d[\p i] >= 0
*/
predicate fzn_disjunctive_strict(array[int] of var int: s,
                             array[int] of var int: d) =
        forall (i in index_set(d)) (d[i] >= 0) /\ 
        optimathsat_disjunctive_strict(s, d)
;

predicate optimathsat_disjunctive_strict(array[int] of var int: s,
                                         array[int] of var int: d);
