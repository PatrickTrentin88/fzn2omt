include "disjunctive_strict.mzn";

/** @group globals.scheduling
  Requires that a set of tasks given by start times \a s and durations \a d
  do not overlap in time. Tasks with duration 0 can be scheduled at any time,
  even in the middle of other tasks.

  Assumptions:
  - forall \p i, \a d[\p i] >= 0
*/
predicate fzn_disjunctive(array[int] of var int: s,
                      array[int] of var int: d) =
        forall (i in index_set(d)) (d[i] >= 0) /\
        if (lb_array(d) > 0) then
          fzn_disjunctive_strict(s,d)
        else
          optimathsat_disjunctive(s, d)
        endif
    ;

predicate optimathsat_disjunctive(array[int] of var int: s,
                                  array[int] of var int: d);
