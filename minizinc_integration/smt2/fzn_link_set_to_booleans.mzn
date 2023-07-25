/** @group globals.channeling
  Constrain the array of Booleans \a b to be a representation of the set \a s:
  \p i in \a s &#8596; \a b[\p i].
  
  The index set of \a b must be a superset of the possible values of \a s.
*/
predicate link_set_to_booleans(var set of int: s, array[int] of var bool: b) =
            optimathsat_link_set_to_booleans(s, b, index_set(b))
    ;

predicate optimathsat_link_set_to_booleans(var set of int: s,
                                           array[int] of var bool: b,
                                           set of int: bdom);
