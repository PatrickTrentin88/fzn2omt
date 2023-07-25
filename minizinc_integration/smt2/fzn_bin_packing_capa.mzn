/**  @group globals.packing
  Requires that each item \p i with weight \a w[\p i], be put into \a bin[\p i] such 
  that the sum of the weights of the items in each bin \p b does not exceed the 
  capacity \a c[\p b].

  Assumptions:
  - forall \p i, \a w[\p i] >=0
  - forall \p b, \a c[\p b] >=0
*/
predicate fzn_bin_packing_capa(array[int] of int: c,
                           array[int] of var int: bin,
                           array[int] of int: w) =
    optimathsat_bin_packing_capa(c, bin, w, index_set(c))
;

predicate optimathsat_bin_packing_capa(array[int] of int: c,
                                       array[int] of var int: bin,
                                       array[int] of int: w,
                                       set of int: cdom);

%-----------------------------------------------------------------------------%
