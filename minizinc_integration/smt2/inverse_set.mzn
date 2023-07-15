/** @group globals.channeling
  Constrains two arrays of set of int variables, \a f and \a invf, so that
  a \p j in f[\p i] iff \p i in invf[\p j].  All the values in each array's sets
  must be within the index set of the other array.
*/
predicate inverse_set(array[int] of var set of int: f,
                      array[int] of var set of int: invf) =
    forall(i in index_set(f)) (
        f[i] subset index_set(invf)
    ) /\
    forall(j in index_set(invf)) (
        invf[j] subset index_set(f)
    ) /\
    optimathsat_inverse_set(f, invf, index_set(f), index_set(invf));

predicate optimathsat_inverse_set(array[int] of var set of int: f,
                                  array[int] of var set of int: invf,
                                  set of int: fdom,
                                  set of int: invfdom);
