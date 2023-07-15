/** @group globals.channeling
  Constrains two arrays of int variables, \a f and \a invf, to represent
  inverse functions.  All the values in each array must be within the index
  set of the other array.
*/
predicate inverse(array[int] of var int: f,
                  array[int] of var int: invf) =
    optimathsat_inverse(f, invf, index_set(f), index_set(invf));

predicate optimathsat_inverse(array[int] of var int: f,
                              array[int] of var int: invf,
                              set of int: fdom,
                              set of int: invfdom);
