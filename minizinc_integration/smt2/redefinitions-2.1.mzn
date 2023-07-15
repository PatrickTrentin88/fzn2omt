predicate float_in(var float: x, float: a, float: b) =
    optimathsat_float_in(x, a, b);

predicate float_dom(var float: x, array[int] of float: as) =
    let {
        float: lower = min([as[2*i-1] | i in 1..length(as) div 2]);
        float: upper = max([as[2*i]   | i in 1..length(as) div 2]);
    } in
        optimathsat_float_dom(x, as, lower, upper);


predicate optimathsat_float_in(var float: x,
                               float: a,
                               float: b);

predicate optimathsat_float_dom(var float: x,
                                array[int] of float: as,
                                float: a,
                                float: b);
