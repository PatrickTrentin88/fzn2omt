predicate optimathsat_int_div_fixed_b(var int: a, int: b, var int: c);
predicate optimathsat_int_div_fixed_ac(int: a, var int: b, int: c);

predicate int_div(var int: a, var int: b, var int: c) =
  if is_fixed(b) then
    optimathsat_int_div_fixed_b(a, fix(b), c)
  elseif is_fixed(a) /\ is_fixed(c) then
    optimathsat_int_div_fixed_ac(fix(a), b, fix(c))
  else
    let {
      any: cs = [bv: if bv != 0 /\ bv in dom(b) then a div bv else lb(c) endif | bv in lb(b)..ub(b)];
    } in b != 0 /\ c = cs[b]
  endif;
