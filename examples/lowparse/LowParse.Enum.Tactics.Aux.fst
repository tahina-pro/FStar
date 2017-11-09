module LowParse.Enum.Tactics.Aux

let gen_enum_univ_destr_cons_partial_nil #repr e t f k' r' v e'
= fun r -> v

let gen_enum_univ_destr_cons_partial_cons #repr e t f k' r' v e' =
  (fun recurse r ->
    if r' = r
    then v
    else recurse (enum_repr_cons_coerce_recip e k' r' e' r))
