module LowParse.Enum.Tactics.Aux
include LowParse.Enum.Base

module T = FStar.Tactics

inline_for_extraction
let enum_key_cons_coerce
  (#repr: eqtype)
  (e: enum repr)
  (k' : string)
  (r' : repr)
  (e' : enum repr)
  (k: enum_key e')
: Pure (enum_key e)
  (requires (e == (k', r') :: e'))
  (ensures (fun _ -> True))
= (k <: string) <: enum_key e

inline_for_extraction
let enum_repr_cons_coerce_recip
  (#repr: eqtype)
  (e: enum repr)
  (k' : string)
  (r' : repr)
  (e' : enum repr)
  (k: enum_repr e)
: Pure (enum_repr e')
  (requires (e == (k', r') :: e' /\ r' <> k))
  (ensures (fun _ -> True))
= (k <: repr) <: enum_repr e'

inline_for_extraction
val gen_enum_univ_destr_cons_partial_nil
  (#repr: eqtype)
  (e: enum repr)
  (t: ((k: enum_key e) -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
  (k' : enum_key e)
  (r' : enum_repr e)
  (v: t k' { v == f k' } )
  (e' : enum repr { e == (k', r') :: e' /\ Nil? e' } )
: (r: enum_repr e) ->
  Tot (t (enum_key_of_repr e r))

inline_for_extraction
val gen_enum_univ_destr_cons_partial_cons
  (#repr: eqtype)
  (e: enum repr)
  (t: ((k: enum_key e) -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
  (k' : enum_key e)
  (r' : enum_repr e)
  (v: t k' { v == f k' } )
  (e' : enum repr { e == (k', r') :: e' /\ Cons? e' } )
:
  (recurse: (
    (r: enum_repr e') ->
    Tot (t (enum_key_cons_coerce #repr e k' r' e' (enum_key_of_repr #repr e' r)))
  )) ->
  (r: enum_repr e) ->
  Tot (t (enum_key_of_repr e r))
