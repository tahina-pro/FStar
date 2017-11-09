module LowParse.Enum.Base
include LowParse.Base

module L = FStar.List.Tot

type enum (repr: eqtype) = (l: list (string * repr) {
  L.noRepeats (L.map fst l) /\
  L.noRepeats (L.map snd l)
})

type enum_key (#repr: eqtype) (e: enum repr) = (s: string { L.mem s (L.map fst e) } )

type enum_repr (#repr: eqtype) (e: enum repr) = (r: repr { L.mem r (L.map snd e) } )

let flip (#a #b: Type) (c: (a * b)) : Tot (b * a) = let (ca, cb) = c in (cb, ca)

let rec map_flip_flip (#a #b: Type) (l: list (a * b)) : Lemma
  (L.map flip (L.map flip l) == l)
= match l with
  | [] -> ()
  | _ :: q -> map_flip_flip q

let rec map_fst_flip (#a #b: Type) (l: list (a * b)) : Lemma
  (L.map fst (L.map flip l) == L.map snd l)
= match l with
  | [] -> ()
  | _ :: q -> map_fst_flip q

let rec map_snd_flip (#a #b: Type) (l: list (a * b)) : Lemma
  (L.map snd (L.map flip l) == L.map fst l)
= match l with
  | [] -> ()
  | _ :: q -> map_snd_flip q

let rec assoc_flip_elim
  (#a #b: eqtype)
  (l: list (a * b))
  (y: b)
  (x: a)
: Lemma
  (requires (
    L.noRepeats (L.map fst l) /\
    L.noRepeats (L.map snd l) /\
    L.assoc y (L.map flip l) == Some x
  ))
  (ensures (
    L.assoc x l == Some y
  ))
  (decreases l)
= let ((x', y') :: l') = l in
  if y' = y
  then ()
  else begin
    assume (x' <> x);
    assoc_flip_elim l' y x
  end

let rec assoc_flip_intro
  (#a #b: eqtype)
  (l: list (a * b))
  (y: b)
  (x: a)
: Lemma
  (requires (
    L.noRepeats (L.map fst l) /\
    L.noRepeats (L.map snd l) /\
    L.assoc x l == Some y
  ))
  (ensures (
    L.assoc y (L.map flip l) == Some x
  ))
= map_fst_flip l;
  map_snd_flip l;
  map_flip_flip l;
  assoc_flip_elim (L.map flip l) x y

let rec enum_key_of_repr
  (#repr: eqtype)
  (e: enum repr)
  (r: enum_repr e)
: Pure (enum_key e)
  (requires True)
  (ensures (fun y -> L.assoc y e == Some r))
= map_fst_flip e;
  let e' = L.map flip e in
  L.assoc_mem r e';
  let k = Some?.v (L.assoc r e') in
  assoc_flip_elim e r k;
  L.assoc_mem k e;
  (k <: enum_key e)

noextract
let rec parse_enum_key
  (#repr: eqtype)
  (p: parser repr)
  (e: enum repr)
: Tot (parser (enum_key e))
= (p
    `parse_filter`
    (fun r -> L.mem r (L.map snd e))
  )
  `parse_synth`
  (fun x -> enum_key_of_repr e x)

let rec enum_repr_of_key
  (#repr: eqtype)
  (e: enum repr)
  (k: enum_key e)
: Pure (enum_repr e)
  (requires True)
  (ensures (fun r -> L.assoc k e == Some r))
= L.assoc_mem k e;
  let r = Some?.v (L.assoc k e) in
  assoc_flip_intro e r k;
  L.assoc_mem r (L.map flip e);
  map_fst_flip e;
  (r <: enum_repr e)

let enum_repr_of_key_of_repr
  (#repr: eqtype)
  (e: enum repr)
  (r: enum_repr e)
: Lemma
  (enum_repr_of_key e (enum_key_of_repr e r) == r)
= ()

let enum_key_of_repr_of_key
  (#repr: eqtype)
  (e: enum repr)
  (k: enum_key e)
: Lemma
  (enum_key_of_repr e (enum_repr_of_key e k) == k)
= assoc_flip_intro e (enum_repr_of_key e k) k

let discr_prop
  (#repr: eqtype)
  (e: enum repr)
  (k: enum_key e)
  (x: repr)
: Lemma
  (x == enum_repr_of_key e k <==> (L.mem x (L.map snd e) /\ enum_key_of_repr e x == k))
= enum_key_of_repr_of_key e k

inline_for_extraction
let discr
  (#repr: eqtype)
  (e: enum repr)
  (k: enum_key e)
: Tot (
    (x: repr) ->
    Tot (y: bool { y == true <==> (L.mem x (L.map snd e) /\ enum_key_of_repr e x == k) } )
  )
= let r = enum_repr_of_key e k in
  fun x ->
    discr_prop e k x;
    x = r

let unknown_enum_key (#repr: eqtype) (e: enum repr) : Tot Type0 =
  (r: repr { L.mem r (L.map snd e) == false } )

type maybe_unknown_key (#repr: eqtype) (e: enum repr) =
| Known of (enum_key e)
| Unknown of (unknown_enum_key e)

let maybe_unknown_key_of_repr
  (#repr: eqtype)
  (e: enum repr)
  (r: repr)
: Tot (maybe_unknown_key e)
= if L.mem r (L.map snd e)
  then Known (enum_key_of_repr e r)
  else Unknown r

inline_for_extraction
let is_known
  (#repr: eqtype)
  (e: enum repr)
  (k: maybe_unknown_key e)
: Tot bool
= match k with
  | Known _ -> true
  | _ -> false

val enum_univ_destr_spec_gen
  (#repr: eqtype)
  (e: enum repr)
  (t: (maybe_unknown_key e -> Tot Type0))
  (f: ((k: maybe_unknown_key e) -> Tot (t k)))
  (r: repr)
: Tot (t (maybe_unknown_key_of_repr e r))

let enum_univ_destr_spec_gen #repr e t f r =
  f (maybe_unknown_key_of_repr e r)

val enum_univ_destr_spec
  (#repr: eqtype)
  (e: enum repr)
  (t: (enum_key e -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
  (r: enum_repr e)
: Tot (t (enum_key_of_repr e r))

let enum_univ_destr_spec #repr e t f r =
  f (enum_key_of_repr e r)
