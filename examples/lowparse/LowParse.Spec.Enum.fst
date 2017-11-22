module LowParse.Spec.Enum
include LowParse.Spec.Combinators

module L = FStar.List.Tot

type enum (key: eqtype) (repr: eqtype) = (l: list (key * repr) {
  L.noRepeats (L.map fst l) /\
  L.noRepeats (L.map snd l)
})

type enum_key (#key #repr: eqtype) (e: enum key repr) = (s: key { L.mem s (L.map fst e) } )

type enum_repr (#key #repr: eqtype) (e: enum key repr) = (r: repr { L.mem r (L.map snd e) } )

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

let rec assoc_mem_snd
  (#a #b: eqtype)
  (l: list (a * b))
  (x: a)
  (y: b)
: Lemma
  (requires (L.assoc x l == Some y))
  (ensures (L.mem y (L.map snd l) == true))
  (decreases l)
= let ((x', y') :: l') = l in
  if x' = x
  then ()
  else assoc_mem_snd l' x y

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
    if x' = x
    then begin
      assert (L.mem x' (L.map fst l') == false);
      assoc_mem_snd (L.map flip l') y x;
      map_snd_flip l';
      assert False
    end
    else
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
  (#key #repr: eqtype)
  (e: enum key repr)
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
  (#b: bool)
  (#key #repr: eqtype)
  (p: parser' b repr)
  (e: enum key repr)
: Tot (parser' b (enum_key e))
= (p
    `parse_filter`
    (fun (r: repr) -> L.mem r (L.map snd e))
  )
  `parse_synth`
  (fun (x: repr {L.mem x (L.map snd e) == true})  -> enum_key_of_repr e x)

let rec enum_repr_of_key
  (#key #repr: eqtype)
  (e: enum key repr)
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
  (#key #repr: eqtype)
  (e: enum key repr)
  (r: enum_repr e)
: Lemma
  (enum_repr_of_key e (enum_key_of_repr e r) == r)
= ()

let enum_key_of_repr_of_key
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: enum_key e)
: Lemma
  (enum_key_of_repr e (enum_repr_of_key e k) == k)
= assoc_flip_intro e (enum_repr_of_key e k) k

let unknown_enum_key (#key #repr: eqtype) (e: enum key repr) : Tot Type0 =
  (r: repr { L.mem r (L.map snd e) == false } )

type maybe_unknown_key (#key #repr: eqtype) (e: enum key repr) =
| Known of (enum_key e)
| Unknown of (unknown_enum_key e)

let maybe_unknown_key_of_repr
  (#key #repr: eqtype)
  (e: enum key repr)
  (r: repr)
: Tot (maybe_unknown_key e)
= if L.mem r (L.map snd e)
  then Known (enum_key_of_repr e r)
  else Unknown r
