module LowParse.Enum
include LowParse.Base

module L = FStar.List.Tot
module T = FStar.Tactics

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
  (#key #repr: eqtype)
  (p: parser repr)
  (e: enum key repr)
: Tot (parser (enum_key e))
= (p
    `parse_filter`
    (fun (r: repr) -> L.mem r (L.map snd e))
  )
  `parse_synth`
  (fun (x: repr {L.mem x (L.map snd e) == true})  -> enum_key_of_repr e x)

let parse_enum_key_injective
  (#key #repr: eqtype)
  (p: parser repr)
  (e: enum key repr)
: Lemma
  (requires (injective p))
  (ensures (injective (parse_enum_key p e)))
= parse_filter_injective p (fun (r: repr) -> L.mem r (L.map snd e));
  parse_synth_injective (p `parse_filter` (fun (r: repr) -> L.mem r (L.map snd e))) (fun (x: repr {L.mem x (L.map snd e) == true})  -> enum_key_of_repr e x)

let mk_if (test e_true e_false: T.term) : Tot T.term =
  let br_true = (T.Pat_Constant T.C_True, e_true) in
  let br_false = (T.Pat_Constant T.C_False, e_false) in
  let m = T.pack (T.Tv_Match test [ br_true; br_false ] ) in
  m

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

let discr_prop
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: enum_key e)
  (x: repr)
: Lemma
  (x == enum_repr_of_key e k <==> (L.mem x (L.map snd e) /\ enum_key_of_repr e x == k))
= enum_key_of_repr_of_key e k

inline_for_extraction
let discr
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: enum_key e)
: Tot (
    (x: repr) ->
    Tot (y: bool { y == true <==> (L.mem x (L.map snd e) /\ enum_key_of_repr e x == k) } )
  )
= let r = enum_repr_of_key e k in
  fun x ->
    discr_prop e k x;
    x = r

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

val enum_univ_destr_spec_gen
  (#key #repr: eqtype)
  (e: enum key repr)
  (t: (maybe_unknown_key e -> Tot Type0))
  (f: ((k: maybe_unknown_key e) -> Tot (t k)))
  (r: repr)
: Tot (t (maybe_unknown_key_of_repr e r))

let enum_univ_destr_spec_gen #key #repr e t f r =
  f (maybe_unknown_key_of_repr e r)

val enum_univ_destr_spec
  (#key #repr: eqtype)
  (e: enum key repr)
  (t: (enum_key e -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
  (r: enum_repr e)
: Tot (t (enum_key_of_repr e r))

let enum_univ_destr_spec #key #repr e t f r =
  f (enum_key_of_repr e r)

inline_for_extraction
let id
  (t: Type0)
  (x: t)
: Tot t
= x

inline_for_extraction
let enum_key_cons_coerce
  (#key #repr: eqtype)
  (e: enum key repr)
  (k' : key)
  (r' : repr)
  (e' : enum key repr)
  (k: enum_key e')
: Pure (enum_key e)
  (requires (e == (k', r') :: e'))
  (ensures (fun _ -> True))
= (k <: key) <: enum_key e

inline_for_extraction
let enum_repr_cons_coerce_recip
  (#key #repr: eqtype)
  (e: enum key repr)
  (k' : key)
  (r' : repr)
  (e' : enum key repr)
  (k: enum_repr e)
: Pure (enum_repr e')
  (requires (e == (k', r') :: e' /\ r' <> k))
  (ensures (fun _ -> True))
= (k <: repr) <: enum_repr e'

noextract
let mk_coercion
  (from_value: T.term)
  (to_typ: T.term)
: Tot (T.tactic T.term)
= T.bind (T.quote id) (fun id' ->
    let res = T.mk_app id' [to_typ, T.Q_Explicit; from_value, T.Q_Explicit] in
    T.return res
  )

noextract
let rec gen_enum_univ_destr_body
  (#key #repr: eqtype)
  (e: enum key repr)
  (t: ((k: enum_key e) -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
  (r: T.term)
: Pure (T.tactic T.term)
  (requires (Cons? e))
  (ensures (fun _ -> True))
  (decreases e)
= match e with
  | ((k', r') :: e') ->
    let e' : enum key repr = e' in
    let k' : enum_key e = k' in
    let fk' = f k' in
    T.bind (T.quote fk') (fun rt ->
      match e' with
      | [] -> T.return rt
      | _ ->
      T.bind (T.quote t) (fun t' ->
      T.bind (T.quote (enum_key_of_repr #key #repr e)) (fun myu ->
      let m_type = T.mk_app t' [T.mk_app myu [r, T.Q_Explicit], T.Q_Explicit] in
      T.bind (mk_coercion rt m_type) (fun rt_constr ->
      T.bind (T.quote (op_Equality #repr r')) (fun eq_repr_k' ->
        let test = T.mk_app eq_repr_k' [
          (r, T.Q_Explicit);
        ]
        in
	T.bind (T.quote (enum_repr_cons_coerce_recip #key #repr e k' r' e')) (fun q_r_false ->
        T.bind (
          gen_enum_univ_destr_body
            e'
            (fun (k: enum_key e') ->
              t (enum_key_cons_coerce #key #repr e k' r' e' k)
            )
            (fun (k: enum_key e') ->
              f (enum_key_cons_coerce #key #repr e k' r' e' k)
            )
            (T.mk_app q_r_false [r, T.Q_Explicit])
        ) (fun t' ->
          T.bind (mk_coercion t' m_type) (fun t'_constr ->
          let m = mk_if test rt_constr t'_constr in
          T.return m
  ))))))))

noextract
let rec gen_enum_univ_destr
  (#key #repr: eqtype)
  (e: enum key repr)
  (t: (enum_key e -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
: Tot (T.tactic unit)
= let open T in
  match e with
  | _ :: _ ->
    tk <-- quote (enum_repr #key #repr e) ;
    let x = fresh_binder tk in
    let r = T.pack (T.Tv_Var x) in
    body <-- gen_enum_univ_destr_body #key #repr e t f r ;
    let res = T.pack (T.Tv_Abs x body) in
    _ <-- print (term_to_string res) ;
    t_exact true false (return res)
  | _ ->
    let g (r: enum_repr #key #repr e) : Tot (t (enum_key_of_repr #key #repr e r)) =
      false_elim ()
    in
    exact_guard (quote g)

let maybe_unknown_key_or_excluded
  (#key #repr: eqtype)
  (e: enum key repr)
  (excluded: list repr)
: Tot Type0
= (k: maybe_unknown_key e {
    match k with
    | Known _ -> True
    | Unknown r -> L.mem r excluded == false
  })

inline_for_extraction
let maybe_unknown_key_or_excluded_cons_coerce
  (#key #repr: eqtype)
  (e: enum key repr)
  (excluded: list repr)
  (k' : key)
  (r' : repr)
  (e' : enum key repr)
  (k: maybe_unknown_key_or_excluded e' (r' :: excluded))
: Pure (maybe_unknown_key_or_excluded e excluded)
  (requires (e == (k', r') :: e'))
  (ensures (fun _ -> True))
= match k with
  | Known r -> Known ((r <: key) <: enum_key e)
  | Unknown r -> Unknown ((r <: repr) <: unknown_enum_key e)

let maybe_unknown_key_or_excluded_of_repr
  (#key #repr: eqtype)
  (e: enum key repr)
  (excluded: list repr)
  (r: repr { L.mem r excluded == false } )
: Tot (maybe_unknown_key_or_excluded e excluded)
= maybe_unknown_key_of_repr e r

noextract
let rec gen_enum_univ_destr_gen_body
  (#key #repr: eqtype)
  (e: enum key repr)
  (excluded: list repr)
  (t: ((k: maybe_unknown_key_or_excluded e excluded) -> Tot Type0))
  (f: ((k: maybe_unknown_key_or_excluded e excluded) -> Tot (t k)))
  (combine_if: ((k: maybe_unknown_key_or_excluded e excluded) -> Tot (if_combinator (t k))))
  (r: T.term)
: Tot (T.tactic T.term)
  (decreases e)
= match e with
  | [] ->
    let g (r' : unknown_enum_key e {L.mem r' excluded == false}) : Tot (t (Unknown r')) =
      f (Unknown r')
    in
    T.bind (T.quote g) (fun g' ->
      let res = T.mk_app g' [
        (r, T.Q_Explicit)
      ]
      in
      T.return res
    )
  | ((k', r') :: e') ->
    let k' : enum_key e = k' in
    let fk' = f (Known k') in
    T.bind (T.quote fk') (fun rt ->
      T.bind (T.quote t) (fun t' ->
      T.bind (T.quote (maybe_unknown_key_or_excluded_of_repr #key #repr e excluded)) (fun myu ->
      let m_key = T.mk_app myu [r, T.Q_Explicit] in
      let m_type = T.mk_app t' [m_key, T.Q_Explicit] in
      T.bind (T.quote (op_Equality #repr r')) (fun eq_repr_k' ->
        let test = T.mk_app eq_repr_k' [
          (r, T.Q_Explicit);
        ]
        in
        let excluded' = r' :: excluded in
        T.bind (
          gen_enum_univ_destr_gen_body
            e'
            excluded'
            (fun (k: maybe_unknown_key_or_excluded e' excluded') ->
              t (maybe_unknown_key_or_excluded_cons_coerce e excluded k' r' e' k)
            )
            (fun (k: maybe_unknown_key_or_excluded e' excluded') ->
              f (maybe_unknown_key_or_excluded_cons_coerce e excluded k' r' e' k)
            )
            (fun (k: maybe_unknown_key_or_excluded e' excluded') ->
              combine_if (maybe_unknown_key_or_excluded_cons_coerce e excluded k' r' e' k)
            )
            r
        ) (fun t' ->
          T.bind (T.quote cond_true) (fun cond_true_q ->
          T.bind (T.quote cond_false) (fun cond_false_q ->
          T.bind (T.quote combine_if) (fun combine_if_q ->
          T.bind (mk_coercion rt m_type) (fun rt_constr ->
          T.bind (mk_coercion t' m_type) (fun t'_constr ->
          let cond_true_type = T.mk_app cond_true_q [test, T.Q_Explicit] in
          let cond_true_var = T.fresh_binder cond_true_type in
          let cond_true_abs = T.pack (T.Tv_Abs cond_true_var rt_constr) in
          let cond_false_type = T.mk_app cond_false_q [test, T.Q_Explicit] in
          let cond_false_var = T.fresh_binder cond_false_type in
          let cond_false_abs = T.pack (T.Tv_Abs cond_false_var t'_constr) in
          let m = T.mk_app combine_if_q [
            m_key, T.Q_Explicit;
            test, T.Q_Explicit;
            cond_true_abs, T.Q_Explicit;
            cond_false_abs, T.Q_Explicit;
          ]
          in
          T.return m
  ))))))))))

noextract
let rec gen_enum_univ_destr_gen
  (#key #repr: eqtype)
  (e: enum key repr)
  (t: ((k: maybe_unknown_key e) -> Tot Type0))
  (f: ((k: maybe_unknown_key e) -> Tot (t k)))
  (combine_if: ((k: maybe_unknown_key e) -> Tot (if_combinator (t k))))
: Tot (T.tactic unit)
= let open T in (
    tk <-- quote repr ;
    let x = fresh_binder tk in
    let r = T.pack (T.Tv_Var x) in
    body <-- gen_enum_univ_destr_gen_body #key #repr e [] t f combine_if r ;
    let res = T.pack (T.Tv_Abs x body) in
    _ <-- print (term_to_string res) ;
    t_exact true false (return res)
  )

inline_for_extraction
let is_known
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: maybe_unknown_key e)
: Tot bool
= match k with
  | Known _ -> true
  | _ -> false
