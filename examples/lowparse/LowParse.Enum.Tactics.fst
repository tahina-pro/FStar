module LowParse.Enum.Tactics
include LowParse.Enum.Base
open LowParse.Enum.Tactics.Aux

module L = FStar.List.Tot
module T = FStar.Tactics

noextract
let mk_coercion
  (from_value: T.term)
  (to_typ: T.term)
: Tot (T.tactic T.term)
= let x = T.fresh_binder to_typ in
  let x' = T.pack (T.Tv_Var x) in
  let res = T.pack (T.Tv_Let x from_value x') in
  T.return res

let mk_if (test e_true e_false: T.term) : Tot T.term =
  let br_true = (T.Pat_Constant T.C_True, e_true) in
  let br_false = (T.Pat_Constant T.C_False, e_false) in
  let m = T.pack (T.Tv_Match test [ br_true; br_false ] ) in
  m

noextract
let rec gen_enum_univ_destr_cons
  (#repr: eqtype)
  (e: enum repr)
  (t: ((k: enum_key e) -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
: Pure (T.tactic (
    (r: enum_repr e) ->
    Tot (t (enum_key_of_repr e r))
  ))
  (requires (Cons? e))
  (ensures (fun _ -> True))
  (decreases e)
= let ((k', r') :: e') = e in
  let e' : enum repr = e' in
  let r' : enum_repr e = r' in
  let k' : enum_key e = k' in
  let (v : t k' { v == f k' }) = f k' in
  match e' with
  | [] ->
    let (e' : enum repr {e == (k', r') :: e' /\ Nil? e' } ) = e' in
    let j = gen_enum_univ_destr_cons_partial_nil #repr e t f k' r' v e' in
    T.return j
  | _ ->
    let t'
      (k: enum_key e')
    : Tot Type0
    = t (enum_key_cons_coerce #repr e k' r' e' k)
    in
    let recurse'
      ()
    : Tot (T.tactic (
        (r: enum_repr e') ->
        Tot (t' (enum_key_of_repr #repr e' r))
      ))
    = gen_enum_univ_destr_cons
        #repr
        e'
        t'
        (fun (k: enum_key e') ->
          f (enum_key_cons_coerce #repr e k' r' e' k)
        )
    in
    let (e' : enum repr {e == (k', r') :: e' /\ Cons? e' }) = e' in
    T.bind (recurse' ()) (fun recurse ->
      let res = gen_enum_univ_destr_cons_partial_cons #repr e t f k' r' v e' recurse in
      T.return res
    )

noextract
let rec gen_enum_univ_destr
  (#repr: eqtype)
  (e: enum repr)
  (t: (enum_key e -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
: Tot (T.tactic unit)
= let open T in
  match e with
  | _ :: _ ->
    res' <-- gen_enum_univ_destr_cons #repr e t f ;
    res <-- quote res' ;
    _ <-- print (term_to_string res) ;
    exact_guard (return res)
  | _ ->
    let g (r: enum_repr #repr e) : Tot (t (enum_key_of_repr #repr e r)) =
      false_elim ()
    in
    exact_guard (quote g)

let maybe_unknown_key_or_excluded
  (#repr: eqtype)
  (e: enum repr)
  (excluded: list repr)
: Tot Type0
= (k: maybe_unknown_key e {
    match k with
    | Known _ -> True
    | Unknown r -> L.mem r excluded == false
  })

inline_for_extraction
let maybe_unknown_key_or_excluded_cons_coerce
  (#repr: eqtype)
  (e: enum repr)
  (excluded: list repr)
  (k' : string)
  (r' : repr)
  (e' : enum repr)
  (k: maybe_unknown_key_or_excluded e' (r' :: excluded))
: Pure (maybe_unknown_key_or_excluded e excluded)
  (requires (e == (k', r') :: e'))
  (ensures (fun _ -> True))
= match k with
  | Known r -> Known ((r <: string) <: enum_key e)
  | Unknown r -> Unknown ((r <: repr) <: unknown_enum_key e)

let maybe_unknown_key_or_excluded_of_repr
  (#repr: eqtype)
  (e: enum repr)
  (excluded: list repr)
  (r: repr { L.mem r excluded == false } )
: Tot (maybe_unknown_key_or_excluded e excluded)
= maybe_unknown_key_of_repr e r

noextract
let rec gen_enum_univ_destr_gen_body
  (#repr: eqtype)
  (e: enum repr)
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
      T.bind (T.quote (maybe_unknown_key_or_excluded_of_repr #repr e excluded)) (fun myu ->
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
  (#repr: eqtype)
  (e: enum repr)
  (t: ((k: maybe_unknown_key e) -> Tot Type0))
  (f: ((k: maybe_unknown_key e) -> Tot (t k)))
  (combine_if: ((k: maybe_unknown_key e) -> Tot (if_combinator (t k))))
: Tot (T.tactic unit)
= let open T in (
    tk <-- quote repr ;
    let x = fresh_binder tk in
    let r = T.pack (T.Tv_Var x) in
    body <-- gen_enum_univ_destr_gen_body #repr e [] t f combine_if r ;
    let res = T.pack (T.Tv_Abs x body) in
    _ <-- print (term_to_string res) ;
    t_exact true false (return res)
  )
