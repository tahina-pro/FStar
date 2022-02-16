module Steel.ST.Selectors

open Steel.ST.Util

let selector
  (v1 v2: vprop)
= t_of v1 -> Tot (t_of v2)

let selector_id
  (v: vprop)
: Tot (selector v v)
= id

let selector_fst
  (v1 v2: vprop)
: Tot (selector (v1 `star` v2) v1)
= fst

let selector_snd
  (v1 v2: vprop)
: Tot (selector (v1 `star` v2) v2)
= snd

let selector_compose
  (#v1 #v2 #v3: vprop)
  (s12: selector v1 v2)
  (s23: selector v2 v3)
: Tot (selector v1 v3)
= fun x1 -> s23 (s12 x1)

let selector_star
  (#v #v1 #v2: vprop)
  (s1: selector v v1)
  (s2: selector v v2)
: Tot (selector v (v1 `star` v2))
= fun x -> (s1 x, s2 x)

module T = FStar.Tactics

let rec inspect_app
  (t: T.term)
: T.Tac (T.term & list T.argv)
= match T.inspect t with
  | T.Tv_App f a ->
    let (f', a') = inspect_app f in
    (f', FStar.List.Tot.snoc (a', a))
  | _ -> (t, [])

let rec get_selector
  (from to: T.term)
: T.Tac T.term
= if T.term_eq from to
  then (T.mk_app (`selector_id) [from, T.Q_Explicit])
  else
    let app =
      match inspect_app to with
      | (tstar, [t1, T.Q_Explicit; t2, T.Q_Explicit]) ->
        if T.term_eq tstar (`star)
        then Some (t1, t2)
        else None
      | _ -> None
    in
    match app with
    | Some (t1, t2) ->
      let s1 = get_selector from t1 in
      let s2 = get_selector from t2 in
      (T.mk_app (`selector_star) [s1, T.Q_Explicit; s2, T.Q_Explicit])
    | _ ->
      begin match inspect_app from with
      | (tstar, [t1, T.Q_Explicit; t2, T.Q_Explicit]) ->
        T.try_with
          (fun _ ->
            let s = get_selector t1 to in
            T.mk_app (`selector_compose) [
              T.mk_app (`selector_fst) [t1, T.Q_Explicit; t2, T.Q_Explicit], T.Q_Explicit;
              s, T.Q_Explicit
            ]
          )
          (fun _ ->
            let s = get_selector t2 to in
            T.mk_app (`selector_compose) [
              T.mk_app (`selector_snd) [t1, T.Q_Explicit; t2, T.Q_Explicit], T.Q_Explicit;
              s, T.Q_Explicit
            ]
          )
      | _ ->
        let s1 = T.term_to_string from in
        let s2 = T.term_to_string to in
        T.fail (FStar.Printf.sprintf "Cannot find selector from %s to %s" s1 s2)
      end

let resolve_selector
  ()
: T.Tac unit
= let tg = T.cur_goal () in
  let s = T.term_to_string tg in
  let msg = FStar.Printf.sprintf "Not a selector goal: %s" s in
  match inspect_app tg with
  | (f, [from, T.Q_Explicit; to, T.Q_Explicit]) ->
    if T.term_eq f (`selector)
    then
      let sel = get_selector from to in
      T.exact sel
    else T.fail msg
  | _ ->
    T.fail msg

let select
  (#from: vprop)
  (to: vprop)
  (#[resolve_selector ()] sel: selector from to)
  (x: t_of from)
: Tot (t_of to)
= sel x

let f1 (v: vprop) (x: t_of v) =
  select v x

let f2 (v1 v2: vprop) (x: t_of (v1 `star` v2)) =
  select v2 x

let g (v1 v2 v3: vprop) (x: t_of (v1 `star` v2 `star` v3)) =
  select v2 x

let h (v1 v2 v3: vprop) (x: t_of (v1 `star` v2 `star` v3)) =
  select (v1 `star` v3) x

(* What about dependencies? *)

noeq
type het : Type u#(a + 1) =
| Het: (ty: Type u#a) -> (elt: ty) -> het

let het_empty = Het unit ()

let het_coll = (nat -> Tot het)

let het_coll_nil : het_coll = fun _ -> het_empty

let het_coll_cons (h: het) (c: het_coll) : Tot het_coll =
  fun x -> if x = 0 then h else c (x - 1)

let nselector (v: vprop) = (x: t_of v) -> het_coll

let nselector_elem (v: vprop) : nselector v = (fun x -> het_coll_cons (Het (t_of v) x) het_coll_nil)

module C = Steel.ST.Combinators

let nselector_vdep (vtag: vprop) (vpl: (t_of vtag -> Tot vprop)) (spl: ((x: t_of vtag) -> nselector (vpl x))) : Tot (nselector (vtag `vdep` vpl)) =
  fun x -> het_coll_cons (Het (t_of vtag) (C.vdep_dfst vtag vpl x)) (spl (C.vdep_dfst vtag vpl x) (C.vdep_dsnd vtag vpl x))

let nselector_star (v1 v2: vprop) (s: nselector v2) : Tot (nselector (v1 `star` v2)) =
  fun x -> het_coll_cons (Het (t_of v1) (fst x)) (s (snd x))

let nselect (#v: vprop) (s: nselector v) (x: t_of v) (n: nat) : Tot het =
  s x n
