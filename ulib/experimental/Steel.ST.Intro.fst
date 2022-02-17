module Steel.ST.Intro
open Steel.ST.Util

(* How to generate introduction principles for cascades of `exists` *)

let intro_t (from to: vprop) : Tot Type =
  (j: _) -> STGhostT unit j from (fun _ -> to)

let intro_ret (v: vprop) : intro_t v v = fun _ -> noop ()

let intro_ex
  (to: vprop)
  (ty: Type)
  (v: (ty -> Tot vprop))
  (v' : vprop)
  (sq: squash (v' == exists_ v))
  (i: intro_t v' to)
  (x: ty)
: Tot (intro_t (v x) to)
= fun j ->
  intro_exists x v;
  rewrite
    (exists_ v)
    v';
  i j

let intro_rewrite
  (from: vprop)
  (to: vprop)
  (i: intro_t from to)
  (from' : vprop)
  (sq: squash (from == from'))
: Tot (intro_t from' to)
= (* i // FIXME: WHY WHY WHY not? *)
  fun j -> rewrite from' from ; i j

noeq
type i_t =
  | IRet: vprop -> i_t
  | IExists: (ty: Type) -> (ty -> i_t) -> i_t

let rec i_as_vprop (x: i_t) : Tot vprop =
  match x with
  | IRet v -> v
  | IExists ty v -> exists_ (fun x -> i_as_vprop (v x))

let rec mk_intro_t (x: i_t) (to: vprop) : Tot Type =
  match x with
  | IRet v -> intro_t v to
  | IExists ty v -> (x: ty) -> mk_intro_t (v x) to

let rec mk_intro' (x: i_t) (to: vprop) (i: intro_t (i_as_vprop x) to) : Tot (mk_intro_t x to) =
  match x with
  | IRet v -> intro_ret v
  | IExists ty v ->
    let i : intro_t (i_as_vprop (IExists ty v)) to = intro_rewrite _ _ i _ () in
    fun s -> mk_intro' (v s) to (intro_ex to ty (fun s'-> i_as_vprop (v s')) (i_as_vprop (IExists ty v)) (_ by (FStar.Tactics.trefl ())) i s)

let mk_intro (x: i_t) : Tot (mk_intro_t x (i_as_vprop x)) =
  mk_intro' x _ (intro_ret (i_as_vprop x))
