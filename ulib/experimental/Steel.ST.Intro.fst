module Steel.ST.Intro
open Steel.ST.Util

(* How to generate introduction principles for cascades of `exists` *)

let intro_t (precond: prop) (from to: vprop) : Tot Type =
  (j: _) -> STGhost unit j from (fun _ -> to) precond (fun _ -> True)

let intro_ret (p: prop) (v: vprop) : intro_t p v (v `star` pure p) = fun _ -> intro_pure p

let intro_ret_true (v: vprop) : intro_t True v v = fun _ -> noop ()

let intro_ex
  (to: vprop)
  (ty: Type)
  (v: (ty -> Tot vprop))
  (v' : vprop)
  (sq: squash (v' == exists_ v))
  (p: prop)
  (i: intro_t p v' to)
  (x: ty)
: Tot (intro_t p (v x) to)
= fun j ->
  intro_exists x v;
  rewrite
    (exists_ v)
    v';
  i j

let intro_rewrite
  (from: vprop)
  (to: vprop)
  (p: prop)
  (i: intro_t p from to)
  (from' : vprop)
  (sq: squash (from == from'))
: Tot (intro_t p from' to)
= (* i // FIXME: WHY WHY WHY not? *)
  fun j -> rewrite from' from ; i j

noeq
type i_t =
  | IRet: vprop -> prop -> i_t
  | IExists: (ty: Type) -> (ty -> i_t) -> i_t

let rec i_as_vprop (x: i_t) : Tot vprop =
  match x with
  | IRet v p -> v `star` pure p
  | IExists ty v -> exists_ (fun x -> i_as_vprop (v x))

let rec mk_intro_t (x: i_t) (to: vprop) : Tot Type =
  match x with
  | IRet v p -> intro_t p v to
  | IExists ty v -> (x: ty) -> mk_intro_t (v x) to

let rec mk_intro' (x: i_t) (to: vprop) (i: intro_t True (i_as_vprop x) to) : Tot (mk_intro_t x to) =
  match x with
  | IRet v p -> intro_ret p v
  | IExists ty v ->
    let i : intro_t True (i_as_vprop (IExists ty v)) to = intro_rewrite _ _ True i _ () in
    fun s -> mk_intro' (v s) to (intro_ex to ty (fun s'-> i_as_vprop (v s')) (i_as_vprop (IExists ty v)) (_ by (FStar.Tactics.trefl ())) True i s)

let mk_intro_i (x: i_t) : Tot (mk_intro_t x (i_as_vprop x)) =
  mk_intro' x _ (intro_ret_true (i_as_vprop x))

noeq
type v_t =
  | VRet: vprop -> v_t
  | VPure: prop -> v_t
  | VStar: v_t -> v_t -> v_t
  | VExists: (ty: Type) -> (ty -> v_t) -> v_t

let rec v_as_vprop (x: v_t) : Tot vprop =
  match x with
  | VRet v -> v
  | VPure p -> pure p
  | VStar v1 v2 -> v_as_vprop v1 `star` v_as_vprop v2
  | VExists ty v -> exists_ (fun x -> v_as_vprop (v x))

let rec i_star_vprop (v: vprop) (p: prop) (i: i_t) : Tot i_t =
  match i with
  | IRet v' p' -> IRet (v `star` v') (p /\ p')
  | IExists ty f -> IExists ty (fun x -> i_star_vprop v p (f x))

let elim_exists_revealed (#a:Type)
                (#opened_invariants:_)
                (#p:a -> vprop)
                (_:unit)
  : STGhostT a opened_invariants
             (exists_ p)
             (fun x -> p x)
= let x = elim_exists () in
  Ghost.reveal x

let rec i_star_vprop_to_v (#j: _) (v: vprop) (p: prop) (i: i_t) : STGhostT unit j
  (i_as_vprop (i_star_vprop v p i))
  (fun _ -> v `star` pure p `star` i_as_vprop i)
=
  match i with
  | IRet v' p' -> 
    rewrite
      (i_as_vprop (i_star_vprop v p i))
      ((v `star` v') `star` pure (p /\ p'));
    elim_pure (p /\ p');
    intro_pure p;
    intro_pure p';
    rewrite
      (v `star` pure p `star` (v' `star` pure p'))
      (v `star` pure p `star` i_as_vprop i)
  | IExists ty f ->
    assert
      (i_as_vprop (i_star_vprop v p (IExists ty f)) ==
        exists_ (fun x -> i_as_vprop (i_star_vprop v p (f x))))
      by (FStar.Tactics.trefl ());
    rewrite
      (i_as_vprop (i_star_vprop v p i))
      (exists_ (fun x -> i_as_vprop (i_star_vprop v p (f x))));
    let x = elim_exists_revealed #ty #_ #(fun x -> i_as_vprop (i_star_vprop v p (f x))) () in
    i_star_vprop_to_v v p (f x);
    intro_exists x (fun x -> i_as_vprop (f x));
    assert
      (i_as_vprop (IExists ty f) == exists_ (fun x -> i_as_vprop (f x)))
      by (FStar.Tactics.trefl ());
    rewrite
      (exists_ (fun x -> i_as_vprop (f x)))
      (i_as_vprop i)

let rec i_star (i1 i2: i_t) : Tot i_t =
  match i1, i2 with
  | IRet v1 p1, _ -> i_star_vprop v1 p1 i2
  | _, IRet v2 p2 -> i_star_vprop v2 p2 i1
  | IExists ty1 f1, IExists ty2 f2 -> IExists ty1 (fun x1 -> IExists ty2 (fun x2 -> i_star (f1 x1) (f2 x2)))

let rec i_star_to_v (#j: _) (i1 i2: i_t) : STGhostT unit j
  (i_as_vprop (i1 `i_star` i2))
  (fun _ -> i_as_vprop i1 `star` i_as_vprop i2)
= match i1 with
  | IRet v1 p1 ->
    rewrite
      (i_as_vprop (i1 `i_star` i2))
      (i_as_vprop (i_star_vprop v1 p1 i2));
    i_star_vprop_to_v v1 p1 i2;
    rewrite
      (v1 `star` pure p1)
      (i_as_vprop i1)
  | IExists ty1 f1 ->
    begin match i2 with
    | IRet v2 p2 ->
      rewrite
        (i_as_vprop (i1 `i_star` i2))
        (i_as_vprop (i_star_vprop v2 p2 i1));
      i_star_vprop_to_v v2 p2 i1;
      rewrite
        (v2 `star` pure p2)
        (i_as_vprop i2)
    | IExists ty2 f2 ->
      assert
        (i_as_vprop (IExists ty1 f1 `i_star` IExists ty2 f2) ==
          exists_ (fun x1 -> exists_ (fun x2 -> i_as_vprop (f1 x1 `i_star` f2 x2))))
        by (FStar.Tactics.trefl ());
      rewrite
        (i_as_vprop (i1 `i_star` i2))
        (exists_ (fun x1 -> exists_ (fun x2 -> i_as_vprop (f1 x1 `i_star` f2 x2))));
      let x1 = elim_exists_revealed () in
      let x2 = elim_exists_revealed () in
      i_star_to_v (f1 x1) (f2 x2);
      intro_exists x1 (fun x1 -> i_as_vprop (f1 x1));
      intro_exists x2 (fun x2 -> i_as_vprop (f2 x2));
      assert
        (i_as_vprop (IExists ty1 f1) ==
          (exists_ (fun x1 -> i_as_vprop (f1 x1))))
        by (FStar.Tactics.trefl ());
      assert
        (i_as_vprop (IExists ty2 f2) ==
          (exists_ (fun x2 -> i_as_vprop (f2 x2))))
        by (FStar.Tactics.trefl ());
      rewrite
        (exists_ (fun x1 -> i_as_vprop (f1 x1)))
        (i_as_vprop i1);
      rewrite
        (exists_ (fun x2 -> i_as_vprop (f2 x2)))
        (i_as_vprop i2)
    end

let rec v_to_i (x: v_t) : Tot i_t =
  match x with
  | VRet v -> IRet v True
  | VPure p -> IRet emp p
  | VExists ty f -> IExists ty (fun x -> v_to_i (f x))
  | VStar v1 v2 -> v_to_i v1 `i_star` v_to_i v2

let rec i_to_v (#j: _) (v: v_t) : STGhostT unit j (i_as_vprop (v_to_i v)) (fun _ -> v_as_vprop v) =
  match v with
  | VRet _ ->
    rewrite
      (i_as_vprop (v_to_i v))
      (v_as_vprop v `star` pure True);
    elim_pure True
  | VPure p ->
    rewrite
      (i_as_vprop (v_to_i v))
      (emp `star` pure p);
    rewrite
      (pure p)
      (v_as_vprop v)
  | VStar v1 v2 ->
    rewrite
      (i_as_vprop (v_to_i v))
      (i_as_vprop (v_to_i v1 `i_star` v_to_i v2));
    i_star_to_v (v_to_i v1) (v_to_i v2);
    i_to_v v1;
    i_to_v v2;
    rewrite
      (v_as_vprop v1 `star` v_as_vprop v2)
      (v_as_vprop v)
  | VExists ty f ->
    assert
      (i_as_vprop (v_to_i (VExists ty f)) ==
        exists_ (fun x -> i_as_vprop (v_to_i (f x))))
      by (FStar.Tactics.trefl ());
    rewrite
      (i_as_vprop (v_to_i v))
      (exists_ (fun x -> i_as_vprop (v_to_i (f x))));
    let x = elim_exists_revealed () in
    i_to_v (f x);
    intro_exists x (fun x -> v_as_vprop (f x));
    assert
      (exists_ (fun x -> v_as_vprop (f x)) ==
        v_as_vprop (VExists ty f))
      by (FStar.Tactics.trefl ());
    rewrite
      (exists_ (fun x -> v_as_vprop (f x)))
      (v_as_vprop v)

let intro_i_to_v
    (v: v_t)
: Tot (intro_t True (i_as_vprop (v_to_i v)) (v_as_vprop v))
= fun _ -> i_to_v v

let mk_intro_v (x: v_t) : Tot (mk_intro_t (v_to_i x) (v_as_vprop x)) =
  mk_intro' (v_to_i x) _ (intro_i_to_v x)
