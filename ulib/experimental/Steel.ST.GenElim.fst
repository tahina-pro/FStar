module Steel.ST.GenElim

let gen_elim_f
  (p: vprop)
  (a: Type)
  (q: (a -> vprop))
  (post: (a -> prop))
: Tot Type
= ((opened: inames) -> STGhost a opened p q True post)

module U = FStar.Universe

let gen_unit_elim_t (i: gen_unit_elim_i) : Tot Type =
  gen_elim_f (compute_gen_unit_elim_p i) (U.raise_t u#_ u#1 unit) (fun _ -> compute_gen_unit_elim_q i) (fun _ -> compute_gen_unit_elim_post i)

let compute_gen_unit_elim_f_id
  (v: vprop)
: Tot (gen_unit_elim_t (GUEId v))
= fun _ -> noop (); U.raise_val ()

let compute_gen_unit_elim_f_pure
  (p: prop)
: Tot (gen_unit_elim_t (GUEPure p))
= fun _ ->
  rewrite (compute_gen_unit_elim_p (GUEPure p)) (pure p);
  elim_pure p;
  U.raise_val ()

let compute_gen_unit_elim_f_star
  (i1 i2: gen_unit_elim_i)
  (f1: gen_unit_elim_t i1)
  (f2: gen_unit_elim_t i2)
: Tot (gen_unit_elim_t (GUEStar i1 i2))
= fun _ ->
  rewrite (compute_gen_unit_elim_p (GUEStar i1 i2)) (compute_gen_unit_elim_p i1 `star` compute_gen_unit_elim_p i2);
  let _ = f1 _ in
  let _ = f2 _ in
  rewrite (compute_gen_unit_elim_q i1 `star` compute_gen_unit_elim_q i2) (compute_gen_unit_elim_q (GUEStar i1 i2));
  U.raise_val ()

let rec compute_gen_unit_elim_f
  (i: gen_unit_elim_i)
: GTot (gen_unit_elim_t i)
= match i returns (gen_unit_elim_t i) with
  | GUEId v -> compute_gen_unit_elim_f_id v
  | GUEPure p -> compute_gen_unit_elim_f_pure p
  | GUEStar i1 i2 -> compute_gen_unit_elim_f_star i1 i2 (compute_gen_unit_elim_f i1) (compute_gen_unit_elim_f i2)

let gen_elim_t (i: gen_elim_i) : Tot Type =
  gen_elim_f (compute_gen_elim_p i) (compute_gen_elim_a i) (compute_gen_elim_q i) (compute_gen_elim_post i)

let compute_gen_elim_f_unit
  (i: gen_unit_elim_i)
: GTot (gen_elim_t (GEUnit i))
= compute_gen_unit_elim_f i

let compute_gen_elim_f_star_l
  (i1: gen_elim_i)
  (f1: gen_elim_t i1)
  (i2: gen_unit_elim_i)
: GTot (gen_elim_t (GEStarL i1 i2))
= let f2 = compute_gen_unit_elim_f i2 in
  fun _ ->
  rewrite (compute_gen_elim_p (GEStarL i1 i2)) (compute_gen_elim_p i1 `star` compute_gen_unit_elim_p i2);
  let res = f1 _ in
  let _ = f2 _ in
  let res' : compute_gen_elim_a (GEStarL i1 i2) = coerce_with_trefl res in
  rewrite (compute_gen_elim_q i1 res `star` compute_gen_unit_elim_q i2) (compute_gen_elim_q (GEStarL i1 i2) res');
  res'

let compute_gen_elim_f_star_r
  (i1: gen_unit_elim_i)
  (i2: gen_elim_i)
  (f2: gen_elim_t i2)
: GTot (gen_elim_t (GEStarR i1 i2))
= let f1 = compute_gen_unit_elim_f i1 in
  fun _ ->
  rewrite (compute_gen_elim_p (GEStarR i1 i2)) (compute_gen_unit_elim_p i1 `star` compute_gen_elim_p i2);
  let _ = f1 _ in
  let res = f2 _ in
  let res' : compute_gen_elim_a (GEStarR i1 i2) = coerce_with_trefl res in
  rewrite (compute_gen_unit_elim_q i1 `star` compute_gen_elim_q i2 res) (compute_gen_elim_q (GEStarR i1 i2) res');
  res'

let compute_gen_elim_f_star
  (i1: gen_elim_i)
  (f1: gen_elim_t i1)
  (i2: gen_elim_i)
  (f2: gen_elim_t i2)
: GTot (gen_elim_t (GEStar i1 i2))
= fun _ ->
  rewrite (compute_gen_elim_p (GEStar i1 i2)) (compute_gen_elim_p i1 `star` compute_gen_elim_p i2);
  let res1 = f1 _ in
  let res2 = f2 _ in
  let res : compute_gen_elim_a (GEStar i1 i2) = coerce_with_trefl (res1, res2) in
  rewrite (compute_gen_elim_q i1 res1 `star` compute_gen_elim_q i2 res2) (compute_gen_elim_q (GEStar i1 i2) res);
  res

let compute_gen_elim_f_exists_no_abs0
  (a: Type0)
  (body: (a -> vprop))
: GTot (gen_elim_t (GEExistsNoAbs0 body))
= fun _ ->
  rewrite (compute_gen_elim_p (GEExistsNoAbs0 body)) (exists_ body);
  let gres = elim_exists () in
  let res : compute_gen_elim_a (GEExistsNoAbs0 body) = U.raise_val (Ghost.reveal gres) in //  coerce_with_trefl (Ghost.reveal gres) in
  rewrite (body gres) (compute_gen_elim_q (GEExistsNoAbs0 body) res);
  res

let rewrite_with_trefl (#opened:_) (p q:vprop)
  : STGhost unit opened
      p
      (fun _ -> q)
      (requires T.with_tactic T.trefl (p == q))
      (ensures fun _ -> True)
= rewrite p q

let compute_gen_elim_f_exists_unit0
  (a: Type0)
  (body: a -> gen_unit_elim_i)
: Tot (gen_elim_t (GEExistsUnit0 body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p (GEExistsUnit0 body)) (exists_ (fun x -> compute_gen_unit_elim_p (body x)));
  let gres = elim_exists () in
  let _ = compute_gen_unit_elim_f (body gres) _ in
  let res : compute_gen_elim_a (GEExistsUnit0 body) = U.raise_val (Ghost.reveal gres) in // coerce_with_trefl (Ghost.reveal gres) in
  rewrite (compute_gen_unit_elim_q (body gres)) (compute_gen_elim_q (GEExistsUnit0 body) res);
  res

let compute_gen_elim_f_exists0
  (a: Type0)
  (body: a -> gen_elim_i)
  (f: (x: a) -> GTot (gen_elim_t (body x)))
: Tot (gen_elim_t (GEExists0 body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p (GEExists0 body)) (exists_ (fun x -> compute_gen_elim_p (body x)));
  let gres1 = elim_exists () in
  let gres2 = f gres1 _ in
  let res : compute_gen_elim_a (GEExists0 body) = coerce_with_trefl (Mkdtuple2 #a #(fun x -> compute_gen_elim_a (body x)) (Ghost.reveal gres1) (Ghost.reveal gres2)) in
  rewrite (compute_gen_elim_q (body gres1) gres2) (compute_gen_elim_q (GEExists0 body) res);
  res

let compute_gen_elim_f_exists_no_abs1
  (a: Type)
  (body: (a -> vprop))
: GTot (gen_elim_t (GEExistsNoAbs1 body))
= fun _ ->
  rewrite (compute_gen_elim_p (GEExistsNoAbs1 body)) (exists_ body);
  let gres = elim_exists () in
  let res : compute_gen_elim_a (GEExistsNoAbs1 body) = coerce_with_trefl (Ghost.reveal gres) in
  rewrite (body gres) (compute_gen_elim_q (GEExistsNoAbs1 body) res);
  res

let compute_gen_elim_f_exists_unit1
  (a: Type)
  (body: a -> gen_unit_elim_i)
: Tot (gen_elim_t (GEExistsUnit1 body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p (GEExistsUnit1 body)) (exists_ (fun x -> compute_gen_unit_elim_p (body x)));
  let gres = elim_exists () in
  let _ = compute_gen_unit_elim_f (body gres) _ in
  let res : compute_gen_elim_a (GEExistsUnit1 body) = coerce_with_trefl (Ghost.reveal gres) in
  rewrite (compute_gen_unit_elim_q (body gres)) (compute_gen_elim_q (GEExistsUnit1 body) res);
  res

let compute_gen_elim_f_exists1
  (a: Type)
  (body: a -> gen_elim_i)
  (f: (x: a) -> GTot (gen_elim_t (body x)))
: Tot (gen_elim_t (GEExists1 body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p (GEExists1 body)) (exists_ (fun x -> compute_gen_elim_p (body x)));
  let gres1 = elim_exists () in
  let gres2 = f gres1 _ in
  let res : compute_gen_elim_a (GEExists1 body) = coerce_with_trefl (Mkdtuple2 #a #(fun x -> compute_gen_elim_a (body x)) (Ghost.reveal gres1) (Ghost.reveal gres2)) in
  rewrite (compute_gen_elim_q (body gres1) gres2) (compute_gen_elim_q (GEExists1 body) res);
  res

let rec compute_gen_elim_f
  (i: gen_elim_i)
: GTot (gen_elim_t i)
= match i returns (gen_elim_t i) with
  | GEUnit i -> compute_gen_elim_f_unit i
  | GEStarL i1 i2 -> compute_gen_elim_f_star_l i1 (compute_gen_elim_f i1) i2
  | GEStarR i1 i2 -> compute_gen_elim_f_star_r i1 i2 (compute_gen_elim_f i2)
  | GEStar i1 i2 -> compute_gen_elim_f_star i1 (compute_gen_elim_f i1) i2 (compute_gen_elim_f i2)
  | GEExistsNoAbs0 body -> compute_gen_elim_f_exists_no_abs0 _ body
  | GEExistsUnit0 body -> compute_gen_elim_f_exists_unit0 _ body
  | GEExists0 body -> compute_gen_elim_f_exists0 _ body (fun x -> compute_gen_elim_f (body x))
  | GEExistsNoAbs1 body -> compute_gen_elim_f_exists_no_abs1 _ body
  | GEExistsUnit1 body -> compute_gen_elim_f_exists_unit1 _ body
  | GEExists1 body -> compute_gen_elim_f_exists1 _ body (fun x -> compute_gen_elim_f (body x))

let rec tele_p (x: gen_elim_tele) : Tot vprop =
  match x with
  | TRet v p -> v `star` pure p
  | TExists0 ty body -> exists_ (fun x -> tele_p (body x))
  | TExists1 ty body -> exists_ (fun x -> tele_p (body x))

let elim_exists' (#a:Type)
                (#opened_invariants:_)
                (#p:a -> vprop)
                (_:unit)
  : STGhostT (a) opened_invariants
             (exists_ p)
             (fun x -> p x)
= let gx = elim_exists () in
  let x = Ghost.reveal gx in
  rewrite (p gx) (p x);
  x

let vprop_rewrite (from to: vprop) : Tot Type =
  gen_elim_f from unit (fun _ -> to) (fun _ -> True)

let tele_star_vprop_correct_ret
  (v': vprop) (p': prop) (v: vprop) (p: prop)
: Tot (vprop_rewrite (tele_p (TRet v' p') `star` v `star` pure p) (tele_p (tele_star_vprop (TRet v' p') v p)))
= fun _ ->
    elim_pure p;
    rewrite (tele_p _) (v' `star` pure p');
    elim_pure p';
    intro_pure (p /\ p');
    rewrite ((v `star` v') `star` pure (p /\ p')) (tele_p _)

let tele_star_vprop_correct_exists0
  (v: vprop) (p: prop)
  (ty: _) (body: ty -> gen_elim_tele) (ih: (x: ty) -> GTot (vprop_rewrite (tele_p (body x) `star` v `star` pure p) (tele_p (tele_star_vprop (body x) v p))))
: Tot (vprop_rewrite (tele_p (TExists0 ty body) `star` v `star` pure p) (tele_p (tele_star_vprop (TExists0 ty body) v p)))
= fun _ ->
    rewrite_with_trefl (tele_p _) (exists_ (fun x -> tele_p (body x)));
    let x = elim_exists' () in
    ih x _;
    intro_exists x (fun x -> tele_p (tele_star_vprop (body x) v p));
    rewrite_with_trefl (exists_ (fun x -> tele_p (tele_star_vprop (body x) v p))) (tele_p _)

let tele_star_vprop_correct_exists1
  (v: vprop) (p: prop)
  (ty: _) (body: ty -> gen_elim_tele) (ih: (x: ty) -> GTot (vprop_rewrite (tele_p (body x) `star` v `star` pure p) (tele_p (tele_star_vprop (body x) v p))))
: Tot (vprop_rewrite (tele_p (TExists1 ty body) `star` v `star` pure p) (tele_p (tele_star_vprop (TExists1 ty body) v p)))
= fun _ ->
    rewrite_with_trefl (tele_p _) (exists_ (fun x -> tele_p (body x)));
    let x = elim_exists' () in
    ih x _;
    intro_exists x (fun x -> tele_p (tele_star_vprop (body x) v p));
    rewrite_with_trefl (exists_ (fun x -> tele_p (tele_star_vprop (body x) v p))) (tele_p _)

let rec tele_star_vprop_correct
  (i: gen_elim_tele) (v: vprop) (p: prop)
: GTot (vprop_rewrite
    (tele_p i `star` v `star` pure p)
    (tele_p (tele_star_vprop i v p))
  )
= match i returns vprop_rewrite
    (tele_p i `star` v `star` pure p)
    (tele_p (tele_star_vprop i v p)) with
  | TRet v' p' -> tele_star_vprop_correct_ret v' p' v p
  | TExists0 ty body -> tele_star_vprop_correct_exists0 v p ty body (fun x -> tele_star_vprop_correct (body x) v p)
  | TExists1 ty body -> tele_star_vprop_correct_exists1 v p ty body (fun x -> tele_star_vprop_correct (body x) v p)

let tele_star_correct_ret_l
  (v1: vprop) (p1: prop) (i2: gen_elim_tele)
: Tot (vprop_rewrite (tele_p (TRet v1 p1) `star` tele_p i2) (tele_p (TRet v1 p1 `tele_star` i2)))
= fun _ ->
  rewrite (tele_p (TRet v1 p1)) (v1 `star` pure p1);
  tele_star_vprop_correct i2 v1 p1 _;
  rewrite (tele_p _) (tele_p _)

let tele_star_correct_ret_r
  (i1: gen_elim_tele { ~ (TRet? i1) }) (v2: vprop) (p2: prop)
: Tot (vprop_rewrite (tele_p i1 `star` tele_p (TRet v2 p2)) (tele_p (i1 `tele_star` TRet v2 p2)))
= fun _ ->
  rewrite (tele_p (TRet v2 p2)) (v2 `star` pure p2);
  tele_star_vprop_correct i1 v2 p2 _;
  rewrite (tele_p _) (tele_p (i1 `tele_star` TRet v2 p2))

let tele_star_correct_exists_gen
  (ty1: Type u#u1) (f1: ty1 -> gen_elim_tele) (ty2: Type u#u2) (f2: ty2 -> gen_elim_tele)
  (ih: (x1: ty1) -> (x2: ty2) -> GTot (vprop_rewrite (tele_p (f1 x1) `star` tele_p (f2 x2)) (tele_p (f1 x1 `tele_star` f2 x2))))
  (tf1: gen_elim_tele)
  (tf1_eq: squash (tele_p tf1 == exists_ (fun x -> tele_p (f1 x))))
  (tf2: gen_elim_tele)
  (tf2_eq: squash (tele_p tf2 == exists_ (fun x -> tele_p (f2 x))))
  (ts: gen_elim_tele)
  (ts_eq: squash (tele_p ts == exists_ (fun x1 -> exists_ (fun x2 -> tele_p (tele_star (f1 x1) (f2 x2))))))
: Tot (vprop_rewrite (tele_p tf1 `star` tele_p tf2) (tele_p ts))
= fun _ ->
  rewrite (tele_p tf1) (exists_ (fun x1 -> tele_p (f1 x1)));
  let x1 = elim_exists' () in
  rewrite (tele_p tf2) (exists_ (fun x2 -> tele_p (f2 x2)));
  let x2 = elim_exists' () in
  ih x1 x2 _;
  intro_exists x2 (fun x2 -> tele_p (tele_star (f1 x1) (f2 x2)));
  intro_exists x1 (fun x1 -> exists_ (fun x2 -> tele_p (tele_star (f1 x1) (f2 x2))));
  rewrite (exists_ _) (tele_p _)

let tele_star_correct_exists_0_0
  (ty1: _) (f1: ty1 -> gen_elim_tele) (ty2: _) (f2: ty2 -> gen_elim_tele)
  (ih: (x1: ty1) -> (x2: ty2) -> GTot (vprop_rewrite (tele_p (f1 x1) `star` tele_p (f2 x2)) (tele_p (f1 x1 `tele_star` f2 x2))))
: Tot (vprop_rewrite (tele_p (TExists0 ty1 f1) `star` tele_p (TExists0 ty2 f2)) (tele_p (tele_star (TExists0 ty1 f1) (TExists0 ty2 f2))))
= tele_star_correct_exists_gen ty1 f1 ty2 f2 ih _ (_ by (T.trefl ())) _ (_ by (T.trefl ())) _ (_ by (T.trefl ()))

let tele_star_correct_exists_0_1
  (ty1: _) (f1: ty1 -> gen_elim_tele) (ty2: _) (f2: ty2 -> gen_elim_tele)
  (ih: (x1: ty1) -> (x2: ty2) -> GTot (vprop_rewrite (tele_p (f1 x1) `star` tele_p (f2 x2)) (tele_p (f1 x1 `tele_star` f2 x2))))
: Tot (vprop_rewrite (tele_p (TExists0 ty1 f1) `star` tele_p (TExists1 ty2 f2)) (tele_p (tele_star (TExists0 ty1 f1) (TExists1 ty2 f2))))
= tele_star_correct_exists_gen ty1 f1 ty2 f2 ih _ (_ by (T.trefl ())) _ (_ by (T.trefl ())) _ (_ by (T.trefl ()))

let tele_star_correct_exists_1_0
  (ty1: _) (f1: ty1 -> gen_elim_tele) (ty2: _) (f2: ty2 -> gen_elim_tele)
  (ih: (x1: ty1) -> (x2: ty2) -> GTot (vprop_rewrite (tele_p (f1 x1) `star` tele_p (f2 x2)) (tele_p (f1 x1 `tele_star` f2 x2))))
: Tot (vprop_rewrite (tele_p (TExists1 ty1 f1) `star` tele_p (TExists0 ty2 f2)) (tele_p (tele_star (TExists1 ty1 f1) (TExists0 ty2 f2))))
= tele_star_correct_exists_gen ty1 f1 ty2 f2 ih _ (_ by (T.trefl ())) _ (_ by (T.trefl ())) _ (_ by (T.trefl ()))

let tele_star_correct_exists_1_1
  (ty1: _) (f1: ty1 -> gen_elim_tele) (ty2: _) (f2: ty2 -> gen_elim_tele)
  (ih: (x1: ty1) -> (x2: ty2) -> GTot (vprop_rewrite (tele_p (f1 x1) `star` tele_p (f2 x2)) (tele_p (f1 x1 `tele_star` f2 x2))))
: Tot (vprop_rewrite (tele_p (TExists1 ty1 f1) `star` tele_p (TExists1 ty2 f2)) (tele_p (tele_star (TExists1 ty1 f1) (TExists1 ty2 f2))))
= tele_star_correct_exists_gen ty1 f1 ty2 f2 ih _ (_ by (T.trefl ())) _ (_ by (T.trefl ())) _ (_ by (T.trefl ()))

let rec tele_star_correct
  (i1 i2: gen_elim_tele)
: GTot (vprop_rewrite (tele_p i1 `star` tele_p i2) (tele_p (i1 `tele_star` i2)))
= match i1, i2 with
  | TRet v1 p1, _ ->
    coerce_eq () (tele_star_correct_ret_l v1 p1 i2)
  | _, TRet v2 p2 ->
    coerce_eq () (tele_star_correct_ret_r i1 v2 p2)
  | _ ->
    begin match i1 with
    | TExists0 ty1 f1 ->
      begin match i2 with
      | TExists0 ty2 f2 -> coerce_eq () (tele_star_correct_exists_0_0 ty1 f1 ty2 f2 (fun x1 x2 -> tele_star_correct (f1 x1) (f2 x2)))
      | TExists1 ty2 f2 -> coerce_eq () (tele_star_correct_exists_0_1 ty1 f1 ty2 f2 (fun x1 x2 -> tele_star_correct (f1 x1) (f2 x2)))
      end
    | TExists1 ty1 f1 ->
      begin match i2 with
      | TExists0 ty2 f2 -> coerce_eq () (tele_star_correct_exists_1_0 ty1 f1 ty2 f2 (fun x1 x2 -> tele_star_correct (f1 x1) (f2 x2)))
      | TExists1 ty2 f2 -> coerce_eq () (tele_star_correct_exists_1_1 ty1 f1 ty2 f2 (fun x1 x2 -> tele_star_correct (f1 x1) (f2 x2)))
      end
    end

[@@noextract_to "Plugin" ]
let ge_to_tele_t
  (i: gen_elim_i)
: Tot Type
= vprop_rewrite (compute_gen_elim_p i) (tele_p (compute_gen_elim_tele i))

let compute_gen_elim_tele_correct_unit
  (v: gen_unit_elim_i)
: Tot (ge_to_tele_t (GEUnit v))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (compute_gen_unit_elim_p v);
  let _ = compute_gen_unit_elim_f v _ in
  intro_pure (compute_gen_unit_elim_post v);
  rewrite_with_trefl (compute_gen_unit_elim_q v `star` pure _) (tele_p _)

let compute_gen_elim_tele_correct_star_l
  (l: gen_elim_i)
  (ihl: ge_to_tele_t l)
  (ru: gen_unit_elim_i)
: Tot (ge_to_tele_t (GEStarL l ru))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (compute_gen_elim_p l `star` compute_gen_unit_elim_p ru);
  ihl _;
  let _ = compute_gen_unit_elim_f ru _ in
  intro_pure (compute_gen_unit_elim_post ru);
  tele_star_vprop_correct _ _ _ _;
  rewrite_with_trefl (tele_p _) (tele_p _)

let compute_gen_elim_tele_correct_star_r
  (lu: gen_unit_elim_i)
  (r: gen_elim_i)
  (ihr: ge_to_tele_t r)
: Tot (ge_to_tele_t (GEStarR lu r))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (compute_gen_unit_elim_p lu `star` compute_gen_elim_p r);
  ihr _;
  let _ = compute_gen_unit_elim_f lu _ in
  intro_pure (compute_gen_unit_elim_post lu);
  tele_star_vprop_correct _ _ _ _;
  rewrite_with_trefl (tele_p _) (tele_p _)

let compute_gen_elim_tele_correct_star
  (l: gen_elim_i)
  (ihl: ge_to_tele_t l)
  (r: gen_elim_i)
  (ihr: ge_to_tele_t r)
: Tot (ge_to_tele_t (GEStar l r))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (compute_gen_elim_p l `star` compute_gen_elim_p r);
  ihl _;
  ihr _;
  tele_star_correct (compute_gen_elim_tele l) (compute_gen_elim_tele r) _;
  rewrite_with_trefl (tele_p _) (tele_p _)

let compute_gen_elim_tele_correct_exists_no_abs0
  (ty: _)
  (body: ty -> vprop)
: Tot (ge_to_tele_t (GEExistsNoAbs0 #ty body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (exists_ body);
  let x = elim_exists' () in
  intro_pure True;
  intro_exists x (fun x -> body x `star` pure True);
  rewrite_with_trefl (exists_ _) (tele_p _)

let compute_gen_elim_tele_correct_exists_unit0
  (ty: _)
  (body: ty -> gen_unit_elim_i)
: Tot (ge_to_tele_t (GEExistsUnit0 #ty body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (exists_ (fun x -> compute_gen_unit_elim_p (body x)));
  let x = elim_exists' () in
  let _ = compute_gen_unit_elim_f (body x) _ in
  intro_pure (compute_gen_unit_elim_post (body x));
  intro_exists x (fun x -> compute_gen_unit_elim_q (body (x)) `star` pure (compute_gen_unit_elim_post (body (x))));
  rewrite_with_trefl (exists_ _) (tele_p _)

let compute_gen_elim_tele_correct_exists0
  (ty: _)
  (body: ty -> gen_elim_i)
  (ih: (x: ty) -> GTot (ge_to_tele_t (body x)))
: Tot (ge_to_tele_t (GEExists0 #ty body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (exists_ (fun x -> compute_gen_elim_p (body x)));
  let x = elim_exists' () in
  ih x _;
  intro_exists (x) (fun x -> tele_p (compute_gen_elim_tele (body (x))));
  rewrite_with_trefl (exists_ _) (tele_p _)

let compute_gen_elim_tele_correct_exists_no_abs1
  (ty: _)
  (body: ty -> vprop)
: Tot (ge_to_tele_t (GEExistsNoAbs1 #ty body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (exists_ body);
  let x = elim_exists' () in
  intro_pure True;
  intro_exists x (fun x -> body x `star` pure True);
  rewrite_with_trefl (exists_ _) (tele_p _)

let compute_gen_elim_tele_correct_exists_unit1
  (ty: _)
  (body: ty -> gen_unit_elim_i)
: Tot (ge_to_tele_t (GEExistsUnit1 #ty body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (exists_ (fun x -> compute_gen_unit_elim_p (body x)));
  let x = elim_exists' () in
  let _ = compute_gen_unit_elim_f (body x) _ in
  intro_pure (compute_gen_unit_elim_post (body x));
  intro_exists x (fun x -> compute_gen_unit_elim_q (body x) `star` pure (compute_gen_unit_elim_post (body x)));
  rewrite_with_trefl (exists_ _) (tele_p _)

let compute_gen_elim_tele_correct_exists1
  (ty: _)
  (body: ty -> gen_elim_i)
  (ih: (x: ty) -> GTot (ge_to_tele_t (body x)))
: Tot (ge_to_tele_t (GEExists1 #ty body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (exists_ (fun x -> compute_gen_elim_p (body x)));
  let x = elim_exists' () in
  ih x _;
  intro_exists x (fun x -> tele_p (compute_gen_elim_tele (body x)));
  rewrite_with_trefl (exists_ _) (tele_p _)

let rec compute_gen_elim_tele_correct
  (x: gen_elim_i)
: GTot (ge_to_tele_t x)
= match x returns ge_to_tele_t x with
  | GEUnit v -> compute_gen_elim_tele_correct_unit v
  | GEStarL l ru -> compute_gen_elim_tele_correct_star_l l (compute_gen_elim_tele_correct l) ru
  | GEStarR lu r -> compute_gen_elim_tele_correct_star_r lu r (compute_gen_elim_tele_correct r)
  | GEStar l r -> compute_gen_elim_tele_correct_star l (compute_gen_elim_tele_correct l) r (compute_gen_elim_tele_correct r)
  | GEExistsNoAbs0 #ty body -> compute_gen_elim_tele_correct_exists_no_abs0 ty body
  | GEExistsUnit0 #ty body -> compute_gen_elim_tele_correct_exists_unit0 ty body
  | GEExists0 #ty body -> compute_gen_elim_tele_correct_exists0 ty body (fun x -> compute_gen_elim_tele_correct (body x))
  | GEExistsNoAbs1 #ty body -> compute_gen_elim_tele_correct_exists_no_abs1 ty body
  | GEExistsUnit1 #ty body -> compute_gen_elim_tele_correct_exists_unit1 ty body
  | GEExists1 #ty body -> compute_gen_elim_tele_correct_exists1 ty body (fun x -> compute_gen_elim_tele_correct (body x))

let rec gen_elim_nondep_p (ty: list (tagged_type)) : Tot (curried_function_type u#2 ty (vprop) -> curried_function_type ty (prop) -> Tot vprop) =
  match ty as ty' returns curried_function_type u#2 ty' (vprop) -> curried_function_type ty' (prop) -> Tot vprop with
  | [] -> fun q post -> q `star` pure post
  | T0 t :: tq -> fun q post -> exists_ (fun x -> gen_elim_nondep_p tq (q x) (post x))
  | T1 t :: tq -> fun q post -> exists_ (fun x -> gen_elim_nondep_p tq (q x) (post x))

let gen_elim_nondep_sem_correct_cons
  (tq: list tagged_type)
  (#ta: Type u#a)
  (q: (ta -> curried_function_type u#2 tq vprop))
  (post: (ta -> curried_function_type tq prop))
  (phi: (
    (x: ta) ->
    Lemma
    (tele_p (gen_elim_nondep_sem tq (q x) (post x)) `equiv` gen_elim_nondep_p tq (q x) (post x))
  ))
  (a: vprop)
  (a_eq: squash (a == exists_ (fun x -> tele_p (gen_elim_nondep_sem tq (q x) (post x)))))
  (b: vprop)
  (b_eq: squash (b == exists_ (fun x -> gen_elim_nondep_p tq (q x) (post x))))
: Lemma
  (a `equiv` b)
= Classical.forall_intro phi;
  exists_equiv (fun x -> tele_p (gen_elim_nondep_sem tq (q x) (post x))) (fun x -> gen_elim_nondep_p tq (q x) (post x))

let rec gen_elim_nondep_sem_correct
  (ty: list (tagged_type))
: Tot ((q: curried_function_type ty _) -> (post: curried_function_type ty _) -> Lemma
    (tele_p (gen_elim_nondep_sem ty q post) `equiv` gen_elim_nondep_p ty q post)
  )
= match ty returns ((q: curried_function_type ty _) -> (post: curried_function_type ty _) -> Lemma
    (tele_p (gen_elim_nondep_sem ty q post) `equiv` gen_elim_nondep_p ty q post)
  )
  with
  | [] -> fun q post -> equiv_refl (q `star` pure (post ))
  | (T0 ta) :: tq ->
    begin fun q post ->
      gen_elim_nondep_sem_correct_cons
        tq q post
        (fun x -> gen_elim_nondep_sem_correct tq (q x) (post x))
        (tele_p (gen_elim_nondep_sem (T0 ta :: tq) q post)) (_ by (T.trefl ()))
        (gen_elim_nondep_p (T0 ta :: tq) q post) (_ by (T.trefl ()))
    end
  | (T1 ta) :: tq ->
    begin fun q post ->
      gen_elim_nondep_sem_correct_cons
        tq q post
        (fun x -> gen_elim_nondep_sem_correct tq (q x) (post x))
        (tele_p (gen_elim_nondep_sem (T1 ta :: tq) q post)) (_ by (T.trefl ()))
        (gen_elim_nondep_p (T1 ta :: tq) q post) (_ by (T.trefl ()))
    end

let compute_gen_elim_nondep_correct_t
  (i0: gen_elim_i)
  (ty: list (tagged_type))
: Tot Type
= (q: _) ->
  (post: _) ->
  (intro: vprop_rewrite (compute_gen_elim_p i0) (gen_elim_nondep_p ty q post)) ->
  GTot (gen_elim_f
    (compute_gen_elim_p i0)
    (compute_gen_elim_nondep_a' ty)
    (compute_uncurry _ (compute_gen_elim_p' i0) ty q)
    (compute_uncurry _ (True) ty post)
  )

let compute_gen_elim_nondep_correct0
  (i0: gen_elim_i)
: Tot (compute_gen_elim_nondep_correct_t i0 [])
= fun q post intro _ ->
    intro _;
    rewrite_with_trefl (gen_elim_nondep_p _ _ _) (q `star` pure (post));
    let res = U.raise_val () in
    elim_pure _;
    rewrite_with_trefl (q) (compute_uncurry _ (compute_gen_elim_p' i0) _ _ res);
    res

let compute_gen_elim_nondep_correct1_0
  (i0: gen_elim_i)
  (t1: Type)
: Tot (compute_gen_elim_nondep_correct_t i0 [T0 t1])
= fun q post intro _ ->
    intro _;
    rewrite_with_trefl (gen_elim_nondep_p _ _ _) (exists_ (fun x1 -> q x1 `star` pure (post x1)));
    let x1 = elim_exists' () in
    let res = U.raise_val u#_ u#1 x1 in
    rewrite (q _) (compute_uncurry vprop (compute_gen_elim_p' i0) [T0 t1] q res);
    elim_pure (post x1);
    res

let compute_gen_elim_nondep_correct1_1
  (i0: gen_elim_i)
  (t1: Type)
: Tot (compute_gen_elim_nondep_correct_t i0 [T1 t1])
= fun q post intro _ ->
    intro _;
    rewrite_with_trefl (gen_elim_nondep_p _ _ _) (exists_ (fun x1 -> q x1 `star` pure (post x1)));
    let x1 = elim_exists' () in
    rewrite (q _) (compute_uncurry vprop (compute_gen_elim_p' i0) [T1 t1] q x1);
    elim_pure (post x1);
    x1

let rewrite_with_squash (#opened:inames)
            (p q: vprop)
            (sq: squash (p == q))
  : STGhostT unit opened p (fun _ -> q)
= rewrite p q

let compute_gen_elim_nondep_correct2_gen
  (t1: Type u#u1)
  (t2: Type u#u2)
  (i0: gen_elim_i)
  (l: list tagged_type)
  (prf: (mktuple: (t1 -> t2 -> compute_gen_elim_nondep_a' l) & (
    (q: curried_function_type u#2 l vprop) ->
    (post: curried_function_type l prop) ->
    (q': (t1 -> t2 -> vprop) & (
      (post': (t1 -> t2 -> prop) & (
        squash (gen_elim_nondep_p l q post == exists_ (fun x1 -> exists_ (fun x2 -> q' x1 x2 `star` pure (post' x1 x2)))) &
        ((x1: t1) -> (x2: t2) -> (
          squash (q' x1 x2 == compute_uncurry vprop (compute_gen_elim_p' i0) l q (mktuple x1 x2)) &
          squash (post' x1 x2 == compute_uncurry prop True l post (mktuple x1 x2))
        ))
      ))
    ))
  )))
: Tot (compute_gen_elim_nondep_correct_t i0 l)
= fun q post intro _ ->
    intro _;
    let (| mktuple, rewrites |) = prf in
    let (| q', (| post', (sq1, f) |) |) = rewrites q post in
    rewrite_with_squash (gen_elim_nondep_p l q post) (exists_ (fun x1 -> exists_ (fun x2 -> q' x1 x2 `star` pure (post' x1 x2)))) sq1;
    let x1 = elim_exists' () in
    let x2 = elim_exists' () in
    let res = mktuple x1 x2 in
    let (sq2, _) = f x1 x2 in
    elim_pure _;
    rewrite_with_squash (q' _ _) (compute_uncurry _ (compute_gen_elim_p' i0) _ _ res) sq2;
    res

let assert_prop
  (p: prop)
: Pure (squash p)
    (requires (normalize p))
    (ensures (fun _ -> True))
= ()

let compute_gen_elim_nondep_correct_aux_1 (tl: list T.term) (lemma: T.term) (constructor: T.term) : T.Tac unit =
  T.apply (
    T.mk_app
      lemma
      (T.map (fun t -> (t, T.Q_Explicit)) tl)
  );
  T.norm [delta_attr [(`%gen_elim_reduce)]; iota; zeta];
  T.apply (T.mk_app (`Mkdtuple2) [constructor, T.Q_Explicit]);
  let q = intro_term () in
  let post = intro_term () in
  T.apply (T.mk_app (`Mkdtuple2) [q, T.Q_Explicit]);
  T.apply (T.mk_app (`Mkdtuple2) [post, T.Q_Explicit]);
  T.apply (`Mktuple2);
  T.trefl ();
  let _ = T.intros () in
  T.apply (`Mktuple2);
  T.trefl ();
  T.trefl ()

let compute_gen_elim_nondep_correct_aux_2 (lemma: T.term) (constructor: T.term) : T.Tac unit =
  let (_, args) = T.collect_app (T.cur_goal ()) in
  match args with
  | _ :: (args, _) :: _ ->
    let args = list_of_term_list args in
    let tl = list_tac_map
      (fun t ->
        let (_, t) = T.collect_app t in
        match t with
        | [] -> T.fail "compute_gen_elim_nondep_correct_aux_2: tl"
        | (t, _) :: _ -> t
      )
      args
    in
    compute_gen_elim_nondep_correct_aux_1 tl lemma constructor
  | _ -> T.fail "compute_gen_elim_nondep_correct_aux_2: args"

let rec compute_gen_elim_nondep_correct_aux_3 (lemma: T.term) (constructor: T.term) (tl: list T.term) : T.Tac unit =
  match tl with
  | [] -> compute_gen_elim_nondep_correct_aux_2 lemma constructor; T.qed ()
  | a :: q ->
    T.destruct a;
    T.iterAll (fun _ ->
      let _ = T.intro () in
      let eq = T.intro () in
      T.rewrite eq;
      compute_gen_elim_nondep_correct_aux_3 lemma constructor q
    )

let compute_gen_elim_nondep_correct_tac (lemma: T.term) (constructor: T.term) : T.Tac unit =
  let (_, args) = T.collect_app (T.cur_goal ()) in
  match args with
  | _ :: (args, _) :: _ ->
    let args = list_of_term_list args in
    compute_gen_elim_nondep_correct_aux_3 lemma constructor args
  | _ -> T.fail "compute_gen_elim_nondep_correct_aux_2: args"

let compute_gen_elim_nondep_correct2
  (i0: gen_elim_i)
  (t1: _) (t2: _)
: Tot (compute_gen_elim_nondep_correct_t i0 [t1; t2])
= (_ by (compute_gen_elim_nondep_correct_tac (`compute_gen_elim_nondep_correct2_gen) (`UTuple2)))

let compute_gen_elim_nondep_correct_default
  (i0: gen_elim_i)
  (t1 t2 t3 (* t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 *) : _) (tq: list _)
: Tot (compute_gen_elim_nondep_correct_t i0 (t1 :: t2 :: t3 (* :: t4 :: t5 :: t6 :: t7 :: t8 :: t9 :: t10 :: t11 :: t12 :: t13 :: t14 :: t15 *) :: tq))
= fun q post intro _ ->
    // default case: no exists is opened
    let res : compute_gen_elim_nondep_a' (t1 :: t2 :: t3 (* :: t4 :: t5 :: t6 :: t7 :: t8 :: t9 :: t10 :: t11 :: t12 :: t13 :: t14 :: t15 *) :: tq) = (U.raise_val ()) in
    rewrite (compute_gen_elim_p i0) (compute_uncurry _ (compute_gen_elim_p' i0) _ _ res);
    res

let compute_gen_elim_nondep_correct'
  (i0: gen_elim_i)
  (ty: list tagged_type)
: Tot (compute_gen_elim_nondep_correct_t i0 ty)
= match ty returns compute_gen_elim_nondep_correct_t i0 ty with
  | [] -> compute_gen_elim_nondep_correct0 i0
  | [T0 t1] -> compute_gen_elim_nondep_correct1_0 i0 t1
  | [T1 t1] -> compute_gen_elim_nondep_correct1_1 i0 t1
  | [t1; t2] -> compute_gen_elim_nondep_correct2 i0 t1 t2
  | t1 :: t2 :: t3 (* :: t4 :: t5 :: t6 :: t7 :: t8 :: t9 :: t10 :: t11 :: t12 :: t13 :: t14 :: t15 *) :: tq -> compute_gen_elim_nondep_correct_default i0 t1 t2 t3 (* t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 *) tq  

let compute_gen_elim_nondep_correct_0
  (i0: gen_elim_i)
  (i: gen_elim_nondep_t)
= match i returns 
  (sq: squash (check_gen_elim_nondep_sem i0 i)) ->
  GTot (gen_elim_f
    (compute_gen_elim_p i0)
    (compute_gen_elim_nondep_a i0 i)
    (compute_gen_elim_nondep_q0 i0 i)
    (compute_gen_elim_nondep_post0 i0 i)
  )
  with
  | GEDep -> fun _ -> compute_gen_elim_f i0
  | GENonDep ty q post -> fun _ ->
    let intro : vprop_rewrite (compute_gen_elim_p i0) (gen_elim_nondep_p ty q post) = fun _ ->
      compute_gen_elim_tele_correct i0 _;
      rewrite (tele_p _) (tele_p (gen_elim_nondep_sem ty q post));
      gen_elim_nondep_sem_correct ty q post;
      rewrite_equiv (tele_p _) (gen_elim_nondep_p _ _ _)
    in
    compute_gen_elim_nondep_correct' i0 ty q post intro

let compute_gen_elim_nondep_correct
  (i0: gen_elim_i)
  (i: gen_elim_nondep_t)
  (sq: squash (check_gen_elim_nondep_sem i0 i))
: Tot (gen_elim_f
    (compute_gen_elim_p i0)
    (Ghost.erased (compute_gen_elim_nondep_a i0 i))
    (compute_gen_elim_nondep_q i0 i)
    (compute_gen_elim_nondep_post i0 i)
  )
= fun _ ->
  let res0 = compute_gen_elim_nondep_correct_0 i0 i sq _ in
  let res = Ghost.hide res0 in
  rewrite (compute_gen_elim_nondep_q0 i0 i res0) (compute_gen_elim_nondep_q i0 i res);
  res

let coerce_with_smt (#tfrom #tto: Type) (x: tfrom) : Pure tto (requires ( (tfrom == tto))) (ensures (fun _ -> True)) = x

let gen_elim'
  #opened enable_nondep_opt p a q post _ ()
=
  let (i, j) = gen_elim_prop_elim enable_nondep_opt p a q post in
  rewrite p (compute_gen_elim_p i);
  let res' = compute_gen_elim_nondep_correct i j () _ in
  let res : Ghost.erased a = Ghost.hide (coerce_with_smt (Ghost.reveal res')) in
  rewrite (compute_gen_elim_nondep_q i j res') (guard_vprop (q res));
  res

let gen_elim
  #opened #p #a #q #post #sq _
= gen_elim' #opened _ p a q post sq ()

let gen_elim_dep
  #opened #p #a #q #post #sq _
= gen_elim' #opened _ p a q post sq ()
